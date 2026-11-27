-- Prove2me | solution 1 for HMBinPacking.divisibility_chain_or_one_bin_quadratic_time
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:46:49.690378+00:00
-- url     : https://prove2.me/submissions/352ea018-063d-45ba-8ac8-a92477fc2c19

import Mathlib.Tactic.Linarith
import Definitions.Def_HMBinPacking_OutputsWithin
import Mathlib.Tactic.FinCases
import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Tactic.Ring
import Definitions.Def_HMBinPacking_Instance
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

open Turing

namespace BitStacks

abbrev Mem (K : Type) := K → List Bool

/-- One straight-line, finitely branching stack instruction. Each read sees one bit or EOF. -/
inductive Action (K Λ : Type) where
  | stop (label : Option Λ)
  | peek (k : K) (next : Option Bool → Action K Λ)
  | drop (k : K) (next : Action K Λ)
  | push (k : K) (b : Bool) (next : Action K Λ)

namespace Action
variable {K Λ : Type} [DecidableEq K]

def run : Action K Λ → Mem K → Option Λ × Mem K
  | .stop l, m => (l,m)
  | .peek k f, m => (f (m k).head?).run m
  | .drop k a, m => a.run (Function.update m k (m k).tail)
  | .push k b a, m => a.run (Function.update m k (b::m k))

def compile : Action K Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool)
  | .stop (some l) => .load (fun _ => none) (.goto (fun _ => l))
  | .stop none => .load (fun _ => none) .halt
  | .peek k f => .peek k (fun _ v => v) (.branch Option.isNone (f none).compile
        (.branch (fun v => v.getD false) (f (some true)).compile (f (some false)).compile))
  | .drop k a => .pop k (fun v _ => v) a.compile
  | .push k b a => .push k (fun _ => b) a.compile

theorem correct (a : Action K Λ) (s : Option Bool) (m : Mem K) :
    TM2.stepAux a.compile s m = ⟨(a.run m).1, none, (a.run m).2⟩ := by
  induction a generalizing s m with
  | stop l => cases l <;> rfl
  | drop k a ih => exact ih _ _
  | push k b a ih => exact ih _ _
  | peek k f ih =>
    cases h : (m k).head? with
    | none => simpa [compile,run,TM2.stepAux,h] using ih none none m
    | some b => cases b <;> simp [compile,run,TM2.stepAux,h,ih]

end Action

variable {K Λ : Type} [DecidableEq K] [Fintype K] [Fintype Λ]
/-- An ordinary bundled Mathlib machine, with Boolean alphabets on every stack. -/
def machine (entry : Λ) (io : K) (code : Λ → Action K Λ) : TM2ComputableAux Bool Bool where
  tm := { K := K, k₀ := io, k₁ := io, Γ := fun _ => Bool, Λ := Λ,
          main := entry, σ := Option Bool, initialState := none, m := fun l => (code l).compile }
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

def isolated (k : K) (s : List Bool) : Mem K :=
  (initList (machine () k (fun _ => .stop none)).tm s).stk

/-- Exactly n bit-stack instructions from a live or halted configuration. -/
inductive Path (code : Λ → Action K Λ) : Option Λ → Mem K → ℕ → Option Λ → Mem K → Prop where
  | refl (l m) : Path code l m 0 l m
  | step {l m} : Path code (some l) m 1 ((code l).run m).1 ((code l).run m).2
  | join {a m b n z p k h} : Path code a m k b n → Path code b n h z p → Path code a m (k+h) z p

theorem Path.outputs {entry io code src dst t bound} (h : Path (K:=K) (Λ:=Λ)
    code (some entry) (isolated (K:=K) io src) t none (isolated (K:=K) io dst)) (hb : t ≤ bound) :
    HMBinPacking.OutputsWithin (machine entry io code) src dst bound := by
  let M := machine entry io code
  let c (l m) : M.tm.Cfg := ⟨l,none,m⟩
  have sem {l m j r n} (p : Path code l m j r n) :
      (flip bind M.tm.step)^[j] (some (c l m)) = some (c r n) := by
    induction p with
    | refl => rfl
    | @step l m =>
      change some (TM2.stepAux (code l).compile none m) = _
      rw [Action.correct]; rfl
    | @join _ _ _ _ _ _ k g _ _ a b => rw [Nat.add_comm k g,Function.iterate_add_apply,a,b]
  have init : initList M.tm (src.map M.inputAlphabet.symm) = c (some entry) (isolated (K:=K) io src) := by
    have eqmap : src.map M.inputAlphabet.symm = src := List.map_id _
    rw [eqmap]
    rfl
  have halt : haltList M.tm (dst.map M.outputAlphabet.symm) = c none (isolated (K:=K) io dst) := by
    have eqmap : dst.map M.outputAlphabet.symm = dst := List.map_id _
    rw [eqmap]
    rfl
  refine ⟨⟨⟨t,?_⟩,hb⟩⟩
  change (flip bind M.tm.step)^[t] (some (initList M.tm (src.map M.inputAlphabet.symm))) =
    some (haltList M.tm (dst.map M.outputAlphabet.symm))
  rw [init,halt]; exact sem h

end BitStacks

namespace BitStacks
variable {Q Λ : Type}
open Action

/-- The four public stacks used by a binary transducer. -/
inductive ZipReg | x | y | rx | ry deriving DecidableEq
instance : Fintype ZipReg := ⟨{.x,.y,.rx,.ry}, by intro k; cases k <;> decide⟩
namespace ZipReg
def store (a b c d : List Bool) : Mem ZipReg
  | x => a | y => b | rx => c | ry => d
@[simp] theorem setX (a b c d s : List Bool) : Function.update (store a b c d) x s = store s b c d := by
  funext k; cases k <;> rfl
@[simp] theorem setY (a b c d s : List Bool) : Function.update (store a b c d) y s = store a s c d := by
  funext k; cases k <;> rfl
@[simp] theorem setA (a b c d s : List Bool) : Function.update (store a b c d) rx s = store a b s d := by
  funext k; cases k <;> rfl
@[simp] theorem setB (a b c d s : List Bool) : Function.update (store a b c d) ry s = store a b c s := by
  funext k; cases k <;> rfl
end ZipReg
open ZipReg

/-- A bitwise finite-state transducer. A missing input bit is explicit, so the
two operands need not have equal lengths. -/
structure Gate (Q : Type) where
  onBits : Q → Option Bool → Option Bool → Q × Option Bool × Option Bool
  finish : Q → Option Bool × Option Bool
  returnBit : Q → Bool := fun _ => false
private abbrev Label (Q : Type) := (Fin 4) × Q
private def emit (r : ZipReg) (o : Option Bool) (a : Action ZipReg Λ) :=
  match o with | none => a | some b => Action.push r b a
private def prepend (o : Option Bool) (a : List Bool) := match o with | none => a | some b => b::a

def zipper (g : Gate Q) (l : Label Q) : Action ZipReg (Label Q) :=
  if l.1=0 then
    .peek x (fun a => .peek y (fun b =>
      if a.isNone && b.isNone then
        emit rx (g.finish l.2).1 (emit ry (g.finish l.2).2 (.stop (some (1,l.2))))
      else
        let out := g.onBits l.2 a b
        .drop x (.drop y (emit rx out.2.1 (emit ry out.2.2 (.stop (some (0,out.1))))))))
  else if l.1=1 then
    .peek rx (fun b => match b with
      | none => .stop (some (2,l.2))
      | some d => .drop rx (.push x d (.stop (some (1,l.2)))))
  else if l.1=2 then
    .peek ry (fun b => match b with
      | none => .stop (some (3,l.2))
      | some d => .drop ry (.push y d (.stop (some (2,l.2)))))
  else .push rx (g.returnBit l.2) (.stop none)

private theorem zstep (g : Gate Q) (q : Q) (a b r s : List Bool) (hv : a≠[] ∨ b≠[]) :
    let out := g.onBits q a.head? b.head?
    Path (zipper g) (some (0,q)) (store a b r s) 1 (some (0,out.1))
      (store a.tail b.tail (prepend out.2.1 r) (prepend out.2.2 s)) := by
  have cond : (a.head?.isNone && b.head?.isNone) = false := by
    cases a <;> cases b <;> simp_all
  have h := Path.step (code:=zipper g) (l:=(0,q)) (m:=store a b r s)
  have nonempty : ¬ (a=[] ∧ b=[]) := by tauto
  generalize eqo : g.onBits q a.head? b.head? = o at *
  obtain ⟨q',p,v⟩ := o
  cases p <;> cases v <;>
    simpa [zipper,Action.run,emit,prepend,store,cond,nonempty,eqo] using h

private theorem zend (g : Gate Q) (q : Q) (r s : List Bool) :
    Path (zipper g) (some (0,q)) (store [] [] r s) 1 (some (1,q))
      (store [] [] (prepend (g.finish q).1 r) (prepend (g.finish q).2 s)) := by
  have h := Path.step (code:=zipper g) (l:=(0,q)) (m:=store [] [] r s)
  generalize eqo : g.finish q = o
  obtain ⟨p,v⟩ := o
  cases p <;> cases v <;> simpa [zipper,Action.run,emit,prepend,store,eqo] using h

private theorem restoreX (g : Gate Q) (q : Q) (a b r s : List Bool) :
    Path (zipper g) (some (1,q)) (store a b r s) (r.length+1) (some (2,q))
      (store (r.reverse++a) b [] s) := by
  induction r generalizing a with
  | nil =>
    have h := Path.step (code:=zipper g) (l:=(1,q)) (m:=store a b [] s)
    simpa [zipper,Action.run,store] using h
  | cons z zs ih =>
    have h := Path.step (code:=zipper g) (l:=(1,q)) (m:=store a b (z::zs) s)
    have p : Path (zipper g) (some (1,q)) (store a b (z::zs) s) 1 (some (1,q)) (store (z::a) b zs s) := by
      simpa [zipper,Action.run,store] using h
    have z := p.join (ih (z::a))
    simpa [List.append_assoc,Nat.add_comm 1] using z

private theorem restoreY (g : Gate Q) (q : Q) (a b s : List Bool) :
    Path (zipper g) (some (2,q)) (store a b [] s) (s.length+1) (some (3,q))
      (store a (s.reverse++b) [] []) := by
  induction s generalizing b with
  | nil =>
    have h := Path.step (code:=zipper g) (l:=(2,q)) (m:=store a b [] [])
    simpa [zipper,Action.run,store] using h
  | cons z zs ih =>
    have h := Path.step (code:=zipper g) (l:=(2,q)) (m:=store a b [] (z::zs))
    have p : Path (zipper g) (some (2,q)) (store a b [] (z::zs)) 1 (some (2,q)) (store a (z::b) [] zs) := by
      simpa [zipper,Action.run,store] using h
    simpa [List.append_assoc,Nat.add_comm 1] using p.join (ih (z::b))

def revPre (o : Option Bool) (xs : List Bool) := match o with | none => xs | some b => b::xs

/-- Logical result of running the gate on the two words, from least to most significant
bit. Missing bits are passed as none. -/
def execute (g : Gate Q) : Q → List Bool → List Bool → Q × List Bool × List Bool
  | q, [], [] => (q,revPre (g.finish q).1 [],revPre (g.finish q).2 [])
  | q, bitX::xs, [] =>
    let r := g.onBits q (some bitX) none
    let z := execute g r.1 xs []
    (z.1,revPre r.2.1 z.2.1,revPre r.2.2 z.2.2)
  | q, [], bitY::ys =>
    let r := g.onBits q none (some bitY)
    let z := execute g r.1 [] ys
    (z.1,revPre r.2.1 z.2.1,revPre r.2.2 z.2.2)
  | q, bitX::xs, bitY::ys =>
    let r := g.onBits q (some bitX) (some bitY)
    let z := execute g r.1 xs ys
    (z.1,revPre r.2.1 z.2.1,revPre r.2.2 z.2.2)
termination_by _ xs ys => xs.length+ys.length
decreasing_by all_goals simp_wf <;> omega

private theorem revPre_rev (o : Option Bool) (a r : List Bool) :
    (revPre o a).reverse++r = a.reverse++prepend o r := by
  cases o <;> simp [revPre,prepend,List.append_assoc]

private theorem stream (g : Gate Q) (q : Q) (a b r s : List Bool) :
    let z := execute g q a b
    Path (zipper g) (some (0,q)) (store a b r s) (max a.length b.length+1) (some (1,z.1))
      (store [] [] (z.2.1.reverse++r) (z.2.2.reverse++s)) := by
  match a,b with
  | [],[] =>
    simpa [execute,revPre_rev] using zend g q r s
  | bitX::xs,[] =>
    let o := g.onBits q (some bitX) none
    have p := zstep g q (bitX::xs) [] r s (by simp)
    have t := stream g o.1 xs [] (prepend o.2.1 r) (prepend o.2.2 s)
    simpa [execute,o,revPre_rev,Nat.add_comm 1] using p.join t
  | [],bitY::ys =>
    let o := g.onBits q none (some bitY)
    have p := zstep g q [] (bitY::ys) r s (by simp)
    have t := stream g o.1 [] ys (prepend o.2.1 r) (prepend o.2.2 s)
    simpa [execute,o,revPre_rev,Nat.add_comm 1] using p.join t
  | bitX::xs,bitY::ys =>
    let o := g.onBits q (some bitX) (some bitY)
    have p := zstep g q (bitX::xs) (bitY::ys) r s (by simp)
    have t := stream g o.1 xs ys (prepend o.2.1 r) (prepend o.2.2 s)
    simpa [execute,o,revPre_rev,Nat.add_comm 1] using p.join t
termination_by a.length+b.length
decreasing_by all_goals simp_wf <;> omega

/-- A finite-state column scan runs on an actual compiled TM2. Both output words
are restored to least-significant-bit-first order; no scratch data remains. -/
theorem zipper_path (g : Gate Q) (q : Q) (a b : List Bool) :
    let z := execute g q a b
    Path (zipper g) (some (0,q)) (store a b [] [])
      (max a.length b.length+1+(z.2.1.length+1)+(z.2.2.length+1))
      (some (3,z.1)) (store z.2.1 z.2.2 [] []) := by
  let z := execute g q a b
  have p := stream g q a b [] []
  change Path _ _ _ _ _ (store [] [] (z.2.1.reverse++[]) (z.2.2.reverse++[])) at p
  simp only [List.append_nil] at p
  have s := restoreX g z.1 [] [] z.2.1.reverse z.2.2.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at s
  have t := restoreY g z.1 z.2.1 [] z.2.2.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at t
  exact (p.join s).join t

end BitStacks

namespace BitStacks
variable {Q : Type}
def val : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*val bs

private def digit (a : Option Bool) := (a.getD false).toNat
private def addBits (c : Bool) (a b : Option Bool) :=
  let n := c.toNat+digit a+digit b
  (decide (2 ≤ n), some (decide (n%2=1)), b)

def addGate : Gate Bool := ⟨addBits,fun c => (if c then some true else none,none),id⟩

private def subBits (c : Bool) (a b : Option Bool) :=
  let debt := digit b+c.toNat
  let x := digit a
  (decide (x<debt),some (decide ((x+2-debt)%2=1)),b)

def subGate : Gate Bool := ⟨subBits,fun _ => (none,none),id⟩

private def compareBits (c : Bool) (a b : Option Bool) :=
  let x := a.getD false
  let y := b.getD false
  (if x=y then c else y,a,b)
def compareGate : Gate Bool := ⟨compareBits,fun _ => (none,none),id⟩

private def carryLE (c : Bool) (x y : ℕ) := decide (x<y ∨ x=y ∧ c=true)
private theorem lowLE (c x y : Bool) (a b : ℕ) :
    carryLE (if x=y then c else y) a b = carryLE c (x.toNat+2*a) (y.toNat+2*b) := by
  apply Bool.eq_iff_iff.mpr; cases c <;> cases x <;> cases y <;> simp [carryLE] <;> omega

private abbrev norm := @revPre

private theorem decomp (g : Gate Q) (c : Q) (a b : List Bool) (h : a≠[] ∨ b≠[]) :
    let r := g.onBits c a.head? b.head?
    let z := execute g r.1 a.tail b.tail
    execute g c a b = (z.1,norm r.2.1 z.2.1,norm r.2.2 z.2.2) := by
  cases a <;> cases b <;> first | (solve | simp at h) | rw [execute];rfl

private theorem valH (a : List Bool) : val a = digit a.head? + 2*val a.tail := by
  cases a <;> rfl
private theorem joinHead (a : List Bool) : norm a.head? a.tail = a := by cases a <;> rfl
private theorem lenStep (a b : List Bool) (h : a≠[] ∨ b≠[]) :
    max a.length b.length = max a.tail.length b.tail.length + 1 := by
  cases a <;> cases b <;> simp_all <;> omega

/-- Bit-serial addition preserves its second operand and computes an unbounded
integer sum; its result has at most one extra digit. -/
theorem add_correct (c : Bool) (a b : List Bool) :
    let z := execute addGate c a b
    val z.2.1 = val a+val b+c.toNat ∧ z.2.2=b ∧
      z.2.1.length ≤ max a.length b.length + 1 := by
  by_cases h : a=[] ∧ b=[]
  · obtain ⟨rfl,rfl⟩ := h; cases c <;> simp [execute,addGate,revPre,val]
  · have live : a≠[] ∨ b≠[] := by tauto
    let r := addBits c a.head? b.head?
    have ih := add_correct r.1 a.tail b.tail
    obtain ⟨iv,iw,il⟩ := ih
    have H : r.1.toNat*2+(decide ((c.toNat+digit a.head?+digit b.head?)%2=1)).toNat =
        c.toNat+digit a.head?+digit b.head? := by
      have digitLaw (c : Bool) (x y : Option Bool) :
          (addBits c x y).1.toNat*2+(decide ((c.toNat+digit x+digit y)%2=1)).toNat =
            c.toNat + digit x + digit y := by
        cases c <;> rcases x with _|(_|_) <;> rcases y with _|(_|_) <;> rfl
      exact digitLaw c _ _
    rw [decomp addGate c a b live]
    let low := decide ((c.toNat+digit a.head?+digit b.head?)%2=1)
    let z := execute addGate r.1 a.tail b.tail
    change val (low::z.2.1) = _ ∧ norm b.head? z.2.2=b ∧ (low::z.2.1).length ≤ _
    change val z.2.1 = _ at iv
    change z.2.2 = _ at iw
    change z.2.1.length ≤ _ at il
    change r.1.toNat*2+low.toNat = _ at H
    rw [val,iv,iw,joinHead, valH a,valH b,lenStep _ _ live]
    have h' := Nat.mul_comm r.1.toNat 2
    refine ⟨?_,rfl,?_⟩ <;> (try simp only [List.length_cons]) <;> omega
termination_by a.length+b.length
decreasing_by
  have : a≠[] ∨ b≠[] := by tauto
  cases a <;> cases b <;> simp_all <;> omega

/-- The borrow bit records underflow modulo exactly 2^(max bit length).
This also handles unequal lengths and leading zeroes. -/
theorem sub_correct (c : Bool) (a b : List Bool) :
    let z := execute subGate c a b
    val a+z.1.toNat*2^(max a.length b.length) = val z.2.1+val b+c.toNat ∧
      z.2.2=b ∧ z.2.1.length = max a.length b.length := by
  by_cases h : a=[] ∧ b=[]
  · obtain ⟨rfl,rfl⟩ := h;cases c <;> simp [execute,subGate,revPre,val]
  · have live : a≠[] ∨ b≠[] := by tauto
    let r := subBits c a.head? b.head?
    let low := decide ((digit a.head?+2-(digit b.head?+c.toNat))%2=1)
    let z := execute subGate r.1 a.tail b.tail
    obtain ⟨iv,iw,il⟩ := sub_correct r.1 a.tail b.tail
    have e (c : Bool) (x y : Option Bool) :
          digit x + (subBits c x y).1.toNat*2 =
            (decide ((digit x+2-(digit y+c.toNat))%2=1)).toNat + digit y+c.toNat := by
      cases c <;> rcases x with _|(_|_) <;> rcases y with _|(_|_) <;> rfl
    have H : digit a.head? + r.1.toNat*2 = low.toNat + digit b.head?+c.toNat := e _ _ _
    rw [decomp subGate c a b live]
    change val a+z.1.toNat*2^(max a.length b.length) = val (low::z.2.1)+val b+c.toNat ∧
      norm b.head? z.2.2=b ∧ (low::z.2.1).length = max a.length b.length
    change val a.tail+z.1.toNat*_ = val z.2.1+val b.tail+r.1.toNat at iv
    change z.2.2 = _ at iw
    change z.2.1.length = _ at il
    rw [valH a,valH b,val,iw,joinHead,lenStep _ _ live,pow_succ]
    refine ⟨?_,rfl,by simp [il]⟩
    have doub := congrArg (fun n : ℕ => 2*n) iv
    nlinarith only [H,doub]
termination_by a.length+b.length
decreasing_by
  have : a≠[] ∨ b≠[] := by tauto
  cases a <;> cases b <;> simp_all <;> omega

/-- The order gate returns the comparison in finite control, leaving both register
words unchanged. Starting with true gives the non-strict ordering. -/
theorem cmp_correct (c : Bool) (a b : List Bool) :
    let z := execute compareGate c a b
    z.1 = carryLE c (val a) (val b) ∧ z.2.1=a ∧ z.2.2=b := by
  by_cases h : a=[] ∧ b=[]
  · obtain ⟨rfl,rfl⟩ := h;cases c <;> simp [execute,compareGate,revPre,val,carryLE]
  · have live : a≠[] ∨ b≠[] := by tauto
    let r := compareBits c a.head? b.head?
    let z := execute compareGate r.1 a.tail b.tail
    obtain ⟨iv,ix,iy⟩ := cmp_correct r.1 a.tail b.tail
    rw [decomp compareGate c a b live]
    change z.1 = carryLE c (val a) (val b) ∧ norm a.head? z.2.1 = a ∧ norm b.head? z.2.2 = b
    change z.1 = _ at iv
    change z.2.1 = _ at ix
    change z.2.2 = _ at iy
    rw [ix,iy,joinHead,joinHead,iv,valH a,valH b]
    exact ⟨lowLE c _ _ _ _,rfl,rfl⟩
termination_by a.length+b.length
decreasing_by
  have : a≠[] ∨ b≠[] := by tauto
  cases a <;> cases b <;> simp_all <;> omega

theorem le_correct (a b : List Bool) :
    let z := execute compareGate true a b
    z.1=decide (val a≤val b) ∧ z.2.1=a ∧ z.2.2=b := by
  have h := cmp_correct true a b
  have e : carryLE true (val a) (val b) = decide (val a≤val b) := by
    apply Bool.eq_iff_iff.mpr; simp [carryLE]; omega
  exact ⟨h.1.trans e,h.2⟩

end BitStacks

namespace BitStacks
open Action
variable {K K' Λ Λ' : Type} [DecidableEq K] [DecidableEq K']

/-- Install a hardware operation in a larger finite machine by renaming its
registers injectively and its labels. No additional steps are charged. -/
def Action.rename (r : K ↪ K') (l : Option Λ → Option Λ') : Action K Λ → Action K' Λ'
  | .stop x => .stop (l x)
  | .peek k f => .peek (r k) (fun b => (f b).rename r l)
  | .drop k a => .drop (r k) (a.rename r l)
  | .push k b a => .push (r k) b (a.rename r l)

def Agrees (r : K ↪ K') (m : Mem K) (n : Mem K') : Prop := ∀ k, n (r k) = m k

private theorem sameUpdate (r : K ↪ K') {m n} (h : Agrees r m n) (k : K) (s : List Bool) :
    Agrees r (Function.update m k s) (Function.update n (r k) s) := by
  intro i; by_cases e : i=k
  · subst i; simp
  · rw [Function.update_of_ne e,Function.update_of_ne (r.injective.ne e)]
    exact h i

theorem renameRun (a : Action K Λ) (r : K ↪ K') (l : Option Λ → Option Λ')
    (m : Mem K) (n : Mem K') (h : Agrees r m n) :
    let small := a.run m
    let large := (a.rename r l).run n
    large.1=l small.1 ∧ Agrees r small.2 large.2 ∧
      ∀ k, (∀ j, r j ≠ k) → large.2 k = n k := by
  induction a generalizing m n with
  | stop z => exact ⟨rfl,h,fun _ _ => rfl⟩
  | peek k f ih =>
    simp only [Action.rename,Action.run,h k]
    exact ih _ m n h
  | drop k a ih =>
    obtain ⟨hl,ha,ho⟩ := ih _ _ (sameUpdate r h k (m k).tail)
    simp only [Action.rename,Action.run,h k]
    refine ⟨hl,ha,?_⟩
    intro p hp;rw [ho p hp,Function.update_of_ne (Ne.symm (hp k))]
  | push k b a ih =>
    obtain ⟨hl,ha,ho⟩ := ih _ _ (sameUpdate r h k (b::m k))
    simp only [Action.rename,Action.run,h k]
    refine ⟨hl,ha,?_⟩
    intro p hp; rw [ho p hp,Function.update_of_ne (Ne.symm (hp k))]

/-- A finite trace can be assembled as a subroutine. The caller may replace a
halt by a continuation and every unused caller register is preserved. -/
theorem Path.rename {program : Λ → Action K Λ} {i m t o n}
    (p : Path program i m t o n) (r : K ↪ K') (label : Λ → Λ') (exit : Option Λ')
    (code : Λ' → Action K' Λ')
    (implementation : ∀ j, code (label j) =
      (program j).rename r (fun q => q.elim exit (fun v => some (label v))))
    (before : Mem K') (h : Agrees r m before) :
    ∃ after : Mem K', Path code (i.elim exit (fun v => some (label v))) before t
        (o.elim exit (fun v => some (label v))) after ∧ Agrees r n after ∧
      ∀ k, (∀ j, r j ≠ k) → after k = before k := by
  induction p generalizing before with
  | refl l m => exact ⟨before,Path.refl _ _,h,fun _ _ => rfl⟩
  | @step j m =>
    have info := renameRun (program j) r (fun q => q.elim exit (fun v => some (label v))) m before h
    have st := Path.step (code:=code) (l:=label j) (m:=before)
    rw [implementation] at st
    exact ⟨_,info.1 ▸ st, info.2⟩
  | @join _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
    obtain ⟨middle,p₁,a₁,rest₁⟩ := h₁ _ h
    obtain ⟨after,p₂,a₂,rest₂⟩ := h₂ _ a₁
    exact ⟨after,p₁.join p₂,a₂,fun k hk => (rest₂ k hk).trans (rest₁ k hk)⟩

end BitStacks

namespace BitStacks
variable {R Λ : Type}

/-- Two private work stacks and any finite number of public (Boolean) stacks. -/
abbrev Bank (R : Type) := Bool ⊕ R
def tmp : Bank R := .inl true
def tmp2 : Bank R := .inl false
def reg (i : R) : Bank R := .inr i

inductive BinaryOp | add | sub | le deriving DecidableEq
def BinaryOp.gate : BinaryOp → Gate Bool
  | .add => addGate | .sub => subGate | .le => compareGate
def BinaryOp.initial : BinaryOp → Bool
  | .le => true | _ => false
theorem BinaryOp.ret (s : BinaryOp) (q : Bool) : s.gate.returnBit q = q := by cases s <;> rfl

inductive Macro (R Λ : Type)
  | bits (a : Action (Bank R) Λ)
  | binary (op : BinaryOp) (i j : R) (h : i ≠ j) (next : Λ)

def ports (i j : R) (h : i≠j) : ZipReg ↪ Bank R where
  toFun | .x => reg i | .y => reg j | .rx => tmp | .ry => tmp2
  inj' := by intro x y; cases x <;> cases y <;> simp_all [reg,tmp,tmp2] <;> tauto

abbrev WordLabel (Λ : Type) := Λ ⊕ (Λ × (Fin 4 × Bool))
def wordCode (P : Λ → Macro R Λ) : WordLabel Λ → Action (Bank R) (WordLabel Λ)
  | .inl k => match P k with
    | .bits a => a.rename (Function.Embedding.refl _) (Option.map Sum.inl)
    | .binary op _ _ _ _ => .stop (some (.inr (k,(0,op.initial))))
  | .inr (k,q) => match P k with
    | .bits _ => .stop none
    | .binary op i j h next =>
      (zipper op.gate q).rename (ports i j h)
        (fun z => z.elim (some (.inl next)) (fun s => some (.inr (k,s))))

variable [DecidableEq R]

def afterGate (m : Mem (Bank R)) (i j : R) (z : Bool × List Bool × List Bool) : Mem (Bank R) :=
  Function.update (Function.update (Function.update m (reg i) z.2.1) (reg j) z.2.2) tmp [z.1]

/-- A binary macro has a trace in the exact bit-stack machine; the result/borrow/comparison
is left on tmp, the two public registers are updated and every other register is unchanged. -/
theorem binary_trace (P : Λ → Macro R Λ) (k n : Λ) (op : BinaryOp) (i j : R) (ne : i≠j)
    (ins : P k = .binary op i j ne n) (m : Mem (Bank R)) (ht : m tmp=[]) (hu : m tmp2=[]) :
    let a := m (reg i)
    let b := m (reg j)
    let z := execute op.gate op.initial a b
    Path (wordCode P) (some (.inl k)) m
      (1+(max a.length b.length+1+(z.2.1.length+1)+(z.2.2.length+1)+1))
      (some (.inl n)) (afterGate m i j z) := by
  let a := m (reg i)
  let b := m (reg j)
  let z := execute op.gate op.initial a b
  let r := ports i j ne
  have p := zipper_path op.gate op.initial a b
  have fin := Path.step (code:=zipper op.gate) (l:=(3,z.1))
    (m:=ZipReg.store z.2.1 z.2.2 [] [])
  have e : Path (zipper op.gate) (some (3,z.1)) (ZipReg.store z.2.1 z.2.2 [] []) 1 none
      (ZipReg.store z.2.1 z.2.2 [z.1] []) := by
    simpa [zipper,Action.run,ZipReg.store,BinaryOp.ret] using fin
  have x := p.join e
  let label (s : Fin 4 × Bool) : WordLabel Λ := .inr (k,s)
  have sub : ∀ l, wordCode P (label l) =
      (zipper op.gate l).rename r (fun q => q.elim (some (.inl n)) (fun v => some (label v))) := by
    intro l; simp [wordCode,label,ins,r]
  have start : Agrees r (ZipReg.store a b [] []) m := by
    intro j; cases j <;> first | rfl | exact ht | exact hu
  obtain ⟨v,trace,agrees,outside⟩ := x.rename r label (some (.inl n)) (wordCode P) sub m start
  have eqout : v=afterGate m i j z := by
    funext s
    cases s with
    | inl c =>
      cases c with
      | true =>
        have vv := agrees ZipReg.rx
        simpa [afterGate,tmp,reg,r,ports,ZipReg.store] using vv
      | false =>
        have vv := agrees ZipReg.ry
        change v tmp2 = _; simp [afterGate,tmp,tmp2,reg] at *; exact vv.trans hu.symm
    | inr k =>
      by_cases ki : k=i
      · subst k; have vv := agrees ZipReg.x
        simpa [afterGate,reg,tmp,ne,r,ports,ZipReg.store] using vv
      · by_cases kj : k=j
        · subst k; have vv := agrees ZipReg.y
          simpa [afterGate,reg,tmp,r,ports,ZipReg.store] using vv
        · have all : ∀ p, r p ≠ .inr k := by
            intro p; cases p <;> simp_all [r,ports,reg,tmp,tmp2,Ne.symm]
          simpa [afterGate,reg,tmp,ki,kj] using outside _ all
  have step := Path.step (code:=wordCode P) (l:=.inl k) (m:=m)
  have beginP : Path (wordCode P) (some (.inl k)) m 1 (some (label (0,op.initial))) m := by
    simpa [wordCode,ins,Action.run,label] using step
  rw [eqout] at trace
  exact beginP.join trace

end BitStacks

namespace BitStacks
variable {R Λ : Type} [DecidableEq R]
def gateResult (op : BinaryOp) (m : Mem (Bank R)) (i j : R) :=
  execute op.gate op.initial (m (reg i)) (m (reg j))
def gateTime (op : BinaryOp) (m : Mem (Bank R)) (i j : R) :=
  let z := gateResult op m i j
  1+(max (m (reg i)).length (m (reg j)).length+1+(z.2.1.length+1)+(z.2.2.length+1)+1)
inductive MacroPath (P : Λ → Macro R Λ) :
    Option Λ → Mem (Bank R) → ℕ → Option Λ → Mem (Bank R) → Prop where
  | refl (l m) : MacroPath P l m 0 l m
  | bits {l m a} (ins : P l = .bits a) : MacroPath P (some l) m 1 (a.run m).1 (a.run m).2
  | binary {l} {m : Mem (Bank R)} {op i j h n} (ins : P l=.binary op i j h n) (hx : m tmp=[]) (hy : m tmp2=[]) :
      MacroPath P (some l) m (gateTime op m i j) (some n) (afterGate m i j (gateResult op m i j))
  | join {l m n a k b t u} : MacroPath P l m t n a → MacroPath P n a u k b →
      MacroPath P l m (t+u) k b

theorem MacroPath.sound {P : Λ → Macro R Λ} {l m n a t} (h : MacroPath P l m t n a) :
    Path (wordCode P) (l.map Sum.inl) m t (n.map Sum.inl) a := by
  induction h with
  | refl l m => exact Path.refl _ _
  | join _ _ a b => exact a.join b
  | binary ins hx hy => exact binary_trace _ _ _ _ _ _ _ ins _ hx hy
  | @bits l m a ins =>
    have p := Path.step (code:=wordCode P) (l:=.inl l) (m:=m)
    have e := renameRun a (Function.Embedding.refl _) (Option.map (@Sum.inl Λ (Λ × (Fin 4 × Bool))))
      m m (fun _ => rfl)
    have eqn : ((a.rename (Function.Embedding.refl _) (Option.map (@Sum.inl Λ (Λ × (Fin 4 × Bool))))).run m).2 =
        (a.run m).2 := funext (fun k => e.2.1 k)
    simp only [wordCode,ins] at p
    rw [eqn,e.1] at p
    exact p

theorem MacroPath.outputs [Fintype R] [Fintype Λ] {P : Λ → Macro R Λ} {l : Λ} {io : Bank R}
    {a b : List Bool} {t T : ℕ}
    (h : MacroPath P (some l) (isolated io a) t none (isolated io b)) (bound : t≤T) :
    HMBinPacking.OutputsWithin (machine (Sum.inl l) io (wordCode P)) a b T :=
  h.sound.outputs bound
end BitStacks

namespace BitStacks
variable {R Λ J : Type} [DecidableEq R]
def Macro.mapLabels (f : Λ → J) : Macro R Λ → Macro R J
  | .bits a => .bits (a.rename (Function.Embedding.refl _) (Option.map f))
  | .binary op i j h n => .binary op i j h (f n)
theorem MacroPath.mapLabels {P : Λ → Macro R Λ} {Q : J → Macro R J} (f : Λ → J)
    (link : ∀ l, Q (f l)=(P l).mapLabels f) {i m t o n} (p : MacroPath P i m t o n) :
    MacroPath Q (i.map f) m t (o.map f) n := by
  induction p with
  | refl l m => exact .refl _ _
  | join _ _ a b => exact a.join b
  | @binary l m op i j h n inst x y =>
    exact MacroPath.binary (show Q (f l)=_ by rw [link,inst];rfl) x y
  | @bits l m a ins =>
    have h := MacroPath.bits (P:=Q) (l:=f l) (m:=m) (a:=a.rename (Function.Embedding.refl _) (Option.map f))
      (by rw [link,ins];rfl)
    have e := renameRun a (Function.Embedding.refl _) (Option.map f) m m (fun _ => rfl)
    have em : ((a.rename (Function.Embedding.refl _) (Option.map f)).run m).2=(a.run m).2 :=
      funext (fun k => e.2.1 k)
    simpa [e.1,em] using h
end BitStacks

namespace OneTypeTM
open BitStacks 
inductive R | tape | rem | den | bins | items | prod | first | second | rev | width | dim deriving DecidableEq
open R
instance : Fintype R := ⟨{tape,rem,den,bins,items,prod,first,second,rev,width,dim},by intro r;cases r <;> decide⟩
abbrev L := (Fin 3 × Fin 5) ⊕ (Fin 10 ⊕ Fin 10)
def H (p : Fin 5) : L := .inl (0,p)
def D (p : Fin 5) : L := .inl (1,p)
def V (p : Fin 5) : L := .inl (2,p)
def A (j : Fin 10) : L := .inr (.inl j)
def C (j : Fin 10) : L := .inr (.inr j)
def dest (p : Fin 5) : R := match p.val with | 0 => rem | 1 => dim | 2 => den | 3 => items | _ => bins
def cleanup (j : Fin 10) : R := match j.val with
  | 0 => rem | 1 => den | 2 => bins | 3 => items | 4 => prod
  | 5 => first | 6 => second | 7 => rev | 8 => width | _ => dim
def jump (l : L) : Action (Bank R) L := .stop (some l)
def next (p : Fin 5) := if p=4 then A 0 else H (p+1)
def code : L → Macro R L
  | .inl (tag,p) =>
    if tag=0 then .bits (.peek (reg tape) (fun v =>
      .drop (reg tape) (if v.getD false then
        .push (reg width) true (if p=0 then .push (reg first) true (.push (reg second) true (jump (H p)))
                                 else jump (H p))
        else jump (D p))))
    else if tag=1 then .bits (.peek (reg width) (fun v => if v.isSome then
      .drop (reg width) (.peek (reg tape) (fun b => .drop (reg tape)
        (.push (reg rev) (b.getD false) (jump (D p))))) else jump (V p)))
    else .bits (.peek (reg rev) (fun b => match b with
      | none => jump (next p) | some bit => .drop (reg rev) (.push (reg (dest p)) bit (jump (V p)))))
  | .inr (.inl j) => match j.val with
    | 0 => .bits (.peek (reg first) (fun b => if b.isSome then
              .drop (reg first) (.push (reg den) false (jump (A 0))) else jump (A 1)))
    | 1 => .bits (.peek (reg second) (fun b => if b.isSome then
              .drop (reg second) (.push (reg rem) false (.push (reg prod) false (jump (A 2))))
              else jump (A 8)))
    | 2 => .binary .le den rem (by decide) (A 3)
    | 3 => .bits (.peek tmp (fun b => .drop tmp (jump (if b.getD false then A 4 else A 1))))
    | 4 => .binary .sub rem den (by decide) (A 5)
    | 5 => .bits (.drop tmp (jump (A 6)))
    | 6 => .binary .add prod bins (by decide) (A 7)
    | 7 => .bits (.drop tmp (jump (A 1)))
    | 8 => .binary .le items prod (by decide) (A 9)
    | _ => .bits (.peek tmp (fun b => .drop tmp (.push (reg tape) (b.getD false) (jump (C 0)))))
  | .inr (.inr j) => .bits (.peek (reg (cleanup j)) (fun v => if v.isSome then
        .drop (reg (cleanup j)) (jump (C j)) else if j=9 then .stop none else jump (C (j+1))))

def machine := BitStacks.machine (.inl (H 0)) (reg tape) (wordCode code)

structure Cells where
  input : List Bool := []
  remainder : List Bool := []
  divisor : List Bool := []
  binCount : List Bool := []
  itemCount : List Bool := []
  product : List Bool := []
  prep : List Bool := []
  todo : List Bool := []
  reversed : List Bool := []
  scratch : List Bool := []
  dimension : List Bool := []
  flag : List Bool := []
  spare : List Bool := []

def Cells.mem (s : Cells) : Mem (Bank R)
  | .inl true => s.flag | .inl false => s.spare
  | .inr .tape => s.input | .inr .rem => s.remainder | .inr .den => s.divisor
  | .inr .bins => s.binCount | .inr .items => s.itemCount | .inr .prod => s.product
  | .inr .first => s.prep | .inr .second => s.todo | .inr .rev => s.reversed
  | .inr .width => s.scratch | .inr .dim => s.dimension
@[simp] theorem Cells.get_input (s : Cells) : s.mem (reg R.tape) = s.input := rfl
@[simp] theorem Cells.get_remainder (s : Cells) : s.mem (reg R.rem) = s.remainder := rfl
@[simp] theorem Cells.get_divisor (s : Cells) : s.mem (reg R.den) = s.divisor := rfl
@[simp] theorem Cells.get_binCount (s : Cells) : s.mem (reg R.bins) = s.binCount := rfl
@[simp] theorem Cells.get_itemCount (s : Cells) : s.mem (reg R.items) = s.itemCount := rfl
@[simp] theorem Cells.get_product (s : Cells) : s.mem (reg R.prod) = s.product := rfl
@[simp] theorem Cells.get_prep (s : Cells) : s.mem (reg R.first) = s.prep := rfl
@[simp] theorem Cells.get_todo (s : Cells) : s.mem (reg R.second) = s.todo := rfl
@[simp] theorem Cells.get_reversed (s : Cells) : s.mem (reg R.rev) = s.reversed := rfl
@[simp] theorem Cells.get_scratch (s : Cells) : s.mem (reg R.width) = s.scratch := rfl
@[simp] theorem Cells.get_dimension (s : Cells) : s.mem (reg R.dim) = s.dimension := rfl
@[simp] theorem Cells.get_flag (s : Cells) : s.mem tmp = s.flag := rfl
@[simp] theorem Cells.get_spare (s : Cells) : s.mem tmp2 = s.spare := rfl

@[simp] theorem Cells.up_input (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.tape) v = ({s with input:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_remainder (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.rem) v = ({s with remainder:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_divisor (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.den) v = ({s with divisor:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_binCount (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.bins) v = ({s with binCount:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_itemCount (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.items) v = ({s with itemCount:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_product (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.prod) v = ({s with product:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_prep (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.first) v = ({s with prep:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_todo (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.second) v = ({s with todo:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_reversed (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.rev) v = ({s with reversed:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_scratch (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.width) v = ({s with scratch:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_dimension (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.dim) v = ({s with dimension:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_flag (s : Cells) (v : List Bool) :
    Function.update s.mem tmp v = ({s with flag:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_spare (s : Cells) (v : List Bool) :
    Function.update s.mem tmp2 v = ({s with spare:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl

abbrev Goes (l : L) (s : Cells) (t : ℕ) (l' : Option L) (z : Cells) :=
  MacroPath code (some l) s.mem t l' z.mem

end OneTypeTM

namespace OneTypeTM
open BitStacks R
def atClear (j : Fin 10) (s : Cells) : List Bool := match j.val with
  | 0 => s.remainder
  | 1 => s.divisor
  | 2 => s.binCount
  | 3 => s.itemCount
  | 4 => s.product
  | 5 => s.prep
  | 6 => s.todo
  | 7 => s.reversed
  | 8 => s.scratch
  | _ => s.dimension
def setClear (j : Fin 10) (w : List Bool) (s : Cells) : Cells := match j.val with
  | 0 => {s with remainder:=w}
  | 1 => {s with divisor:=w}
  | 2 => {s with binCount:=w}
  | 3 => {s with itemCount:=w}
  | 4 => {s with product:=w}
  | 5 => {s with prep:=w}
  | 6 => {s with todo:=w}
  | 7 => {s with reversed:=w}
  | 8 => {s with scratch:=w}
  | _ => {s with dimension:=w}

def nextClear (j : Fin 10) : Option L := if j=9 then none else some (C (j+1))

theorem clearStep (j : Fin 10) (w : List Bool) (s : Cells) :
    Goes (C j) (setClear j w s) (w.length+1) (nextClear j) (setClear j [] s) := by
  induction w with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=C j) (m:=(setClear j [] s).mem) (a:=_) (by rfl)
    fin_cases j <;> simpa [code,C,cleanup,setClear,Action.run,jump,nextClear] using e
  | cons b bs ih =>
    have e := MacroPath.bits (P:=code) (l:=C j) (m:=(setClear j (b::bs) s).mem) (a:=_) (by rfl)
    have step : Goes (C j) (setClear j (b::bs) s) 1 (C j) (setClear j bs s) := by
      fin_cases j <;> simpa [code,C,cleanup,setClear,Action.run,jump] using e
    simpa [Nat.add_comm 1] using step.join ih

def costClear (s : Cells) :=
  s.remainder.length + s.divisor.length + s.binCount.length + s.itemCount.length + s.product.length + s.prep.length + s.todo.length + s.reversed.length + s.scratch.length + s.dimension.length + 11

theorem finish (s : Cells) (b : Bool) (hi : s.input=[]) (hflag : s.flag=[b]) (hsp : s.spare=[]) :
    Goes (A 9) s (costClear s) none ({input:=[b]} : Cells) := by
  have e := MacroPath.bits (P:=code) (l:=A 9) (m:=s.mem) (a:=_) (by rfl)
  let m0 := {s with input:=[b],flag:=[]}
  have p0 : Goes (A 9) s 1 (C 0) m0 := by
    simpa [m0,code,A,Action.run,jump,hi,hflag] using e
  let m1 := {m0 with remainder:=[]}
  have p1 : Goes (C 0) m0 (s.remainder.length+1) (C 1) m1 := clearStep 0 _ m0
  let m2 := {m1 with divisor:=[]}
  have p2 : Goes (C 1) m1 (s.divisor.length+1) (C 2) m2 := clearStep 1 _ m1
  let m3 := {m2 with binCount:=[]}
  have p3 : Goes (C 2) m2 (s.binCount.length+1) (C 3) m3 := clearStep 2 _ m2
  let m4 := {m3 with itemCount:=[]}
  have p4 : Goes (C 3) m3 (s.itemCount.length+1) (C 4) m4 := clearStep 3 _ m3
  let m5 := {m4 with product:=[]}
  have p5 : Goes (C 4) m4 (s.product.length+1) (C 5) m5 := clearStep 4 _ m4
  let m6 := {m5 with prep:=[]}
  have p6 : Goes (C 5) m5 (s.prep.length+1) (C 6) m6 := clearStep 5 _ m5
  let m7 := {m6 with todo:=[]}
  have p7 : Goes (C 6) m6 (s.todo.length+1) (C 7) m7 := clearStep 6 _ m6
  let m8 := {m7 with reversed:=[]}
  have p8 : Goes (C 7) m7 (s.reversed.length+1) (C 8) m8 := clearStep 7 _ m7
  let m9 := {m8 with scratch:=[]}
  have p9 : Goes (C 8) m8 (s.scratch.length+1) (C 9) m9 := clearStep 8 _ m8
  let m10 := {m9 with dimension:=[]}
  have p10 : Goes (C 9) m9 (s.dimension.length+1) none m10 := clearStep 9 _ m9
  have path := ((((((((((p0.join p1).join p2).join p3).join p4).join p5).join p6).join p7).join p8).join p9).join p10)
  have final : m10 = ({input:=[b]} : Cells) := by simp [m10,m9,m8,m7,m6,m5,m4,m3,m2,m1,m0,hsp]
  rw [final] at path
  convert path using 1 <;> simp [costClear] <;> omega
end OneTypeTM

namespace WeightedTM
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
abbrev L := OneTypeTM.L ⊕ ((Fin 3 × Fin 5) ⊕ (Fin 13 ⊕ (Bool × Fin 4)))
def old (l : OneTypeTM.L) : L := .inl l
def H (p : Fin 5) : L := .inr (.inl (0,p))
def D (p : Fin 5) : L := .inr (.inl (1,p))
def V (p : Fin 5) : L := .inr (.inl (2,p))
def A (j : Fin 13) : L := .inr (.inr (.inl j))
def M (right : Bool) (j : Fin 4) : L := .inr (.inr (.inr (right,j)))
def jump (l : L) : Action (Bank R) L := .stop (some l)
def next (p : Fin 5) : L := match p.val with
 | 0 => H 1 | 1 => A 0 | 2 => A 3 | 3 => A 7 | _ => M false 0
def src (p : Fin 5) : R := if p=4 then first else tape
def dest (p : Fin 5) : R := match p.val with | 0 => rem | 1 => dim | 3 => bins | _ => den
def factor (right : Bool) : R := if right then rem else den
def accum (right : Bool) : R := if right then prod else items
def code : L → Macro R L
  | .inl l => (OneTypeTM.code l).mapLabels old
  | .inr (.inl (tag,p)) =>
    if tag=0 then .bits (.peek (reg (src p)) (fun v =>
      .drop (reg (src p)) (if v.getD false then .push (reg width) true (jump (H p)) else jump (D p))))
    else if tag=1 then .bits (.peek (reg width) (fun v => if v.isSome then
      .drop (reg width) (.peek (reg (src p)) (fun b => .drop (reg (src p))
        (.push (reg rev) (b.getD false) (jump (D p))))) else jump (V p)))
    else .bits (.peek (reg rev) (fun b => match b with
      | none => jump (next p) | some bit => .drop (reg rev) (if p=2 then jump (V p)
        else .push (reg (dest p)) bit (jump (V p)))))
  | .inr (.inr (.inl j)) => match j.val with
    | 0 => .bits (.peek (reg tape) (fun v => match v with
         | none => jump (A 1) | some b => .drop (reg tape) (.push (reg second) b (jump (A 0)))))
    | 1 => .bits (.peek (reg second) (fun v => match v with
         | none => .push (reg den) true (jump (H 2))
         | some b => .drop (reg second) (.push (reg tape) b (.push (reg first) b (jump (A 1))))))
    | 3 => .binary .sub dim den (by decide) (A 4)
    | 4 => .bits (.drop tmp (jump (A 5)))
    | 5 => .binary .le dim prod (by decide) (A 6)
    | 6 => .bits (.peek tmp (fun b => .drop tmp (if b.getD false then .drop (reg den) (jump (H 3)) else jump (H 2))))
    | 7 => .bits (.peek (reg tape) (fun b => if b.isSome then jump (H 4) else jump (M true 0)))
    | 8 => .bits (.peek (reg bins) (fun b => if b.isSome then .drop (reg bins) (jump (A 8)) else jump (H 3)))
    | _ => .binary .le items prod (by decide) (old (OneTypeTM.A 9))
  | .inr (.inr (.inr (right,j))) => match j.val with
    | 0 => .bits (.peek (reg (factor right)) (fun b => match b with
           | none => jump (if right then A 9 else A 8)
           | some x => .drop (reg (factor right)) (jump (if x then M right 1 else M right 3))))
    | 1 => .binary .add (accum right) bins (by cases right <;> decide) (M right 2)
    | 2 => .bits (.drop tmp (jump (M right 3)))
    | _ => .bits (.push (reg bins) false (jump (M right 0)))
def machine := BitStacks.machine (.inl (H 0)) (reg tape) (wordCode code)
abbrev Goes (l : L) (s : Cells) (t : ℕ) (o : Option L) (z : Cells) :=
  MacroPath code (some l) s.mem t o z.mem
def Runs (l : L) (s : Cells) (bound : ℕ) (out : Option L) (t : Cells) : Prop := ∃ n ≤ bound, Goes l s n out t
theorem Runs.mono {i s a o t b} (h : Runs i s a o t) (le : a≤b) : Runs i s b o t := by
  obtain ⟨n,u,v⟩:=h; exact ⟨n,u.trans le,v⟩
theorem Runs.seq {i s a j t b k v} (h : Runs i s a (some j) t) (q : Runs j t b k v) : Runs i s (a+b) k v := by
  obtain ⟨n,u,x⟩:=h;obtain ⟨m,z,y⟩:=q;exact ⟨n+m,Nat.add_le_add u z,x.join y⟩
theorem smallRun {i s t o z} (h : Goes i s t o z) : Runs i s t o z := ⟨t,le_rfl,h⟩
end WeightedTM

open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
namespace WeightedTM
open OneTypeTM (Cells R)
open OneTypeTM.R

def putWord (p : Fin 5) (w : List Bool) (m : Cells) : Cells := match p.val with
  | 0 => {m with remainder:=w++m.remainder} | 1 => {m with dimension:=w++m.dimension}
  | 2 => m | 3 => {m with binCount:=w++m.binCount} | _ => {m with divisor:=w++m.divisor}

def putInput (p : Fin 5) (w : List Bool) (m : Cells) : Cells :=
  if p=4 then {m with prep:=w} else {m with input:=w}

private theorem HT (p : Fin 5) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (true::bs) m) 1 (H p)
      (putInput p bs {m with scratch:=true::m.scratch}) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (true::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,putInput,src,Action.run,jump] using e

private theorem HF (p : Fin 5) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (false::bs) m) 1 (D p) (putInput p bs m) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (false::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,D,putInput,src,Action.run,jump] using e

private theorem header (p : Fin 5) (k : ℕ) (m : Cells) (t : List Bool) :
    Goes (H p) (putInput p (List.replicate k true ++ false::t) m) (k+1) (D p)
      (putInput p t {m with scratch:=List.replicate k true++m.scratch}) := by
  induction k generalizing m with
  | zero => simpa using HF p m t
  | succ k ih =>
    have st := HT p m (List.replicate k true ++ false::t)
    have eqc (c : List Bool) : List.replicate k true ++ true::c = true::(List.replicate k true ++ c) := by
      calc
        _ = (List.replicate k true ++ [true])++c := by simp
        _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
    have e := st.join (ih {m with scratch:=true::m.scratch})
    simpa [List.replicate_succ,eqc,Nat.add_comm 1] using e

private theorem DT (p : Fin 5) (m : Cells) (b : Bool) (t c : List Bool) :
    Goes (D p) (putInput p (b::t) {m with scratch:=true::c}) 1 (D p)
      (putInput p t {m with scratch:=c,reversed:=b::m.reversed}) := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=(putInput p (b::t) {m with scratch:=true::c}).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,D,putInput,src,Action.run,jump] using e
private theorem DF (p : Fin 5) (m : Cells) :
    Goes (D p) {m with scratch:=[]} 1 (V p) {m with scratch:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=({m with scratch:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,D,V,Action.run,jump] using e

private theorem digits (p : Fin 5) (bs t : List Bool) (m : Cells) :
    Goes (D p) (putInput p (bs++t) {m with scratch:=List.replicate bs.length true})
      (bs.length+1) (V p) (putInput p t {m with scratch:=[],reversed:=bs.reverse++m.reversed}) := by
  induction bs generalizing m with
  | nil =>
    have f := DF p (putInput p t m)
    fin_cases p <;> simpa [putInput] using f
  | cons b bs ih =>
    have st := DT p m b (bs++t) (List.replicate bs.length true)
    have z := st.join (ih {m with reversed:=b::m.reversed})
    simpa [List.replicate_succ,List.append_assoc,Nat.add_comm 1] using z

private theorem VT (p : Fin 5) (m : Cells) (b : Bool) (r : List Bool) :
    Goes (V p) {m with reversed:=b::r} 1 (V p) (putWord p [b] {m with reversed:=r}) := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=b::r}:Cells).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,V,Action.run,jump,putWord,dest] using e

private theorem VF (p : Fin 5) (m : Cells) :
    Goes (V p) {m with reversed:=[]} 1 (next p) {m with reversed:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,V,Action.run,jump] using e

private theorem backwards (p : Fin 5) (bs : List Bool) (m : Cells) :
    Goes (V p) {m with reversed:=bs} (bs.length+1) (next p) (putWord p bs.reverse {m with reversed:=[]}) := by
  induction bs generalizing m with
  | nil => fin_cases p <;> simpa [putWord] using VF _ m
  | cons b bs ih =>
    have st := VT p m b bs
    have t := ih (putWord p [b] m)
    fin_cases p <;> simp [putWord] at st t ⊢ <;>
      first | simpa [List.append_assoc,Nat.add_comm 1] using st.join t

theorem field (p : Fin 5) (n : ℕ) (t : List Bool) (m : Cells) (hs : m.scratch=[]) (hr : m.reversed=[]) :
    Goes (H p) (putInput p (encodeNat n++t) m) (3*(n.bits.length+1)) (next p)
      (putWord p n.bits (putInput p t m)) := by
  have h := header p n.bits.length m (n.bits++t)
  have d := digits p n.bits t m
  have r := backwards p n.bits.reverse (putInput p t m)
  fin_cases p <;> simp [putInput,hs,hr] at h d r ⊢ <;>
    have z := (h.join d).join r <;>
    simpa [encodeNat,List.append_assoc,Nat.mul_comm,Nat.mul_add,Nat.mul_succ,Nat.add_assoc,hs,hr] using z

end WeightedTM

namespace WeightedTM
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks

private theorem sweep (xs : List Bool) (s : Cells) :
    Goes (A 0) {s with input:=xs} (xs.length+1) (A 1) {s with input:=[],todo:=xs.reverse++s.todo} := by
  induction xs generalizing s with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using e
  | cons b xs ih =>
    have e := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=b::xs}:Cells).mem) (a:=_) (by rfl)
    have p : Goes (A 0) {s with input:=b::xs} 1 (A 0) {s with input:=xs,todo:=b::s.todo} := by
      simpa [code,A,Action.run,jump] using e
    have tr := p.join (ih {s with todo:=b::s.todo})
    simpa [List.append_assoc,Nat.add_comm 1] using tr

private theorem restore (xs : List Bool) (s : Cells) :
    Goes (A 1) {s with todo:=xs} (xs.length+1) (H 2)
      {s with todo:=[],input:=xs.reverse++s.input,prep:=xs.reverse++s.prep,divisor:=true::s.divisor} := by
  induction xs generalizing s with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=A 1) (m:=({s with todo:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using e
  | cons b xs ih =>
    have e := MacroPath.bits (P:=code) (l:=A 1) (m:=({s with todo:=b::xs}:Cells).mem) (a:=_) (by rfl)
    have p : Goes (A 1) {s with todo:=b::xs} 1 (A 1) {s with todo:=xs,input:=b::s.input,prep:=b::s.prep} := by
      simpa [code,A,Action.run,jump] using e
    have tr := p.join (ih {s with input:=b::s.input,prep:=b::s.prep})
    simpa [List.append_assoc,Nat.add_comm 1] using tr

theorem duplicate (s : Cells) (h : s.todo=[]) (p : s.prep=[]) :
    Goes (A 0) s (2*(s.input.length+1)) (H 2) {s with prep:=s.input,divisor:=true::s.divisor} := by
  have a := sweep s.input s
  have b := restore s.input.reverse {s with input:=[]}
  simp [h,p] at a b
  have total := a.join b
  cases s; simp_all [two_mul]
end WeightedTM

namespace WeightedTM
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
private theorem val_small (w : List Bool) : val w < 2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih => cases b <;> simp [val,pow_succ] <;> omega

theorem decrement (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true])
    (n : ℕ) (v : val s.dimension=n+1) :
    ∃ d : List Bool, Runs (A 3) s (3*(s.dimension.length+1)+8) (A 5) {s with dimension:=d,flag:=[]} ∧
      val d=n ∧ d.length ≤ max s.dimension.length 1 := by
  have e := MacroPath.binary (P:=code) (l:=A 3) (m:=s.mem) (op:=.sub) (i:=dim) (j:=den)
    (h:=by decide) (n:=A 4) (by rfl) f sp
  let z := execute subGate false s.dimension s.divisor
  obtain ⟨eq,right,len⟩ := sub_correct false s.dimension s.divisor
  change val s.dimension+z.1.toNat*2^(max s.dimension.length s.divisor.length)=val z.2.1+val s.divisor+0 at eq
  change z.2.2=_ at right;change z.2.1.length=_ at len
  have one : val s.divisor=1 := by rw [a];rfl
  have value : val z.2.1=n := by
    have sm := val_small z.2.1
    rw [len] at sm
    cases h : z.1 <;> rw [h,one,v] at eq <;> simp at eq <;> omega
  have zl : gateResult .sub s.mem dim den = z := rfl
  let mid := {s with dimension:=z.2.1,flag:=[z.1]}
  have gate : Goes (A 3) s (gateTime .sub s.mem dim den) (A 4) mid := by simpa [zl,afterGate,mid,right] using e
  have step := MacroPath.bits (P:=code) (l:=A 4) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 4) mid 1 (A 5) {s with dimension:=z.2.1,flag:=[]} := by simpa [mid,code,A,Action.run,jump] using step
  refine ⟨z.2.1,⟨_,?_,gate.join pop⟩,value,by simpa [a] using len.le⟩
  simp [gateTime,zl,right,len,a]; omega

theorem testDim (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true]) (prod0 : s.product=[]) :
    Runs (A 5) s (3*s.dimension.length+7)
      (if val s.dimension=0 then H 3 else H 2)
      {s with divisor:=if val s.dimension=0 then [] else s.divisor,flag:=[]} := by
  have e := MacroPath.binary (P:=code) (l:=A 5) (m:=s.mem) (op:=.le) (i:=dim) (j:=prod)
    (h:=by decide) (n:=A 6) (by rfl) f sp
  let z := execute compareGate true s.dimension s.product
  obtain ⟨ans,left,right⟩ := le_correct s.dimension s.product
  change z.1=_ at ans; change z.2.1=_ at left; change z.2.2=_ at right
  have zl : gateResult .le s.mem dim prod = z := rfl
  let mid := {s with flag:=[z.1]}
  have gate : Goes (A 5) s (gateTime .le s.mem dim prod) (A 6) mid := by simpa [zl,afterGate,mid,left,right] using e
  have step := MacroPath.bits (P:=code) (l:=A 6) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 6) mid 1 (if val s.dimension=0 then H 3 else H 2)
      {s with divisor:=if val s.dimension=0 then [] else s.divisor,flag:=[]} := by
    by_cases c : val s.dimension=0 <;> simpa [mid,code,A,Action.run,jump,ans,prod0,val,c,a] using step
  refine ⟨_,?_,gate.join pop⟩
  simp [gateTime,zl,left,right,prod0]; omega


end WeightedTM

namespace WeightedTM
open OneTypeTM (Cells R)
open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)

def words (xs : List ℕ) := xs.flatMap encodeNat
@[simp] theorem words_nil : words []=[] := rfl
@[simp] theorem words_cons (x : ℕ) (xs : List ℕ) : words (x::xs)=encodeNat x++words xs := rfl
theorem bits_lt (x : ℕ) : x.bits.length+1 ≤ (encodeNat x).length := by simp [encodeNat]
theorem count_words (xs : List ℕ) : xs.length≤(words xs).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp; have := bits_lt x;omega
theorem val_bits (n : ℕ) : val n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit _ _ h,val,ih,Nat.bit_val]; omega

def headState (B d : ℕ) (rest : List Bool) : Cells :=
  {input:=rest,prep:=rest,remainder:=B.bits,dimension:=d.bits,divisor:=[true]}

theorem head (B d : ℕ) (rest : List Bool) :
    Goes (H 0) ({input:=encodeNat B++(encodeNat d++rest)}:Cells)
      (3*(B.bits.length+1)+3*(d.bits.length+1)+2*(rest.length+1)) (H 2) (headState B d rest) := by
  let m0 : Cells := {}
  let m1 := putWord 0 B.bits (putInput 0 (encodeNat d++rest) m0)
  let m2 := putWord 1 d.bits (putInput 1 rest m1)
  have a := field 0 B (encodeNat d++rest) m0 rfl rfl
  have b := field 1 d rest m1 rfl rfl
  have c := duplicate m2 rfl rfl
  have p := (a.join b).join c
  simpa [m0,m1,m2,next,putWord,putInput,headState] using p
theorem sizes (xs : List ℕ) (tail : List Bool) (s : Cells) (K : ℕ) (hk : 1≤K)
    (d : val s.dimension=xs.length+1) (size : s.dimension.length≤K)
    (inp : s.input=words xs++tail) (len : (words xs).length≤K) (it : s.divisor=[true])
    (f : s.flag=[]) (sp : s.spare=[]) (p : s.product=[]) (hs : s.scratch=[]) (hr : s.reversed=[]) :
    ∃ ds : List Bool, Runs (A 3) s ((xs.length+1)*(20*(K+1))) (H 3)
      {s with dimension:=ds,input:=tail,divisor:=[],flag:=[]} ∧ ds.length≤K := by
  induction xs generalizing s with
  | nil =>
    obtain ⟨ds,dec,v,l⟩ := decrement s f sp it 0 (by simpa using d)
    let u := {s with dimension:=ds,flag:=[]}
    have check := testDim u rfl sp it p
    have fin := dec.seq (by simpa [u,v] using check)
    have lim : ds.length≤K := by omega
    refine ⟨ds,?_,lim⟩
    simpa [u,inp] using fin.mono (show _ ≤ 20*(K+1) by omega)
  | cons x xs ih =>
    obtain ⟨ds,dec,v,l⟩ := decrement s f sp it (xs.length+1) (by simpa using d)
    let u := {s with dimension:=ds,flag:=[]}
    let after := {u with input:=words xs++tail}
    have check := testDim u rfl sp it p
    have step := field 2 x (words xs++tail) u hs hr
    have c : Runs (A 5) u (3*ds.length+7) (H 2) u := by simpa [u,v] using check
    have read : Goes (H 2) u (3*(x.bits.length+1)) (A 3) after := by
      simpa [u,after,inp,next,putWord,putInput,List.append_assoc] using step
    have lim : ds.length≤K := by omega
    have lh : (words xs).length≤K := by simp at len;omega
    obtain ⟨di,path,li⟩ := ih after v lim rfl lh it rfl sp p hs hr
    have total := ((dec.seq c).seq (smallRun read)).seq path
    refine ⟨di,?_,li⟩
    have bl := bits_lt x
    simp only [words_cons,List.length_append] at len
    apply total.mono
    simp only [List.length_cons,Nat.succ_mul,Nat.add_mul]; omega

end WeightedTM

namespace WeightedTM
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
def xWord (r : Bool) (s : Cells) := if r then s.remainder else s.divisor
def zWord (r : Bool) (s : Cells) := if r then s.product else s.itemCount
def putX (r : Bool) (w : List Bool) (s : Cells) : Cells := if r then {s with remainder:=w} else {s with divisor:=w}
def putZ (r : Bool) (w : List Bool) (s : Cells) : Cells := if r then {s with product:=w} else {s with itemCount:=w}
def mulExit (r : Bool) := if r then A 9 else A 8
def mulOut (r : Bool) (n : ℕ) (z : List Bool) (s : Cells) := putZ r z (putX r []
  {s with binCount:=List.replicate n false ++ s.binCount,flag:=[]})

private theorem advance (r : Bool) (s : Cells) (b : Bool) (bs : List Bool) (h : xWord r s=b::bs) :
    Goes (M r 0) s 1 (if b then M r 1 else M r 3) (putX r bs s) := by
  have step := MacroPath.bits (P:=code) (l:=M r 0) (m:=s.mem) (a:=_) (by rfl)
  cases r <;> cases b <;> simp [xWord] at h <;> simpa [M,code,putX,factor,Action.run,jump,h] using step

private theorem doneMul (r : Bool) (s : Cells) (h : xWord r s=[]) :
    Goes (M r 0) s 1 (mulExit r) s := by
  have step := MacroPath.bits (P:=code) (l:=M r 0) (m:=s.mem) (a:=_) (by rfl)
  cases r <;> simp [xWord] at h <;> simpa [M,code,factor,mulExit,Action.run,jump,h] using step

private theorem shift (r : Bool) (s : Cells) : Goes (M r 3) s 1 (M r 0) {s with binCount:=false::s.binCount} := by
  have step := MacroPath.bits (P:=code) (l:=M r 3) (m:=s.mem) (a:=_) (by rfl)
  simpa [M,code,Action.run,jump] using step

private theorem addTo (r : Bool) (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) :
    ∃ z : List Bool, Runs (M r 1) s (3*(max (zWord r s).length s.binCount.length+3)) (M r 3)
      (putZ r z {s with flag:=[]}) ∧ val z=val (zWord r s)+val s.binCount ∧
      z.length ≤ max (zWord r s).length s.binCount.length+1 := by
  have e := MacroPath.binary (P:=code) (l:=M r 1) (m:=s.mem) (op:=.add) (i:=accum r) (j:=bins)
    (h:=by cases r <;> decide) (n:=M r 2) (by rfl) f sp
  let z := execute addGate false (zWord r s) s.binCount
  obtain ⟨v,c,l⟩ := add_correct false (zWord r s) s.binCount
  change val z.2.1=_ at v;change z.2.2=_ at c;change z.2.1.length≤_ at l
  have zl : gateResult .add s.mem (accum r) bins=z := by cases r <;> rfl
  let mid := putZ r z.2.1 {s with flag:=[z.1]}
  have gate : Goes (M r 1) s (gateTime .add s.mem (accum r) bins) (M r 2) mid := by
    rw [zl] at e
    cases r <;> simpa [afterGate,mid,accum,putZ,c] using e
  have one := MacroPath.bits (P:=code) (l:=M r 2) (m:=mid.mem) (a:=_) (by rfl)
  have drop : Goes (M r 2) mid 1 (M r 3) (putZ r z.2.1 {s with flag:=[]}) := by
    cases r <;> simpa [M,code,mid,putZ,Action.run,jump] using one
  refine ⟨z.2.1,⟨_,?_,gate.join drop⟩,by simpa using v,l⟩
  have inp : s.mem (reg (accum r))=zWord r s := by cases r <;>rfl
  simp [gateTime,zl,c,inp]; omega

private theorem oneBit (r : Bool) (s : Cells) (b : Bool) (bs : List Bool) (h : xWord r s=b::bs)
    (f : s.flag=[]) (sp : s.spare=[]) (S : ℕ) (hz : (zWord r s).length≤S) (hy : s.binCount.length≤S) :
    ∃ z : List Bool, Runs (M r 0) s (4*(S+4)) (M r 0) (putZ r z (putX r bs {s with binCount:=false::s.binCount,flag:=[]})) ∧
      val z=val (zWord r s)+b.toNat*val s.binCount ∧ z.length≤S+1 := by
  let t := putX r bs s
  have adv := smallRun (advance r s b bs h)
  have zt : zWord r t = zWord r s := by cases r <;>rfl
  have yt : t.binCount=s.binCount := by cases r <;>rfl
  have ft : t.flag=[] := by cases r <;> exact f
  have st : t.spare=[] := by cases r <;> exact sp
  cases b with
  | false =>
    have path := adv.seq (smallRun (shift r t))
    refine ⟨zWord r s,?_,by simp,by omega⟩
    have ht : 1+1≤4*(S+4) := by omega
    cases r <;> simpa [t,putX,putZ,zWord,f] using path.mono ht
  | true =>
    obtain ⟨z,plus,v,l⟩ := addTo r t ft st
    have path := (adv.seq plus).seq (smallRun (shift r _))
    have ht : 1+3*(max (zWord r t).length t.binCount.length+3)+1≤4*(S+4) := by rw [zt,yt];omega
    refine ⟨z,?_,by simpa [zt,yt] using v,by rw [zt,yt] at l;omega⟩
    cases r <;> simpa [t,putX,putZ] using path.mono ht

theorem multiplyAcc (r : Bool) (xs : List Bool) (s : Cells) (S K : ℕ)
    (h : xWord r s=xs) (f : s.flag=[]) (sp : s.spare=[]) (hz : (zWord r s).length≤S)
    (hy : s.binCount.length≤S) (space : S+xs.length≤K) :
    ∃ z : List Bool, Runs (M r 0) s (xs.length*(4*(K+4))+1) (mulExit r) (mulOut r xs.length z s) ∧
      val z=val (zWord r s)+val xs*val s.binCount ∧ z.length≤S+xs.length := by
  induction xs generalizing s S with
  | nil =>
    refine ⟨zWord r s,?_,by simp [val],by simpa using hz⟩
    have p := smallRun (doneMul r s h)
    cases s
    cases r <;> simp [xWord] at h <;> dsimp only at f <;> simpa [mulOut,putX,putZ,zWord,h,f] using p
  | cons b bs ih =>
    obtain ⟨z,first,v,l⟩ := oneBit r s b bs h f sp S hz hy
    let t := putZ r z (putX r bs {s with binCount:=false::s.binCount,flag:=[]})
    have x' : xWord r t=bs := by cases r <;>rfl
    have z' : zWord r t=z := by cases r <;>rfl
    have y' : t.binCount=false::s.binCount := by cases r <;>rfl
    have fm : t.flag=[] := by cases r <;>rfl
    have sm : t.spare=[] := by cases r <;>exact sp
    obtain ⟨out,tail,vo,lo⟩ := ih t (S+1) x' fm sm (z' ▸ l) (by rw [y'];simp;omega) (by simp at space;omega)
    have path := first.seq tail
    have sl : S≤K := by omega
    have tm : 4*(S+4)+(bs.length*(4*(K+4))+1) ≤ (b::bs).length*(4*(K+4))+1 := by simp [Nat.succ_mul];omega
    have rep (a : List Bool) : List.replicate bs.length false ++ false::a=false::(List.replicate bs.length false++a) := by
      calc
        _ = (List.replicate bs.length false ++ [false])++a := by simp
        _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
    refine ⟨out,?_,?_,by simp;omega⟩
    · cases r <;> simpa [t,putZ,putX,mulOut,List.replicate_succ,rep] using path.mono tm
    · rw [z',y',v] at vo; simp [val] at vo ⊢;nlinarith only [vo]
end WeightedTM

namespace WeightedTM
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
def sizesWord (ps : List (ℕ×ℕ)) := words (ps.map Prod.fst)
def countsWord (ps : List (ℕ×ℕ)) := words (ps.map Prod.snd)
def pairMass (ps : List (ℕ×ℕ)) := (ps.map fun x => x.1*x.2).sum
@[simp] theorem sizes_nil : sizesWord []=[] := rfl
@[simp] theorem counts_nil : countsWord []=[] := rfl
@[simp] theorem sizes_cons (x y : ℕ) (ps : List (ℕ×ℕ)) : sizesWord ((x,y)::ps)=encodeNat x++sizesWord ps := rfl
@[simp] theorem counts_cons (x y : ℕ) (ps : List (ℕ×ℕ)) : countsWord ((x,y)::ps)=encodeNat y++countsWord ps := rfl

theorem clearBins (s : Cells) (bs : List Bool) : Goes (A 8) {s with binCount:=bs} (bs.length+1)
    (H 3) {s with binCount:=[]} := by
  induction bs with
  | nil =>
    have st := MacroPath.bits (P:=code) (l:=A 8) (m:=({s with binCount:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using st
  | cons b bs ih =>
    have st := MacroPath.bits (P:=code) (l:=A 8) (m:=({s with binCount:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (A 8) {s with binCount:=b::bs} 1 (A 8) {s with binCount:=bs} := by simpa [code,A,Action.run,jump] using st
    simpa [Nat.add_comm 1] using one.join ih

def fuel (ps : List (ℕ×ℕ)) (b : ℕ) := (sizesWord ps).length+(countsWord ps).length+(encodeNat b).length+1

theorem pairs (ps : List (ℕ×ℕ)) (b : ℕ) (back : List Bool) (s : Cells) (K : ℕ)
    (inp : s.input=countsWord ps++encodeNat b) (saved : s.prep=sizesWord ps++back)
    (room : s.itemCount.length+(sizesWord ps).length+(countsWord ps).length≤K)
    (bf : s.binCount=[]) (df : s.divisor=[]) (f : s.flag=[]) (sp : s.spare=[])
    (hs : s.scratch=[]) (hr : s.reversed=[]) :
    ∃ w : List Bool, Runs (H 3) s (fuel ps b*(20*(K+4))) (M true 0)
      {s with itemCount:=w,binCount:=b.bits,input:=[],prep:=back,divisor:=[],flag:=[]} ∧
      val w=val s.itemCount+pairMass ps ∧ w.length≤K := by
  induction ps generalizing s with
  | nil =>
    let u := {s with input:=[],binCount:=b.bits}
    have read := field 3 b [] s hs hr
    have p : Goes (H 3) s (3*(b.bits.length+1)) (A 7) u := by
      cases s; simp at inp; simpa [u,inp,bf,next,putWord,putInput] using read
    have sel := MacroPath.bits (P:=code) (l:=A 7) (m:=u.mem) (a:=_) (by rfl)
    have done : Goes (A 7) u 1 (M true 0) u := by simpa [u,code,A,Action.run,jump] using sel
    have tr := smallRun (p.join done)
    have bl := bits_lt b
    have ct : 3*(b.bits.length+1)+1≤fuel [] b*(20*(K+4)) := by
      simp [fuel];nlinarith
    refine ⟨s.itemCount,?_,by simp [pairMass],by simpa using room⟩
    simp at saved
    cases s; dsimp only at df f saved; simpa [u,df,f,saved] using tr.mono ct
  | cons xy ps ih =>
    obtain ⟨x,y⟩ := xy
    let rest := countsWord ps++encodeNat b
    let mirror := sizesWord ps++back
    let u := {s with input:=rest,binCount:=y.bits}
    let v := {u with prep:=mirror,divisor:=x.bits}
    have fromY := field 3 y rest s hs hr
    have py : Goes (H 3) s (3*(y.bits.length+1)) (A 7) u := by
      cases s; simp [List.append_assoc] at inp;simpa [u,rest,inp,bf,next,putWord,putInput] using fromY
    have live : u.input≠[] := by simp [u,rest,encodeNat]
    have sel := MacroPath.bits (P:=code) (l:=A 7) (m:=u.mem) (a:=_) (by rfl)
    have cont : Goes (A 7) u 1 (H 4) u := by
      cases hi : u.input with
      | nil => contradiction
      | cons b bs => simpa [code,A,Action.run,jump,hi] using sel
    have fromX := field 4 x mirror u hs hr
    have px : Goes (H 4) u (3*(x.bits.length+1)) (M false 0) v := by
      cases s; simp [List.append_assoc] at saved;simpa [u,v,mirror,saved,df,next,putWord,putInput] using fromX
    let S := max s.itemCount.length y.bits.length
    have lx := bits_lt x;have ly := bits_lt y
    simp only [sizes_cons,counts_cons,List.length_append] at room
    have space : S+x.bits.length≤K := by dsimp [S];omega
    obtain ⟨z,mult,vz,lz⟩ := multiplyAcc false x.bits v S K rfl f sp
      (by dsimp [v,u,zWord,S];omega) (by dsimp [v,u,S];omega) space
    let post := mulOut false x.bits.length z v
    let dst := {v with divisor:=[],binCount:=[],itemCount:=z,flag:=[]}
    have cl : Goes (A 8) post (x.bits.length+y.bits.length+1) (H 3) dst := by
      simpa [post,dst,mulOut,putX,putZ,u,v] using clearBins post post.binCount
    have rm : dst.itemCount.length+(sizesWord ps).length+(countsWord ps).length≤K := by dsimp [dst];dsimp [S] at lz;omega
    obtain ⟨w,recP,vw,lw⟩ := ih dst rfl rfl rm rfl rfl rfl sp hs hr
    have path := ((((smallRun py).seq (smallRun cont)).seq (smallRun px)).seq mult).seq (smallRun cl)
    have total := path.seq recP
    refine ⟨w,?_,?_,lw⟩
    · apply total.mono
      simp only [fuel,sizes_cons,counts_cons,List.length_append]
      have xx := Nat.mul_le_mul_right (4*(K+4)) lx
      nlinarith only [xx,lx,ly]
    · change val w=val z+pairMass ps at vw
      change val z=val s.itemCount+val x.bits*val y.bits at vz
      rw [vw,vz,val_bits,val_bits];simp [pairMass,Nat.add_assoc]
end WeightedTM

namespace WeightedTM
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)
def input (B d : ℕ) (ps : List (ℕ×ℕ)) (b : ℕ) :=
  encodeNat B++(encodeNat d++(sizesWord ps++(countsWord ps++encodeNat b)))

private theorem finalCmp (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) :
    Runs (A 9) s (3*(max s.itemCount.length s.product.length+2)) (old (OneTypeTM.A 9))
      {s with flag:=[decide (val s.itemCount≤val s.product)]} := by
  have e := MacroPath.binary (P:=code) (l:=A 9) (m:=s.mem) (op:=.le) (i:=items) (j:=prod)
    (h:=by decide) (n:=old (OneTypeTM.A 9)) (by rfl) f sp
  let z := execute compareGate true s.itemCount s.product
  obtain ⟨a,x,y⟩ := le_correct s.itemCount s.product
  change z.1=_ at a;change z.2.1=_ at x;change z.2.2=_ at y
  have zl : gateResult .le s.mem items prod=z := rfl
  refine ⟨gateTime .le s.mem items prod,?_,?_⟩
  · simp [gateTime,zl,x,y];omega
  · simpa [afterGate,zl,a,x,y] using e

private theorem isolatedWord (w : List Bool) : ({input:=w}:Cells).mem=isolated (reg R.tape) w := by
  funext k
  cases k with
  | inl z => cases z <;>rfl
  | inr z => cases z <;>rfl

theorem decideVolume (B d : ℕ) (xs : List (ℕ×ℕ)) (b : ℕ) (hd : d=xs.length) (pos : 0<d) :
    OutputsWithin machine (input B d xs b) [decide (pairMass xs≤b*B)] (500*((input B d xs b).length+1)^2) := by
  cases xs with
  | nil => simp at hd;omega
  | cons xy ps =>
    obtain ⟨x,y⟩ := xy
    let qs := (x,y)::ps
    let K := (input B d qs b).length
    let tail := countsWord qs++encodeNat b
    let body := sizesWord qs++tail
    let m := headState B d body
    let v := {m with input:=sizesWord ps++tail}
    have lk : (encodeNat B).length+(encodeNat d).length+(sizesWord qs).length+
        (countsWord qs).length+(encodeNat b).length=K := by simp [K,input];omega
    have ly : tail.length=(countsWord qs).length+(encodeNat b).length := List.length_append
    have lb : body.length=(sizesWord qs).length+tail.length := List.length_append
    have sx : (sizesWord qs).length=(encodeNat x).length+(sizesWord ps).length := by simp [qs]
    have hB := bits_lt B;have hb := bits_lt b;have hD := bits_lt d;have hx := bits_lt x
    have p0 := smallRun (head B d body)
    have fst := field 2 x (sizesWord ps++tail) m rfl rfl
    have sfirst : Goes (H 2) m (3*(x.bits.length+1)) (A 3) v := by
      simpa [v,m,body,qs,headState,next,putInput,putWord,List.append_assoc] using fst
    obtain ⟨ds,sc,dl⟩ := sizes (ps.map Prod.fst) tail v K (by omega)
      (by simp [v,m,headState,val_bits]; simpa using hd) (by dsimp [v,m,headState];omega)
      rfl (show (sizesWord ps).length≤K by omega) rfl rfl rfl rfl rfl rfl
    let n := {v with input:=tail,dimension:=ds,divisor:=[],flag:=[]}
    obtain ⟨w,scan,vw,lw⟩ := pairs qs b tail n K rfl rfl
      (show 0+(sizesWord qs).length+(countsWord qs).length≤K by omega) rfl rfl rfl rfl rfl rfl
    let t := {n with itemCount:=w,binCount:=b.bits,input:=[],prep:=tail,divisor:=[],flag:=[]}
    have vol : val w=pairMass qs := by simpa [n,v,m,headState,val] using vw
    obtain ⟨r,mul,vr,lr⟩ := multiplyAcc true B.bits t b.bits.length K rfl rfl rfl (by simp [t,n,v,m,headState,zWord]) le_rfl (by omega)
    let u := mulOut true B.bits.length r t
    have capacity : val r=b*B := by simpa [t,n,v,m,headState,zWord,val,val_bits,Nat.mul_comm] using vr
    have cmp := finalCmp u rfl rfl
    have bit : decide (val u.itemCount≤val u.product)=decide (pairMass qs≤b*B) := by
      change decide (val w ≤ val r)=_; rw [vol,capacity]
    rw [bit] at cmp
    let z := {u with flag:=[decide (pairMass qs≤b*B)]}
    have halt := OneTypeTM.finish z (decide (pairMass qs≤b*B)) rfl rfl rfl
    have lift : Goes (old (OneTypeTM.A 9)) z (OneTypeTM.costClear z) none ({input:=[decide (pairMass qs≤b*B)]}:Cells) :=
      halt.mapLabels (Q:=code) old (by intro l;rfl)
    have path := (((((p0.seq (smallRun sfirst)).seq sc).seq scan).seq mul).seq cmp).seq (smallRun lift)
    obtain ⟨time,tt,run⟩ := path
    apply MacroPath.outputs (t:=time)
    · rw [←isolatedWord,←isolatedWord];exact run
    · have ca : ps.length≤(sizesWord ps).length := by simpa [sizesWord] using count_words (ps.map Prod.fst)
      have csize : ((ps.map Prod.fst).length+1)*(20*(K+1))≤(K+1)*(20*(K+1)) :=
        Nat.mul_le_mul_right _ (by simp;omega)
      have cpair : fuel qs b*(20*(K+4))≤(K+1)*(20*(K+4)) := Nat.mul_le_mul_right _ (by dsimp [fuel];omega)
      have cmul : B.bits.length*(4*(K+4))≤K*(4*(K+4)) := Nat.mul_le_mul_right _ (by omega)
      have cc : OneTypeTM.costClear z ≤ 6*K+11 := by
        simp [z,u,t,n,v,m,mulOut,putZ,putX,headState,OneTypeTM.costClear];omega
      have ck : max u.itemCount.length u.product.length≤K := by change max w.length r.length≤K;omega
      change time≤500*(K+1)^2
      nlinarith only [tt,cc,ck,csize,cpair,cmul,lk,lb,ly,hB,hD,hx,sx]
end WeightedTM

open HMBinPacking
namespace PackingVolume

def mass (I : Instance) := ∑ i, I.s i * I.a i

private theorem allocation {X : Type} [DecidableEq X] (b : ℕ) (size : X → ℕ)
    (pos : ∀ x, 0 < size x) (chain : ∀ x y, size x ∣ size y ∨ size y ∣ size x)
    (T : Finset X) (cap : Fin b → ℕ)
    (divides : ∀ x ∈ T, ∀ k, size x ∣ cap k)
    (space : ∑ x ∈ T, size x ≤ ∑ k, cap k) :
    ∃ f : X → Option (Fin b), (∀ x ∈ T, (f x).isSome) ∧
      ∀ k, ∑ x ∈ T, (if f x=some k then size x else 0) ≤ cap k := by
  classical
  induction T using Finset.strongInductionOn generalizing cap with
  | _ T ih =>
    by_cases emp : T.Nonempty
    · obtain ⟨x,hx,hmax⟩ := Finset.exists_max_image T size emp
      have hmass := Finset.sum_erase_add T size hx
      have kpos : ∃ k, 0 < cap k := by
        by_contra! h
        have hz : ∀ k,cap k=0 := fun k => Nat.eq_zero_of_le_zero (h k)
        have xp := pos x
        have htotal : (∑ j,cap j)=0 := by simp [hz]
        rw [htotal] at space;omega
      obtain ⟨k,hk⟩ := kpos
      have room := Nat.le_of_dvd hk (divides x hx k)
      let c' (j : Fin b) := if j=k then cap j-size x else cap j
      have cs (j : Fin b) : c' j+(if j=k then size x else 0)=cap j := by
        by_cases e : j=k
        · subst j; simp [c',Nat.sub_add_cancel room]
        · simp [c',e]
      have sumCap : ∑ j,c' j + size x = ∑ j,cap j := by
        calc
          _ = ∑ j, (c' j + if j=k then size x else 0) := by simp [Finset.sum_add_distrib]
          _ = _ := Finset.sum_congr rfl (fun j _ => cs j)
      have smaller : ∀ y ∈ T.erase x, size y ∣ size x := by
        intro y hy
        rcases chain y x with c | c
        · exact c
        · have eq := Nat.le_of_dvd (pos y) c
          have rev := hmax y (Finset.mem_of_mem_erase hy)
          rw [show size y=size x by omega]
      have cdiv : ∀ y ∈ T.erase x, ∀ j, size y ∣ c' j := by
        intro y hy j
        have cd := divides y (Finset.mem_of_mem_erase hy) j
        by_cases e : j=k
        · simp only [c',if_pos e];exact Nat.dvd_sub cd (smaller y hy)
        · simpa [c',e] using cd
      obtain ⟨f,all,fit⟩ := ih (T.erase x) (Finset.erase_ssubset hx) c' cdiv (by omega)
      let g := Function.update f x (some k)
      refine ⟨g,?_,?_⟩
      · intro y hy
        by_cases e : y=x
        · simp [g,e]
        · simpa [g,e] using all y (Finset.mem_erase.mpr ⟨e,hy⟩)
      · intro j
        have gj : ∑ y ∈ T.erase x, (if g y=some j then size y else 0) =
            ∑ y ∈ T.erase x, (if f y=some j then size y else 0) := by
          apply Finset.sum_congr rfl
          intro y hy
          simp [g,(Finset.mem_erase.mp hy).1]
        have decomp := Finset.sum_erase_add T (fun y => if g y=some j then size y else 0) hx
        rw [gj] at decomp
        have term : (if g x=some j then size x else 0)=(if j=k then size x else 0) := by simp [g,eq_comm]
        rw [term] at decomp
        exact decomp ▸ ((Nat.add_le_add_right (fit j) _).trans_eq (cs j))
    · rw [Finset.not_nonempty_iff_eq_empty.mp emp]
      exact ⟨fun _ => none, by simp,by simp⟩

private theorem total (I : Instance) : (∑ x : (i : Fin I.d) × Fin (I.a i), I.s x.1)=mass I := by
  rw [Fintype.sum_sigma]
  simp [mass,Nat.mul_comm]

theorem necessary (I : Instance) (hf : Feasible I) : mass I ≤ I.b*I.B := by
  classical
  obtain ⟨f,h⟩ := hf
  have p := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => h j)
  rw [←total]
  simpa [Finset.sum_filter,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)] using p

theorem one_bin (I : Instance) (hb : I.b=1) : Feasible I ↔ mass I ≤ I.b*I.B := by
  classical
  constructor
  · exact necessary I
  · intro space
    let k : Fin I.b := ⟨0,by omega⟩
    refine ⟨fun _ => k,fun j => ?_⟩
    have e : k=j := Fin.ext (by have := k.isLt;have := j.isLt;omega)
    simpa [e,total,hb] using space

/-- Greedy packing in nonincreasing order is exact for a divisibility chain
whose sizes divide the bin capacity. -/
theorem chain_iff (I : Instance) (chain : ∀ i j, I.s i ∣ I.s j ∨ I.s j ∣ I.s i)
    (part : ∀ i, I.s i ∣ I.B) : Feasible I ↔ mass I ≤ I.b*I.B := by
  classical
  constructor
  · exact necessary I
  · intro space
    let X := (i : Fin I.d) × Fin (I.a i)
    obtain ⟨f,live,cap⟩ := allocation I.b (X:=X) (fun x => I.s x.1) (fun x => I.s_pos x.1)
      (fun x y => chain x.1 y.1) Finset.univ (fun _ => I.B) (fun x _ _ => part x.1)
      (by simpa [X,total,Nat.mul_comm] using space)
    let g (x : X) := (f x).get (live x (Finset.mem_univ x))
    refine ⟨g,fun j => ?_⟩
    rw [Finset.sum_filter]
    apply le_trans _ (cap j)
    apply Finset.sum_le_sum
    intro x _
    have eq : some (g x)=f x := Option.some_get _
    by_cases c : g x=j
    · simp [←eq,c]
    · simp [←eq,c]
end PackingVolume

open HMBinPacking
namespace PackingVolume
theorem machine_mass (I : Instance) :
    OutputsWithin WeightedTM.machine (encodeInstance I) [decide (mass I≤I.b*I.B)] (500*(inputLength I+1)^2) := by
  let ps := List.ofFn (fun i : Fin I.d => (I.s i,I.a i))
  have ws : WeightedTM.sizesWord ps=encodeNatVec I.s := by
    rw [WeightedTM.sizesWord,show ps.map Prod.fst=List.ofFn I.s by simp [ps,List.map_ofFn,Function.comp_def]]
    rw [WeightedTM.words,List.flatMap_def,List.map_ofFn];rfl
  have wa : WeightedTM.countsWord ps=encodeNatVec I.a := by
    rw [WeightedTM.countsWord,show ps.map Prod.snd=List.ofFn I.a by simp [ps,List.map_ofFn,Function.comp_def]]
    rw [WeightedTM.words,List.flatMap_def,List.map_ofFn];rfl
  have eq : WeightedTM.input I.B I.d ps I.b=encodeInstance I := by
    simp [WeightedTM.input,encodeInstance,ws,wa,List.append_assoc]
  have data : WeightedTM.pairMass ps=mass I := by
    rw [WeightedTM.pairMass,show ps.map (fun x => x.1*x.2)=List.ofFn (fun i => I.s i*I.a i) by simp [ps,List.map_ofFn,Function.comp_def]]
    exact List.sum_ofFn
  simpa [eq,data,inputLength] using WeightedTM.decideVolume I.B I.d ps I.b (by simp [ps]) I.d_pos
end PackingVolume

/-- A single machine covers unrestricted types with one bin, and arbitrarily
many bins and types when the sizes form a divisibility chain and divide the capacity. -/
theorem solution :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ I : Instance,
      (I.b=1 ∨ ((∀ i j, I.s i ∣ I.s j ∨ I.s j ∣ I.s i) ∧ (∀ i, I.s i ∣ I.B))) →
      (Feasible I → OutputsWithin M (encodeInstance I) [true] (500*(inputLength I+1)^2)) ∧
      (¬Feasible I → OutputsWithin M (encodeInstance I) [false] (500*(inputLength I+1)^2)) := by
  refine ⟨WeightedTM.machine,?_⟩
  intro I promise
  have geom : Feasible I ↔ PackingVolume.mass I≤I.b*I.B := by
    rcases promise with h | ⟨chain,cap⟩
    · exact PackingVolume.one_bin I h
    · exact PackingVolume.chain_iff I chain cap
  have run := PackingVolume.machine_mass I
  constructor
  · intro h; simpa [geom.mp h] using run
  · intro h; have no : ¬PackingVolume.mass I≤I.b*I.B := fun c => h (geom.mpr c)
    simpa [no] using run
