-- Prove2me | solution 1 for HMBinPacking.one_type_quadratic_time
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:25:44.542918+00:00
-- url     : https://prove2.me/submissions/eec317e7-bd65-49bb-b0d3-ede89e2fd721

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Instance

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

open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
namespace OneTypeTM
open R

def putWord (p : Fin 5) (w : List Bool) (m : Cells) : Cells :=
  match p.val with
  | 0 => {m with remainder:=w++m.remainder} | 1 => {m with dimension:=w++m.dimension}
  | 2 => {m with divisor:=w++m.divisor} | 3 => {m with itemCount:=w++m.itemCount}
  | _ => {m with binCount:=w++m.binCount}

def clock (p : Fin 5) (k : ℕ) (m : Cells) : Cells :=
  if p=0 then {m with prep:=List.replicate k true ++ m.prep,todo:=List.replicate k true ++ m.todo} else m

private theorem HT (p : Fin 5) (m : Cells) (bs : List Bool) :
    Goes (H p) {m with input:=true::bs} 1 (H p)
      (clock p 1 {m with input:=bs, scratch:=true::m.scratch}) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=({m with input:=true::bs}:Cells).mem) (a:=_) (by rfl)
  by_cases h : p=0 <;> simpa [code,H,clock,h,Action.run,jump] using e

private theorem HF (p : Fin 5) (m : Cells) (bs : List Bool) :
    Goes (H p) {m with input:=false::bs} 1 (D p) {m with input:=bs} := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=({m with input:=false::bs}:Cells).mem) (a:=_) (by rfl)
  simpa [code,H,D,Action.run,jump] using e

private theorem header (p : Fin 5) (k : ℕ) (m : Cells) (t : List Bool) :
    Goes (H p) {m with input:=List.replicate k true ++ false :: t} (k+1) (D p)
      (clock p k {m with input:=t,scratch:=List.replicate k true++m.scratch}) := by
  induction k generalizing m with
  | zero => simpa [clock] using HF p m t
  | succ k ih =>
    let z := clock p 1 {m with scratch:=true::m.scratch}
    have st := HT p m (List.replicate k true ++ false::t)
    have eqc (c : List Bool) : List.replicate k true ++ true::c = true::(List.replicate k true ++ c) := by
      calc
        _ = (List.replicate k true ++ [true])++c := by simp
        _ = _ := by rw [←List.replicate_succ', List.replicate_succ,List.cons_append]
    by_cases hp : p=0
    · subst p
      have z := st.join (ih (clock 0 1 {m with scratch:=true::m.scratch}))
      simpa [clock,List.replicate_succ,eqc,Nat.add_comm 1] using z
    · simp [clock,hp] at st
      have z := st.join (ih {m with scratch:=true::m.scratch})
      simpa [clock,hp,List.replicate_succ,eqc,Nat.add_comm 1] using z

private theorem DT (p : Fin 5) (m : Cells) (b : Bool) (t c : List Bool) :
    Goes (D p) {m with input:=b::t,scratch:=true::c} 1 (D p)
      {m with input:=t,scratch:=c,reversed:=b::m.reversed} := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=({m with input:=b::t,scratch:=true::c}:Cells).mem) (a:=_) (by rfl)
  simpa [code,D,Action.run,jump] using e
private theorem DF (p : Fin 5) (m : Cells) :
    Goes (D p) {m with scratch:=[]} 1 (V p) {m with scratch:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=({m with scratch:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,D,V,Action.run,jump] using e

private theorem digits (p : Fin 5) (bs t : List Bool) (m : Cells) :
    Goes (D p) {m with input:=bs++t,scratch:=List.replicate bs.length true}
      (bs.length+1) (V p) {m with input:=t,scratch:=[],reversed:=bs.reverse++m.reversed} := by
  induction bs generalizing m with
  | nil => simpa using DF p {m with input:=t}
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
    Goes (H p) {m with input:=encodeNat n++t} (3*(n.bits.length+1)) (next p)
      (putWord p n.bits (clock p n.bits.length {m with input:=t})) := by
  have h := header p n.bits.length m (n.bits++t)
  have d := digits p n.bits t (clock p n.bits.length m)
  have r := backwards p n.bits.reverse (clock p n.bits.length {m with input:=t})
  by_cases hp : p=0 <;> simp [clock,hp,hs,hr] at h d r ⊢ <;>
    have z := (h.join d).join r <;>
    simpa [encodeNat,List.append_assoc,Nat.mul_comm,Nat.mul_add,Nat.mul_succ,Nat.add_assoc, hs,hr] using z

end OneTypeTM

namespace OneTypeTM
open BitStacks HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)
def input (B s a b : ℕ) := encodeNat B++encodeNat 1++encodeNat s++encodeNat a++encodeNat b
def parsed (B s a b : ℕ) : Cells :=
  {remainder:=B.bits,divisor:=s.bits,itemCount:=a.bits,binCount:=b.bits,
   dimension:=(1:ℕ).bits,prep:=List.replicate B.bits.length true,todo:=List.replicate B.bits.length true}
def parseCost (B s a b : ℕ) := 3*(B.bits.length+1)+3*((1:ℕ).bits.length+1)+
    3*(s.bits.length+1)+3*(a.bits.length+1)+3*(b.bits.length+1)
theorem readInput (B s a b : ℕ) :
    Goes (H 0) ({input:=input B s a b} : Cells) (parseCost B s a b) (A 0) (parsed B s a b) := by
  let t4 := encodeNat b
  let t3 := encodeNat a++t4
  let t2 := encodeNat s++t3
  let t1 := encodeNat 1++t2
  let m0 : Cells := {}
  let m1 := putWord 0 B.bits (clock 0 B.bits.length {m0 with input:=t1})
  let m2 := putWord 1 (1:ℕ).bits (clock 1 (1:ℕ).bits.length {m1 with input:=t2})
  let m3 := putWord 2 s.bits (clock 2 s.bits.length {m2 with input:=t3})
  let m4 := putWord 3 a.bits (clock 3 a.bits.length {m3 with input:=t4})
  have p0 := field 0 B t1 m0 rfl rfl
  have p1 := field 1 1 t2 m1 rfl rfl
  have p2 := field 2 s t3 m2 rfl rfl
  have p3 := field 3 a t4 m3 rfl rfl
  have p4 := field 4 b [] m4 rfl rfl
  simp only [List.append_nil] at p4
  have p := (((p0.join p1).join p2).join p3).join p4
  simpa [input,parsed,parseCost,t1,t2,t3,t4,m0,m1,m2,m3,m4,putWord,clock,List.append_assoc,next] using p

theorem val_bits (n : ℕ) : val n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit _ _ h, val, ih, Nat.bit_val]; omega

theorem length_input (B s a b : ℕ) : (input B s a b).length =
    2*(B.bits.length+s.bits.length+a.bits.length+b.bits.length)+7 := by
  simp [input,encodeNat]; omega

theorem cost_input (B s a b : ℕ) : parseCost B s a b ≤ 3*((input B s a b).length+1) := by
  rw [length_input]; simp [parseCost];omega
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

namespace OneTypeTM
open R BitStacks

def room (s : Cells) (N : ℕ) : Prop :=
  s.remainder.length ≤ N ∧ s.divisor.length ≤ N ∧ s.binCount.length ≤ N ∧
  s.itemCount.length ≤ N ∧ s.product.length ≤ N

def Runs (l : L) (s : Cells) (bound : ℕ) (out : Option L) (t : Cells) : Prop :=
  ∃ steps ≤ bound, Goes l s steps out t

theorem Runs.mono {l s a o t b} (h : Runs l s a o t) (h' : a≤b) : Runs l s b o t := by
  obtain ⟨z,p,q⟩ := h; exact ⟨z,p.trans h',q⟩
theorem Runs.seq {l s a j u b k v} (h : Runs l s a (some j) u) (h' : Runs j u b k v) :
    Runs l s (a+b) k v := by
  obtain ⟨g,gh,gp⟩ := h; obtain ⟨f,fh,fp⟩ := h'
  exact ⟨g+f,Nat.add_le_add gh fh,gp.join fp⟩
theorem smallRun {l s n o t} (p : Goes l s n o t) : Runs l s n o t := ⟨n,le_rfl,p⟩

private theorem val_small (w : List Bool) : val w < 2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih => cases b <;> simp [val,pow_succ] <;> omega

private theorem sub_ok (x y : List Bool) (h : val y ≤ val x) :
    let z := execute subGate false x y
    z.1=false ∧ val z.2.1=val x-val y ∧ z.2.2=y ∧ z.2.1.length=max x.length y.length := by
  let z := execute subGate false x y
  obtain ⟨v,w,len⟩ := sub_correct false x y
  change val x+z.1.toNat*2^(max x.length y.length)=val z.2.1+val y+0 at v
  change z.2.1.length=max x.length y.length at len
  have sm := val_small z.2.1
  rw [len] at sm
  have no : z.1=false := by
    cases g : z.1 with
    | false => rfl
    | true => rw [g] at v; simp at v;omega
  rw [no] at v
  simp only [Bool.toNat_false,Nat.zero_mul,Nat.add_zero] at v
  have result : val z.2.1=val x-val y := by omega
  exact ⟨no,result,w,len⟩

theorem scaleOne (s : Cells) (b : Bool) (bs : List Bool) :
    Goes (A 0) {s with prep:=b::bs} 1 (A 0) {s with prep:=bs,divisor:=false::s.divisor} := by
  have e := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with prep:=b::bs}:Cells).mem) (a:=_) (by rfl)
  simpa [code,A,Action.run,jump] using e
theorem scaleEnd (s : Cells) :
    Goes (A 0) {s with prep:=[]} 1 (A 1) {s with prep:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with prep:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,A,Action.run,jump] using e

theorem scaleAll (s : Cells) (bs : List Bool) :
    Goes (A 0) {s with prep:=bs} (bs.length+1) (A 1)
      {s with prep:=[],divisor:=List.replicate bs.length false ++ s.divisor} := by
  induction bs generalizing s with
  | nil => simpa using scaleEnd s
  | cons b bs ih =>
    have eqc : List.replicate bs.length false ++ false::s.divisor =
        false :: (List.replicate bs.length false ++ s.divisor) := by
      change _ = false::(List.replicate bs.length false ++ s.divisor)
      calc
        _ = (List.replicate bs.length false ++ [false])++s.divisor := by simp
        _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
    change List.replicate bs.length false ++ false::s.divisor = false::(List.replicate bs.length false ++ s.divisor) at eqc
    have e := (scaleOne s b bs).join (ih {s with divisor:=false::s.divisor})
    simpa [List.replicate_succ,eqc,Nat.add_comm 1] using e

def doubled (s : Cells) := {s with todo:=s.todo.tail,remainder:=false::s.remainder,product:=false::s.product}
theorem beginRound (s : Cells) (b : Bool) (bs : List Bool) (h : s.todo=b::bs) :
    Goes (A 1) s 1 (A 2) (doubled s) := by
  have e := MacroPath.bits (P:=code) (l:=A 1) (m:=s.mem) (a:=_) (by rfl)
  simpa [code,A,Action.run,jump,doubled,h] using e

theorem loopEnd (s : Cells) (h : s.todo=[]) : Goes (A 1) s 1 (A 8) s := by
  have e := MacroPath.bits (P:=code) (l:=A 1) (m:=s.mem) (a:=_) (by rfl)
  simpa [code,A,Action.run,jump,h] using e

theorem branch (s : Cells) (b : Bool) : Goes (A 3) {s with flag:=[b]} 1
    (if b then A 4 else A 1) {s with flag:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=A 3) (m:=({s with flag:=[b]}:Cells).mem) (a:=_) (by rfl)
  cases b <;> simpa [code,A,Action.run,jump] using e

theorem cmp (s : Cells) (N : ℕ) (f : s.flag=[]) (w : s.spare=[]) (fit : room s N) :
    Runs (A 2) s (3*N+6) (A 3) {s with flag:=[decide (val s.divisor ≤ val s.remainder)]} := by
  have e := MacroPath.binary (P:=code) (l:=A 2) (m:=s.mem) (op:=.le) (i:=den) (j:=rem)
    (h:=by decide) (n:=A 3) (by rfl) f w
  let z := execute compareGate true s.divisor s.remainder
  obtain ⟨ans,x,y⟩ := le_correct s.divisor s.remainder
  change z.1=_ at ans; change z.2.1=_ at x; change z.2.2=_ at y
  have zr : gateResult .le s.mem den rem = z := rfl
  refine ⟨gateTime .le s.mem den rem,?_,?_⟩
  · change gateTime .le s.mem den rem ≤ _
    simp [gateTime,zr,x,y]; rcases fit with ⟨a,b,_,_,_⟩; omega
  · change MacroPath code (some (A 2)) s.mem _ _ _
    simpa [zr,afterGate,ans,x,y] using e

theorem finalCmp (s : Cells) (N : ℕ) (f : s.flag=[]) (w : s.spare=[]) (fit : room s N) :
    Runs (A 8) s (3*N+6) (A 9) {s with flag:=[decide (val s.itemCount ≤ val s.product)]} := by
  have e := MacroPath.binary (P:=code) (l:=A 8) (m:=s.mem) (op:=.le) (i:=items) (j:=prod)
    (h:=by decide) (n:=A 9) (by rfl) f w
  let z := execute compareGate true s.itemCount s.product
  obtain ⟨ans,x,y⟩ := le_correct s.itemCount s.product
  change z.1=_ at ans; change z.2.1=_ at x; change z.2.2=_ at y
  have zr : gateResult .le s.mem items prod = z := rfl
  refine ⟨gateTime .le s.mem items prod,?_,?_⟩
  · change gateTime .le s.mem items prod ≤ _
    simp [gateTime,zr,x,y]; rcases fit with ⟨_,_,_,a,b⟩; omega
  · simpa [zr,afterGate,ans,x,y] using e

theorem subtractMove (s : Cells) (N : ℕ) (f : s.flag=[]) (w : s.spare=[]) (fit : room s N)
    (ge : val s.divisor ≤ val s.remainder) :
    ∃ res : List Bool, Runs (A 4) s (3*N+7) (A 6) {s with remainder:=res,flag:=[]} ∧
      val res=val s.remainder-val s.divisor ∧ res.length ≤ N := by
  have e := MacroPath.binary (P:=code) (l:=A 4) (m:=s.mem) (op:=.sub) (i:=rem) (j:=den)
    (h:=by decide) (n:=A 5) (by rfl) f w
  let z := execute subGate false s.remainder s.divisor
  obtain ⟨flag,value,right,len⟩ := sub_ok _ _ ge
  change z.1=_ at flag; change val z.2.1=_ at value; change z.2.2=_ at right; change z.2.1.length=_ at len
  have zr : gateResult .sub s.mem rem den = z := rfl
  let mid : Cells := {s with remainder:=z.2.1,flag:=[false]}
  have gate : Goes (A 4) s (gateTime .sub s.mem rem den) (A 5) mid := by
    simpa [zr,afterGate,mid,flag,right] using e
  have p := MacroPath.bits (P:=code) (l:=A 5) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 5) mid 1 (A 6) {s with remainder:=z.2.1,flag:=[]} := by
    simpa [code,A,Action.run,jump,mid] using p
  obtain ⟨r,d,_,_,_⟩ := fit
  refine ⟨z.2.1,⟨_,?_,gate.join pop⟩,value,by omega⟩
  simp [gateTime,zr,len,right]; omega

theorem addMove (s : Cells) (N : ℕ) (f : s.flag=[]) (w : s.spare=[]) (fit : room s N) :
    ∃ res : List Bool, Runs (A 6) s (3*N+8) (A 1) {s with product:=res,flag:=[]} ∧
      val res=val s.product+val s.binCount ∧ res.length ≤ N+1 := by
  have e := MacroPath.binary (P:=code) (l:=A 6) (m:=s.mem) (op:=.add) (i:=prod) (j:=bins)
    (h:=by decide) (n:=A 7) (by rfl) f w
  let z := execute addGate false s.product s.binCount
  obtain ⟨value,right,len⟩ := add_correct false s.product s.binCount
  change val z.2.1=_ at value; change z.2.2=_ at right; change z.2.1.length≤_ at len
  have zr : gateResult .add s.mem prod bins = z := rfl
  let mid : Cells := {s with product:=z.2.1,flag:=[z.1]}
  have gate : Goes (A 6) s (gateTime .add s.mem prod bins) (A 7) mid := by
    simpa [zr,afterGate,mid,right] using e
  have p := MacroPath.bits (P:=code) (l:=A 7) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 7) mid 1 (A 1) {s with product:=z.2.1,flag:=[]} := by
    simpa [code,A,Action.run,jump,mid] using p
  obtain ⟨_,_,b,_,x⟩ := fit
  refine ⟨z.2.1,⟨_,?_,gate.join pop⟩,by simpa using value,by omega⟩
  simp [gateTime,zr,right]; omega

end OneTypeTM

namespace OneTypeTM
open R BitStacks

private theorem roundStep (s : Cells) (N : ℕ) (flag : s.flag=[]) (sp : s.spare=[]) (fit : room s N)
    (bb : Bool) (bs : List Bool) (ht : s.todo=bb::bs) :
    ∃ (rv pv : List Bool),
    Runs (A 1) s (12*(N+5)) (A 1)
      {s with remainder:=rv,product:=pv,todo:=bs,flag:=[]} ∧
    (let take := val s.divisor ≤ 2*val s.remainder
     val rv = (if take then 2*val s.remainder-val s.divisor else 2*val s.remainder) ∧
     val pv = (if take then 2*val s.product+val s.binCount else 2*val s.product)) ∧
    rv.length≤N+2 ∧ pv.length≤N+2 := by
  let d := doubled s
  have beginP := smallRun (beginRound s bb bs ht)
  have fit' : room d (N+1) := by
    rcases fit with ⟨f1,f2,f3,f4,f5⟩; simp [room,d,doubled]; omega
  have cmpP := cmp d (N+1) flag sp fit'
  by_cases c : val s.divisor ≤ 2*val s.remainder
  · have a : decide (val d.divisor ≤ val d.remainder) = true := by simpa [d,doubled,val] using c
    rw [a] at cmpP
    have b := smallRun (branch d true)
    let e : Cells := {d with flag:=[]}
    obtain ⟨rr,subP,vr,sr⟩ := subtractMove e (N+1) rfl sp fit' (by simpa [e,d,doubled,val] using c)
    let e' : Cells := {e with remainder:=rr,flag:=[]}
    have fit2 : room e' (N+1) := ⟨sr,fit'.2⟩
    obtain ⟨zz,addP,vz,sz⟩ := addMove e' (N+1) rfl sp fit2
    have path := (((beginP.seq cmpP).seq b).seq subP).seq addP
    refine ⟨rr,zz,?_,⟨?_,?_⟩,by omega,by omega⟩
    · simpa [e',e,d,doubled,ht] using path.mono (show _ ≤ 12*(N+5) by omega)
    · simpa [e,d,doubled,val,c] using vr
    · simpa [e',e,d,doubled,val,c] using vz
  · have a : decide (val d.divisor ≤ val d.remainder) = false := by simpa [d,doubled,val] using c
    rw [a] at cmpP
    have path := (beginP.seq cmpP).seq (smallRun (branch d false))
    refine ⟨false::s.remainder,false::s.product,?_,?_,?_,?_⟩
    · simpa [d,doubled,ht] using path.mono (show _ ≤ 12*(N+5) by omega)
    · simp [c,val]
    · have := fit.1; simp; omega
    · have := fit.2.2.2.2; simp; omega

/-- Process all quotient bits by repeated doubling in a scaled denominator. -/
theorem rounds (t : List Bool) (s : Cells) (N M B w q : ℕ)
    (fit : room s N) (space : N+2*t.length ≤ M)
    (ht : s.todo=t) (flag : s.flag=[]) (sp : s.spare=[]) (num : t.length ≤ w)
    (hr : val s.remainder < val s.divisor)
    (eq : q*val s.divisor+val s.remainder=B*2^(w-t.length))
    (prod : val s.product = q*val s.binCount) :
    ∃ z : Cells, Runs (A 1) s (t.length*(12*(M+5))+1) (A 8) z ∧
      z.input=s.input ∧ z.divisor=s.divisor ∧ z.binCount=s.binCount ∧
      z.itemCount=s.itemCount ∧ z.dimension=s.dimension ∧ z.todo=[] ∧ z.prep=s.prep ∧
      z.reversed=s.reversed ∧ z.scratch=s.scratch ∧ z.flag=[] ∧ z.spare=[] ∧ room z M ∧
      ∃ qf, qf*val s.divisor+val z.remainder=B*2^w ∧ val z.remainder<val s.divisor ∧
        val z.product=qf*val s.binCount := by
  induction t generalizing s N q with
  | nil =>
    refine ⟨s,by simpa using smallRun (loopEnd s ht),rfl,rfl,rfl,rfl,rfl,ht,rfl,rfl,rfl,flag,sp,?_,
      q,by simpa using eq,hr,prod⟩
    rcases fit with ⟨f1,f2,f3,f4,f5⟩
    simp at space
    exact ⟨f1.trans space,f2.trans space,f3.trans space,f4.trans space,f5.trans space⟩
  | cons b bs ih =>
    obtain ⟨rr,pp,step,⟨vr,vp⟩,sr,sz⟩ := roundStep s N flag sp fit b bs ht
    let s' := {s with remainder:=rr,product:=pp,todo:=bs,flag:=[]}
    let take := val s.divisor ≤ 2*val s.remainder
    let q' := if take then 2*q+1 else 2*q
    have exp : w-bs.length = w-(b::bs).length+1 := by simp at *;omega
    have rlt : val rr<val s.divisor := by split at vr <;>omega
    have value : q'*val s.divisor+val rr=B*2^(w-bs.length) := by
      rw [exp,pow_succ]; by_cases c : take
      · have ge : val s.divisor≤2*val s.remainder := c
        rw [if_pos ge] at vr
        have sq := Nat.sub_add_cancel ge
        simp only [q',if_pos c];nlinarith only [eq,vr,sq]
      · have ng : ¬val s.divisor≤2*val s.remainder := c
        rw [if_neg ng] at vr
        simp only [q',if_neg c];nlinarith only [eq,vr]
    have product : val pp=q'*val s.binCount := by
      by_cases c : take
      · have c' : val s.divisor ≤ 2*val s.remainder := c
        simpa [q',c,c',prod,add_mul,Nat.mul_assoc] using vp
      · have c' : ¬val s.divisor ≤ 2*val s.remainder := c
        simpa [q',c,c',prod,Nat.mul_assoc] using vp
    have more : room s' (N+2) := by
      rcases fit with ⟨_,fd,fb,fa,_⟩; dsimp [s',room]; exact ⟨sr,by omega,by omega,by omega,sz⟩
    have u := ih s' (N+2) q' more (by simp at space;omega) rfl rfl sp (by simp at num;omega) rlt value product
    obtain ⟨z,trail,rest⟩ := u
    refine ⟨z,?_,rest⟩
    have c := step.seq trail
    apply c.mono
    simp only [List.length_cons,Nat.succ_mul]; have h : N≤M := by omega
    omega

theorem zeroPrefix (k : ℕ) (s : List Bool) : val (List.replicate k false ++ s) = val s*2^k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ,val,ih,pow_succ]; ring

end OneTypeTM

namespace OneTypeTM
open BitStacks HMBinPacking R

private theorem tape_only (w : List Bool) : ({input:=w} : Cells).mem = isolated (reg R.tape) w := by
  funext k
  cases k with
  | inl b => cases b <;> rfl
  | inr r => cases r <;> rfl

/-- Starting on the official five-field word, the bit-stack machine first scales a divisor,
then computes the quotient-product using one quotient digit per input bit. -/
theorem decideInput (B s a b : ℕ) (pos : 0<s) :
    OutputsWithin machine (input B s a b) [decide (a≤(B/s)*b)] (200*((input B s a b).length+1)^2) := by
  let L := (input B s a b).length
  let w := B.bits.length
  let n := 2*L
  let M := 4*L
  let p := parsed B s a b
  let u := {p with prep:=[],divisor:=List.replicate w false ++ s.bits}
  have lens : 2*(B.bits.length+s.bits.length+a.bits.length+b.bits.length)+7=L := (length_input _ _ _ _).symm
  have start := smallRun (readInput B s a b)
  have scaled : Goes (A 0) p (w+1) (A 1) u := by
    simpa [p,u,parsed,w] using scaleAll p (List.replicate w true)
  have initial : room u n := by
    simp [room,u,p,parsed,w,n]; omega
  have space : n+2*u.todo.length≤M := by
    simp [n,M,u,p,parsed,w]; omega
  have den : val u.divisor=s*2^w := by simp [u,zeroPrefix,val_bits]
  have rem : val u.remainder=B := by simp [u,p,parsed,val_bits]
  have bins : val u.binCount=b := by simp [u,p,parsed,val_bits]
  have num : u.todo.length=w := by simp [u,p,parsed,w]
  have small : B < 2^w := by simpa [w,Nat.size_eq_bits_len] using Nat.lt_size_self B
  have size : B < val u.divisor := by
    rw [den]; exact small.trans_le (by simpa using Nat.mul_le_mul_right (2^w) pos)
  have r := rounds u.todo u n M B w 0 initial space rfl rfl rfl num.le
    (rem ▸ size) (by simp [num,rem]) (by simp [u,p,parsed,val])
  obtain ⟨z,path,zi,zd,zb,za,zdim,zt,zp,zr,zsc,zf,zsp,fit,q,eq,rlt,prod⟩ := r
  rw [den] at eq rlt
  have nz : 0<2^w := by positivity
  have qval := congrArg (fun h : ℕ => h/(s*2^w)) eq
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.mul_pos pos nz),Nat.div_eq_of_lt rlt,
      Nat.zero_add,Nat.mul_div_mul_right _ _ nz] at qval
  have fin := finalCmp z M zf zsp fit
  have answer : decide (val z.itemCount≤val z.product) = decide (a≤(B/s)*b) := by
    rw [za,prod,qval,bins]; simp [u,p,parsed,val_bits]
  rw [answer] at fin
  let v := {z with flag:=[decide (a≤(B/s)*b)]}
  have fin' := smallRun (finish v (decide (a≤(B/s)*b)) zi rfl zsp)
  have bound : costClear v ≤ 5*M+12 := by
    obtain ⟨f1,f2,f3,f4,f5⟩ := fit
    simp [costClear,v,zt,zp,zr,zsc,zdim,u,p,parsed] ; omega
  have all := (((start.seq (smallRun scaled)).seq path).seq fin).seq fin'
  obtain ⟨t,ht,run⟩ := all
  apply MacroPath.outputs (t:=t)
  · rw [←tape_only,←tape_only]; exact run
  · have cut := cost_input B s a b
    change parseCost B s a b ≤ 3*(L+1) at cut
    rw [num] at ht
    change t ≤ 200*(L+1)^2
    have mult : w*(12*(M+5))≤L*(12*(M+5)) := Nat.mul_le_mul_right _ (by dsimp [w];omega)
    dsimp [M] at ht mult bound; nlinarith
end OneTypeTM

open HMBinPacking
namespace HeavyPacking

/-- Exact criterion for arbitrary capacities and arbitrary multiplicities of any
number of types of a common size. In particular it decides every one-type instance. -/
theorem equalSize_iff (I : Instance) (s : ℕ) (hs : 0 < s) (equal : ∀ i, I.s i = s) :
    Feasible I ↔ (∑ i, I.a i) ≤ I.b * (I.B / s) := by
  classical
  let Items := (i : Fin I.d) × Fin (I.a i)
  let k := I.B / s
  have hc : Fintype.card Items = ∑ i, I.a i := by simp [Items,Fintype.card_sigma]
  constructor
  · rintro ⟨f,h⟩
    have cap (j : Fin I.b) : (Finset.univ.filter (fun x : Items => f x = j)).card ≤ k := by
      apply (Nat.le_div_iff_mul_le hs).mpr
      simpa [equal] using h j
    have partitions := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset Items))
      (t := (Finset.univ : Finset (Fin I.b))) (f := f) (fun _ _ => Finset.mem_univ _)
    have sum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin I.b))) => cap j)
    rw [←partitions] at sum
    simpa [hc,k] using sum
  · intro h
    obtain ⟨g⟩ : Nonempty (Items ↪ Fin I.b × Fin k) :=
      Function.Embedding.nonempty_of_card_le (by simpa [hc,k] using h)
    refine ⟨fun x => (g x).1,fun j => ?_⟩
    let S := Finset.univ.filter (fun x : Items => (g x).1 = j)
    have bound : S.card ≤ k := by
      have h' := Finset.card_le_card_of_injOn (s := S) (t := (Finset.univ : Finset (Fin k)))
        (fun x => (g x).2) (fun _ _ => Finset.mem_univ _) (by
          intro x hx y hy hxy
          have px := (Finset.mem_filter.mp hx).2
          have py := (Finset.mem_filter.mp hy).2
          exact g.injective (Prod.ext (px.trans py.symm) hxy))
      simpa using h'
    have hcap := (Nat.le_div_iff_mul_le hs).mp bound
    simpa [S,equal] using hcap

end HeavyPacking

open HMBinPacking

/-- A single deterministic bit-stack Turing machine decides every one-type instance
within a quadratic bound in the original encoded input length. -/
theorem solution :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ I : Instance, I.d = 1 →
      (Feasible I → OutputsWithin M (encodeInstance I) [true] (200*(inputLength I+1)^2)) ∧
      (¬Feasible I → OutputsWithin M (encodeInstance I) [false] (200*(inputLength I+1)^2)) := by
  refine ⟨OneTypeTM.machine,?_⟩
  rintro ⟨B,d,s,a,b,Bpos,dpos,spos⟩ hd
  change d=1 at hd
  subst d
  let I : Instance := ⟨B,1,s,a,b,Bpos,dpos,spos⟩
  have enc : encodeInstance I = OneTypeTM.input B (s 0) (a 0) b := by
    simp [I,encodeInstance,encodeNatVec,OneTypeTM.input,List.ofFn_succ,List.append_assoc]
  have equal : Feasible I ↔ a 0 ≤ (B/s 0)*b := by
    have e := HeavyPacking.equalSize_iff I (s 0) (spos 0) (fun i => by
      have h : i=0 := Subsingleton.elim _ _
      subst i; rfl)
    simpa [I,Nat.mul_comm] using e
  have run := OneTypeTM.decideInput B (s 0) (a 0) b (spos _)
  rw [←enc] at run
  change (Feasible I → OutputsWithin _ (encodeInstance I) [true] _) ∧
    (¬Feasible I → OutputsWithin _ (encodeInstance I) [false] _)
  constructor
  · intro hf; simpa [equal.mp hf,inputLength] using run
  · intro hf; have h : ¬a 0 ≤ (B/s 0)*b := fun c => hf (equal.mpr c)
    simpa [h,inputLength] using run
