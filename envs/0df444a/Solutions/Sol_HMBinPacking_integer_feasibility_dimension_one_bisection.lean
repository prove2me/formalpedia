-- Prove2me | solution 1 for HMBinPacking.integer_feasibility_dimension_one_bisection
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:26:12.501407+00:00
-- url     : https://prove2.me/submissions/76daf403-044d-4a7e-b055-e3acc8b4ce92

import Mathlib.Tactic.Linarith
import Definitions.Def_HMBinPacking_OutputsWithin
import Mathlib.Tactic.FinCases
import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Positivity
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_HMBinPacking_Oracles
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith.Frontend

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

namespace DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
open ExponomialAssortment.FPTAS (encodeRat)
abbrev L := Bool ⊕ ((Fin 3 × Fin 2) ⊕ (Fin 8 ⊕ OneTypeTM.L))
def init (m : Bool) : L := .inl m
def old (l : OneTypeTM.L) : L := .inr (.inr (.inr l))
def H (p : Fin 2) : L := .inr (.inl (0,p))
def D (p : Fin 2) : L := .inr (.inl (1,p))
def V (p : Fin 2) : L := .inr (.inl (2,p))
def A (j : Fin 8) : L := .inr (.inr (.inl j))
def block (m : Bool) : List Bool := if m then encodeRat 0 else [false]
def suffix (m : Bool) : List Bool := if m then encodeRat (-1) else []
def tagWord (m : Bool) : List Bool := if m then [false] else []
def pushWord : List Bool → Action (Bank R) L → Action (Bank R) L
  | [],a => a
  | b::bs,a => pushWord bs (.push (reg tape) b a)
def jump (l : L) : Action (Bank R) L := .stop (some l)
def next (p : Fin 2) : L := if p=0 then H 1 else A 0
def dest (p : Fin 2) : R := if p=0 then rem else dim
def code : L → Macro R L
  | .inl m => .bits (.push (reg items) m (jump (H 0)))
  | .inr (.inr (.inr l)) => (OneTypeTM.code l).mapLabels old
  | .inr (.inl (tag,p)) =>
    if tag=0 then .bits (.peek (reg tape) (fun v => .drop (reg tape)
      (if v.getD false then .push (reg width) true (jump (H p)) else jump (D p))))
    else if tag=1 then .bits (.peek (reg width) (fun v => if v.isSome then
      .drop (reg width) (.peek (reg tape) (fun b => .drop (reg tape)
        (.push (reg rev) (b.getD false) (jump (D p))))) else jump (V p)))
    else .bits (.peek (reg rev) (fun b => match b with
      | none => jump (next p) | some bit => .drop (reg rev) (.push (reg (dest p)) bit (jump (V p)))))
  | .inr (.inr (.inl j)) => match j.val with
    | 0 => .bits (.peek (reg tape) (fun b => if b.isSome then .drop (reg tape) (jump (A 0)) else
        .peek (reg items) (fun m => pushWord (suffix (m.getD false)) (.push (reg den) true (jump (A 5))))))
    | 3 => .binary .sub dim den (by decide) (A 4)
    | 4 => .bits (.drop tmp (.peek (reg items) (fun m => pushWord (block (m.getD false)) (jump (A 5)))))
    | 5 => .binary .le dim prod (by decide) (A 6)
    | 6 => .bits (.peek tmp (fun b=>.drop tmp (jump (if b.getD false then A 7 else A 3))))
    | _ => .bits (.peek (reg items) (fun m => pushWord (tagWord (m.getD false)) (jump (old (OneTypeTM.C 0)))))
def machine (m : Bool) := BitStacks.machine (.inl (init m)) (reg tape) (wordCode code)
abbrev Goes (l : L) (s : Cells) (t : ℕ) (o : Option L) (z : Cells) :=
  MacroPath code (some l) s.mem t o z.mem
def Runs (l : L) (s : Cells) (bound : ℕ) (out : Option L) (t : Cells) : Prop := ∃ n ≤ bound, Goes l s n out t
theorem Runs.mono {i s a o t b} (h : Runs i s a o t) (le : a≤b) : Runs i s b o t := by
  obtain ⟨n,u,v⟩:=h; exact ⟨n,u.trans le,v⟩
theorem Runs.seq {i s a j t b k v} (h : Runs i s a (some j) t) (q : Runs j t b k v) : Runs i s (a+b) k v := by
  obtain ⟨n,u,x⟩:=h;obtain ⟨m,z,y⟩:=q;exact ⟨n+m,Nat.add_le_add u z,x.join y⟩
theorem smallRun {i s t o z} (h : Goes i s t o z) : Runs i s t o z := ⟨t,le_rfl,h⟩
theorem pushRun (w : List Bool) (a : Action (Bank R) L) (s : Cells) :
    (pushWord w a).run s.mem=a.run ({s with input:=w++s.input}:Cells).mem := by
  induction w generalizing a with
  | nil => rfl
  | cons b bs ih => rw [pushWord,ih];simp [Action.run]

theorem clean (s : Cells) (hf : s.flag=[]) (hsp : s.spare=[]) :
    Runs (old (OneTypeTM.C 0)) s (OneTypeTM.costClear s) none ({input:=s.input}:Cells) := by
  let m0 := s
  let m1 := {m0 with remainder:=[]}
  have p1 : OneTypeTM.Goes (OneTypeTM.C 0) m0 (s.remainder.length+1) (OneTypeTM.C 1) m1 := OneTypeTM.clearStep 0 _ m0
  let m2 := {m1 with divisor:=[]}
  have p2 : OneTypeTM.Goes (OneTypeTM.C 1) m1 (s.divisor.length+1) (OneTypeTM.C 2) m2 := OneTypeTM.clearStep 1 _ m1
  let m3 := {m2 with binCount:=[]}
  have p3 : OneTypeTM.Goes (OneTypeTM.C 2) m2 (s.binCount.length+1) (OneTypeTM.C 3) m3 := OneTypeTM.clearStep 2 _ m2
  let m4 := {m3 with itemCount:=[]}
  have p4 : OneTypeTM.Goes (OneTypeTM.C 3) m3 (s.itemCount.length+1) (OneTypeTM.C 4) m4 := OneTypeTM.clearStep 3 _ m3
  let m5 := {m4 with product:=[]}
  have p5 : OneTypeTM.Goes (OneTypeTM.C 4) m4 (s.product.length+1) (OneTypeTM.C 5) m5 := OneTypeTM.clearStep 4 _ m4
  let m6 := {m5 with prep:=[]}
  have p6 : OneTypeTM.Goes (OneTypeTM.C 5) m5 (s.prep.length+1) (OneTypeTM.C 6) m6 := OneTypeTM.clearStep 5 _ m5
  let m7 := {m6 with todo:=[]}
  have p7 : OneTypeTM.Goes (OneTypeTM.C 6) m6 (s.todo.length+1) (OneTypeTM.C 7) m7 := OneTypeTM.clearStep 6 _ m6
  let m8 := {m7 with reversed:=[]}
  have p8 : OneTypeTM.Goes (OneTypeTM.C 7) m7 (s.reversed.length+1) (OneTypeTM.C 8) m8 := OneTypeTM.clearStep 7 _ m7
  let m9 := {m8 with scratch:=[]}
  have p9 : OneTypeTM.Goes (OneTypeTM.C 8) m8 (s.scratch.length+1) (OneTypeTM.C 9) m9 := OneTypeTM.clearStep 8 _ m8
  let m10 := {m9 with dimension:=[]}
  have p10 : OneTypeTM.Goes (OneTypeTM.C 9) m9 (s.dimension.length+1) none m10 := OneTypeTM.clearStep 9 _ m9
  have path := (((((((((p1.join p2).join p3).join p4).join p5).join p6).join p7).join p8).join p9).join p10)
  have final : m10 = ({input:=s.input} : Cells) := by simp [m10,m9,m8,m7,m6,m5,m4,m3,m2,m1,m0,hsp,hf]
  rw [final] at path
  have sim := path.mapLabels (Q:=code) old (by intro l;rfl)
  refine ⟨_,?_,sim⟩
  simp [OneTypeTM.costClear];omega
end DimensionEmitter

namespace DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
private theorem val_small (w : List Bool) : val w < 2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih => cases b <;> simp [val,pow_succ] <;> omega

theorem decrement (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true])
    (mode : Bool) (type : s.itemCount=[mode]) (n : ℕ) (v : val s.dimension=n+1) :
    ∃ d : List Bool, Runs (A 3) s (3*(s.dimension.length+1)+8) (A 5) {s with dimension:=d,flag:=[],input:=block mode++s.input} ∧
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
  have pop : Goes (A 4) mid 1 (A 5) {s with dimension:=z.2.1,flag:=[],input:=block mode++s.input} := by simpa [mid,code,A,Action.run,jump,pushRun,type] using step
  refine ⟨z.2.1,⟨_,?_,gate.join pop⟩,value,by simpa [a] using len.le⟩
  simp [gateTime,zl,right,len,a]; omega

theorem testDim (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true]) (prod0 : s.product=[]) :
    Runs (A 5) s (3*s.dimension.length+7)
      (if val s.dimension=0 then A 7 else A 3)
      {s with flag:=[]} := by
  have e := MacroPath.binary (P:=code) (l:=A 5) (m:=s.mem) (op:=.le) (i:=dim) (j:=prod)
    (h:=by decide) (n:=A 6) (by rfl) f sp
  let z := execute compareGate true s.dimension s.product
  obtain ⟨ans,left,right⟩ := le_correct s.dimension s.product
  change z.1=_ at ans; change z.2.1=_ at left; change z.2.2=_ at right
  have zl : gateResult .le s.mem dim prod = z := rfl
  let mid := {s with flag:=[z.1]}
  have gate : Goes (A 5) s (gateTime .le s.mem dim prod) (A 6) mid := by simpa [zl,afterGate,mid,left,right] using e
  have step := MacroPath.bits (P:=code) (l:=A 6) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 6) mid 1 (if val s.dimension=0 then A 7 else A 3)
      {s with flag:=[]} := by
    by_cases c : val s.dimension=0 <;> simpa [mid,code,A,Action.run,jump,ans,prod0,val,c,a] using step
  refine ⟨_,?_,gate.join pop⟩
  simp [gateTime,zl,left,right,prod0]; omega


end DimensionEmitter

open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
namespace DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R

def putWord (p : Fin 2) (w : List Bool) (m : Cells) : Cells :=
  if p=0 then {m with remainder:=w++m.remainder} else {m with dimension:=w++m.dimension}
def putInput (_ : Fin 2) (w : List Bool) (m : Cells) : Cells := {m with input:=w}

private theorem HT (p : Fin 2) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (true::bs) m) 1 (H p)
      (putInput p bs {m with scratch:=true::m.scratch}) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (true::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,putInput,Action.run,jump] using e

private theorem HF (p : Fin 2) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (false::bs) m) 1 (D p) (putInput p bs m) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (false::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,D,putInput,Action.run,jump] using e

private theorem header (p : Fin 2) (k : ℕ) (m : Cells) (t : List Bool) :
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

private theorem DT (p : Fin 2) (m : Cells) (b : Bool) (t c : List Bool) :
    Goes (D p) (putInput p (b::t) {m with scratch:=true::c}) 1 (D p)
      (putInput p t {m with scratch:=c,reversed:=b::m.reversed}) := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=(putInput p (b::t) {m with scratch:=true::c}).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,D,putInput,Action.run,jump] using e
private theorem DF (p : Fin 2) (m : Cells) :
    Goes (D p) {m with scratch:=[]} 1 (V p) {m with scratch:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=({m with scratch:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,D,V,Action.run,jump] using e

private theorem digits (p : Fin 2) (bs t : List Bool) (m : Cells) :
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

private theorem VT (p : Fin 2) (m : Cells) (b : Bool) (r : List Bool) :
    Goes (V p) {m with reversed:=b::r} 1 (V p) (putWord p [b] {m with reversed:=r}) := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=b::r}:Cells).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,V,Action.run,jump,putWord,dest] using e

private theorem VF (p : Fin 2) (m : Cells) :
    Goes (V p) {m with reversed:=[]} 1 (next p) {m with reversed:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,V,Action.run,jump] using e

private theorem backwards (p : Fin 2) (bs : List Bool) (m : Cells) :
    Goes (V p) {m with reversed:=bs} (bs.length+1) (next p) (putWord p bs.reverse {m with reversed:=[]}) := by
  induction bs generalizing m with
  | nil => fin_cases p <;> simpa [putWord] using VF _ m
  | cons b bs ih =>
    have st := VT p m b bs
    have t := ih (putWord p [b] m)
    fin_cases p <;> simp [putWord] at st t ⊢ <;>
      first | simpa [List.append_assoc,Nat.add_comm 1] using st.join t

theorem field (p : Fin 2) (n : ℕ) (t : List Bool) (m : Cells) (hs : m.scratch=[]) (hr : m.reversed=[]) :
    Goes (H p) (putInput p (encodeNat n++t) m) (3*(n.bits.length+1)) (next p)
      (putWord p n.bits (putInput p t m)) := by
  have h := header p n.bits.length m (n.bits++t)
  have d := digits p n.bits t m
  have r := backwards p n.bits.reverse (putInput p t m)
  fin_cases p <;> simp [putInput,hs,hr] at h d r ⊢ <;>
    have z := (h.join d).join r <;>
    simpa [encodeNat,List.append_assoc,Nat.mul_comm,Nat.mul_add,Nat.mul_succ,Nat.add_assoc,hs,hr] using z

end DimensionEmitter

namespace DimensionEmitter.Extended
open DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)
def repeatWord (m : Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => block m++repeatWord m n

private theorem repeat_last (m : Bool) (n : ℕ) : repeatWord m n++block m=block m++repeatWord m n := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord,List.append_assoc,ih]

private theorem remaining (bs : List Bool) (s : Cells) (m : Bool) (type : s.itemCount=[m]) :
    Goes (A 0) {s with input:=bs} (bs.length+1) (A 5) {s with input:=suffix m,divisor:=true::s.divisor} := by
  induction bs with
  | nil =>
    have a := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump,pushRun,type] using a
  | cons b bs ih =>
    have a := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (A 0) {s with input:=b::bs} 1 (A 0) {s with input:=bs} := by
      simpa [code,A,Action.run,jump] using a
    simpa [Nat.add_comm 1] using one.join ih

private theorem loop (n K : ℕ) (s : Cells) (m : Bool) (type : s.itemCount=[m])
    (v : val s.dimension=n) (unit : s.divisor=[true]) (zero : s.product=[])
    (f : s.flag=[]) (sp : s.spare=[]) (lim : s.dimension.length≤K) (pos : 1≤K) :
    ∃ ds : List Bool, Runs (A 5) s ((n+1)*(10*(K+3))) (A 7)
      {s with dimension:=ds,flag:=[],input:=repeatWord m n++s.input} ∧ ds.length≤K := by
  induction n generalizing s with
  | zero =>
    have check := testDim s f sp unit zero
    simp [v] at check
    refine ⟨s.dimension,?_,lim⟩
    simpa [repeatWord] using check.mono (show 3*s.dimension.length+7≤(0+1)*(10*(K+3)) by omega)
  | succ n ih =>
    have check := testDim s f sp unit zero
    simp [v] at check
    obtain ⟨ds,dec,eq,len⟩ := decrement {s with flag:=[]} rfl sp unit m type n v
    let t := {s with dimension:=ds,flag:=[],input:=block m++s.input}
    have dsl : ds.length≤K := by change ds.length ≤ max s.dimension.length 1 at len;omega
    obtain ⟨ws,lp,ll⟩ := ih t type eq unit zero rfl sp dsl
    have path := (check.seq dec).seq lp
    refine ⟨ws,?_,ll⟩
    have tm : 3*s.dimension.length+7+(3*(s.dimension.length+1)+8)+((n+1)*(10*(K+3)))≤(n+1+1)*(10*(K+3)) := by
      rw [Nat.succ_mul (n+1)];omega
    simpa [t,repeatWord,←List.append_assoc,repeat_last] using path.mono tm

private theorem bitsValue (n : ℕ) : val n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit _ _ h,val,ih,Nat.bit_val];omega

private theorem isolatedWord (w : List Bool) : ({input:=w}:Cells).mem = isolated (reg tape) w := by
  funext k
  cases k with
  | inl z => cases z <;>rfl
  | inr z => cases z <;>rfl

def raw (B d : ℕ) (t : List Bool) := encodeNat B++(encodeNat d++t)
def result (m : Bool) (d : ℕ) := tagWord m++(repeatWord m d ++ suffix m)

theorem emitLarge (m : Bool) (B d : ℕ) (t : List Bool) :
    OutputsWithin (machine m) (raw B d t) (result m d) (100*((raw B d t).length+1+d)^2) := by
  let word := raw B d t
  let K := word.length+1
  let initCells : Cells := {input:=word}
  let initial := {initCells with itemCount:=[m]}
  have a := MacroPath.bits (P:=code) (l:=init m) (m:=initCells.mem) (a:=_) (by rfl)
  have start : Goes (init m) initCells 1 (H 0) initial := by simpa [code,init,initial,Action.run,jump] using a
  let s0 : Cells := {itemCount:=[m]}
  let s1 := {s0 with input:=encodeNat d++t,remainder:=B.bits}
  let s2 := {s1 with input:=t,dimension:=d.bits}
  let s3 := {s2 with input:=suffix m,divisor:=[true]}
  have f0 : Goes (H 0) initial (3*(B.bits.length+1)) (H 1) s1 := by
    simpa [initial,initCells,word,raw,s0,s1,putWord,putInput,next] using field 0 B (encodeNat d++t) s0 rfl rfl
  have f1 : Goes (H 1) s1 (3*(d.bits.length+1)) (A 0) s2 := by
    simpa [s1,s2,s0,putWord,putInput,next] using field 1 d t s1 rfl rfl
  have purge : Goes (A 0) s2 (t.length+1) (A 5) s3 := remaining t s2 m rfl
  have size : 2*(B.bits.length+d.bits.length)+2+t.length+1=K := by simp [K,word,raw,encodeNat];omega
  obtain ⟨ds,lp,dsl⟩ := loop d K s3 m rfl (bitsValue _) rfl rfl rfl rfl (by dsimp [s3,s2];omega) (by omega)
  let z := {s3 with dimension:=ds,flag:=[],input:=repeatWord m d++suffix m}
  let out := {z with input:=result m d}
  have g := MacroPath.bits (P:=code) (l:=A 7) (m:=z.mem) (a:=_) (by rfl)
  have finish : Goes (A 7) z 1 (old (OneTypeTM.C 0)) out := by
    simpa [z,s3,s2,s1,s0,out,code,A,Action.run,jump,result,pushRun] using g
  have done := clean out rfl rfl
  obtain ⟨n,nt,path⟩:=((((((smallRun start).seq (smallRun f0)).seq (smallRun f1)).seq (smallRun purge)).seq lp).seq (smallRun finish)).seq done
  apply MacroPath.outputs (t:=n)
  · rw [←isolatedWord,←isolatedWord];exact path
  · have c : OneTypeTM.costClear out≤3*K+14 := by simp [out,z,s3,s2,s1,s0,OneTypeTM.costClear];omega
    have bd : d+1≤K+d := by omega
    have bound:=Nat.mul_le_mul_right (10*(K+3)) bd
    change n≤100*(K+d)^2
    nlinarith only [nt,bound,c,size]
end DimensionEmitter.Extended

open Turing
namespace BitStacks
variable {K J : Type} [DecidableEq K] [Fintype K] [Fintype J]

/-- A bounded Prove2Me run of a compiled stack program can itself be used as a
bounded subroutine trace. No reflection or new time assumption is needed. -/
theorem ofOutputs {entry : J} {io : K} {code : J→Action K J} {s w : List Bool} {T : ℕ}
    (h : HMBinPacking.OutputsWithin (machine entry io code) s w T) :
    ∃ t≤T,Path code (some entry) (isolated io s) t none (isolated io w) := by
  let M:=machine entry io code
  let c (l : Option J) (m : Mem K) : M.tm.Cfg := ⟨l,none,m⟩
  have soundBack (t : ℕ) (l l' : Option J) (m n : Mem K)
      (e : (flip bind M.tm.step)^[t] (some (c l m))=some (c l' n)) : Path code l m t l' n := by
    induction t generalizing l m with
    | zero =>
      change some (c l m)=some (c l' n) at e
      have a:= congrArg (fun q => q.l) (Option.some.inj e)
      have b:= congrArg (fun q => q.stk) (Option.some.inj e)
      change l=l' at a;change m=n at b;subst l';subst n;exact .refl _ _
    | succ t ih =>
      rw [Function.iterate_succ_apply] at e
      cases l with
      | none =>
        have stay (k : ℕ) : (flip bind M.tm.step)^[k] none=none := by induction k with
          | zero=>rfl
          | succ k ih => rw [Function.iterate_succ_apply];exact ih
        change (flip bind M.tm.step)^[t] none=some _ at e
        rw [stay] at e;cases e
      | some l =>
        have s1 : flip bind M.tm.step (some (c (some l) m))=some (c ((code l).run m).1 ((code l).run m).2) := by
          change some (TM2.stepAux (code l).compile none m)=_;rw [Action.correct];rfl
        rw [s1] at e
        simpa [Nat.add_comm 1] using (Path.step (code:=code) (l:=l) (m:=m)).join (ih _ _ e)
  obtain ⟨⟨trace,clock⟩⟩ := h
  obtain ⟨t,e⟩:=trace
  refine ⟨t,clock,?_⟩
  apply soundBack
  have eqmap (x : List Bool) : x.map M.inputAlphabet.symm=x := List.map_id _
  have eqout (x : List Bool) : x.map M.outputAlphabet.symm=x := List.map_id _
  change (flip bind M.tm.step)^[t] (some (initList M.tm (s.map M.inputAlphabet.symm)))=
    some (haltList M.tm (w.map M.outputAlphabet.symm)) at e
  rw [eqmap,eqout] at e;exact e
end BitStacks

namespace BitGrid
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
abbrev L:=Fin 9
def jump (i:L):Action (Bank R) L:=.stop (some i)
def branch (r : R) (act done : Action (Bank R) L) := Action.peek (reg r) fun b=>if b.isSome then .drop (reg r) act else done
def digit (a:Action (Bank R) L):=Action.push (reg tape) false (.push (reg tape) true a)
def code (i:L) : Action (Bank R) L := match i.val with
 | 0=>branch tape (.push (reg rem) false (.push (reg den) false (.push (reg bins) false (jump 0)))) (jump 1)
 | 1=>branch rem (jump 2) (jump 4)
 | 2=>branch den (.push (reg prod) false (.push (reg width) false (jump 2))) (jump 3)
 | 3=>branch width (.push (reg den) false (jump 3)) (jump 1)
 | 4=>branch den (jump 4) (jump 5)
 | 5=>branch bins (.push (reg tape) false (jump 6)) (jump 8)
 | 6=>branch prod (.push (reg width) false (digit (jump 6))) (jump 7)
 | 7=>branch width (.push (reg prod) false (jump 7)) (digit (jump 5))
 | _=>branch prod (jump 8) (.stop none)
def copies (w:List Bool):ℕ→List Bool
  | 0=>[] | k+1=>w++copies w k
def u (n:ℕ):=copies [false] n
def d (n:ℕ):=copies [true,false] n
def grid (n m:ℕ):=copies (d (m+1)++[false]) n
@[simp] theorem repeat_zero (w:List Bool):copies w 0=[]:=rfl
@[simp] theorem repeat_next (w:List Bool) (n:ℕ):copies w (n+1)=w++copies w n:=rfl
theorem rep_last (w:List Bool) (n:ℕ):copies w n++w=w++copies w n:=by induction n with
 | zero=>simp | succ n ih=>simp [List.append_assoc,ih]
theorem rep_comm (w:List Bool) (n:ℕ) (t:List Bool):copies w n++(w++t)=w++(copies w n++t):=by
 rw [←List.append_assoc,rep_last,List.append_assoc]
theorem rep_add (w:List Bool) (n m:ℕ):copies w (n+m)=copies w n++copies w m:=by
 induction n with
 | zero=>simp | succ n ih=>rw [Nat.succ_add];simp [ih,List.append_assoc]
@[simp] theorem u_zero : u 0=[]:=rfl
@[simp] theorem u_next (n:ℕ): u (n+1)=false::u n:=rfl
@[simp] theorem d_zero : d 0=[]:=rfl
@[simp] theorem d_next (n:ℕ):d (n+1)=true::false::d n:=rfl
@[simp] theorem u_comm (n:ℕ) (t:List Bool):u n++false::t=false::(u n++t):=rep_comm [false] n t
@[simp] theorem d_comm (n:ℕ) (t:List Bool):d n++true::false::t=true::false::(d n++t):=rep_comm [true,false] n t
abbrev Goes (i:L) (s:Cells) (t:ℕ) (j:Option L) (z:Cells):=Path code (some i) s.mem t j z.mem
theorem fork (n:ℕ) (s:Cells) :
    Goes 0 {s with input:=u n} (n+1) (some 1) {s with input:=[],remainder:=u n++s.remainder,divisor:=u n++s.divisor,binCount:=u n++s.binCount} := by
  induction n generalizing s with
  | zero=>simpa [Goes,code,branch,digit,jump,Action.run] using
      (Path.step (code:=code) (l:=0) (m:=({s with input:=[]}:Cells).mem))
  | succ n ih=>
    let z:Cells:={s with remainder:=false::s.remainder,divisor:=false::s.divisor,binCount:=false::s.binCount}
    have st : Goes 0 {s with input:=u (n+1)} 1 (some 0) {z with input:=u n} := by
      simpa [Goes,code,branch,digit,jump,Action.run,z] using
        (Path.step (code:=code) (l:=0) (m:=({s with input:=u (n+1)}:Cells).mem))
    simpa [z,Nat.add_comm 1] using st.join (ih z)
theorem multiply (n:ℕ) (s:Cells) :
    Goes 2 {s with divisor:=u n} (n+1) (some 3) {s with divisor:=[],product:=u n++s.product,scratch:=u n++s.scratch} := by
  induction n generalizing s with
  | zero=>simpa [Goes,code,branch,digit,jump,Action.run] using
      (Path.step (code:=code) (l:=2) (m:=({s with divisor:=[]}:Cells).mem))
  | succ n ih=>
    let z:Cells:={s with product:=false::s.product,scratch:=false::s.scratch}
    have st : Goes 2 {s with divisor:=u (n+1)} 1 (some 2) {z with divisor:=u n} := by
      simpa [Goes,code,branch,digit,jump,Action.run,z] using
        (Path.step (code:=code) (l:=2) (m:=({s with divisor:=u (n+1)}:Cells).mem))
    simpa [z,Nat.add_comm 1] using st.join (ih z)
theorem restoreDen (n:ℕ) (s:Cells) :
    Goes 3 {s with scratch:=u n} (n+1) (some 1) {s with scratch:=[],divisor:=u n++s.divisor} := by
  induction n generalizing s with
  | zero=>simpa [Goes,code,branch,digit,jump,Action.run] using
      (Path.step (code:=code) (l:=3) (m:=({s with scratch:=[]}:Cells).mem))
  | succ n ih=>
    let z:Cells:={s with divisor:=false::s.divisor}
    have st : Goes 3 {s with scratch:=u (n+1)} 1 (some 3) {z with scratch:=u n} := by
      simpa [Goes,code,branch,digit,jump,Action.run,z] using
        (Path.step (code:=code) (l:=3) (m:=({s with scratch:=u (n+1)}:Cells).mem))
    simpa [z,Nat.add_comm 1] using st.join (ih z)
theorem wipeDen (n:ℕ) (s:Cells) :
    Goes 4 {s with divisor:=u n} (n+1) (some 5) {s with divisor:=[]} := by
  induction n generalizing s with
  | zero=>simpa [Goes,code,branch,digit,jump,Action.run] using
      (Path.step (code:=code) (l:=4) (m:=({s with divisor:=[]}:Cells).mem))
  | succ n ih=>
    let z:Cells:=s
    have st : Goes 4 {s with divisor:=u (n+1)} 1 (some 4) {z with divisor:=u n} := by
      simpa [Goes,code,branch,digit,jump,Action.run,z] using
        (Path.step (code:=code) (l:=4) (m:=({s with divisor:=u (n+1)}:Cells).mem))
    simpa [z,Nat.add_comm 1] using st.join (ih z)
theorem putDigits (n:ℕ) (s:Cells) :
    Goes 6 {s with product:=u n} (n+1) (some 7) {s with product:=[],scratch:=u n++s.scratch,input:=d n++s.input} := by
  induction n generalizing s with
  | zero=>simpa [Goes,code,branch,digit,jump,Action.run] using
      (Path.step (code:=code) (l:=6) (m:=({s with product:=[]}:Cells).mem))
  | succ n ih=>
    let z:Cells:={s with scratch:=false::s.scratch,input:=true::false::s.input}
    have st : Goes 6 {s with product:=u (n+1)} 1 (some 6) {z with product:=u n} := by
      simpa [Goes,code,branch,digit,jump,Action.run,z] using
        (Path.step (code:=code) (l:=6) (m:=({s with product:=u (n+1)}:Cells).mem))
    simpa [z,Nat.add_comm 1] using st.join (ih z)
theorem restoreProd (n:ℕ) (s:Cells) :
    Goes 7 {s with scratch:=u n} (n+1) (some 5) {s with scratch:=[],product:=u n++s.product,input:=true::false::s.input} := by
  induction n generalizing s with
  | zero=>simpa [Goes,code,branch,digit,jump,Action.run] using
      (Path.step (code:=code) (l:=7) (m:=({s with scratch:=[]}:Cells).mem))
  | succ n ih=>
    let z:Cells:={s with product:=false::s.product}
    have st : Goes 7 {s with scratch:=u (n+1)} 1 (some 7) {z with scratch:=u n} := by
      simpa [Goes,code,branch,digit,jump,Action.run,z] using
        (Path.step (code:=code) (l:=7) (m:=({s with scratch:=u (n+1)}:Cells).mem))
    simpa [z,Nat.add_comm 1] using st.join (ih z)
theorem wipeProd (n:ℕ) (s:Cells) :
    Goes 8 {s with product:=u n} (n+1) none {s with product:=[]} := by
  induction n generalizing s with
  | zero=>simpa [Goes,code,branch,digit,jump,Action.run] using
      (Path.step (code:=code) (l:=8) (m:=({s with product:=[]}:Cells).mem))
  | succ n ih=>
    let z:Cells:=s
    have st : Goes 8 {s with product:=u (n+1)} 1 (some 8) {z with product:=u n} := by
      simpa [Goes,code,branch,digit,jump,Action.run,z] using
        (Path.step (code:=code) (l:=8) (m:=({s with product:=u (n+1)}:Cells).mem))
    simpa [z,Nat.add_comm 1] using st.join (ih z)
end BitGrid

namespace BitGrid.Radius
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
abbrev L:=Fin 12 ⊕ (Bool ⊕ BitGrid.L)
def a(i:Fin 12):L:=.inl i
def back(b:Bool):L:=.inr (.inl b)
def grow(i:BitGrid.L):L:=.inr (.inr i)
def jump(i:L):Action (Bank R) L:=.stop (some i)
def branch(r:R)(act endA:Action (Bank R) L):Action (Bank R) L:=.peek (reg r) fun v=>if v.isSome then .drop (reg r) act else endA
def hd(r:R)(on stop:Action (Bank R) L):Action (Bank R) L:=.peek (reg r) fun v=>.drop (reg r) (if v.getD false then on else stop)
def code:L→Action (Bank R) L
 | .inr (.inr i)=>(BitGrid.code i).rename (.refl _) (fun o=>o.map grow)
 | .inr (.inl b)=>branch width (.push (reg bins) false (jump (back b))) (if b then .push (reg bins) false (jump (a 7)) else jump (a 7))
 | .inl i=>match i.val with
   | 0=>hd tape (.push (reg width) false (jump (a 0))) (jump (a 1))
   | 1=>branch width (.peek (reg tape) (fun b=>.drop (reg tape) (.push (reg dim) (b.getD false) (jump (a 1)))))
       (.drop (reg tape) (.push (reg prod) false (jump (a 2))))
   | 2=>hd tape (.push (reg prod) false (.push (reg width) false (jump (a 2)))) (jump (a 3))
   | 3=>branch width (.drop (reg tape) (jump (a 3))) (jump (a 4))
   | 4=>hd tape (.drop (reg prod) (jump (a 4))) (jump (a 5))
   | 5=>branch tape (jump (a 5)) (jump (a 7))
   | 7=>.peek (reg dim) (fun v=>match v with | none=>jump (grow 5) | some b=>.drop (reg dim) (jump (if b then a 9 else a 8)))
   | 8=>branch bins (.push (reg width) false (.push (reg width) false (jump (a 8)))) (jump (back false))
   | _=>branch bins (.push (reg width) false (.push (reg width) false (jump (a 9)))) (jump (back true))
abbrev Goes (i:L) (s:Cells) (n:ℕ) (j:Option L) (z:Cells):=Path code (some i) s.mem n j z.mem
theorem iso(w:List Bool):({input:=w}:Cells).mem=isolated (reg tape) w:=by
 funext r;cases r with | inl t=>cases t <;>rfl | inr t=>cases t <;>rfl
def mWidth (T:ℚ):=T.num.natAbs.size+1-T.den.size
theorem headerN (k:ℕ) (tail:List Bool) (s:Cells):Goes (a 0) {s with input:=List.replicate k true++false::tail} (k+1) (a 1) {s with input:=tail,scratch:=u k++s.scratch} := by
  induction k generalizing s with
  | zero=>simpa [Goes,code,a,hd,jump,Action.run] using
      (Path.step (code:=code) (l:=a 0) (m:=({s with input:=false::tail}:Cells).mem))
  | succ k ih=>
    let z:Cells:={s with scratch:=false::s.scratch}
    have on:Goes (a 0) {s with input:=List.replicate (k+1) true++false::tail} 1 (a 0) {z with input:=List.replicate k true++false::tail}:=by
      simpa [Goes,code,a,hd,jump,Action.run,z,List.replicate_succ] using
        (Path.step (code:=code) (l:=a 0) (m:=({s with input:=List.replicate (k+1) true++false::tail}:Cells).mem))
    simpa [z,Nat.add_comm 1] using on.join (ih z)
theorem headerNum (k:ℕ) (tail:List Bool) (s:Cells):Goes (a 2) {s with input:=List.replicate k true++false::tail} (k+1) (a 3) {s with input:=tail,product:=u k++s.product,scratch:=u k++s.scratch} := by
  induction k generalizing s with
  | zero=>simpa [Goes,code,a,hd,jump,Action.run] using
      (Path.step (code:=code) (l:=a 2) (m:=({s with input:=false::tail}:Cells).mem))
  | succ k ih=>
    let z:Cells:={s with product:=false::s.product,scratch:=false::s.scratch}
    have on:Goes (a 2) {s with input:=List.replicate (k+1) true++false::tail} 1 (a 2) {z with input:=List.replicate k true++false::tail}:=by
      simpa [Goes,code,a,hd,jump,Action.run,z,List.replicate_succ] using
        (Path.step (code:=code) (l:=a 2) (m:=({s with input:=List.replicate (k+1) true++false::tail}:Cells).mem))
    simpa [z,Nat.add_comm 1] using on.join (ih z)
end BitGrid.Radius

namespace BitGrid.Radius
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
theorem dataN (bs:List Bool) (neg:Bool) (tail:List Bool) (s:Cells):
   Goes (a 1) {s with input:=bs++neg::tail,scratch:=u bs.length} (bs.length+1) (a 2)
     {s with input:=tail,scratch:=[],dimension:=bs.reverse++s.dimension,product:=false::s.product}:=by
  induction bs generalizing s with
  | nil=>simpa [Goes,code,a,branch,jump,Action.run] using (Path.step (code:=code) (l:=a 1) (m:=({s with input:=neg::tail,scratch:=[]}:Cells).mem))
  | cons b bs ih=>
    let z:Cells:={s with dimension:=b::s.dimension}
    have st:Goes (a 1) {s with input:=(b::bs)++neg::tail,scratch:=u (bs.length+1)} 1 (a 1) {z with input:=bs++neg::tail,scratch:=u bs.length} := by
      simpa [Goes,code,a,branch,jump,Action.run,z] using (Path.step (code:=code) (l:=a 1) (m:=({s with input:=(b::bs)++neg::tail,scratch:=u (bs.length+1)}:Cells).mem))
    simpa [z,List.append_assoc,Nat.add_comm 1] using st.join (ih z)
theorem dataNum (bs tail:List Bool) (s:Cells):Goes (a 3) {s with input:=bs++tail,scratch:=u bs.length} (bs.length+1) (a 4) {s with input:=tail,scratch:=[]} := by
  induction bs with
  | nil=>simpa [Goes,code,a,branch,jump,Action.run] using (Path.step (code:=code) (l:=a 3) (m:=({s with input:=tail,scratch:=[]}:Cells).mem))
  | cons b bs ih=>
    have st:Goes (a 3) {s with input:=(b::bs)++tail,scratch:=u (bs.length+1)} 1 (a 3) {s with input:=bs++tail,scratch:=u bs.length} := by
      simpa [Goes,code,a,branch,jump,Action.run] using (Path.step (code:=code) (l:=a 3) (m:=({s with input:=(b::bs)++tail,scratch:=u (bs.length+1)}:Cells).mem))
    simpa [Nat.add_comm 1] using st.join ih
theorem dataDen (k p:ℕ) (tail:List Bool) (s:Cells) : Goes (a 4) {s with input:=List.replicate k true++false::tail,product:=u p}
   (k+1) (a 5) {s with input:=tail,product:=u (p-k)}:=by
  induction k generalizing p with
  | zero=>simpa [Goes,code,a,hd,jump,Action.run] using (Path.step (code:=code) (l:=a 4) (m:=({s with input:=false::tail,product:=u p}:Cells).mem))
  | succ k ih=>
    have st:Goes (a 4) {s with input:=List.replicate (k+1) true++false::tail,product:=u p} 1 (a 4)
         {s with input:=List.replicate k true++false::tail,product:=u (p-1)} := by
      have z:=Path.step (code:=code) (l:=a 4) (m:=({s with input:=List.replicate (k+1) true++false::tail,product:=u p}:Cells).mem)
      cases p <;>simpa [Goes,code,a,hd,jump,Action.run,List.replicate_succ] using z
    simpa [Nat.sub_sub,Nat.add_comm 1] using st.join (ih (p-1))
theorem clearTail (bs:List Bool) (s:Cells):Goes (a 5) {s with input:=bs} (bs.length+1) (a 7) {s with input:=[]}:=by
  induction bs with
  | nil=>simpa [Goes,code,a,branch,jump,Action.run] using (Path.step (code:=code) (l:=a 5) (m:=({s with input:=[]}:Cells).mem))
  | cons b bs ih=>
    have st:Goes (a 5) {s with input:=b::bs} 1 (a 5) {s with input:=bs} := by
      simpa [Goes,code,a,branch,jump,Action.run] using (Path.step (code:=code) (l:=a 5) (m:=({s with input:=b::bs}:Cells).mem))
    simpa [Nat.add_comm 1] using st.join ih
theorem parse (n:ℕ) (T:ℚ) (tail:List Bool) :
  let raw:=encodeNat n++encodeRat T++tail
  ∃ t≤3*raw.length+10,Goes (a 0) {input:=raw} t (a 7) {dimension:=n.bits.reverse,product:=u (mWidth T)} := by
  let N:=T.num.natAbs.bits
  let D:=T.den.bits
  let dh:=List.replicate D.length true++false::(D++tail)
  let nh:=List.replicate N.length true++false::(N++dh)
  let sg:=decide (T.num<0)
  have h1:=headerN n.bits.length (n.bits++sg::nh) ({}:Cells)
  have h2:=dataN n.bits sg nh ({}:Cells)
  have h3:=headerNum N.length (N++dh) ({product:=[false],dimension:=n.bits.reverse}:Cells)
  have h4:=dataNum N dh ({product:=u (N.length+1),dimension:=n.bits.reverse}:Cells)
  have h5:=dataDen D.length (N.length+1) (D++tail) ({dimension:=n.bits.reverse}:Cells)
  have h6:=clearTail (D++tail) ({product:=u (N.length+1-D.length),dimension:=n.bits.reverse}:Cells)
  simp only [List.append_nil,u_comm,u_next] at h1 h2 h3 h4 h5 h6
  have path:=((((h1.join h2).join h3).join h4).join h5).join h6
  refine ⟨n.bits.length+1+(n.bits.length+1)+(N.length+1)+(N.length+1)+(D.length+1)+((D++tail).length+1),?_,?_⟩
  · change _≤3*(encodeNat n++encodeRat T++tail).length+10
    exact (show n.bits.length+1+(n.bits.length+1)+(N.length+1)+(N.length+1)+(D.length+1)+((D++tail).length+1)≤_ by
      simp [N,D,encodeNat,encodeRat,encodeInt];omega)
  · simpa [N,D,sg,dh,nh,encodeNat,encodeInt,encodeRat,mWidth,Nat.size_eq_bits_len,List.append_assoc,u_next] using path
end BitGrid.Radius

namespace BitGrid
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
private theorem u_add (n m:ℕ):u n++u m=u (n+m):=(rep_add _ _ _).symm
private def squareState (k n m b:ℕ):Cells:={remainder:=u k,divisor:=u n,product:=u m,binCount:=u b}
theorem square (k n m b : ℕ) : Goes 1 (squareState k n m b) (k*(2*n+3)+1) (some 4) (squareState 0 n (k*n+m) b) := by
  induction k generalizing m with
  | zero=>simpa [squareState,Goes,code,branch,jump,Action.run] using
      (Path.step (code:=code) (l:=1) (m:=(squareState 0 n m b).mem))
  | succ k ih=>
    have on : Goes 1 (squareState (k+1) n m b) 1 (some 2) (squareState k n m b) := by
      simpa [squareState,Goes,code,branch,jump,Action.run] using
        (Path.step (code:=code) (l:=1) (m:=(squareState (k+1) n m b).mem))
    have copy:=multiply n (squareState k 0 m b)
    have back:=restoreDen n (squareState k 0 (n+m) b)
    simp [squareState,u_add] at copy back on
    have recu:=ih (n+m)
    simp [squareState] at recu ⊢
    simpa [Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.two_mul] using ((on.join copy).join back).join recu
private def gridState (k m:ℕ) (w:List Bool):Cells:={input:=w,product:=u m,binCount:=u k}
theorem rows (k m:ℕ) (w:List Bool) : Goes 5 (gridState k m w) (k*(2*m+3)+1) (some 8) (gridState 0 m (grid k m++w)) := by
  induction k generalizing w with
  | zero=>simpa [grid,gridState,Goes,code,branch,jump,Action.run] using
      (Path.step (code:=code) (l:=5) (m:=(gridState 0 m w).mem))
  | succ k ih=>
    let r:=d (m+1)++[false]
    have on : Goes 5 (gridState (k+1) m w) 1 (some 6) (gridState k m (false::w)) := by
      simpa [gridState,Goes,code,branch,jump,Action.run] using
        (Path.step (code:=code) (l:=5) (m:=(gridState (k+1) m w).mem))
    have copy:=putDigits m (gridState k 0 (false::w))
    have back:=restoreProd m (gridState k 0 (d m++false::w))
    have eqr : r++w=true::false::(d m++false::w) := by simp [r,List.append_assoc]
    have recu : Goes 5 (gridState k m (true::false::(d m++false::w))) (k*(2*m+3)+1) (some 8) (gridState 0 m (grid k m++(r++w))) := by simpa only [eqr] using ih (r++w)
    simp [gridState] at on copy back
    simp [gridState] at recu
    have tr:=((on.join copy).join back).join recu
    have eq : grid k m++(r++w)=grid (k+1) m++w := by
      change copies r k++(r++w)=copies r (k+1)++w
      rw [rep_comm,repeat_next];simp [r,List.append_assoc]
    simp only [gridState] at tr ⊢
    simpa [eq,Nat.succ_mul,Nat.two_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tr
theorem expand (n:ℕ):HMBinPacking.OutputsWithin (machine 0 (reg tape) code) (u n) (grid n (n*n))
    (20*(n+1)^3) := by
  have forked:=fork n ({}:Cells)
  have made:=square n n 0 n
  have clear:=wipeDen n (squareState 0 0 (n*n) n)
  have put:=rows n (n*n) []
  have last:=wipeProd (n*n) (gridState 0 0 (grid n (n*n)))
  simp [squareState,gridState] at forked made clear put last
  have path:=(((forked.join made).join clear).join put).join last
  have iso (w:List Bool):({input:=w}:Cells).mem=isolated (reg tape) w := by
    funext i;cases i with | inl k=>cases k <;> rfl | inr k=>cases k <;> rfl
  rw [iso,iso] at path
  exact path.outputs (by nlinarith)
end BitGrid

namespace BitGrid
open BitStacks
def tag (v:Option Bool):List Bool := match v with | none=>[false] | some b=>[true,b]
def tagged (xs:List (Option Bool)):=xs.flatMap tag
def significant : List Bool→List Bool
 | []=>[] | false::bs=>significant bs | true::bs=>true::bs
def magnitude (bs:List Bool):=val bs.reverse
def signed (neg:Bool) (bs:List Bool):ℤ:=if neg then - (magnitude bs:ℤ) else magnitude bs
theorem valAppend (a b:List Bool):val (a++b)=val a+2^a.length*val b:=by
  induction a with
  | nil=>simp [val]
  | cons i a ih=>simp [val,ih,pow_succ,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm];omega
theorem valBits (n:ℕ):val n.bits=n:=by
  induction n using Nat.binaryRec' with
  | zero=>rfl
  | bit b k h ih=>rw [Nat.bits_append_bit _ _ h,val,ih,Nat.bit_val];omega
private theorem valZero {bs:List Bool} (z:val bs=0):∀ b∈bs,b=false:=by
  induction bs with
  | nil=>simp
  | cons b bs ih=>
    cases b <;> simp [val] at z ⊢
    intro h;simpa using ih z true h
private theorem canonical (w:List Bool) (last:w=[] ∨ w.getLast?=some true): (val w).bits=w := by
  induction w with
  | nil=>rfl
  | cons b bs ih=>
    have tail : bs=[] ∨ bs.getLast?=some true := by
      cases bs with
      | nil=>simp
      | cons c cs=> simpa using last
    have guard : val bs=0→b=true := by
      intro z
      cases bs with
      | nil=>simpa using last
      | cons c cs=>
        have hl : (c::cs).getLast?=some true := tail.resolve_left (by simp)
        have member : true∈c::cs := List.mem_of_getLast? hl
        simpa using (valZero z true member)
    rw [show val (b::bs)=Nat.bit b (val bs) by simp [val,Nat.bit_val,Nat.add_comm],Nat.bits_append_bit _ _ guard,ih tail]
theorem magnitudeBits (xs:List Bool):(magnitude xs).bits=(significant xs).reverse := by
  induction xs with
  | nil=>rfl
  | cons b bs ih=>
    cases b with
    | false=>simpa [magnitude,significant,valAppend,val] using ih
    | true=>apply canonical;right;simp [significant]
theorem signCode (neg:Bool) (bs:List Bool) :
    ExponomialAssortment.FPTAS.encodeInt (signed neg bs)=
      (neg && !(significant bs).isEmpty)::(List.replicate (significant bs).length true++[false]++(significant bs).reverse) := by
  have zero : magnitude bs=0 ↔ significant bs=[] := by
    rw [←List.reverse_eq_nil_iff,←magnitudeBits]
    constructor
    · rintro eq;rw [eq];rfl
    · intro eq;have v:=valBits (magnitude bs);rw [eq] at v;simpa [val] using v.symm
  cases neg <;> simp [signed,ExponomialAssortment.FPTAS.encodeInt,ExponomialAssortment.FPTAS.encodeNat,magnitudeBits] <;>
    by_cases h:magnitude bs=0 <;> simp_all [List.isEmpty_iff, Nat.pos_iff_ne_zero, List.isEmpty_eq_false_iff]
theorem magnitudeFits (xs:List Bool):magnitude xs<2^xs.length := by
  have le (w:List Bool):val w<2^w.length:=by
    induction w with
    | nil=>decide
    | cons b bs ih=>cases b <;> simp [val,pow_succ] <;> omega
  simpa [magnitude] using le xs.reverse
theorem encodeFixed (width:ℕ) (x:ℤ) (bound:x.natAbs<2^width) :
    ∃ neg : Bool,∃ bs : List Bool,bs.length=width ∧ signed neg bs=x := by
  have size : x.natAbs.bits.length≤width := by rw [Nat.size_eq_bits_len];exact Nat.size_le.mpr bound
  let bits:=List.replicate (width-x.natAbs.bits.length) false++x.natAbs.bits.reverse
  have len : bits.length=width := by simp [bits];omega
  have zeros (k:ℕ):val (List.replicate k false)=0:=by
    induction k with | zero=>rfl | succ k ih=>simp [List.replicate_succ,val,ih]
  have v : magnitude bits=x.natAbs := by simp [magnitude,bits,valAppend,zeros,valBits]
  refine ⟨decide (x<0),bits,len,?_⟩
  by_cases h:x<0
  · simp [signed,v,h,abs_of_neg h]
  · simp [signed,v,h,abs_of_nonneg (le_of_not_gt h)]
end BitGrid

namespace BitGrid.Radius
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
def loc(b:Bool):L:=if b then a 9 else a 8
theorem double (k:ℕ) (b:Bool) (s:Cells): Goes (loc b) {s with binCount:=u k} (k+1) (back b) {s with binCount:=[],scratch:=u (2*k)++s.scratch}:=by
  induction k generalizing s with
  | zero=>
    have z:=Path.step (code:=code) (l:=loc b) (m:=({s with binCount:=[]}:Cells).mem)
    cases b <;>simpa [Goes,code,a,loc,branch,jump,Action.run] using z
  | succ k ih=>
    let z:Cells:={s with scratch:=false::false::s.scratch}
    have on : Goes (loc b) {s with binCount:=u (k+1)} 1 (loc b) {z with binCount:=u k}:=by
      have st:=Path.step (code:=code) (l:=loc b) (m:=({s with binCount:=u (k+1)}:Cells).mem)
      cases b <;>simpa [Goes,code,a,loc,branch,jump,Action.run,z] using st
    simpa [z,Nat.mul_succ,Nat.add_comm 1] using on.join (ih z)
theorem undouble (k:ℕ) (b:Bool) (s:Cells):Goes (back b) {s with scratch:=u k} (k+1) (a 7) {s with scratch:=[],binCount:=u (b.toNat+k)++s.binCount}:=by
  induction k generalizing s with
  | zero=>
    have z:=Path.step (code:=code) (l:=back b) (m:=({s with scratch:=[]}:Cells).mem)
    cases b <;>simpa [Goes,code,a,back,branch,jump,Action.run] using z
  | succ k ih=>
    let z:Cells:={s with binCount:=false::s.binCount}
    have on:Goes (back b) {s with scratch:=u (k+1)} 1 (back b) {z with scratch:=u k}:=by
      simpa [Goes,code,back,branch,jump,Action.run,z] using (Path.step (code:=code) (l:=back b) (m:=({s with scratch:=u (k+1)}:Cells).mem))
    simpa only [z,Nat.add_succ,u_next,List.cons_append,u_comm,Nat.add_comm 1 (k+1)] using on.join (ih z)
def accum (bs:List Bool) (p:ℕ):=p*2^bs.length+val bs.reverse
theorem accum_pos (bs:List Bool) (p:ℕ):p≤accum bs p:=by
  have one:=Nat.mul_le_mul_left p (Nat.one_le_pow bs.length 2 (by decide))
  simp only [Nat.mul_one] at one
  unfold accum;omega
theorem accum_cons (b:Bool) (bs:List Bool) (p:ℕ):accum (b::bs) p=accum bs (b.toNat+2*p):=by
  simp [accum,valAppend,val,pow_succ,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
theorem unary (bs:List Bool) (p m:ℕ): ∃t≤(bs.length+1)*(5*(accum bs p+1)),
   Goes (a 7) {dimension:=bs,product:=u m,binCount:=u p} t (grow 5) {product:=u m,binCount:=u (accum bs p)}:=by
  induction bs generalizing p with
  | nil=>
    have z:=Path.step (code:=code) (l:=a 7) (m:=({product:=u m,binCount:=u p}:Cells).mem)
    refine ⟨1,by simp [accum,val];omega,?_⟩
    simpa [Goes,code,a,accum,val,jump,Action.run] using z
  | cons b bs ih=>
    let s:Cells:={dimension:=bs,product:=u m}
    have next:Goes (a 7) {s with dimension:=b::bs,binCount:=u p} 1 (loc b) {s with binCount:=u p}:=by
      simpa [Goes,code,a,loc,jump,Action.run,s] using (Path.step (code:=code) (l:=a 7) (m:=({s with dimension:=b::bs,binCount:=u p}:Cells).mem))
    have cp:=double p b s
    have undo:=undouble (2*p) b s
    obtain ⟨t,ct,recP⟩:=ih (b.toNat+2*p)
    simp [s] at cp undo next
    have tr:=((next.join cp).join undo).join recP
    rw [accum_cons]
    refine ⟨_,?_,tr⟩
    have cap:=accum_pos bs (b.toNat+2*p)
    rw [List.length_cons,Nat.succ_mul (bs.length+1)];omega
theorem growTrace {i m n j z} (tr:Path BitGrid.code i m n j z) :
    Path code (i.map grow) m n (j.map grow) z:=by
  have functions : (fun o:Option BitGrid.L=>o.map grow)=(fun o=>o.elim none (fun v=>some (grow v))):=by funext o;cases o <;>rfl
  obtain ⟨v,pp,agree,_⟩:=tr.rename (.refl _) grow none code (by intro l;change (BitGrid.code l).rename _ (fun o=>o.map grow)=_;rw [functions]) m (fun _=>rfl)
  have same:v=z:=funext (fun k=>agree k)
  rw [same] at pp
  cases i <;> cases j <;> exact pp
end BitGrid.Radius

namespace BitGrid.Radius
open HMBinPacking ExponomialAssortment.FPTAS
theorem value_bounds (T:ℚ) (unit:1≤T) : T < (2:ℚ)^(mWidth T) ∧ (2:ℚ)^(mWidth T)≤4*T:=by
  let a:=T.num.natAbs
  let b:=T.den
  let m:=mWidth T
  have bp:0<b:=T.den_pos
  have br:0<(b:ℚ):=by exact_mod_cast bp
  have rat:(T.num:ℚ)/(b:ℚ)=T:=T.num_div_den
  have z:(T.num:ℚ)=T*b:=(div_eq_iff br.ne').mp rat
  have nn:0≤T.num:=by exact_mod_cast (show (0:ℚ)≤(T.num:ℚ) by rw [z];positivity)
  have cast:(a:ℚ)=T*b:=by
    have k:(Int.ofNat a)=T.num:=by simpa [a,abs_of_nonneg nn] using Int.natCast_natAbs T.num
    exact (show (a:ℚ)=(T.num:ℚ) by exact_mod_cast k).trans z
  have ab:b≤a:=by exact_mod_cast (show (b:ℚ)≤(a:ℚ) by rw [cast];simpa using mul_le_mul_of_nonneg_right unit br.le)
  have sz:=Nat.size_le_size ab
  have expo:m+b.size=a.size+1:=by dsimp [m,mWidth,a,b] at *;omega
  have powEq:2^m*2^b.size=2*2^a.size:=by rw [←pow_add,expo,pow_succ,Nat.mul_comm]
  have two (k:ℕ) (pos:0<k):2^k.size≤2*k:=by
    have ks:=Nat.size_pos.mpr pos
    have low:=Nat.lt_size.mp (show k.size-1<k.size by omega)
    rw [show k.size=k.size-1+1 by omega,pow_succ]
    omega
  have ba:=two b bp
  have aa:=two a (bp.trans_le ab)
  have lo:=Nat.lt_size_self a
  have hi:=Nat.lt_size_self b
  have low:=Nat.mul_le_mul_left (2^m) ba
  have high:=Nat.mul_le_mul_left (2^m) hi.le
  rw [powEq,Nat.mul_left_comm (2^m) 2 b] at low
  rw [powEq] at high
  have bounds:a<2^m*b ∧ 2^m*b≤4*a:=by omega
  have ar:(a:ℚ)<2^m*(b:ℚ):=by exact_mod_cast bounds.1
  have bs:(2:ℚ)^m*(b:ℚ)≤4*a:=by exact_mod_cast bounds.2
  rw [cast] at ar bs
  exact ⟨(mul_lt_mul_iff_left₀ br).mp ar,(mul_le_mul_iff_left₀ br).mp (by simpa [mul_assoc] using bs)⟩
theorem width_enc (T:ℚ):mWidth T≤enc T:=by
  change mWidth T≤(encodeRat T).length
  simp [mWidth,encodeRat,encodeInt,encodeNat,Nat.size_eq_bits_len];omega
end BitGrid.Radius

namespace BitGrid.Radius
open BitStacks HMBinPacking ExponomialAssortment.FPTAS
open OneTypeTM (Cells R)
open OneTypeTM.R
private theorem clock (N n k m:ℕ) (hk:k≤N) (hm:m≤N):
   3*N+10+(k+1)*(5*(n+1))+(n*(2*m+3)+1)+(m+1)≤200*(N+n+2)^2 := by
  let K:=N+n+2
  have k0:1≤K:=by dsimp [K];omega
  have G:K≤K*K:=by simpa using Nat.mul_le_mul_left K k0
  have kn:=Nat.mul_le_mul (show k+1≤K by dsimp [K];omega) (show 5*(n+1)≤5*K by dsimp [K];omega)
  have nm:=Nat.mul_le_mul (show n≤K by dsimp [K];omega) (show 2*m+3≤3*K by dsimp [K];omega)
  rw [Nat.mul_left_comm K 5 K] at kn
  rw [Nat.mul_left_comm K 3 K] at nm
  change _≤200*K^2
  rw [pow_two]
  have le:N≤K:=by dsimp [K];omega
  omega
theorem generate (n:ℕ) (T:ℚ) (tail:List Bool):
    let raw:=encodeNat n++encodeRat T++tail
    OutputsWithin (BitStacks.machine (a 0) (reg tape) code) raw (grid n (mWidth T)) (200*(raw.length+n+2)^2) := by
  let raw:=encodeNat n++encodeRat T++tail
  let m:=mWidth T
  obtain ⟨t,ct,pa⟩:=parse n T tail
  obtain ⟨v,cv,un⟩:=unary n.bits.reverse 0 m
  have c:accum n.bits.reverse 0=n:=by simp [accum,valBits]
  rw [c,List.length_reverse] at cv
  rw [c] at un
  have rowsP:=BitGrid.rows n m []
  have endP:=BitGrid.wipeProd m ({input:=grid n m}:Cells)
  have build:=growTrace rowsP
  have done:=growTrace endP
  simp [BitGrid.u_zero] at build done un
  have whole:=((pa.join un).join build).join done
  rw [iso,iso] at whole
  exact whole.outputs (by
    have k:n.bits.length≤raw.length:=by simp [raw,encodeNat]
    have mL:m≤raw.length:=by have e:=width_enc T;change m≤(encodeRat T).length at e;simp [raw];omega
    have budget:=clock raw.length n n.bits.length m k mL
    change t≤3*raw.length+10 at ct
    change _≤200*(raw.length+n+2)^2
    omega)
end BitGrid.Radius

namespace BitGrid.Scanner
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
abbrev L:=Unit ⊕ ((Bool×Bool) ⊕ Bool)
def start:L:=.inl ()
def read (neg active:Bool):L:=.inr (.inl (neg,active))
def header (neg:Bool):L:=.inr (.inr neg)
def jump (j:L): Action (Bank R) L:=.stop (some j)
def backup (b:Bool) (a:Action (Bank R) L):=Action.push (reg second) b (.push (reg second) true a)
def both (b:Bool) (a:Action (Bank R) L):=Action.push (reg first) b (.push (reg prod) b a)
def code : L→Action (Bank R) L
 | .inl _=>.peek (reg tape) (fun b=>if b.isSome then
      .drop (reg tape) (.peek (reg tape) (fun v=>.drop (reg tape) (backup (v.getD false)
       (.push (reg first) true (.push (reg first) false (.push (reg first) true (jump (read (v.getD false) false))))))))
      else .stop none)
 | .inr (.inl (neg,active))=>.peek (reg tape) (fun tag=>.drop (reg tape) (if tag.getD false then
      .peek (reg tape) (fun v=>.drop (reg tape) (backup (v.getD false) (if active || v.getD false then
         .push (reg width) true (both (v.getD false) (jump (read neg true))) else jump (read neg false))))
      else .push (reg second) false (both false (jump (header (neg && active))))))
 | .inr (.inr neg)=>.peek (reg width) (fun v=>if v.isSome then .drop (reg width) (both true (jump (header neg)))
     else both neg (jump start))
abbrev Goes (i:L) (s:Cells) (n:ℕ) (j:Option L) (z:Cells):=Path code (some i) s.mem n j z.mem
def saved (bs:List Bool):=tagged (bs.map some)
@[simp] theorem saved_nil : saved []=[]:=rfl
@[simp] theorem saved_cons (b:Bool) (bs:List Bool): saved (b::bs)=true::b::saved bs:=rfl
@[simp] theorem saved_app (a b:List Bool): saved (a++b)=saved a++saved b:=by simp [saved,tagged]
theorem heads (n:ℕ) (neg:Bool) (s:Cells) : Goes (header neg) {s with scratch:=List.replicate n true} (n+1) start
   {s with scratch:=[],prep:=neg::(List.replicate n true++s.prep),product:=neg::(List.replicate n true++s.product)} := by
 induction n generalizing s with
 | zero=>simpa [Goes,code,header,jump,both,Action.run] using
     (Path.step (code:=code) (l:=header neg) (m:=({s with scratch:=[]}:Cells).mem))
 | succ n ih=>
   let z:Cells:={s with prep:=true::s.prep,product:=true::s.product}
   have st : Goes (header neg) {s with scratch:=List.replicate (n+1) true} 1 (header neg) {z with scratch:=List.replicate n true} := by
     simpa [Goes,code,header,jump,both,Action.run,z,List.replicate_succ] using
       (Path.step (code:=code) (l:=header neg) (m:=({s with scratch:=List.replicate (n+1) true}:Cells).mem))
   have comm (t:List Bool):List.replicate n true++true::t=true::(List.replicate n true++t):=by
     calc
       _=(List.replicate n true++[true])++t:=by simp
       _=_:=by rw [←List.replicate_succ',List.replicate_succ];rfl
   simpa [z,List.replicate_succ,comm,Nat.add_comm 1] using st.join (ih z)
def emit (active:Bool) (bs:List Bool):=if active then bs else significant bs
def nonzero (active:Bool) (bs:List Bool):=active || !(significant bs).isEmpty
theorem scanBits (neg active:Bool) (bs tail:List Bool) (s:Cells) :
    let e:=emit active bs
    Goes (read neg active) {s with input:=saved bs++false::tail} (bs.length+1) (header (neg && nonzero active bs))
      {s with input:=tail,scratch:=List.replicate e.length true++s.scratch,todo:=false::(saved bs.reverse++s.todo),prep:=false::(e.reverse++s.prep),product:=false::(e.reverse++s.product)} := by
  induction bs generalizing active s with
  | nil=>
    have st:=Path.step (code:=code) (l:=read neg active) (m:=({s with input:=false::tail}:Cells).mem)
    cases active <;> simpa [Goes,code,read,nonzero,emit,significant,jump,both,backup,Action.run] using st
  | cons b bs ih=>
    let a:=active||b
    let z:Cells:={s with todo:=true::b::s.todo,scratch:=if a then true::s.scratch else s.scratch,prep:=if a then b::s.prep else s.prep,product:=if a then b::s.product else s.product}
    have st : Goes (read neg active) {s with input:=saved (b::bs)++false::tail} 1 (read neg a) {z with input:=saved bs++false::tail} := by
      have step:=Path.step (code:=code) (l:=read neg active) (m:=({s with input:=saved (b::bs)++false::tail}:Cells).mem)
      cases active <;> cases b <;> simpa [Goes,code,read,a,z,both,jump,backup,Action.run] using step
    have comm (n:ℕ)(t:List Bool):List.replicate n true++true::t=true::(List.replicate n true++t):=by
      calc
       _=(List.replicate n true++[true])++t:=by simp
       _=_:=by rw [←List.replicate_succ',List.replicate_succ];rfl
    have tr:=st.join (ih a z)
    cases active <;> cases b <;>
      simpa [a,z,emit,nonzero,significant,List.append_assoc,List.replicate_succ,comm,Nat.add_comm 1] using tr
end BitGrid.Scanner

namespace BitGrid.Scanner
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
abbrev Row:=Bool×List Bool
def rowTags (r:Row):List (Option Bool) := some r.1::(r.2.map some++[none])
def tags (rs:List Row):=rs.flatMap rowTags
def qWord (rs:List Row):=rs.flatMap fun r=>encodeRat (signed r.1 r.2:ℚ)
def xWord (rs:List Row):=rs.flatMap fun r=>encodeInt (signed r.1 r.2)
def cost (r:Row):=r.2.length+(significant r.2).length+3
def clocks (rs:List Row):=(rs.map cost).sum
theorem one (r:Row) (rest:List Bool) (s:Cells):Goes start {s with input:=tagged (rowTags r)++rest,scratch:=[]} (cost r) start
    {s with input:=rest,scratch:=[],todo:=tagged (rowTags r).reverse++s.todo,prep:=encodeRat (signed r.1 r.2:ℚ)++s.prep,product:=encodeInt (signed r.1 r.2)++s.product} := by
 obtain ⟨neg,bs⟩:=r
 let s₁:Cells:={s with todo:=true::neg::s.todo,prep:=true::false::true::s.prep,scratch:=[]}
 let ys:=significant bs
 let s₂:Cells:={s₁ with input:=rest,todo:=false::(saved bs.reverse++s₁.todo),prep:=false::(ys.reverse++s₁.prep),product:=false::(ys.reverse++s₁.product)}
 have on : Goes start {s with input:=tagged (rowTags (neg,bs))++rest,scratch:=[]} 1 (read neg false) {s₁ with input:=saved bs++false::rest} := by
    simpa [Goes,code,start,read,jump,backup,tagged,rowTags,saved,tag,s₁,List.append_assoc,Action.run] using
       (Path.step (code:=code) (l:=start) (m:=({s with input:=tagged (rowTags (neg,bs))++rest,scratch:=[]}:Cells).mem))
 have readP:=scanBits neg false bs rest s₁
 have scan : Goes (read neg false) {s₁ with input:=saved bs++false::rest} (bs.length+1)
     (header (neg && !ys.isEmpty)) {s₂ with scratch:=List.replicate ys.length true} := by
   simpa [ys,s₁,s₂,emit,nonzero] using readP
 have hh:=heads ys.length (neg && !ys.isEmpty) s₂
 have path:=(on.join scan).join hh
 have denom : encodeNat 1=[true,false,true]:=rfl
 simpa [cost,encodeRat,signCode,denom,s₁,s₂,ys,rowTags,saved,tagged,List.map_reverse,List.append_assoc,tag,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using path

theorem many (rs:List Row) (s:Cells):Goes start {s with input:=tagged (tags rs),scratch:=[]} (clocks rs+1) none
   {s with input:=[],scratch:=[],todo:=tagged (tags rs).reverse++s.todo,prep:=qWord rs.reverse++s.prep,product:=xWord rs.reverse++s.product} := by
 induction rs generalizing s with
 | nil=>simpa [Goes,code,start,tagged,tags,clocks,qWord,xWord,Action.run] using
     (Path.step (code:=code) (l:=start) (m:=({s with input:=[],scratch:=[]}:Cells).mem))
 | cons r rs ih=>
   let z:Cells:={s with todo:=tagged (rowTags r).reverse++s.todo,prep:=encodeRat (signed r.1 r.2:ℚ)++s.prep,product:=encodeInt (signed r.1 r.2)++s.product}
   have step:=one r (tagged (tags rs)) s
   have recu:=ih z
   have path:=step.join recu
   simpa [z,tagged,tags,clocks,qWord,xWord,List.append_assoc,Nat.add_assoc] using path
end BitGrid.Scanner

open HMBinPacking Turing
namespace BitStacks.Oracle
variable {K J : Type} [DecidableEq K] [DecidableEq J] [Fintype K] [Fintype J]

def model (start : J) (io qs : K) (ask resume : J) (program : J→Action K J) : OracleMachine where
  M:=machine start io program
  qs:=qs
  qsAlphabet:=Equiv.refl _
  ask:=ask
  resume:=resume
  decEqΛ:=inferInstanceAs (DecidableEq J)

private theorem ordinaryStep (OM : OracleMachine) (O : List Bool→List Bool) (c : OCfg OM) (h : c.l≠some OM.ask) :
    oStep OM O c=OM.M.tm.step c := by
  letI:=OM.decEqΛ
  exact if_neg h

private theorem queryStep (OM : OracleMachine) (O : List Bool→List Bool) (c : OCfg OM) (h : c.l=some OM.ask) :
    oStep OM O c=some ⟨some OM.resume,c.var,Function.update c.stk OM.qs ((O ((c.stk OM.qs).map OM.qsAlphabet)).map OM.qsAlphabet.symm)⟩ := by
  letI:=OM.decEqΛ
  exact if_pos h

inductive Trace (program : J→Action K J) (O : List Bool→List Bool) (qs : K) (ask resume : J) (Q : ℕ) :
    Option J→Mem K→ℕ→Option J→Mem K→Prop where
  | refl (l m) : Trace program O qs ask resume Q l m 0 l m
  | bits {l m} (ordinary : l≠ask) : Trace program O qs ask resume Q (some l) m 1
      ((program l).run m).1 ((program l).run m).2
  | call {m : Mem K} (bounded : (m qs).length≤Q) : Trace program O qs ask resume Q (some ask) m 1
      (some resume) (Function.update m qs (O (m qs)))
  | join {i m t j n u k z} : Trace program O qs ask resume Q i m t j n →
      Trace program O qs ask resume Q j n u k z → Trace program O qs ask resume Q i m (t+u) k z

theorem Trace.registered {pg : J→Action K J} {O qs ak re Q} {src dst : List Bool} {start io t T}
    (path : Trace pg O qs ak re Q (some start) (isolated io src) t none (isolated io dst)) (clock : t≤T) :
    ORunsWithin (model start io qs ak re pg) O src dst T Q := by
  let OM:=model start io qs ak re pg
  let cfg (l : Option J) (m : Mem K) : OCfg OM := ⟨l,none,m⟩
  let step : Option (OCfg OM)→Option (OCfg OM) := flip bind (oStep OM O)
  have sem {l m j r n} (p : Trace pg O qs ak re Q l m j r n) :
      step^[j] (some (cfg l m))=some (cfg r n) ∧
      ∀ i<j,∀ c,step^[i] (some (cfg l m))=some c → c.l=some OM.ask → (c.stk OM.qs).length≤Q := by
    induction p with
    | refl l m => exact ⟨rfl,fun _ lt => (Nat.not_lt_zero _ lt).elim⟩
    | @bits l m hs =>
      refine ⟨?_,?_⟩
      · change oStep OM O (cfg (some l) m)=some _
        rw [ordinaryStep OM O _ (show (cfg (some l) m).l≠some OM.ask by exact fun h=>hs (Option.some.inj h))]
        change some (TM2.stepAux (pg l).compile none m)=_
        rw [Action.correct];rfl
      · intro i hi c e a
        have z : i=0:=by omega
        subst i
        change some (cfg (some l) m)=some c at e;cases e
        exact (hs (Option.some.inj a)).elim
    | @call m hl =>
      refine ⟨?_,?_⟩
      · change oStep OM O (cfg (some ak) m)=some _
        rw [queryStep OM O _ rfl]
        change some (cfg (some re) (Function.update m qs ((O ((m qs).map id)).map id)))=_
        simp
      · intro i hi c e _
        have z : i=0:=by omega
        subst i
        change some (cfg (some ak) m)=some c at e;cases e;exact hl
    | @join l m j r n k v z p q hp hq =>
      constructor
      · rw [Nat.add_comm j k,Function.iterate_add_apply,hp.1,hq.1]
      · intro i hi c e a
        by_cases le : i<j
        · exact hp.2 _ le _ e a
        · have dec : i=(i-j)+j := by omega
          rw [dec,Function.iterate_add_apply,hp.1] at e
          exact hq.2 _ (by omega) _ e a
  have proof:=sem path
  have ini : initList OM.M.tm (src.map OM.M.inputAlphabet.symm)=cfg (some start) (isolated io src) := by
    rw [show src.map OM.M.inputAlphabet.symm=src from List.map_id _];rfl
  have endc : haltList OM.M.tm (dst.map OM.M.outputAlphabet.symm)=cfg none (isolated io dst) := by
    rw [show dst.map OM.M.outputAlphabet.symm=dst from List.map_id _];rfl
  refine ⟨t,clock,?_,?_⟩
  · change step^[t] (some (initList OM.M.tm (src.map OM.M.inputAlphabet.symm)))=some _
    rw [ini,endc];exact proof.1
  · intro i le c e a
    change step^[i] (some (initList OM.M.tm (src.map OM.M.inputAlphabet.symm)))=some c at e
    rw [ini] at e;exact proof.2 _ le _ e a
end BitStacks.Oracle

namespace BitStacks.Oracle
variable {K A J : Type} [DecidableEq K] [DecidableEq J]

theorem lift {ac : A→Action K A} {i m t j n} (h : Path ac i m t j n)
    (O : List Bool→List Bool) (qs : K) (ak re : J) (Q : ℕ) (code : J→Action K J)
    (lbl : A→J) (exit : Option J) (ordinary : ∀ j,lbl j≠ak)
    (impl : ∀ j,code (lbl j)=(ac j).rename (Function.Embedding.refl _) (fun l=>l.elim exit (fun x=>some (lbl x)))) :
    Trace code O qs ak re Q (i.elim exit (fun x=>some (lbl x))) m t (j.elim exit (fun x=>some (lbl x))) n := by
  induction h with
  | refl => exact .refl _ _
  | join _ _ hp hq => exact hp.join hq
  | @step l m =>
    have eq:=renameRun (ac l) (Function.Embedding.refl _) (fun o=>o.elim exit (fun x=>some (lbl x))) m m (fun _=>rfl)
    let z:=(code (lbl l)).run m
    have el : z.1=((ac l).run m).1.elim exit (fun x=>some (lbl x)) := by simpa [z,impl] using eq.1
    have mem : z.2=((ac l).run m).2 := funext (fun k=>by simpa [z,impl] using eq.2.1 k)
    have step:=Trace.bits (program:=code) (O:=O) (qs:=qs) (resume:=re) (Q:=Q) (m:=m) (ordinary l)
    change Trace code O qs ak re Q (some (lbl l)) m 1 z.1 z.2 at step
    rwa [el,mem] at step
end BitStacks.Oracle

set_option synthInstance.maxSize 3000
namespace BitGrid.Line.TM
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
abbrev L:=Fin 24 ⊕ (Radius.L ⊕ Scanner.L)
def a(i:Fin 24):L:=.inl i
def front(i:Radius.L):L:=.inr (.inl i)
def scan(i:Scanner.L):L:=.inr (.inr i)
def jump(i:L):Action (Bank R) L:=.stop (some i)
def put(b:Bool)(next:Action (Bank R) L):=Action.push (reg tape) b (.push (reg tape) true next)
def wipe(r:R)(next:L)(done:Action (Bank R) L):Action (Bank R) L:=.peek (reg r) (fun b=>if b.isSome then .drop (reg r) (jump next) else done)
def move(r t:R)(next:L)(done:Action (Bank R) L):Action (Bank R) L:=.peek (reg r) (fun b=>match b with | none=>done | some v=>.drop (reg r) (.push (reg t) v (jump next)))
def push(r:R):List Bool → Action (Bank R) L → Action (Bank R) L
 | [],act=>act | b::bs,act=>push r bs (.push (reg r) b act)
def finish(ok:Bool):Action (Bank R) L:=.push (reg items) ok (jump (a 13))
def decode:Action (Bank R) L:=.peek (reg first) fun b=>.drop (reg first)
  (if b.getD false then finish true else .peek (reg first) fun sg=>.drop (reg first) <|
    .peek (reg first) fun bit=>.drop (reg first) <| if bit.getD false then .push (reg items) (sg.getD false) (jump (a 4)) else finish false)
def code:L → Action (Bank R) L
 | .inr (.inl i)=>(Radius.code i).rename (.refl _) (fun o=>o.elim (some (a 0)) (some ∘ front))
 | .inr (.inr i)=>(Scanner.code i).rename (.refl _) (fun o=>o.elim (some (a 2)) (some ∘ scan))
 | .inl i=>match i.val with
   | 0=>.drop (reg tape) (.drop (reg tape) (jump (a 1)))
   | 1=>.peek (reg tape) (fun b=>.drop (reg tape) (if b.getD false then .drop (reg tape) (.push (reg bins) false (jump (a 1)))
        else push first (encodeRat 0) (push prod (encodeInt 0) (jump (a 2)))))
   | 2=>.stop none
   | 3=>decode
   | 4=>wipe first (a 4) (jump (a 5))
   | 5=>wipe second (a 5) (jump (a 6))
   | 6=>wipe prod (a 6) (jump (a 7))
   | 7=>.peek (reg items) (fun sg=>.drop (reg items) (.peek (reg dim) (fun b=>match b with
      | none=>.push (reg dim) (!(sg.getD false)) (jump (a 8))
      | some neg=>.push (reg den) (xor (sg.getD false) neg) (jump (a 8)))))
   | 8=>.peek (reg bins) (fun b=>if b.isSome then .drop (reg bins) (.push (reg tape) false (jump (a 9))) else finish false)
   | 9=>.peek (reg bins) (fun b=>if b.isSome then .drop (reg bins) (.push (reg width) false (put false (jump (a 9)))) else jump (a 10))
   | 10=>move width bins (a 10) (put true (jump (a 11)))
   | 11=>.peek (reg den) (fun v=>match v with | some b=>.drop (reg den) (.push (reg rem) b (put b (jump (a 11)))) | none=>jump (a 12))
   | 12=>move rem den (a 12) (.peek (reg dim) (fun b=>put (b.getD false) (jump (scan Scanner.start))))
   | 13=>wipe first (a 13) (jump (a 14))
   | 14=>wipe second (a 14) (jump (a 15))
   | 15=>wipe bins (a 15) (jump (a 16))
   | 16=>wipe den (a 16) (jump (a 17))
   | 17=>wipe dim (a 17) (jump (a 18))
   | 18=>.peek (reg items) (fun b=>.drop (reg items) (jump (if b.getD false then a 19 else a 21)))
   | 19=>move prod rev (a 19) (jump (a 20))
   | 20=>move rev tape (a 20) (.push (reg tape) true (.stop none))
   | _=>wipe prod (a 21) (.push (reg tape) false (.stop none))
def oracle:=Oracle.model (front (Radius.a 0)) (reg tape) (reg first) (a 2) (a 3) code
abbrev Goes (O:List Bool → List Bool) (Q:ℕ) (i:L) (s:Cells) (t:ℕ) (j:Option L) (z:Cells):=
  Oracle.Trace code O (reg first) (a 2) (a 3) Q (some i) s.mem t j z.mem
end BitGrid.Line.TM

namespace BitGrid.Line.TM
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
theorem loop9 (O:List Bool → List Bool) (Q:ℕ) (k:ℕ) (s:Cells):Goes O Q (a 9) {s with binCount:=u k} (k+1) (a 10) {s with binCount:=[],scratch:=u k++s.scratch,input:=d k++s.input} := by
  induction k generalizing s with
  | zero=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with binCount:=[]}:Cells).mem) (show a 9≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | succ k ih=>
    let z:Cells:={s with scratch:=false::s.scratch,input:=true::false::s.input}
    have firstPath:Goes O Q (a 9) {s with binCount:=u (k+1)} 1 (a 9) {z with binCount:=u k} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with binCount:=u (k+1)}:Cells).mem) (show a 9≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop10 (O:List Bool → List Bool) (Q:ℕ) (k:ℕ) (s:Cells):Goes O Q (a 10) {s with scratch:=u k} (k+1) (a 11) {s with scratch:=[],binCount:=u k++s.binCount,input:=true::true::s.input} := by
  induction k generalizing s with
  | zero=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with scratch:=[]}:Cells).mem) (show a 10≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | succ k ih=>
    let z:Cells:={s with binCount:=false::s.binCount}
    have firstPath:Goes O Q (a 10) {s with scratch:=u (k+1)} 1 (a 10) {z with scratch:=u k} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with scratch:=u (k+1)}:Cells).mem) (show a 10≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop11 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 11) {s with divisor:=w} (w.length+1) (a 12) {s with divisor:=[],remainder:=w.reverse++s.remainder,input:=Scanner.saved w.reverse++s.input} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with divisor:=[]}:Cells).mem) (show a 11≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:={s with remainder:=b::s.remainder,input:=true::b::s.input}
    have firstPath:Goes O Q (a 11) {s with divisor:=b::w} 1 (a 11) {z with divisor:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with divisor:=b::w}:Cells).mem) (show a 11≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop12 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 12) {s with remainder:=w} (w.length+1) (scan Scanner.start) {s with remainder:=[],divisor:=w.reverse++s.divisor,input:=true::s.dimension.head?.getD false::s.input} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with remainder:=[]}:Cells).mem) (show a 12≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:={s with divisor:=b::s.divisor}
    have firstPath:Goes O Q (a 12) {s with remainder:=b::w} 1 (a 12) {z with remainder:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with remainder:=b::w}:Cells).mem) (show a 12≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
end BitGrid.Line.TM

namespace BitGrid.Line
open HMBinPacking ExponomialAssortment.FPTAS
inductive Reply where | member | empty | smaller | larger deriving DecidableEq
def readReply (bits:List Bool):Reply := match bits with
  | true::_=>.member
  | false::neg::true::_=>if neg then .larger else .smaller
  | _=>.empty
def point(x:ℤ):Fin 1→ℤ:=fun _=>x
def query(x:ℤ):=encodeRat (x:ℚ)
def Valid (Q:Set (Fin 1→ℝ)) (x:ℤ):Reply → Prop
 | .member=>zCast (point x)∈Q
 | .empty=>∀ v:Fin 1→ℤ,zCast v∉Q
 | .smaller=>∀ v:Fin 1→ℤ,zCast v∈Q → v 0 < x
 | .larger=>∀ v:Fin 1→ℤ,zCast v∈Q → x < v 0
theorem encOne (y:Fin 1→ℚ):encVec y=encodeRat (y 0):=by simp [encVec,List.ofFn_succ]
theorem xOne (x:ℤ):encodeIntVec (point x)=encodeInt x:=by simp [encodeIntVec,point,List.ofFn_succ]
private theorem numZero (r:ℚ):r.num=0 ↔ r=0:=by
 constructor
 · intro h;rw [←r.num_div_den,h];simp
 · rintro rfl;rfl
private theorem hdNum (r:ℚ) (tail:List Bool) :
    readReply (false::(encodeRat r++tail))=if r=0 then Reply.empty else if r<0 then .larger else .smaller := by
  by_cases z:r=0
  · subst r;rfl
  · have bits:r.num.natAbs.bits.length≠0:=by
      intro v;apply z;apply (numZero r).mp;have q:=Nat.size_eq_zero.mp (Nat.size_eq_bits_len _ ▸ v);omega
    obtain ⟨k,len⟩:=Nat.exists_eq_succ_of_ne_zero bits
    have sg:r.num<0 ↔ r<0:=Rat.num_neg
    simp [readReply,encodeRat,encodeInt,encodeNat,len,List.replicate_succ,z,sg,List.append_assoc]
theorem direction (Q:Set (Fin 1→ℝ)) (x:ℤ) (O:List Bool → List Bool)
    (spec:∀y:Fin 1→ℚ,IsSepAnswer Q y (O (encVec y))) :
    Valid Q x (readReply (O (query x))) := by
  let y:Fin 1→ℚ:=fun _=>(x:ℚ)
  have code:encVec y=query x:=encOne y
  have yes:qCast y=zCast (point x):=by funext i;simp [qCast,zCast,point,y]
  have response:=spec y
  rcases response with ⟨h,hx⟩|⟨u,a,h,all,st⟩
  · rw [code] at h;rw [h];change zCast (point x)∈Q;rwa [←yes]
  · rw [code,encOne] at h
    rw [h,hdNum]
    have strong:(a:ℝ)<(u 0:ℝ)*x:=by simpa [y] using st
    have weak (v:Fin 1→ℤ) (mem:zCast v∈Q):(u 0:ℝ)*(v 0:ℝ) ≤ a:=by simpa [zCast] using all (zCast v) mem
    split
    · rename_i hz
      intro v mem
      have w:=weak v mem
      simp [hz] at w strong;linarith
    · split
      · rename_i un
        intro v mem
        have c:(u 0:ℝ)<0:=by exact_mod_cast un
        have s:=lt_of_le_of_lt (weak v mem) strong
        by_contra! bad
        have badR:(v 0:ℝ) ≤ x:=by exact_mod_cast bad
        exact s.not_ge (mul_le_mul_of_nonpos_left badR c.le)
      · rename_i hp
        have hn : 0 < u 0:=by rename_i nz;exact lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm nz)
        have c:(0:ℝ)<(u 0:ℝ):=by exact_mod_cast hn
        intro v mem
        have g:= (mul_lt_mul_iff_right₀ c).mp (lt_of_le_of_lt (weak v mem) strong)
        exact_mod_cast g
end BitGrid.Line

namespace BitGrid.Line
open HMBinPacking
def orient (neg:Bool) (x:ℤ):ℤ:=if neg then -x else x
def midpoint (neg:Bool) (p k:ℕ):ℤ:=orient neg (((2*p+1)*2^k:ℕ):ℤ)
def search (O:List Bool → List Bool) (neg:Bool):ℕ→ℕ → Option ℤ×ℕ
 | 0,_=>(none,0)
 | k+1,p=>
   let x:=midpoint neg p k
   match readReply (O (query x)) with
   | .member=>(some x,1)
   | .empty=>(none,1)
   | .smaller=>let v:=search O neg k (2*p+neg.toNat);(v.1,v.2+1)
   | .larger=>let v:=search O neg k (2*p+(!neg).toNat);(v.1,v.2+1)
def inside (neg:Bool) (p k:ℕ) (v:ℤ):Prop:=
  ((p*2^k:ℕ):ℤ) < orient neg v ∧ orient neg v< (((p+1)*2^k:ℕ):ℤ)
def answerOK (Q:Set (Fin 1→ℝ)):Option ℤ → Prop
 | some x=>zCast (point x)∈Q
 | none=>∀v:Fin 1→ℤ,zCast v∉Q
theorem half (neg bigger:Bool) (p k:ℕ) (v:ℤ) (old:inside neg p (k+1) v)
    (dir:if bigger then midpoint neg p k < v else v < midpoint neg p k):
     inside neg (2*p+(xor bigger neg).toNat) k v:=by
  have ll:p*2^(k+1)=2*(p*2^k):=by rw [pow_succ];ac_rfl
  have uu:(p+1)*2^(k+1)=2*(p*2^k)+2*2^k:=by rw [Nat.add_mul,pow_succ,Nat.one_mul];ring
  have mi:(2*p+1)*2^k=2*(p*2^k)+2^k:=by rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
  cases neg <;> cases bigger <;>
    simp [inside,midpoint,orient,ll,uu,mi,Nat.add_mul,Nat.mul_assoc] at * <;> omega
theorem descent (O:List Bool → List Bool) (Q:Set (Fin 1→ℝ))
    (spec:∀y:Fin 1→ℚ,IsSepAnswer Q y (O (encVec y))) (neg:Bool) (k p:ℕ)
    (range:∀v:Fin 1→ℤ,zCast v∈Q → inside neg p k (v 0)):
    answerOK Q (search O neg k p).1 ∧ (search O neg k p).2 ≤ k:=by
  induction k generalizing p with
  | zero=>
    refine ⟨?_,by simp [search]⟩
    intro v mem
    have impossible:=range v mem
    simp [inside] at impossible
    omega
  | succ k ih=>
    have dir:=direction Q (midpoint neg p k) O spec
    cases h:readReply (O (query (midpoint neg p k))) with
    | member=>simpa [search,h,answerOK,Valid] using dir
    | empty=>simpa [search,h,answerOK,Valid] using dir
    | smaller=>
      rw [h] at dir
      have hp (v:Fin 1→ℤ) (mem:zCast v∈Q):inside neg (2*p+neg.toNat) k (v 0):=by
        simpa using half neg false p k (v 0) (range v mem) (dir v mem)
      simpa [search,h] using ih _ hp
    | larger=>
      rw [h] at dir
      have hp (v:Fin 1→ℤ) (mem:zCast v∈Q):inside neg (2*p+(!neg).toNat) k (v 0):=by
        simpa using half neg true p k (v 0) (range v mem) (dir v mem)
      simpa [search,h] using ih _ hp
end BitGrid.Line

set_option synthInstance.maxSize 3000
namespace BitGrid.Line.TM
open BitStacks Scanner
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
def candidate (p:List Bool) (k:ℕ):=p++true::List.replicate k false
def frontier (neg:Bool) (p:List Bool) (k:ℕ):Cells:={divisor:=p.reverse,binCount:=u k,dimension:=[neg]}
def beforeAsk (neg:Bool) (p:List Bool) (k:ℕ):Cells:=
  let x:=midpoint neg (magnitude p) k
  {frontier neg p k with prep:=query x,product:=encodeInt x,todo:=tagged (rowTags (neg,candidate p k)).reverse}
theorem magCandidate (p:List Bool) (k:ℕ):magnitude (candidate p k)=(2*magnitude p+1)*2^k:=by
  have zeros(j:ℕ):val (List.replicate j false)=0:=by
    induction j with | zero=>rfl | succ j ih=>simp [List.replicate_succ,val,ih]
  simp [magnitude,candidate,List.append_assoc,valAppend,val,zeros,Nat.mul_comm,Nat.add_comm]
theorem signedCandidate (neg:Bool) (p:List Bool) (k:ℕ):signed neg (candidate p k)=midpoint neg (magnitude p) k:=by
  cases neg <;>simp [signed,magCandidate,orient,midpoint]
theorem magAppend (p:List Bool) (b:Bool):magnitude (p++[b])=2*magnitude p+b.toNat:=by simp [magnitude,val,Nat.add_comm]
theorem size_u (k:ℕ):(u k).length=k:=by induction k with | zero=>rfl | succ k ih=>simp [ih]
theorem size_d (k:ℕ):d k=saved (List.replicate k false):=by
  induction k with | zero=>rfl | succ k ih=>simp [List.replicate_succ,ih]
theorem produce (O:List Bool → List Bool) (Q:ℕ) (neg:Bool) (p:List Bool) (k:ℕ):
    ∃t≤10*(p.length+k+3),Goes O Q (a 8) (frontier neg p (k+1)) t (a 2) (beforeAsk neg p k) := by
  let s:=frontier neg p 0
  let z:Cells:={s with input:=[false]}
  have openP:Goes O Q (a 8) (frontier neg p (k+1)) 1 (a 9) {z with binCount:=u k}:=by
    have st:=Oracle.Trace.bits (program:=TM.code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=(frontier neg p (k+1)).mem) (show a 8≠a 2 by decide)
    simpa [Goes,frontier,TM.code,z,s,a,finish,jump,Action.run] using st
  have prep:=loop9 O Q k z
  have restore:=loop10 O Q k {z with input:=d k++[false]}
  let b:Cells:={frontier neg [] k with input:=true::true::(d k++[false])}
  have pre:=loop11 O Q p.reverse b
  have rev:=loop12 O Q p {b with input:=saved p++b.input}
  simp [z,b,s,frontier] at prep restore pre rev
  have path:=(((openP.join prep).join restore).join pre).join rev
  let bs:=candidate p k
  have run:=many [(neg,bs)] (frontier neg p k)
  have lift:=Oracle.lift run O (reg first) (a 2) (a 3) Q TM.code scan (some (a 2)) (by intro i;simp [scan,a]) (by intro i;rfl)
  have tape:tagged (rowTags (neg,bs))=true::neg::(saved p++true::true::(d k++[false])):=by
    simp [bs,candidate,saved,tagged,tags,rowTags,tag,List.append_assoc,size_d]
  have step:Goes O Q (scan start) {frontier neg p k with input:=true::neg::(saved p++true::true::(d k++[false]))} (clocks [(neg,bs)]+1) (a 2) (beforeAsk neg p k):=by
    simpa [Goes,frontier,beforeAsk,tape,show tags [(neg,bs)]=rowTags (neg,bs) by simp [tags],Scanner.xWord,Scanner.qWord,bs,signedCandidate,query] using lift
  have tr:=path.join step
  refine ⟨_,?_,tr⟩
  have sig:(significant bs).length ≤ bs.length:=by
    have hl(w:List Bool):(significant w).length ≤ w.length:=by
      induction w with | nil=>rfl | cons b w ih=>cases b <;>simp [significant] <;>omega
    exact hl _
  simp [clocks,cost,bs,candidate] at *;omega
end BitGrid.Line.TM

namespace BitGrid.Line.TM
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
theorem loop4 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 4) {s with prep:=w} (w.length+1) (a 5) {s with prep:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with prep:=[]}:Cells).mem) (show a 4≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 4) {s with prep:=b::w} 1 (a 4) {z with prep:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with prep:=b::w}:Cells).mem) (show a 4≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop5 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 5) {s with todo:=w} (w.length+1) (a 6) {s with todo:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with todo:=[]}:Cells).mem) (show a 5≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 5) {s with todo:=b::w} 1 (a 5) {z with todo:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with todo:=b::w}:Cells).mem) (show a 5≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop6 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 6) {s with product:=w} (w.length+1) (a 7) {s with product:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with product:=[]}:Cells).mem) (show a 6≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 6) {s with product:=b::w} 1 (a 6) {z with product:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with product:=b::w}:Cells).mem) (show a 6≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop13 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 13) {s with prep:=w} (w.length+1) (a 14) {s with prep:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with prep:=[]}:Cells).mem) (show a 13≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 13) {s with prep:=b::w} 1 (a 13) {z with prep:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with prep:=b::w}:Cells).mem) (show a 13≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop14 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 14) {s with todo:=w} (w.length+1) (a 15) {s with todo:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with todo:=[]}:Cells).mem) (show a 14≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 14) {s with todo:=b::w} 1 (a 14) {z with todo:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with todo:=b::w}:Cells).mem) (show a 14≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop15 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 15) {s with binCount:=w} (w.length+1) (a 16) {s with binCount:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with binCount:=[]}:Cells).mem) (show a 15≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 15) {s with binCount:=b::w} 1 (a 15) {z with binCount:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with binCount:=b::w}:Cells).mem) (show a 15≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop16 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 16) {s with divisor:=w} (w.length+1) (a 17) {s with divisor:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with divisor:=[]}:Cells).mem) (show a 16≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 16) {s with divisor:=b::w} 1 (a 16) {z with divisor:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with divisor:=b::w}:Cells).mem) (show a 16≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop17 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 17) {s with dimension:=w} (w.length+1) (a 18) {s with dimension:=[]} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with dimension:=[]}:Cells).mem) (show a 17≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 17) {s with dimension:=b::w} 1 (a 17) {z with dimension:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with dimension:=b::w}:Cells).mem) (show a 17≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop19 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 19) {s with product:=w} (w.length+1) (a 20) {s with product:=[],reversed:=w.reverse++s.reversed} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with product:=[]}:Cells).mem) (show a 19≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:={s with reversed:=b::s.reversed}
    have firstPath:Goes O Q (a 19) {s with product:=b::w} 1 (a 19) {z with product:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with product:=b::w}:Cells).mem) (show a 19≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop20 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 20) {s with reversed:=w} (w.length+1) none {s with reversed:=[],input:=true::(w.reverse++s.input)} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with reversed:=[]}:Cells).mem) (show a 20≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:={s with input:=b::s.input}
    have firstPath:Goes O Q (a 20) {s with reversed:=b::w} 1 (a 20) {z with reversed:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with reversed:=b::w}:Cells).mem) (show a 20≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
theorem loop21 (O:List Bool → List Bool) (Q:ℕ) (w:List Bool) (s:Cells):Goes O Q (a 21) {s with product:=w} (w.length+1) none {s with product:=[],input:=false::s.input} := by
  induction w generalizing s with
  | nil=>
    have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with product:=[]}:Cells).mem) (show a 21≠a 2 by decide)
    simpa [Goes,code,a,wipe,move,put,jump,Action.run] using step
  | cons b w ih=>
    let z:Cells:=s
    have firstPath:Goes O Q (a 21) {s with product:=b::w} 1 (a 21) {z with product:=w} := by
      have step:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with product:=b::w}:Cells).mem) (show a 21≠a 2 by decide)
      simpa [Goes,code,a,wipe,move,put,jump,Action.run,z] using step
    simpa [z,List.append_assoc,Nat.add_comm 1] using firstPath.join (ih z)
end BitGrid.Line.TM

set_option synthInstance.maxSize 3000
namespace BitGrid.Line.TM
open BitStacks
open OneTypeTM (Cells R)
open OneTypeTM.R
def frame (mode:Option Bool) (p:List Bool) (k:ℕ) (value backup ans flags:List Bool):Cells:=
 {dimension:=mode.toList,divisor:=p.reverse,binCount:=u k,product:=value,todo:=backup,prep:=ans,itemCount:=flags}
def leftover(w:List Bool):=if w.head?.getD false then w.tail else w.drop 3
def indicator : Reply → Bool | .member=>true | .empty=>false | .smaller=>false | .larger=>true
def location : Reply → L | .member|.empty=>a 13 | _=>a 4
theorem classify (O:List Bool → List Bool) (Q:ℕ) (mode:Option Bool) (p:List Bool) (k:ℕ) (v b w:List Bool):
   Goes O Q (a 3) (frame mode p k v b w []) 1 (location (readReply w))
     (frame mode p k v b (leftover w) [indicator (readReply w)]) := by
   have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q)
     (m:=(frame mode p k v b w []).mem) (show a 3≠a 2 by decide)
   cases w with
   | nil=>simpa [Goes,code,a,frame,decode,finish,jump,Action.run,readReply,location,indicator,leftover] using st
   | cons hd t=>
     cases hd with
     | true=>simpa [Goes,code,a,frame,decode,finish,jump,Action.run,readReply,location,indicator,leftover] using st
     | false=>
       cases t with
       | nil=>simpa [Goes,code,a,frame,decode,finish,jump,Action.run,readReply,location,indicator,leftover] using st
       | cons sg ys=>
         cases ys with
         | nil=>cases sg <;>simpa [Goes,code,a,frame,decode,finish,jump,Action.run,readReply,location,indicator,leftover] using st
         | cons bit tl=>cases sg <;> cases bit <;>simpa [Goes,code,a,frame,decode,finish,jump,Action.run,readReply,location,indicator,leftover] using st
theorem residueLength(w:List Bool):(leftover w).length ≤ w.length:=by
 unfold leftover;split <;>simp
theorem call (O:List Bool → List Bool) (Q:ℕ) (mode:Option Bool) (p:List Bool) (k:ℕ) (v b w:List Bool) (len:w.length ≤ Q):
   let ans:=O w
   Goes O Q (a 2) (frame mode p k v b w []) 2 (location (readReply ans))
     (frame mode p k v b (leftover ans) [indicator (readReply ans)]) := by
  have st:=Oracle.Trace.call (program:=code) (O:=O) (qs:=reg first) (ask:=a 2) (resume:=a 3) (Q:=Q) (m:=(frame mode p k v b w []).mem) len
  have ask:Goes O Q (a 2) (frame mode p k v b w []) 1 (a 3) (frame mode p k v b (O w) []):=by simpa [Goes,frame] using st
  exact ask.join (classify O Q mode p k v b (O w))
theorem stop (O:List Bool → List Bool) (Q:ℕ) (mode:Option Bool) (p:List Bool) (k:ℕ) (v b w:List Bool) (ok:Bool):
    ∃ t ≤ w.length+b.length+k+p.length+2*v.length+11,Goes O Q (a 13) (frame mode p k v b w [ok]) t none {input:=if ok then true::v else [false]} := by
  let s:=frame mode p k v b w [ok]
  have e0:=loop13 O Q w s
  have e1:=loop14 O Q b {s with prep:=[]}
  have e2:=loop15 O Q (u k) {s with prep:=[],todo:=[]}
  have e3:=loop16 O Q p.reverse {s with prep:=[],todo:=[],binCount:=[]}
  have e4:=loop17 O Q mode.toList ({product:=v,itemCount:=[ok]}:Cells)
  let last:Cells:={product:=v,itemCount:=[ok]}
  have pick:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=last.mem) (show a 18≠a 2 by decide)
  simp [s,frame] at e0 e1 e2 e3
  have work:=(((e0.join e1).join e2).join e3).join e4
  have U(j:ℕ):(u j).length=j:=by induction j with | zero=>rfl | succ j ih=>simp [ih]
  have ml:mode.toList.length≤1:=by cases mode <;>simp
  cases ok with
  | false=>
    have choose:Goes O Q (a 18) last 1 (a 21) {product:=v}:=by simpa [Goes,code,a,last,jump,Action.run] using pick
    have del:=loop21 O Q v ({}:Cells)
    have tr:=(work.join choose).join del
    refine ⟨_,?_,tr⟩
    simp only [U,List.length_reverse];omega
  | true=>
    have choose:Goes O Q (a 18) last 1 (a 19) {product:=v}:=by simpa [Goes,code,a,last,jump,Action.run] using pick
    have move0:=loop19 O Q v ({}:Cells)
    have move1:=loop20 O Q v.reverse ({}:Cells)
    simp only [List.append_nil,List.reverse_reverse] at move0 move1
    have tr:=((work.join choose).join move0).join move1
    refine ⟨_,?_,tr⟩
    simp only [U,List.length_reverse];omega
def follow (mode:Option Bool) (p:List Bool) (sg:Bool):Bool×List Bool:=
  match mode with | none=>(!sg,p) | some neg=>(neg,p++[xor sg neg])
theorem routeNext (O:List Bool → List Bool) (Q:ℕ) (mode:Option Bool) (p:List Bool) (k:ℕ) (v b w:List Bool) (sg:Bool):
    Goes O Q (a 4) (frame mode p k v b w [sg]) (w.length+1+(b.length+1)+(v.length+1)+1) (a 8)
      (frame (some (follow mode p sg).1) (follow mode p sg).2 k [] [] [] []) := by
  let s:=frame mode p k v b w [sg]
  have e0:=loop4 O Q w s
  have e1:=loop5 O Q b {s with prep:=[]}
  have e2:=loop6 O Q v {s with prep:=[],todo:=[]}
  let before:=frame mode p k [] [] [] [sg]
  have pick:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=before.mem) (show a 7≠a 2 by decide)
  have after:Goes O Q (a 7) before 1 (a 8) (frame (some (follow mode p sg).1) (follow mode p sg).2 k [] [] [] []):=by
    cases mode <;>simpa [Goes,code,a,before,frame,follow,jump,Action.run] using pick
  exact ((e0.join e1).join e2).join after
end BitGrid.Line.TM

set_option synthInstance.maxSize 3000
namespace BitGrid.Line.TM
open BitStacks Scanner
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
def result:Option ℤ → List Bool | none=>[false] | some x=>true::encodeInt x
def costAt(m R:ℕ):=60*(m+1)+R+30
private theorem sizes (neg:Bool) (p:List Bool) (k m:ℕ) (bound:p.length+k+1 ≤ m):
  let x:=midpoint neg (magnitude p) k
  (query x).length≤2*m+5 ∧ (encodeInt x).length≤2*m+2 ∧ (tagged (rowTags (neg,candidate p k)).reverse).length≤2*m+4:=by
  let bs:=candidate p k
  have len:bs.length ≤ m:=by simp [bs,candidate];omega
  have sig:(significant bs).length ≤ bs.length:=by
    have h(w:List Bool):(significant w).length ≤ w.length:=by
      induction w with | nil=>rfl | cons b w ih=>cases b <;> simp [significant] <;> omega
    exact h bs
  have int:(encodeInt (midpoint neg (magnitude p) k)).length≤2*m+2:=by
    rw [←signedCandidate,signCode];change (_::(List.replicate (significant bs).length true++[false]++(significant bs).reverse)).length ≤ _;simp;omega
  have data(w:List (Option Bool)):(tagged w).length≤2*w.length:=by
    induction w with | nil=>rfl | cons i w ih=>cases i <;>simp [tagged,tag] at * <;>omega
  have bk:=data (rowTags (neg,bs)).reverse
  rw [List.length_reverse,show (rowTags (neg,bs)).length=bs.length+2 by simp [rowTags]] at bk
  refine ⟨?_,int,?_⟩
  · simp [query,encodeRat,show (encodeNat 1).length=3 by decide];omega
  · exact bk.trans (show 2*(bs.length+2)≤2*m+4 by omega)
theorem calculate (O:List Bool → List Bool) (m R:ℕ) (limit:∀x:ℤ,(query x).length≤2*m+5→(O (query x)).length ≤ R)
    (neg:Bool) (p:List Bool) (k:ℕ) (width:p.length+k ≤ m):
    ∃ t≤(k+1)*costAt m R,Goes O (2*m+5) (a 8) (frontier neg p k) t none {input:=result (search O neg k (magnitude p)).1}:=by
  let Q:=2*m+5
  induction k generalizing p with
  | zero=>
    have z:=Oracle.Trace.bits (program:=TM.code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=(frontier neg p 0).mem) (show a 8≠a 2 by decide)
    have on:Goes O Q (a 8) (frontier neg p 0) 1 (a 13) (frame (some neg) p 0 [] [] [] [false]):=by
      simpa [Goes,frontier,frame,TM.code,a,finish,TM.jump,Action.run] using z
    obtain ⟨t,bd,done⟩:=stop O Q (some neg) p 0 [] [] [] false
    refine ⟨_,?_,on.join done⟩
    simp [costAt] at *;omega
  | succ k ih=>
    let x:=midpoint neg (magnitude p) k
    let backup:=tagged (rowTags (neg,candidate p k)).reverse
    let ans:=O (query x)
    obtain ⟨s,sc,gen⟩:=produce O Q neg p k
    obtain ⟨ql,xl,bl⟩:=sizes neg p k m (by omega)
    have ol:=limit x ql
    have remLen:(leftover ans).length ≤ R:=(residueLength ans).trans ol
    have asked:=call O Q (some neg) p k (encodeInt x) backup (query x) ql
    have path:Goes O Q (a 8) (frontier neg p (k+1)) (s+2) (location (readReply ans))
        (frame (some neg) p k (encodeInt x) backup (leftover ans) [indicator (readReply ans)]):=gen.join asked
    have clock : s+2+(leftover ans).length+backup.length+k+p.length+2*(encodeInt x).length+11 ≤ costAt m R :=by
      change backup.length≤2*m+4 at bl
      change (encodeInt x).length≤2*m+2 at xl
      dsimp [costAt];omega
    have total:costAt m R≤(k+1+1)*costAt m R:=by rw [Nat.succ_mul];omega
    have endCase (flag:Bool) (hyp:readReply ans=if flag then .member else .empty):
        ∃ t≤(k+1+1)*costAt m R,Goes O Q (a 8) (frontier neg p (k+1)) t none {input:=if flag then true::encodeInt x else [false]}:=by
      obtain ⟨t,tm,fin⟩:=stop O Q (some neg) p k (encodeInt x) backup (leftover ans) flag
      have tr:Goes O Q (a 8) (frontier neg p (k+1)) (s+2) (a 13) (frame (some neg) p k (encodeInt x) backup (leftover ans) [flag]):=by
        cases flag <;>simpa [hyp,location,indicator] using path
      exact ⟨s+2+t,by omega,tr.join fin⟩
    have branchCase (sg:Bool) (hyp:readReply ans=if sg then .larger else .smaller):
        ∃ t≤(k+1+1)*costAt m R,Goes O Q (a 8) (frontier neg p (k+1)) t none
          {input:=result (search O neg k (2*magnitude p+(xor sg neg).toNat)).1}:=by
      have tr:Goes O Q (a 8) (frontier neg p (k+1)) (s+2) (a 4) (frame (some neg) p k (encodeInt x) backup (leftover ans) [sg]):=by
        cases sg <;>simpa [hyp,location,indicator] using path
      have route:=routeNext O Q (some neg) p k (encodeInt x) backup (leftover ans) sg
      let pp:=p++[xor sg neg]
      obtain ⟨t,tm,nextStep⟩:=ih pp (by simp [pp];omega)
      have fullPath:=(tr.join route).join nextStep
      refine ⟨_,?_,by simpa [pp,magAppend] using fullPath⟩
      rw [Nat.succ_mul (k+1)];omega
    cases casesR:readReply ans with
    | member=>simpa [search,show readReply (O (query (midpoint neg (magnitude p) k)))=.member from casesR,result,x] using endCase true casesR
    | empty=>simpa [search,show readReply (O (query (midpoint neg (magnitude p) k)))=.empty from casesR,result] using endCase false casesR
    | smaller=>simpa [search,show readReply (O (query (midpoint neg (magnitude p) k)))=.smaller from casesR] using branchCase false casesR
    | larger=>simpa [search,show readReply (O (query (midpoint neg (magnitude p) k)))=.larger from casesR] using branchCase true casesR
end BitGrid.Line.TM

set_option synthInstance.maxSize 3000
namespace BitGrid.Line.TM
open BitStacks HMBinPacking
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
private theorem counter (O:List Bool → List Bool) (Q:ℕ) (k:ℕ) (s:Cells):
  Goes O Q (a 1) {s with input:=d k++[false]} (k+1) (a 2)
    {s with input:=[],binCount:=u k++s.binCount,prep:=encodeRat 0++s.prep,product:=encodeInt 0++s.product}:=by
  induction k generalizing s with
  | zero=>
    have z:=Oracle.Trace.bits (program:=TM.code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with input:=[false]}:Cells).mem) (show a 1≠a 2 by decide)
    have er:encodeRat 0=[false,false,true,false,true]:=rfl
    have ei:encodeInt 0=[false,false]:=rfl
    simpa [Goes,TM.code,a,er,ei,push,jump,Action.run] using z
  | succ k ih=>
    let v:Cells:={s with binCount:=false::s.binCount}
    have on:Goes O Q (a 1) {s with input:=d (k+1)++[false]} 1 (a 1) {v with input:=d k++[false]}:=by
      have z:=Oracle.Trace.bits (program:=TM.code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({s with input:=d (k+1)++[false]}:Cells).mem) (show a 1≠a 2 by decide)
      simpa [Goes,TM.code,a,v,jump,Action.run] using z
    simpa [v,Nat.add_comm 1] using on.join (ih v)
theorem startInput (T:ℚ) (tail:List Bool) (O:List Bool → List Bool) (Q:ℕ):
    let raw:=encodeNat 1++encodeRat T++tail
    let m:=Radius.mWidth T
    ∃t≤200*(raw.length+3)^2+m+2,Oracle.Trace TM.code O (reg first) (a 2) (a 3) Q (some (front (Radius.a 0))) (isolated (reg tape) raw) t
       (some (a 2)) (frame none [] m (encodeInt 0) [] (query 0) []).mem:=by
  let m:=Radius.mWidth T
  obtain ⟨s,sl,tr⟩:=ofOutputs (Radius.generate 1 T tail)
  have prep:=Oracle.lift tr O (reg first) (a 2) (a 3) Q TM.code front (some (a 0)) (by intro n;simp [a,front]) (by intro i;rfl)
  have gridEq:grid 1 m=true::false::(d m++[false]):=by simp [grid]
  rw [←Radius.iso (grid 1 m),gridEq] at prep
  have entry:Goes O Q (a 0) {input:=true::false::(d m++[false])} 1 (a 1) {input:=d m++[false]}:=by
    have z:=Oracle.Trace.bits (program:=TM.code) (O:=O) (qs:=reg first) (resume:=a 3) (Q:=Q) (m:=({input:=true::false::(d m++[false])}:Cells).mem) (show a 0≠a 2 by decide)
    simpa [Goes,TM.code,a,jump,Action.run] using z
  have counted:=counter O Q m ({}:Cells)
  simp at counted
  have path:=(prep.join entry).join counted
  refine ⟨_,?_,path⟩
  have eq (z:ℕ):z+1+2=z+3:=by omega
  simp only [eq] at sl
  omega
end BitGrid.Line.TM

namespace BitGrid.Line
open HMBinPacking
def solutionFor (O:List Bool → List Bool) (m:ℕ):Option ℤ:=
 match readReply (O (query 0)) with
 | .member=>some 0 | .empty=>none
 | .smaller=>(search O true m 0).1 | .larger=>(search O false m 0).1
theorem value (T:ℚ) (unit:1 ≤ T) (Q:Set (Fin 1→ℝ)) (box:∀x∈Q,∀i,|x i|≤(T:ℝ)) (O:List Bool → List Bool)
    (spec:∀y:Fin 1→ℚ,IsSepAnswer Q y (O (encVec y))) :answerOK Q (solutionFor O (Radius.mWidth T)):=by
  let m:=Radius.mWidth T
  have hl:(T:ℝ)<(2:ℝ)^m:=by exact_mod_cast (Radius.value_bounds T unit).1
  have bounds (v:Fin 1→ℤ) (mem:zCast v∈Q): |v 0|<(2:ℤ)^m:=by
    have h:|((v 0:ℤ):ℝ)|<(2:ℝ)^m:=(box _ mem 0).trans_lt hl
    exact_mod_cast h
  have first:=direction Q 0 O spec
  unfold solutionFor
  cases dec:readReply (O (query 0)) with
  | member=>rwa [dec] at first
  | empty=>rwa [dec] at first
  | smaller=>
    rw [dec] at first
    refine (descent O Q spec true m 0 ?_).1
    intro v mem
    have small:=first v mem
    have bd:=abs_lt.mp (bounds v mem)
    simp [inside,orient];omega
  | larger=>
    rw [dec] at first
    refine (descent O Q spec false m 0 ?_).1
    intro v mem
    have large:=first v mem
    have bd:=abs_lt.mp (bounds v mem)
    simp [inside,orient];omega
end BitGrid.Line

set_option synthInstance.maxSize 3000
namespace BitGrid.Line.TM
open BitStacks HMBinPacking
open OneTypeTM (Cells R)
open OneTypeTM.R
open ExponomialAssortment.FPTAS
theorem beginSearch (O:List Bool → List Bool) (m R:ℕ) (limit:∀x:ℤ,(query x).length≤2*m+5→(O (query x)).length ≤ R):
   let Q:=2*m+5
   ∃ t≤(m+2)*costAt m R,Goes O Q (a 2) (frame none [] m (encodeInt 0) [] (query 0) []) t none {input:=result (solutionFor O m)}:=by
  let Q:=2*m+5
  let y:=O (query 0)
  let s:=frame none [] m (encodeInt 0) [] (query 0) []
  have qLen:(query 0).length=5:=rfl
  have zLen:(encodeInt 0).length=2:=rfl
  have bound:(query 0).length ≤ Q:=by dsimp [Q];omega
  have rest:(leftover y).length ≤ R:=(residueLength y).trans (limit 0 bound)
  have called:=call O Q none [] m (encodeInt 0) [] (query 0) bound
  have short:2+(leftover y).length+m+15 ≤ costAt m R:=by dsimp [costAt];omega
  have total:costAt m R≤(m+2)*costAt m R:=by rw [Nat.succ_mul (m+1)];omega
  have stopCase (flag:Bool) (hyp:readReply y=if flag then .member else .empty):
       ∃t≤(m+2)*costAt m R,Goes O Q (a 2) s t none {input:=if flag then true::encodeInt 0 else [false]}:=by
    have entry:Goes O Q (a 2) s 2 (a 13) (frame none [] m (encodeInt 0) [] (leftover y) [flag]):=by
      change Goes O Q (a 2) s 2 (location (readReply y)) (frame none [] m (encodeInt 0) [] (leftover y) [indicator (readReply y)]) at called
      cases flag <;>simpa [hyp,location,indicator] using called
    obtain ⟨t,tm,tr⟩:=stop O Q none [] m (encodeInt 0) [] (leftover y) flag
    exact ⟨2+t,by simp [zLen] at tm;omega,entry.join tr⟩
  have dirCase (sg:Bool) (hyp:readReply y=if sg then .larger else .smaller):
       ∃t≤(m+2)*costAt m R,Goes O Q (a 2) s t none {input:=result (search O (!sg) m 0).1}:=by
    have entry:Goes O Q (a 2) s 2 (a 4) (frame none [] m (encodeInt 0) [] (leftover y) [sg]):=by
      change Goes O Q (a 2) s 2 (location (readReply y)) (frame none [] m (encodeInt 0) [] (leftover y) [indicator (readReply y)]) at called
      cases sg <;>simpa [hyp,location,indicator] using called
    have route:=routeNext O Q none [] m (encodeInt 0) [] (leftover y) sg
    obtain ⟨t,tm,tr⟩:=calculate O m R limit (!sg) [] m (by simp)
    have all:=(entry.join route).join tr
    refine ⟨_,?_,by simpa [magnitude,val] using all⟩
    rw [Nat.succ_mul (m+1)];simp only [List.length_nil,zLen];omega
  cases h: readReply y with
  | member=>simpa [solutionFor,show readReply (O (query 0))=.member from h,result] using stopCase true h
  | empty=>simpa [solutionFor,show readReply (O (query 0))=.empty from h,result] using stopCase false h
  | smaller=>simpa [solutionFor,show readReply (O (query 0))=.smaller from h] using dirCase false h
  | larger=>simpa [solutionFor,show readReply (O (query 0))=.larger from h] using dirCase true h

theorem runtime (e σ:ℕ) (T:ℚ) (O:List Bool → List Bool)
    (spec:∀y:Fin 1→ℚ,(O (encVec y)).length≤(σ+(encVec y).length)^e):
    let m:=Radius.mWidth T
    let q:=2*m+5
    let raw:=encodeNat 1++encodeRat T++encodeNat σ
    ORunsWithin oracle O raw (result (solutionFor O m)) (200*(raw.length+3)^2+(m+5)*costAt m ((σ+q)^e)) q:=by
  let m:=Radius.mWidth T
  let Q:=2*m+5
  let R:=(σ+Q)^e
  have cap (x:ℤ) (len:(query x).length ≤ Q):(O (query x)).length ≤ R:=by
    have z:=spec (fun _=>(x:ℚ))
    rw [encOne] at z
    exact z.trans (Nat.pow_le_pow_left (Nat.add_le_add_left len σ) _)
  obtain ⟨s,sc,start⟩:=startInput T (encodeNat σ) O Q
  obtain ⟨t,ct,finish⟩:=beginSearch O m R cap
  unfold Goes at finish
  rw [Radius.iso] at finish
  have tr:=start.join finish
  apply tr.registered
  change s+t≤200*((encodeNat 1++encodeRat T++encodeNat σ).length+3)^2+(m+5)*costAt m R
  change s≤200*((encodeNat 1++encodeRat T++encodeNat σ).length+3)^2+m+2 at sc
  have big:m+2≤3*costAt m R:=by dsimp [costAt];omega
  rw [show m+5=(m+2)+3 by omega,Nat.add_mul]
  omega
end BitGrid.Line.TM

namespace BitGrid.Line
theorem limits (e m σ N:ℕ) (pos:1≤σ) (sm:m≤σ) (sz:N≤4*σ+2):
    let q:=2*m+5
    let c:=3*e+24
    200*(N+3)^2+(m+5)*(60*(m+1)+(σ+q)^e+30)≤2^c*σ^c ∧ q≤2^c*σ^c:=by
  let p:=e+1
  let c:=3*e+24
  let q:=2*m+5
  change 200*(N+3)^2+(m+5)*(60*(m+1)+(σ+q)^e+30)≤2^c*σ^c ∧ q≤2^c*σ^c
  have qq:q≤7*σ:=by dsimp [q];omega
  have qq':σ+q≤8*σ:=by omega
  have a:=Nat.pow_le_pow_left qq' e
  rw [Nat.mul_pow] at a
  have ep:σ^e≤σ^p:=Nat.pow_le_pow_right pos (by dsimp [p];omega)
  have ans:=a.trans (Nat.mul_le_mul_left _ ep)
  have sp:σ≤σ^p:=by simpa using Nat.pow_le_pow_right pos (show 1 ≤ p by dsimp [p];omega)
  have st:60*(m+1)+(σ+q)^e+30≤(150+8^e)*σ^p:=by rw [Nat.add_mul];omega
  have many:=Nat.mul_le_mul (show m+5≤6*σ by omega) st
  have ss:σ*σ^p≤σ^c:=by rw [←pow_succ'];exact Nat.pow_le_pow_right pos (by dsimp [p,c];omega)
  have re:6*σ*((150+8^e)*σ^p)=6*(150+8^e)*(σ*σ^p):=by ac_rfl
  rw [re] at many
  have all:=many.trans (Nat.mul_le_mul_left _ ss)
  have raw:=Nat.pow_le_pow_left (show N+3≤9*σ by omega) 2
  rw [Nat.mul_pow] at raw
  norm_num at raw
  have sc:σ^2≤σ^c:=Nat.pow_le_pow_right pos (by dsimp [c];omega)
  have s1:σ≤σ^c:=by simpa using Nat.pow_le_pow_right pos (show 1 ≤ c by dsimp [c];omega)
  have const:16200+6*(150+8^e)≤2^c:=by
    change _≤2^(3*e+24)
    rw [pow_add,pow_mul];norm_num
    have :=Nat.one_le_pow e 8 (by decide);omega
  have total:=Nat.mul_le_mul_right (σ^c) const
  rw [Nat.add_mul] at total
  constructor <;>omega
end BitGrid.Line

open HMBinPacking ExponomialAssortment.FPTAS
namespace BitGrid.Line
private theorem natLength(k:ℕ):(encodeNat k).length≤2*k+1:=by
  have sz:k.size ≤ k:=Nat.size_le.mpr Nat.lt_two_pow_self
  simp [encodeNat,Nat.size_eq_bits_len];omega
end BitGrid.Line

/-- The registered integer-feasibility specification in dimension one, with
a single oracle machine for every rational radius and response exponent. -/
theorem solution :
    ∃ OM:OracleMachine,∀ e:ℕ,∀ T:ℚ,1 ≤ T → ∀ σ:ℕ,1+enc T≤σ →
      ∀ Q:Set (Fin 1→ℝ),(∀x∈Q,∀i,|x i|≤(T:ℝ)) → ∀ O:List Bool → List Bool,
      (∀y:Fin 1→ℚ,IsSepAnswer Q y (O (encVec y)) ∧ (O (encVec y)).length≤(σ+(encVec y).length)^e) →
      let raw:=encodeNat 1++encodeRat T++encodeNat σ
      let m:=T.num.natAbs.size+1-T.den.size
      let q:=2*m+5
      let t:=200*(raw.length+3)^2+(m+5)*(60*(m+1)+(σ+q)^e+30)
      let c:=3*e+24
      let B:=2^c*σ^c
      ∃w:List Bool,ORunsWithin OM O raw w (min t B) (min q B) ∧
         ((∃x:Fin 1→ℤ,w=true::encodeIntVec x ∧ zCast x∈Q) ∨ (w=[false] ∧ ∀x:Fin 1→ℤ,zCast x∉Q)) := by
  refine ⟨BitGrid.Line.TM.oracle,?_⟩
  intro e T unit σ size Q box O spec
  let m:=BitGrid.Radius.mWidth T
  let raw:=encodeNat 1++encodeRat T++encodeNat σ
  have pos:1≤σ:=by omega
  have ml:m≤σ:=by have z:=BitGrid.Radius.width_enc T;change m ≤ enc T at z;omega
  have N:raw.length≤4*σ+2:=by
    have s:=BitGrid.Line.natLength σ
    change 1+(encodeRat T).length≤σ at size
    simp [raw,show (encodeNat 1).length=3 by decide];omega
  have bound:=BitGrid.Line.limits e m σ raw.length pos ml N
  have exec:=BitGrid.Line.TM.runtime e σ T O (fun y=>(spec y).2)
  have ok:=BitGrid.Line.value T unit Q box O (fun y=>(spec y).1)
  let result:=BitGrid.Line.solutionFor O m
  refine ⟨BitGrid.Line.TM.result result,?_,?_⟩
  · let q:=2*m+5
    let c:=3*e+24
    let t:=200*(raw.length+3)^2+(m+5)*(60*(m+1)+(σ+q)^e+30)
    change ORunsWithin BitGrid.Line.TM.oracle O raw (BitGrid.Line.TM.result result) (min t (2^c*σ^c)) (min q (2^c*σ^c))
    rw [min_eq_left (show t≤2^c*σ^c from bound.1),min_eq_left (show q≤2^c*σ^c from bound.2)]
    exact exec
  · change BitGrid.Line.answerOK Q result at ok
    cases h:result with
    | none=>rw [h] at ok;exact Or.inr ⟨rfl,ok⟩
    | some v=>
      rw [h] at ok
      exact Or.inl ⟨BitGrid.Line.point v,by simp [BitGrid.Line.TM.result,BitGrid.Line.xOne],ok⟩
