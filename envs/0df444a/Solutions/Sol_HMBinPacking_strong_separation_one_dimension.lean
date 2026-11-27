-- Prove2me | solution 1 for HMBinPacking.strong_separation_one_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:16:16.439038+00:00
-- url     : https://prove2.me/submissions/f5da2c0a-d086-4388-86ea-b44b0c00628e

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_Encoding
import Theorems.Thm_HMBinPacking_lenstra_residue_optimization
import Definitions.Def_HMBinPacking_Oracles
open HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)
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

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
abbrev L := OneTypeTM.L ⊕ ((Fin 3 × Fin 8) ⊕ (Fin 7 ⊕ (Fin 4 ⊕ (Fin 8 ⊕ (Bool × Fin 4)))))
def old (l : OneTypeTM.L) : L := .inl l
def H (p : Fin 8) : L := .inr (.inl (0,p))
def D (p : Fin 8) : L := .inr (.inl (1,p))
def V (p : Fin 8) : L := .inr (.inl (2,p))
def A (j : Fin 7) : L := .inr (.inr (.inl j))
def E (j : Fin 4) : L := .inr (.inr (.inr (.inl j)))
def G (j : Fin 8) : L := .inr (.inr (.inr (.inr (.inl j))))
def M (r : Bool) (j : Fin 4) : L := .inr (.inr (.inr (.inr (.inr (r,j)))))
open ExponomialAssortment.FPTAS (encodeRat encodeNat)
def lowWord := false::(encodeRat (-1)++encodeRat 0)
def prefixWord := false::(encodeRat 1++[false])
def upperWord (q : ℕ) := prefixWord++(encodeNat q++encodeNat 1)
def pushWord : List Bool → Action (Bank R) L → Action (Bank R) L
  | [],a => a
  | b::bs,a => pushWord bs (.push (reg tape) b a)
def factor (r : Bool) : R := if r then rem else den
def accum (r : Bool) : R := if r then prod else items
def jump (l : L) : Action (Bank R) L := .stop (some l)
def next (p : Fin 8) : L := if p=5 then A 0 else if p=7 then G 2 else H (p+1)
def dest (p : Fin 8) : R := if p=0 then rem else if p=6 then second else den
def code : L → Macro R L
  | .inl l => (OneTypeTM.code l).mapLabels old
  | .inr (.inl (tag,p)) =>
    if tag=0 then .bits (.peek (reg tape) (fun v => .drop (reg tape)
      (if v.getD false then .push (reg width) true (jump (H p)) else jump (D p))))
    else if tag=1 then .bits (.peek (reg width) (fun v => if v.isSome then
      .drop (reg width) (.peek (reg tape) (fun b => .drop (reg tape)
        (.push (reg rev) (b.getD false) (jump (D p))))) else jump (V p)))
    else .bits (.peek (reg rev) (fun b => match b with
      | none => jump (next p) | some bit => .drop (reg rev) (if p=0 ∨ p=2 ∨ p=6 ∨ p=7 then
           .push (reg (dest p)) bit (jump (V p)) else jump (V p))))
  | .inr (.inr (.inl j)) => match j.val with
    | 0 => .bits (.peek (reg tape) (fun b => .drop (reg tape) (jump (if b.getD false then G 6 else A 1))))
    | 1 => .bits (.peek (reg rem) (fun b => match b with
      | none => jump (A 2) | some v => .drop (reg rem) (.push (reg first) v (jump (A 1)))))
    | 2 => .bits (.peek (reg first) (fun b => match b with
      | none => jump (G 0) | some v => .drop (reg first) (.push (reg bins) v (jump (A 3)))))
    | 3 => .binary .le den bins (by decide) (A 4)
    | 4 => .bits (.peek tmp (fun b => .drop tmp (if b.getD false then jump (A 5) else
         .peek (reg prod) (fun c => if c.isSome then .push (reg prod) false (jump (A 2)) else jump (A 2)))))
    | 5 => .binary .sub bins den (by decide) (A 6)
    | _ => .bits (.drop tmp (.push (reg prod) true (jump (A 2))))
  | .inr (.inr (.inr (.inl j))) => match j.val with
    | 0 => .bits (pushWord (encodeNat 1) (jump (E 1)))
    | 1 => .bits (.peek (reg prod) (fun b => match b with
      | none => jump (E 2) | some v => .drop (reg prod) (.push (reg rev) v (.push (reg width) true (jump (E 1))))))
    | 2 => .bits (.peek (reg rev) (fun b => match b with
      | none => .push (reg tape) false (jump (E 3)) | some v => .drop (reg rev) (.push (reg tape) v (jump (E 2)))))
    | _ => .bits (.peek (reg width) (fun b => if b.isSome then .drop (reg width) (.push (reg tape) true (jump (E 3)))
         else pushWord prefixWord (jump (old (OneTypeTM.C 0)))))
  | .inr (.inr (.inr (.inr (.inl j)))) => match j.val with
    | 0 => .bits (.peek (reg den) (fun b => if b.isSome then .drop (reg den) (jump (G 0)) else jump (G 1)))
    | 1 => .bits (.peek (reg bins) (fun b => if b.isSome then .drop (reg bins) (jump (G 1)) else jump (H 6)))
    | 2 => .bits (.peek (reg prod) (fun b => match b with
        | none => jump (G 3)
        | some v => .drop (reg prod) (.push (reg rev) v (jump (G 2)))))
    | 3 => .bits (.peek (reg rev) (fun b => match b with
        | none => jump (M false 0)
        | some v => .drop (reg rev) (.push (reg prod) v (.push (reg bins) v (jump (G 3))))))
    | 4 => .binary .le second items (by decide) (G 5)
    | 5 => .bits (.peek tmp (fun b => .drop tmp (jump (if b.getD false then G 7 else E 0))))
    | _ => .bits (.peek (reg tape) (fun b => if b.isSome then .drop (reg tape) (jump (G j))
        else pushWord (if j=6 then lowWord else [true]) (jump (old (OneTypeTM.C 0)))))
  | .inr (.inr (.inr (.inr (.inr (r,j))))) => match j.val with
    | 0 => .bits (.peek (reg (factor r)) (fun b => match b with
           | none => jump (G 4)
           | some x => .drop (reg (factor r)) (jump (if x then M r 1 else M r 3))))
    | 1 => .binary .add (accum r) bins (by cases r <;> decide) (M r 2)
    | 2 => .bits (.drop tmp (jump (M r 3)))
    | _ => .bits (.push (reg bins) false (jump (M r 0)))
def machine := BitStacks.machine (.inl (H 0)) (reg tape) (wordCode code)
abbrev Goes (l : L) (s : Cells) (t : ℕ) (o : Option L) (z : Cells) :=
  MacroPath code (some l) s.mem t o z.mem
def Runs (l : L) (s : Cells) (bound : ℕ) (out : Option L) (t : Cells) : Prop := ∃ n ≤ bound, Goes l s n out t
theorem Runs.mono {i s a o t b} (h : Runs i s a o t) (le : a≤b) : Runs i s b o t := by
  obtain ⟨n,u,v⟩:=h; exact ⟨n,u.trans le,v⟩
theorem Runs.seq {i s a j t b k v} (h : Runs i s a (some j) t) (q : Runs j t b k v) : Runs i s (a+b) k v := by
  obtain ⟨n,u,x⟩:=h;obtain ⟨m,z,y⟩:=q;exact ⟨n+m,Nat.add_le_add u z,x.join y⟩
theorem smallRun {i s t o z} (h : Goes i s t o z) : Runs i s t o z := ⟨t,le_rfl,h⟩
end OneDimSeparator

open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R

def putWord (p : Fin 8) (w : List Bool) (m : Cells) : Cells :=
  if p=0 then {m with remainder:=w++m.remainder} else if p=2 ∨ p=7 then {m with divisor:=w++m.divisor} else if p=6 then {m with todo:=w++m.todo} else m
def putInput (_ : Fin 8) (w : List Bool) (m : Cells) : Cells := {m with input:=w}

private theorem HT (p : Fin 8) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (true::bs) m) 1 (H p)
      (putInput p bs {m with scratch:=true::m.scratch}) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (true::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,putInput,Action.run,jump] using e

private theorem HF (p : Fin 8) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (false::bs) m) 1 (D p) (putInput p bs m) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (false::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,D,putInput,Action.run,jump] using e

private theorem header (p : Fin 8) (k : ℕ) (m : Cells) (t : List Bool) :
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

private theorem DT (p : Fin 8) (m : Cells) (b : Bool) (t c : List Bool) :
    Goes (D p) (putInput p (b::t) {m with scratch:=true::c}) 1 (D p)
      (putInput p t {m with scratch:=c,reversed:=b::m.reversed}) := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=(putInput p (b::t) {m with scratch:=true::c}).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,D,putInput,Action.run,jump] using e
private theorem DF (p : Fin 8) (m : Cells) :
    Goes (D p) {m with scratch:=[]} 1 (V p) {m with scratch:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=({m with scratch:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,D,V,Action.run,jump] using e

private theorem digits (p : Fin 8) (bs t : List Bool) (m : Cells) :
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

private theorem VT (p : Fin 8) (m : Cells) (b : Bool) (r : List Bool) :
    Goes (V p) {m with reversed:=b::r} 1 (V p) (putWord p [b] {m with reversed:=r}) := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=b::r}:Cells).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,V,Action.run,jump,putWord,dest] using e

private theorem VF (p : Fin 8) (m : Cells) :
    Goes (V p) {m with reversed:=[]} 1 (next p) {m with reversed:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,V,Action.run,jump] using e

private theorem backwards (p : Fin 8) (bs : List Bool) (m : Cells) :
    Goes (V p) {m with reversed:=bs} (bs.length+1) (next p) (putWord p bs.reverse {m with reversed:=[]}) := by
  induction bs generalizing m with
  | nil => fin_cases p <;> simpa [putWord] using VF _ m
  | cons b bs ih =>
    have st := VT p m b bs
    have t := ih (putWord p [b] m)
    fin_cases p <;> simp [putWord] at st t ⊢ <;>
      first | simpa [List.append_assoc,Nat.add_comm 1] using st.join t

theorem field (p : Fin 8) (n : ℕ) (t : List Bool) (m : Cells) (hs : m.scratch=[]) (hr : m.reversed=[]) :
    Goes (H p) (putInput p (encodeNat n++t) m) (3*(n.bits.length+1)) (next p)
      (putWord p n.bits (putInput p t m)) := by
  have h := header p n.bits.length m (n.bits++t)
  have d := digits p n.bits t m
  have r := backwards p n.bits.reverse (putInput p t m)
  fin_cases p <;> simp [putInput,hs,hr] at h d r ⊢ <;>
    have z := (h.join d).join r <;>
    simpa [encodeNat,List.append_assoc,Nat.mul_comm,Nat.mul_add,Nat.mul_succ,Nat.add_assoc,hs,hr] using z

end OneDimSeparator

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks

def pushQ (b : Bool) (w : List Bool) : List Bool := if b then true::w else if w.isEmpty then [] else false::w
private theorem val_lt (w : List Bool) : val w<2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih => cases b <;> simp [val,pow_succ] <;>omega
theorem qlen (b : Bool) (w : List Bool) : (pushQ b w).length≤w.length+1 := by cases b <;> cases w <;> simp [pushQ]
theorem qbits (b : Bool) (q : ℕ) : pushQ b q.bits=(2*q+b.toNat).bits := by
  cases b with
  | false =>
    by_cases z : q=0
    · subst q; rfl
    · have live : q.bits≠[] := by
        intro h;have eq := Nat.size_eq_bits_len q
        rw [h] at eq;simp at eq;exact z (Nat.size_eq_zero.mp eq.symm)
      rw [show (false:Bool).toNat=0 by rfl,Nat.add_zero,Nat.bit0_bits _ z]
      cases h : q.bits <;> simp_all [pushQ]
  | true => simp [pushQ]

private theorem cmp (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) :
    Runs (A 3) s (3*(max s.divisor.length s.binCount.length+2)) (A 4)
      {s with flag:=[decide (val s.divisor≤val s.binCount)]} := by
  have e := MacroPath.binary (P:=code) (l:=A 3) (m:=s.mem) (op:=.le) (i:=den) (j:=bins)
    (h:=by decide) (n:=A 4) (by rfl) f sp
  let z := execute compareGate true s.divisor s.binCount
  obtain ⟨a,x,y⟩ := le_correct s.divisor s.binCount
  change z.1=_ at a;change z.2.1=_ at x;change z.2.2=_ at y
  have zl : gateResult .le s.mem den bins=z := rfl
  refine ⟨gateTime .le s.mem den bins,?_,?_⟩
  · simp [gateTime,zl,x,y];omega
  · simpa [zl,afterGate,a,x,y] using e

private theorem subtract (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (ge : val s.divisor≤val s.binCount) :
    ∃ w : List Bool, Runs (A 5) s (3*(max s.divisor.length s.binCount.length+3)) (A 2)
      {s with binCount:=w,product:=true::s.product,flag:=[]} ∧
      val w=val s.binCount-val s.divisor ∧ w.length=max s.divisor.length s.binCount.length := by
  have e := MacroPath.binary (P:=code) (l:=A 5) (m:=s.mem) (op:=.sub) (i:=bins) (j:=den)
    (h:=by decide) (n:=A 6) (by rfl) f sp
  let z := execute subGate false s.binCount s.divisor
  obtain ⟨eq,right,len⟩ := sub_correct false s.binCount s.divisor
  change val s.binCount+z.1.toNat*2^(max s.binCount.length s.divisor.length)=val z.2.1+val s.divisor+0 at eq
  change z.2.2=_ at right;change z.2.1.length=_ at len
  have res : val z.2.1=val s.binCount-val s.divisor := by
    have sm := val_lt z.2.1
    rw [len] at sm
    cases h : z.1 <;> rw [h] at eq <;> simp only [Bool.toNat_true,Bool.toNat_false,Nat.zero_mul,Nat.one_mul,Nat.add_zero] at eq <;>omega
  have zl : gateResult .sub s.mem bins den=z := rfl
  let mid := {s with binCount:=z.2.1,flag:=[z.1]}
  have gate : Goes (A 5) s (gateTime .sub s.mem bins den) (A 6) mid := by simpa [afterGate,zl,right,mid] using e
  have one := MacroPath.bits (P:=code) (l:=A 6) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 6) mid 1 (A 2) {s with binCount:=z.2.1,product:=true::s.product,flag:=[]} := by
    simpa [A,code,mid,Action.run,jump] using one
  refine ⟨z.2.1,⟨_,?_,gate.join pop⟩,res,by rw [len,max_comm]⟩
  simp [gateTime,zl,right,len]; omega

theorem stepOne (s : Cells) (b : Bool) (bs : List Bool) (tw : s.prep=b::bs)
    (f : s.flag=[]) (sp : s.spare=[]) (N : ℕ) (hn : s.binCount.length≤N) (hs : s.divisor.length≤N) :
    let t := b.toNat+2*val s.binCount
    let take := decide (val s.divisor≤t)
    ∃ w : List Bool, Runs (A 2) s (9*(N+5)) (A 2)
      {s with prep:=bs,binCount:=w,product:=pushQ take s.product,flag:=[]} ∧
      val w=(if take then t-val s.divisor else t) ∧ w.length≤N+1 := by
  let t := {s with prep:=bs,binCount:=b::s.binCount}
  have one := MacroPath.bits (P:=code) (l:=A 2) (m:=s.mem) (a:=_) (by rfl)
  have beginP : Goes (A 2) s 1 (A 3) t := by simpa [t,A,code,Action.run,jump,tw] using one
  have comp := cmp t f sp
  by_cases c : val s.divisor≤b.toNat+2*val s.binCount
  · have cm : decide (val t.divisor≤val t.binCount)=true := by simp [t,val,c]
    rw [cm] at comp
    let mid := {t with flag:=[true]}
    have bi := MacroPath.bits (P:=code) (l:=A 4) (m:=mid.mem) (a:=_) (by rfl)
    have yes : Goes (A 4) mid 1 (A 5) {t with flag:=[]} := by simpa [mid,A,code,Action.run,jump] using bi
    obtain ⟨w,sub,v,l⟩ := subtract {t with flag:=[]} rfl sp (by simpa [t,val] using c)
    have path := (((smallRun beginP).seq comp).seq (smallRun yes)).seq sub
    refine ⟨w,?_,?_,?_⟩
    · simpa [t,c,pushQ] using path.mono (show _≤9*(N+5) by dsimp [t];omega)
    · simpa [t,c,val] using v
    · dsimp [t] at l;omega
  · have cm : decide (val t.divisor≤val t.binCount)=false := by simp [t,val,c]
    rw [cm] at comp
    let mid := {t with flag:=[false]}
    have bi := MacroPath.bits (P:=code) (l:=A 4) (m:=mid.mem) (a:=_) (by rfl)
    have no : Goes (A 4) mid 1 (A 2) {t with flag:=[],product:=pushQ false s.product} := by
      cases hp : s.product <;> simpa [mid,t,A,code,Action.run,jump,pushQ,hp] using bi
    have path := ((smallRun beginP).seq comp).seq (smallRun no)
    refine ⟨b::s.binCount,?_,?_,by simp;omega⟩
    · simpa [t,c] using path.mono (show _≤9*(N+5) by dsimp [t];omega)
    · simp [c,val]
end OneDimSeparator

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks

def foldDigits : List Bool → ℕ → ℕ
  | [],p => p
  | b::bs,p => foldDigits bs (2*p+b.toNat)
private theorem fold_append (x y : List Bool) (p : ℕ) : foldDigits (x++y) p=foldDigits y (foldDigits x p) := by
  induction x generalizing p with
  | nil => rfl
  | cons b bs ih => simpa [foldDigits] using ih (2*p+b.toNat)
theorem readLE (w : List Bool) : foldDigits w.reverse 0=val w := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [fold_append,foldDigits,ih,val,Nat.add_comm]

theorem rounds (bs : List Bool) (s : Cells) (q p D N K : ℕ) (live : s.prep=bs)
    (f : s.flag=[]) (sp : s.spare=[]) (hq : s.product=q.bits) (hd : val s.divisor=D)
    (inv : q*D+val s.binCount=p) (rlt : val s.binCount<D)
    (hn : s.binCount.length≤N) (hw : s.divisor.length≤N) (space : N+bs.length≤K) :
    ∃ (w : List Bool) (qf : ℕ), Runs (A 2) s (bs.length*(9*(K+5))+1) (G 0)
      {s with prep:=[],binCount:=w,product:=qf.bits,flag:=[]} ∧
      qf*D+val w=foldDigits bs p ∧ val w<D ∧ w.length≤K ∧ qf.bits.length≤q.bits.length+bs.length := by
  induction bs generalizing s q p N with
  | nil =>
    have st := MacroPath.bits (P:=code) (l:=A 2) (m:=s.mem) (a:=_) (by rfl)
    have done : Runs (A 2) s 1 (G 0) s := by apply smallRun;simpa [A,code,Action.run,jump,live] using st
    refine ⟨s.binCount,q,?_,inv,rlt,by simp at space;omega,by simp⟩
    cases s;dsimp only at live f hq;simpa [live,f,hq] using done
  | cons b bs ih =>
    obtain ⟨w,go,value,length⟩ := stepOne s b bs live f sp N hn hw
    let t := b.toNat+2*val s.binCount
    let take := decide (val s.divisor≤t)
    let q' := 2*q+take.toNat
    let u := {s with prep:=bs,binCount:=w,product:=pushQ take s.product,flag:=[]}
    have nq : u.product=q'.bits := by simp [u,q',hq,qbits]
    have bv : b.toNat≤1 := by cases b <;> decide
    have vr : val w<D := by
      change val w=(if take then t-val s.divisor else t) at value
      by_cases c : val s.divisor≤t
      · simp [take,c] at value; dsimp [t] at c value;omega
      · simp [take,c] at value; dsimp [t] at c value;omega
    have eq : q'*D+val w=2*p+b.toNat := by
      change val w=(if take then t-val s.divisor else t) at value
      by_cases c : val s.divisor≤t
      · have e := Nat.sub_add_cancel c
        simp [take,c] at value; simp [q',take,c]; dsimp [t] at e value
        nlinarith only [inv,e,value,hd]
      · simp [take,c] at value; simp [q',take,c]; dsimp [t] at value
        nlinarith only [inv,value]
    obtain ⟨ww,qf,run,vv,rr,ll,qq⟩ := ih u q' (2*p+b.toNat) (N+1) rfl rfl sp nq hd eq vr length
      (by dsimp [u];omega) (by simp at space;omega)
    have path := go.seq run
    have small : N≤K := by omega
    have tm : 9*(N+5)+(bs.length*(9*(K+5))+1)≤(b::bs).length*(9*(K+5))+1 := by simp [Nat.succ_mul];omega
    refine ⟨ww,qf,?_,vv,rr,ll,?_⟩
    · exact path.mono tm
    · have ln := qlen take q.bits
      rw [qbits] at ln
      change (2*q+take.toNat).bits.length≤q.bits.length+1 at ln
      dsimp [q'] at qq;simp;omega
end OneDimSeparator

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
theorem clearDiv (s : Cells) (bs : List Bool) : Goes (G 0) {s with divisor:=bs} (bs.length+1)
    (G 1) {s with divisor:=[]} := by
  induction bs with
  | nil =>
    have st := MacroPath.bits (P:=code) (l:=G 0) (m:=({s with divisor:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,G,Action.run,jump] using st
  | cons b bs ih =>
    have st := MacroPath.bits (P:=code) (l:=G 0) (m:=({s with divisor:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (G 0) {s with divisor:=b::bs} 1 (G 0) {s with divisor:=bs} := by simpa [code,G,Action.run,jump] using st
    simpa [Nat.add_comm 1] using one.join ih

theorem clearRem (s : Cells) (bs : List Bool) : Goes (G 1) {s with binCount:=bs} (bs.length+1)
    (H 6) {s with binCount:=[]} := by
  induction bs with
  | nil =>
    have st := MacroPath.bits (P:=code) (l:=G 1) (m:=({s with binCount:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,G,Action.run,jump] using st
  | cons b bs ih =>
    have st := MacroPath.bits (P:=code) (l:=G 1) (m:=({s with binCount:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (G 1) {s with binCount:=b::bs} 1 (G 1) {s with binCount:=bs} := by simpa [code,G,Action.run,jump] using st
    simpa [Nat.add_comm 1] using one.join ih

private theorem sweep (xs : List Bool) (s : Cells) :
    Goes (G 2) {s with product:=xs} (xs.length+1) (G 3) {s with product:=[],reversed:=xs.reverse++s.reversed} := by
  induction xs generalizing s with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=G 2) (m:=({s with product:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,G,Action.run,jump] using e
  | cons b xs ih =>
    have e := MacroPath.bits (P:=code) (l:=G 2) (m:=({s with product:=b::xs}:Cells).mem) (a:=_) (by rfl)
    have p : Goes (G 2) {s with product:=b::xs} 1 (G 2) {s with product:=xs,reversed:=b::s.reversed} := by
      simpa [code,G,Action.run,jump] using e
    have tr := p.join (ih {s with reversed:=b::s.reversed})
    simpa [List.append_assoc,Nat.add_comm 1] using tr

private theorem restore (xs : List Bool) (s : Cells) :
    Goes (G 3) {s with reversed:=xs} (xs.length+1) (M false 0)
      {s with reversed:=[],product:=xs.reverse++s.product,binCount:=xs.reverse++s.binCount} := by
  induction xs generalizing s with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=G 3) (m:=({s with reversed:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,G,Action.run,jump] using e
  | cons b xs ih =>
    have e := MacroPath.bits (P:=code) (l:=G 3) (m:=({s with reversed:=b::xs}:Cells).mem) (a:=_) (by rfl)
    have p : Goes (G 3) {s with reversed:=b::xs} 1 (G 3) {s with reversed:=xs,product:=b::s.product,binCount:=b::s.binCount} := by
      simpa [code,G,Action.run,jump] using e
    have tr := p.join (ih {s with product:=b::s.product,binCount:=b::s.binCount})
    simpa [List.append_assoc,Nat.add_comm 1] using tr

theorem duplicate (s : Cells) (h : s.reversed=[]) (p : s.binCount=[]) :
    Goes (G 2) s (2*(s.product.length+1)) (M false 0) {s with binCount:=s.product} := by
  have a := sweep s.product s
  have b := restore s.product.reverse {s with product:=[]}
  simp [h,p] at a b
  have total := a.join b
  cases s; simp_all [two_mul]

theorem finalCmp (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) :
    Runs (G 4) s (3*(max s.todo.length s.itemCount.length+2)) (G 5)
      {s with flag:=[decide (val s.todo≤val s.itemCount)]} := by
  have e := MacroPath.binary (P:=code) (l:=G 4) (m:=s.mem) (op:=.le) (i:=second) (j:=items)
    (h:=by decide) (n:=G 5) (by rfl) f sp
  let z := execute compareGate true s.todo s.itemCount
  obtain ⟨a,x,y⟩ := le_correct s.todo s.itemCount
  change z.1=_ at a;change z.2.1=_ at x;change z.2.2=_ at y
  have zl : gateResult .le s.mem second items=z := rfl
  refine ⟨gateTime .le s.mem second items,?_,?_⟩
  · simp [gateTime,zl,x,y];omega
  · simpa [afterGate,zl,a,x,y] using e

end OneDimSeparator

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
def xWord (r : Bool) (s : Cells) := if r then s.remainder else s.divisor
def zWord (r : Bool) (s : Cells) := if r then s.product else s.itemCount
def putX (r : Bool) (w : List Bool) (s : Cells) : Cells := if r then {s with remainder:=w} else {s with divisor:=w}
def putZ (r : Bool) (w : List Bool) (s : Cells) : Cells := if r then {s with product:=w} else {s with itemCount:=w}
def mulExit (_ : Bool) := G 4
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
end OneDimSeparator

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
open ExponomialAssortment.FPTAS (encodeNat)

theorem pushRun (w : List Bool) (a : Action (Bank R) L) (s : Cells) :
    (pushWord w a).run s.mem=a.run ({s with input:=w++s.input}:Cells).mem := by
  induction w generalizing a with
  | nil => rfl
  | cons b bs ih => rw [pushWord,ih];simp [Action.run]

private theorem flipBits (w : List Bool) (s : Cells) : Goes (E 1) {s with product:=w} (w.length+1) (E 2)
    {s with product:=[],reversed:=w.reverse++s.reversed,scratch:=List.replicate w.length true++s.scratch} := by
  induction w generalizing s with
  | nil =>
    have p := MacroPath.bits (P:=code) (l:=E 1) (m:=({s with product:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,E,Action.run,jump] using p
  | cons b bs ih =>
    have p := MacroPath.bits (P:=code) (l:=E 1) (m:=({s with product:=b::bs}:Cells).mem) (a:=_) (by rfl)
    let t := {s with reversed:=b::s.reversed,scratch:=true::s.scratch}
    have one : Goes (E 1) {s with product:=b::bs} 1 (E 1) {t with product:=bs} := by
      simpa [t,code,E,Action.run,jump] using p
    have same : List.replicate bs.length true ++ true::s.scratch=true::(List.replicate bs.length true++s.scratch) := by
      calc
        _ = (List.replicate bs.length true++[true])++s.scratch := by simp
        _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
    simpa [t,List.replicate_succ,List.append_assoc,same,Nat.add_comm 1] using one.join (ih t)

private theorem outputBits (w : List Bool) (s : Cells) : Goes (E 2) {s with reversed:=w} (w.length+1) (E 3)
    {s with reversed:=[],input:=false::(w.reverse++s.input)} := by
  induction w generalizing s with
  | nil =>
    have p := MacroPath.bits (P:=code) (l:=E 2) (m:=({s with reversed:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,E,Action.run,jump] using p
  | cons b bs ih =>
    have p := MacroPath.bits (P:=code) (l:=E 2) (m:=({s with reversed:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (E 2) {s with reversed:=b::bs} 1 (E 2) {s with reversed:=bs,input:=b::s.input} := by
      simpa [code,E,Action.run,jump] using p
    simpa [List.append_assoc,Nat.add_comm 1] using one.join (ih {s with input:=b::s.input})

private theorem outputLength (k : ℕ) (s : Cells) : Goes (E 3) {s with scratch:=List.replicate k true} (k+1) (old (OneTypeTM.C 0))
    {s with scratch:=[],input:=prefixWord++(List.replicate k true++s.input)} := by
  induction k generalizing s with
  | zero =>
    have p := MacroPath.bits (P:=code) (l:=E 3) (m:=({s with scratch:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,E,Action.run,pushRun,jump] using p
  | succ k ih =>
    have p := MacroPath.bits (P:=code) (l:=E 3) (m:=({s with scratch:=true::List.replicate k true}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (E 3) {s with scratch:=true::List.replicate k true} 1 (E 3)
        {s with scratch:=List.replicate k true,input:=true::s.input} := by simpa [code,E,Action.run,jump] using p
    have same : List.replicate k true ++ true::s.input=true::(List.replicate k true++s.input) := by
      calc
        _ = (List.replicate k true++[true])++s.input := by simp
        _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
    simpa [List.replicate_succ,same,Nat.add_comm 1] using one.join (ih {s with input:=true::s.input})

theorem emitUpper (s : Cells) (q : ℕ) (hi : s.input=[]) (prod : s.product=q.bits) (rev : s.reversed=[]) (wid : s.scratch=[]) :
    Goes (E 0) s (1+(q.bits.length+1)+(q.bits.length+1)+(q.bits.length+1)) (old (OneTypeTM.C 0))
      {s with input:=upperWord q,product:=[],reversed:=[],scratch:=[]} := by
  have a := MacroPath.bits (P:=code) (l:=E 0) (m:=s.mem) (a:=_) (by rfl)
  have p0 : Goes (E 0) s 1 (E 1) {s with input:=encodeNat 1} := by
    simpa [code,E,pushRun,jump,Action.run,hi] using a
  have b := flipBits s.product {s with input:=encodeNat 1}
  have c := outputBits s.product.reverse {s with product:=[],input:=encodeNat 1,scratch:=List.replicate s.product.length true}
  have d := outputLength s.product.length {s with product:=[],reversed:=[],input:=false::(s.product++encodeNat 1)}
  simp [rev,wid] at p0 b c d
  have p := ((p0.join b).join c).join d
  cases s;dsimp only at rev wid prod hi;simpa [hi,prod,rev,wid,upperWord,encodeNat,List.append_assoc] using p

def fixedEntry (lower : Bool) := if lower then G 6 else G 7
def fixedResult (lower : Bool) := if lower then lowWord else [true]
theorem fixed (lower : Bool) (xs : List Bool) (s : Cells) :
    Goes (fixedEntry lower) {s with input:=xs} (xs.length+1) (old (OneTypeTM.C 0))
      {s with input:=fixedResult lower} := by
  cases lower with
  | false =>
    induction xs with
    | nil =>
      have p := MacroPath.bits (P:=code) (l:=fixedEntry false) (m:=({s with input:=[]}:Cells).mem) (a:=_) (by rfl)
      simpa [code,G,fixedEntry,fixedResult,pushRun,Action.run,jump] using p
    | cons b bs ih =>
      have p := MacroPath.bits (P:=code) (l:=fixedEntry false) (m:=({s with input:=b::bs}:Cells).mem) (a:=_) (by rfl)
      have one : Goes (fixedEntry false) {s with input:=b::bs} 1 (fixedEntry false) {s with input:=bs} := by
        simpa [code,G,fixedEntry,Action.run,jump] using p
      simpa [Nat.add_comm 1] using one.join ih
  
  | true =>
    induction xs with
    | nil =>
      have p := MacroPath.bits (P:=code) (l:=fixedEntry true) (m:=({s with input:=[]}:Cells).mem) (a:=_) (by rfl)
      simpa [code,G,fixedEntry,fixedResult,pushRun,Action.run,jump] using p
    | cons b bs ih =>
      have p := MacroPath.bits (P:=code) (l:=fixedEntry true) (m:=({s with input:=b::bs}:Cells).mem) (a:=_) (by rfl)
      have one : Goes (fixedEntry true) {s with input:=b::bs} 1 (fixedEntry true) {s with input:=bs} := by
        simpa [code,G,fixedEntry,Action.run,jump] using p
      simpa [Nat.add_comm 1] using one.join ih
  

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
end OneDimSeparator

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)

theorem bitsValue (n : ℕ) : val n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit _ _ h,val,ih,Nat.bit_val];omega

theorem sendFixed (v : Bool) (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) :
    Runs (fixedEntry v) s (s.input.length+1+OneTypeTM.costClear s) none ({input:=fixedResult v}:Cells) := by
  let z := {s with input:=fixedResult v}
  exact (smallRun (fixed v s.input s)).seq (clean z f sp)

private theorem sendUpper (s : Cells) (q : ℕ) (hi : s.input=[]) (pq : s.product=q.bits)
    (hr : s.reversed=[]) (hw : s.scratch=[]) (hf : s.flag=[]) (sp : s.spare=[]) :
    Runs (E 0) s (3*q.bits.length+4+OneTypeTM.costClear s) none ({input:=upperWord q}:Cells) := by
  let z := {s with input:=upperWord q,product:=[],reversed:=[],scratch:=[]}
  have p := (smallRun (emitUpper s q hi pq hr hw)).seq (clean z hf sp)
  apply p.mono
  simp [z,OneTypeTM.costClear];omega

def ratTail (n d : ℕ) := encodeNat n++encodeNat d
def divState (q n d : ℕ) (s r : List Bool) : Cells :=
  {input:=ratTail n d,product:=q.bits,divisor:=s,binCount:=r}
theorem positiveTail (q n d : ℕ) (s r : List Bool) (K : ℕ)
    (hq : q.bits.length≤K) (hn : n.bits.length≤K) (hd : d.bits.length≤K)
    (hs : s.length≤K) (hr : r.length≤K) :
    Runs (G 0) (divState q n d s r) (200*(K+1)^2) none
      ({input:=if n≤q*d then [true] else upperWord q}:Cells) := by
  let u := divState q n d s r
  let c := {u with divisor:=[]}
  let v := {c with binCount:=[]}
  let x := {v with input:=encodeNat d,todo:=n.bits}
  let y := {x with input:=[],divisor:=d.bits}
  let b := {y with binCount:=q.bits}
  have p0 := smallRun (clearDiv u s)
  have p1 := smallRun (clearRem c r)
  have pr : Runs (G 0) u (s.length+1+(r.length+1)) (H 6) v := p0.seq p1
  have f6 : Goes (H 6) v (3*(n.bits.length+1)) (H 7) x := by
    simpa [v,x,c,u,divState,ratTail,putInput,putWord,next] using field 6 n (encodeNat d) v rfl rfl
  have f7 : Goes (H 7) x (3*(d.bits.length+1)) (G 2) y := by
    simpa [y,x,c,u,v,divState,putInput,putWord,next] using field 7 d [] x rfl rfl
  have cp : Goes (G 2) y (2*(q.bits.length+1)) (M false 0) b := duplicate y rfl rfl
  obtain ⟨w,mul,value,lim⟩ := multiplyAcc false d.bits b q.bits.length (2*K) rfl rfl rfl (by simp [b,y,x,v,c,u,divState,zWord]) le_rfl (by omega)
  let t := mulOut false d.bits.length w b
  have vw : val w=q*d := by simpa [b,y,x,c,v,u,divState,zWord,val,bitsValue,Nat.mul_comm] using value
  have comp := finalCmp t rfl rfl
  have eq : decide (val t.todo≤val t.itemCount)=decide (n≤q*d) := by
    change decide (val n.bits≤val w)=_;rw [vw,bitsValue]
  rw [eq] at comp
  let z := {t with flag:=[decide (n≤q*d)]}
  have entry := MacroPath.bits (P:=code) (l:=G 5) (m:=z.mem) (a:=_) (by rfl)
  have path := (((((pr.seq (smallRun f6)).seq (smallRun f7)).seq (smallRun cp)).seq mul).seq comp)
  have zc : OneTypeTM.costClear t≤8*K+11 := by
    simp [t,b,y,x,c,v,u,divState,OneTypeTM.costClear,mulOut,putZ,putX];omega
  have wc : 3*(max t.todo.length t.itemCount.length+2)≤6*K+6 := by
    change 3*(max n.bits.length w.length+2)≤_;omega
  have mc : d.bits.length*(4*(2*K+4))≤K*(4*(2*K+4)) := Nat.mul_le_mul_right _ hd
  by_cases h : n≤q*d
  · have branch : Goes (G 5) z 1 (G 7) t := by
      simpa [code,G,z,Action.run,jump,h,t,mulOut,putZ,putX] using entry
    have total := (path.seq (smallRun branch)).seq (sendFixed false t rfl rfl)
    simp only [if_pos h]
    apply total.mono
    have inp : t.input.length=0 := rfl
    rw [inp];nlinarith only [hq,hn,hd,hs,hr,wc,mc,zc]
  · have branch : Goes (G 5) z 1 (E 0) t := by
      simpa [code,G,z,Action.run,jump,h,t,mulOut,putZ,putX] using entry
    have total := (path.seq (smallRun branch)).seq (sendUpper t q rfl rfl rfl rfl rfl rfl)
    simp only [if_neg h]
    apply total.mono
    nlinarith only [hq,hn,hd,hs,hr,wc,mc,zc]
end OneDimSeparator

namespace OneDimSeparator
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)
def tape (B s a b : ℕ) (sign : Bool) (tail : List Bool) :=
  encodeNat B++(encodeNat 1++(encodeNat s++(encodeNat a++(encodeNat b++(encodeNat 0++(sign::tail))))))
def headCost (B s a b : ℕ) := 3*(B.bits.length+1)+6+3*(s.bits.length+1)+3*(a.bits.length+1)+3*(b.bits.length+1)+3
def initial (B s : ℕ) (sign : Bool) (tail : List Bool) : Cells := {input:=sign::tail,remainder:=B.bits,divisor:=s.bits}
theorem parse (B s a b : ℕ) (sg : Bool) (tail : List Bool) :
    Goes (H 0) ({input:=tape B s a b sg tail}:Cells) (headCost B s a b) (A 0) (initial B s sg tail) := by
  let t5 := sg::tail
  let t4 := encodeNat 0++t5
  let t3 := encodeNat b++t4
  let t2 := encodeNat a++t3
  let t1 := encodeNat s++t2
  let t0 := encodeNat 1++t1
  let m0 : Cells := {}
  let m1 := putWord 0 B.bits (putInput 0 t0 m0)
  let m2 := putWord 1 (1:ℕ).bits (putInput 1 t1 m1)
  let m3 := putWord 2 s.bits (putInput 2 t2 m2)
  let m4 := putWord 3 a.bits (putInput 3 t3 m3)
  let m5 := putWord 4 b.bits (putInput 4 t4 m4)
  have p0 := field 0 B t0 m0 rfl rfl
  have p1 := field 1 1 t1 m1 rfl rfl
  have p2 := field 2 s t2 m2 rfl rfl
  have p3 := field 3 a t3 m3 rfl rfl
  have p4 := field 4 b t4 m4 rfl rfl
  have p5 := field 5 0 t5 m5 rfl rfl
  have p := ((((p0.join p1).join p2).join p3).join p4).join p5
  simpa [tape,initial,headCost,t0,t1,t2,t3,t4,t5,m0,m1,m2,m3,m4,m5,next,putWord,putInput] using p

private theorem revA (xs : List Bool) (s : Cells) : Goes (A 1) {s with remainder:=xs} (xs.length+1) (A 2)
    {s with remainder:=[],prep:=xs.reverse++s.prep} := by
  induction xs generalizing s with
  | nil =>
    have p := MacroPath.bits (P:=code) (l:=A 1) (m:=({s with remainder:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using p
  | cons b bs ih =>
    have p := MacroPath.bits (P:=code) (l:=A 1) (m:=({s with remainder:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (A 1) {s with remainder:=b::bs} 1 (A 1) {s with remainder:=bs,prep:=b::s.prep} := by
      simpa [A,code,Action.run,jump] using p
    simpa [List.append_assoc,Nat.add_comm 1] using one.join (ih {s with prep:=b::s.prep})

private theorem isolatedWord (x : List Bool) : ({input:=x}:Cells).mem=isolated (reg R.tape) x := by
  funext j; cases j with
  | inl q => cases q <;>rfl
  | inr q => cases q <;>rfl

theorem separate (B s a b n d : ℕ) (sg : Bool) (pos : 0<s) :
    OutputsWithin machine (tape B s a b sg (ratTail n d))
      (if sg then lowWord else if n≤B/s*d then [true] else upperWord (B/s))
      (1000*((tape B s a b sg (ratTail n d)).length+1)^2) := by
  let tail := ratTail n d
  let K := (tape B s a b sg tail).length
  let m := initial B s sg tail
  let m' := {m with input:=tail}
  have len : 2*(B.bits.length+s.bits.length+a.bits.length+b.bits.length)+tail.length+9=K := by
    simp [K,tape,encodeNat];omega
  have td : 2*(n.bits.length+d.bits.length)+2=tail.length := by simp [tail,ratTail,encodeNat];omega
  have pc : headCost B s a b≤3*(K+1) := by dsimp [headCost];omega
  have start := smallRun (parse B s a b sg tail)
  have entry := MacroPath.bits (P:=code) (l:=A 0) (m:=m.mem) (a:=_) (by rfl)
  cases sg with
  | true =>
    have neg : Goes (A 0) m 1 (G 6) m' := by simpa [m',m,initial,code,A,Action.run,jump] using entry
    have fin := sendFixed true m' rfl rfl
    obtain ⟨t,tm,proof⟩ := (start.seq (smallRun neg)).seq fin
    apply MacroPath.outputs (t:=t)
    · rw [←isolatedWord,←isolatedWord];exact proof
    · change t≤1000*(K+1)^2
      simp [m',m,initial,OneTypeTM.costClear] at tm
      nlinarith only [tm,len,pc]
  | false =>
    have plus : Goes (A 0) m 1 (A 1) m' := by simpa [m',m,initial,code,A,Action.run,jump] using entry
    let u := {m' with remainder:=[],prep:=B.bits.reverse}
    have rev : Goes (A 1) m' (B.bits.length+1) (A 2) u := by simpa [m',m,u,initial] using revA B.bits m'
    obtain ⟨r,q,loop,e,rlt,rl,ql⟩ := rounds B.bits.reverse u 0 0 s s.bits.length K rfl rfl rfl rfl
      (by simp [u,m',m,initial,bitsValue]) (by simp [u,m',m,initial,val]) (by simpa [u,m',m,initial,val] using pos)
      (by simp [u,m',m,initial]) le_rfl (by simp;omega)
    rw [readLE,bitsValue] at e
    have ans := congrArg (fun v : ℕ => v/s) e
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt rlt,Nat.zero_add] at ans
    simp at ql
    have fin := positiveTail q n d s.bits r K (by omega) (by omega) (by omega) (by omega) rl
    obtain ⟨t,tm,proof⟩ := ((((start.seq (smallRun plus)).seq (smallRun rev)).seq loop).seq fin)
    apply MacroPath.outputs (t:=t)
    · rw [←isolatedWord,←isolatedWord,←ans];exact proof
    · have lim : B.bits.reverse.length*(9*(K+5))≤K*(9*(K+5)) := Nat.mul_le_mul_right _ (by simp;omega)
      change t≤1000*(K+1)^2
      nlinarith only [len,pc,tm,lim]
end OneDimSeparator

open HMBinPacking ExponomialAssortment.FPTAS
namespace OneDimSeparator
private theorem between {C : Set (Fin 1 → ℝ)} (conv : Convex ℝ C) (Q : ℕ)
    (left : (fun _ => 0) ∈ C) (right : (fun _ => (Q:ℝ)) ∈ C) (x : Fin 1 → ℝ)
    (lo : 0≤x 0) (hi : x 0≤(Q:ℝ)) : x∈C := by
  by_cases pos : 0<(Q:ℝ)
  · let t := x 0/(Q:ℝ)
    have hl : 0≤t := div_nonneg lo pos.le
    have hh : t≤1 := (div_le_one pos).mpr hi
    have y := conv left right (show 0≤1-t by linarith) hl (show 1-t+t=1 by ring)
    have e : (1-t) • (fun _ : Fin 1 => (0:ℝ)) + t • (fun _ : Fin 1 => (Q:ℝ)) = x := by
      funext i;have e0 : i=0 := Subsingleton.elim _ _;subst i
      simp [Pi.add_apply,Pi.smul_apply,t,ne_of_gt pos]
    rwa [e] at y
  · have eq : x=fun _ => 0 := by
      funext i;have e : i=0 := Subsingleton.elim _ _;subst i;linarith
    rwa [eq]

theorem interval (B : ℕ) (s a : Fin 1 → ℕ) (b : ℕ) (Bp : 0<B) (sp : ∀ i,0<s i)
    (r : Fin 1 → Fin 1) (x : Fin 1 → ℝ) :
    let I : Instance := ⟨B,1,s,a,b,Bp,by decide,sp⟩
    x∈Pr I r ↔ 0≤x 0 ∧ x 0 ≤ ((B/s 0 : ℕ):ℝ) := by
  let I : Instance := ⟨B,1,s,a,b,Bp,by decide,sp⟩
  let Q := B/s 0
  have rr (i : Fin 1) : r i=0 := Subsingleton.elim _ _
  have g := lenstra_residue_optimization I r (by simp [I,rr])
  obtain ⟨_,_,mem,maxi⟩ := g
  have hzero : (fun _ : Fin 1 => (0:ℝ))∈Pr I r := by
    have z := mem (fun _ => 0) (by simp [I,rr]);simpa [I,rr] using z
  have hQ : (fun _ : Fin 1 => (Q:ℝ))∈Pr I r := by
    have z := mem (fun _ => Q) (by simpa [I,rr,Q,Nat.mul_comm] using Nat.div_mul_le_self B (s 0))
    simpa [I,rr] using z
  change x∈Pr I r ↔ _
  constructor
  · intro hx
    have bound (u : ℚ) : ∃ t : ℕ, t≤Q ∧ (u:ℝ)*x 0 ≤ (u:ℝ)*(t:ℝ) := by
      obtain ⟨y,cap,_,ma,_⟩ := maxi (fun _ => u)
      have cs : s 0*y 0 ≤ B := by simpa [I,rr] using cap
      have best := ma.2 ⟨x,hx,rfl⟩
      refine ⟨y 0,(Nat.le_div_iff_mul_le (sp 0)).mpr (by simpa [Nat.mul_comm] using cs),?_⟩
      simpa [I,rr] using best
    obtain ⟨a,_,lower⟩ := bound (-1)
    obtain ⟨v,upper,le⟩ := bound 1
    have lim : (v:ℝ) ≤ (Q:ℝ) := by exact_mod_cast upper
    norm_num at lower le
    constructor
    · exact (Nat.cast_nonneg (α:=ℝ) a).trans lower
    · exact le.trans lim
  · rintro ⟨l,h⟩
    exact between (convex_convexHull _ _) Q hzero hQ x l h

private theorem ratLE (z : ℚ) (Q : ℕ) (nn : 0≤z.num) :
    z.num.natAbs≤Q*z.den ↔ z≤(Q:ℚ) := by
  have den : 0<(z.den:ℚ) := by exact_mod_cast z.den_pos
  have numerator : (z.num.natAbs:ℚ)=(z.num:ℚ) := by
    have e : (z.num.natAbs : ℤ)=z.num := Int.natAbs_of_nonneg nn
    simpa only [Int.cast_natCast] using congrArg (fun i : ℤ => (i:ℚ)) e
  calc
    _ ↔ (z.num.natAbs:ℚ)≤(Q:ℚ)*(z.den:ℚ) := by exact_mod_cast Iff.rfl
    _ ↔ (z.num:ℚ)/(z.den:ℚ) ≤ (Q:ℚ) := by rw [numerator,div_le_iff₀ den]
    _ ↔ _ := by rw [Rat.num_div_den]

def answer (Q : ℕ) (z : ℚ) := if z.num<0 then lowWord else if z.num.natAbs≤Q*z.den then [true] else upperWord Q

theorem certificate (B : ℕ) (s a : Fin 1 → ℕ) (b : ℕ) (Bp : 0<B) (sp : ∀ i,0<s i)
    (r : Fin 1 → Fin 1) (y : Fin 1 → ℚ) :
    let I : Instance := ⟨B,1,s,a,b,Bp,by decide,sp⟩
    IsSepAnswer (Pr I r) y (answer (B/s 0) (y 0)) := by
  let I : Instance := ⟨B,1,s,a,b,Bp,by decide,sp⟩
  let Q := B/s 0
  have intervalX := interval B s a b Bp sp r
  let z := y 0
  by_cases h : z.num<0
  · have neg : z<0 := lt_of_not_ge (fun h0 => h.not_ge (Rat.num_nonneg.mpr h0))
    have negR : (z:ℝ)<0 := by exact_mod_cast neg
    right
    refine ⟨fun _ => -1,0,?_,?_,?_⟩
    · simp [answer,z] at h ⊢
      simp [h,lowWord,encVec,List.ofFn_succ]
    · intro x hx; have l := ((intervalX x).mp hx).1
      simpa [I] using l
    · simpa [I,z] using negR
  · have nn := le_of_not_gt h
    have lo : 0≤(z:ℝ) := by exact_mod_cast (Rat.num_nonneg.mp nn)
    by_cases hi : z.num.natAbs≤Q*z.den
    · have upper : (z:ℝ)≤(Q:ℝ) := by exact_mod_cast (ratLE z Q nn).mp hi
      left
      exact ⟨by simpa [answer,←show y 0=z by rfl,←show B/s 0=Q by rfl] using
        (show answer Q z=[true] by simp [answer,h,hi]), (intervalX (qCast y)).mpr ⟨lo,upper⟩⟩
    · have greater : (Q:ℚ)<z := lt_of_not_ge (fun e => hi ((ratLE z Q nn).mpr e))
      have gr : (Q:ℝ)<(z:ℝ) := by exact_mod_cast greater
      right
      refine ⟨fun _ => 1,(Q:ℚ),?_,?_,?_⟩
      · change answer Q z=_
        simp [answer,h,hi,upperWord,prefixWord,encVec,encodeRat,encodeInt,List.ofFn_succ,List.append_assoc]
        exact decide_eq_false (not_lt_of_ge (Int.natCast_nonneg Q))
      · intro x hx;have hx' := ((intervalX x).mp hx).2;simpa [I,Q] using hx'
      · simpa [I,Q,z] using gr
end OneDimSeparator

namespace OneDimSeparator
open HMBinPacking ExponomialAssortment.FPTAS

private theorem outLength (Q : ℕ) (z : ℚ) : (answer Q z).length≤13+2*Q.bits.length := by
  have lo : lowWord.length=13 := by decide
  have pr : prefixWord.length=9 := by decide
  have one : (encodeNat 1).length=3 := by decide
  by_cases h : z.num<0
  · simp [answer,h,lo]
  · by_cases hi : z.num.natAbs≤Q*z.den
    · simp [answer,h,hi];omega
    · simp [answer,h,hi,upperWord,pr,encodeNat];omega

private theorem adjusted (L : ℕ) (pos : 1≤L) : 1000*(L+1+1)^2≤2^(16*(1:ℕ)^3)*L^16 := by
  have square : (L+1+1)^2≤(3*L)^2 := Nat.pow_le_pow_left (by omega) _
  have pow16 : L^2≤L^16 := Nat.pow_le_pow_right pos (by decide)
  norm_num
  calc
    _ ≤ 1000*(3*L)^2 := Nat.mul_le_mul_left _ square
    _ ≤ 65536*L^2 := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ pow16

theorem practical (B : ℕ) (s a : Fin 1 → ℕ) (b : ℕ) (Bp : 0<B) (sp : ∀ i,0<s i)
    (r : Fin 1 → Fin 1) (y : Fin 1 → ℚ) :
    let I : Instance := ⟨B,1,s,a,b,Bp,by decide,sp⟩
    ∃ w : List Bool,
      OutputsWithin machine (encodeInstance I++encodeResidue r++encVec y) w
        (2^(16*I.d^3)*(inputLength I+(encVec y).length)^16) ∧
      IsSepAnswer (Pr I r) y w ∧ w.length≤(I.d+inputLength I+(encVec y).length)^16 := by
  let I : Instance := ⟨B,1,s,a,b,Bp,by decide,sp⟩
  let z := y 0
  have hr (i : Fin 1) : r i=0 := Subsingleton.elim _ _
  let word := encodeInstance I++encodeResidue r++encVec y
  have et : word=tape B (s 0) (a 0) b (decide (z.num<0)) (ratTail z.num.natAbs z.den) := by
    simp [I,word,tape,ratTail,encodeInstance,encodeNatVec,encodeResidue,encVec,encodeInt,encodeRat,hr,z,List.ofFn_succ,List.append_assoc]
  have core := separate B (s 0) (a 0) b z.num.natAbs z.den (decide (z.num<0)) (sp _)
  rw [←et] at core
  have core' : OutputsWithin machine word (answer (B/s 0) z) (1000*(word.length+1)^2) := by
    by_cases h : z.num<0 <;> simpa [answer,h] using core
  let L := inputLength I+(encVec y).length
  have lens : word.length = L+1 := by
    simp [word,L,inputLength,encodeResidue,encodeNatVec,hr,encodeNat,List.ofFn_succ];omega
  have large : B.bits.length+4≤L := by simp [L,inputLength,I,encodeInstance,encodeNat];omega
  have cost : 1000*(word.length+1)^2≤2^(16*I.d^3)*L^16 := by
    rw [lens,show I.d=1 by rfl];exact adjusted L (by omega)
  obtain ⟨⟨trace,steps⟩⟩ := core'
  refine ⟨answer (B/s 0) z,⟨⟨trace,steps.trans cost⟩⟩,certificate B s a b Bp sp r y,?_⟩
  have divBound : (B/s 0).bits.length≤B.bits.length := by
    simp only [Nat.size_eq_bits_len];exact Nat.size_le_size (Nat.div_le_self _ _)
  have out := outLength (B/s 0) z
  have larger : 13+2*B.bits.length≤(1+L)^2 := by nlinarith only [large]
  have expo : (1+L)^2≤(1+L)^16 := Nat.pow_le_pow_right (by omega) (by decide)
  change _≤(1+inputLength I+(encVec y).length)^16
  rw [Nat.add_assoc];exact (out.trans (by omega : 13+2*(B/s 0).bits.length≤13+2*B.bits.length)).trans (larger.trans expo)
end OneDimSeparator
open HMBinPacking

/-- The registered strong separation oracle, specialized only in dimension. -/
theorem solution :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ),
      ∀ (I : Instance), I.d=1 → ∀ (r : Fin I.d → Fin I.d) (y : Fin I.d → ℚ), ∃ w : List Bool,
        OutputsWithin M (encodeInstance I ++ encodeResidue r ++ encVec y) w
          (2 ^ (c * I.d ^ 3) * (inputLength I + (encVec y).length) ^ c) ∧
        IsSepAnswer (Pr I r) y w ∧
        w.length ≤ (I.d + inputLength I + (encVec y).length) ^ c := by
  refine ⟨OneDimSeparator.machine,16,?_⟩
  intro I dim
  obtain ⟨B,d,s,a,b,Bp,dp,sp⟩ := I
  change d=1 at dim;subst d
  exact OneDimSeparator.practical B s a b Bp sp
