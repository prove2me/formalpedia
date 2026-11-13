-- Prove2me | solution 1 for NadlerCLS.scaleLam_polyTime
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-12T21:01:36.330216+00:00
-- url     : https://prove2.me/submissions/39944eee-d9aa-4fd1-bc7d-590c3e642fce

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_Circ
import Definitions.Def_NadlerCLS_COInstance
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The instance map of Theorem C.3 is polynomial-time computable

The map is computed by a stack program (in the sense of `CookPvsNP.StackProg`) on nine stacks.
It reads the code `enc(f) enc(p) enc(δ) enc(λ)` from the left, copies `enc(f) enc(p) enc(δ)` to
the output, and replaces `enc(λ)` by the code of `λ' = 2^(|w| + n)`, where `|w|` is the length of
the input.  Sections: the frame (stacks, states, Hoare-style rules), the number block, the gate
block, the counter block, lists and circuits, the start-up and final blocks, and the theorem.
-/

namespace ScaleLam

open CookPvsNP

/-- The stacks of the program. -/
inductive Stk
  | inp | outr | cnt | dig | una | rest | t1 | t2 | out
  deriving DecidableEq

instance : Fintype Stk :=
  ⟨{Stk.inp, Stk.outr, Stk.cnt, Stk.dig, Stk.una, Stk.rest, Stk.t1, Stk.t2, Stk.out},
    fun x => by cases x <;> simp⟩

/-- The contents of all stacks. -/
@[ext] structure St where
  inp : List Bool
  outr : List Bool
  cnt : List Bool
  dig : List Bool
  una : List Bool
  rest : List Bool
  t1 : List Bool
  t2 : List Bool
  out : List Bool

/-- The store of a state. -/
def St.store (s : St) : Stk → List Bool
  | .inp => s.inp
  | .outr => s.outr
  | .cnt => s.cnt
  | .dig => s.dig
  | .una => s.una
  | .rest => s.rest
  | .t1 => s.t1
  | .t2 => s.t2
  | .out => s.out

/-- `Impl P Q p f B`: from every state satisfying `P`, the program `p` runs in at most `B` steps
to the state `f s`, which satisfies `Q`. -/
def Impl (P Q : St → Prop) (p : StackProg Stk Bool) (f : St → St) (B : ℕ) : Prop :=
  ∀ s, P s → Q (f s) ∧ ∃ t, t ≤ B ∧ p.Exec s.store (f s).store t

theorem Impl.act {P Q : St → Prop} {a : (Stk → Option Bool) → Stk → StackAct Bool} {f : St → St}
    (h : ∀ s, P s → StackProg.applyAct a s.store = (f s).store ∧ Q (f s)) :
    Impl P Q (.act a) f 1 := by
  intro s hs
  obtain ⟨e, hq⟩ := h s hs
  refine ⟨hq, 1, le_refl _, ?_⟩
  rw [← e]
  exact StackProg.Exec.act a s.store

theorem Impl.seq {P Q R : St → Prop} {p q : StackProg Stk Bool} {f g : St → St} {B C : ℕ}
    (hp : Impl P Q p f B) (hq : Impl Q R q g C) :
    Impl P R (.seq p q) (fun s => g (f s)) (B + 1 + C) := by
  intro s hs
  obtain ⟨h1, t1, ht1, e1⟩ := hp s hs
  obtain ⟨h2, t2, ht2, e2⟩ := hq (f s) h1
  exact ⟨h2, t1 + 1 + t2, by omega, StackProg.Exec.seq e1 e2⟩

theorem Impl.branch {P Q : St → Prop} {p q : StackProg Stk Bool} {f g : St → St} {B C : ℕ}
    {test : (Stk → Option Bool) → Bool} (b : St → Bool)
    (hb : ∀ s, P s → test (fun k => (s.store k).head?) = b s)
    (hp : Impl (fun s => P s ∧ b s = true) Q p f B)
    (hq : Impl (fun s => P s ∧ b s = false) Q q g C) :
    Impl P Q (.branch test p q) (fun s => if b s = true then f s else g s) (1 + max B C) := by
  intro s hs
  cases hbs : b s with
  | true =>
    obtain ⟨h1, t, ht, e⟩ := hp s ⟨hs, hbs⟩
    simp only [hbs, if_true]
    refine ⟨h1, 1 + t, ?_, StackProg.Exec.branchTrue (by rw [hb s hs, hbs]) e⟩
    have := le_max_left B C
    omega
  | false =>
    obtain ⟨h1, t, ht, e⟩ := hq s ⟨hs, hbs⟩
    simp only [hbs, Bool.false_eq_true, if_false]
    refine ⟨h1, 1 + t, ?_, StackProg.Exec.branchFalse (by rw [hb s hs, hbs]) e⟩
    have := le_max_right B C
    omega

theorem Impl.loop {P : St → Prop} {p : StackProg Stk Bool} {f : St → St} {B : ℕ}
    {test : (Stk → Option Bool) → Bool} (rank : St → ℕ) (N : ℕ)
    (ht : ∀ s, P s → test (fun k => (s.store k).head?) = decide (0 < rank s))
    (hd : ∀ s, P s → 0 < rank s → rank (f s) + 1 = rank s)
    (hN : ∀ s, P s → rank s ≤ N)
    (hp : Impl (fun s => P s ∧ 0 < rank s) P p f B) :
    Impl P (fun s => P s ∧ rank s = 0) (.loop test p) (fun s => f^[rank s] s)
      (N * (B + 2) + 1) := by
  have key : ∀ n s, P s → rank s = n →
      (P (f^[n] s) ∧ rank (f^[n] s) = 0) ∧
        ∃ t, t ≤ n * (B + 2) + 1 ∧ (StackProg.loop test p).Exec s.store (f^[n] s).store t := by
    intro n
    induction n with
    | zero =>
      intro s hs hr
      refine ⟨⟨hs, hr⟩, 1, by omega, ?_⟩
      apply StackProg.Exec.loopFalse
      rw [ht s hs, hr]
      simp
    | succ n ih =>
      intro s hs hr
      have hpos : 0 < rank s := by omega
      obtain ⟨hP1, t1, ht1, e1⟩ := hp s ⟨hs, hpos⟩
      have hr1 : rank (f s) = n := by
        have := hd s hs hpos
        omega
      obtain ⟨hq, t2, ht2, e2⟩ := ih (f s) hP1 hr1
      rw [Function.iterate_succ_apply]
      refine ⟨hq, 1 + t1 + 1 + t2, ?_, ?_⟩
      · have : (n + 1) * (B + 2) = n * (B + 2) + (B + 2) := by ring
        omega
      · exact StackProg.Exec.loopTrue (by rw [ht s hs]; simp [hpos]) e1 e2
  intro s hs
  obtain ⟨hq, t, ht', e⟩ := key (rank s) s hs rfl
  refine ⟨hq, t, le_trans ht' ?_, e⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hN s hs)) 1

theorem Impl.conseq {P P' Q Q' : St → Prop} {p : StackProg Stk Bool} {f : St → St} {B B' : ℕ}
    (h : Impl P Q p f B) (hP : ∀ s, P' s → P s) (hQ : ∀ s, P' s → Q (f s) → Q' (f s))
    (hB : B ≤ B') : Impl P' Q' p f B' := by
  intro s hs
  obtain ⟨h1, t, ht, e⟩ := h s (hP s hs)
  exact ⟨hQ s hs h1, t, le_trans ht hB, e⟩

theorem Impl.congr {P Q : St → Prop} {p : StackProg Stk Bool} {f g : St → St} {B : ℕ}
    (h : Impl P Q p f B) (e : ∀ s, P s → f s = g s) : Impl P Q p g B := by
  intro s hs
  have := h s hs
  rw [e s hs] at this
  exact this

/-! ### Polynomially bounded step counts -/

/-- A step bound that is at most a fixed multiple of a fixed power of `L + 1`. -/
def PolyB (b : ℕ → ℕ) : Prop := ∃ A d : ℕ, ∀ L, b L ≤ A * (L + 1) ^ d

theorem PolyB.const (c : ℕ) : PolyB (fun _ => c) := ⟨c, 0, fun L => by simp⟩

theorem PolyB.id : PolyB (fun L => L) := ⟨1, 1, fun L => by simp⟩

theorem PolyB.add {b c : ℕ → ℕ} (hb : PolyB b) (hc : PolyB c) : PolyB (fun L => b L + c L) := by
  obtain ⟨A, d, h1⟩ := hb
  obtain ⟨A', d', h2⟩ := hc
  refine ⟨A + A', max d d', fun L => ?_⟩
  have e1 : (L + 1) ^ d ≤ (L + 1) ^ max d d' := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e2 : (L + 1) ^ d' ≤ (L + 1) ^ max d d' := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc b L + c L ≤ A * (L + 1) ^ d + A' * (L + 1) ^ d' := Nat.add_le_add (h1 L) (h2 L)
    _ ≤ A * (L + 1) ^ max d d' + A' * (L + 1) ^ max d d' :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (A + A') * (L + 1) ^ max d d' := by ring

theorem PolyB.mul {b c : ℕ → ℕ} (hb : PolyB b) (hc : PolyB c) : PolyB (fun L => b L * c L) := by
  obtain ⟨A, d, h1⟩ := hb
  obtain ⟨A', d', h2⟩ := hc
  refine ⟨A * A', d + d', fun L => ?_⟩
  calc b L * c L ≤ (A * (L + 1) ^ d) * (A' * (L + 1) ^ d') := Nat.mul_le_mul (h1 L) (h2 L)
    _ = A * A' * (L + 1) ^ (d + d') := by ring

theorem PolyB.mono {b c : ℕ → ℕ} (hc : PolyB c) (h : ∀ L, b L ≤ c L) : PolyB b := by
  obtain ⟨A, d, h1⟩ := hc
  exact ⟨A, d, fun L => le_trans (h L) (h1 L)⟩

end ScaleLam

namespace ScaleLam

open CookPvsNP

/-- The invariant of the parsing phase; it is used only to bound running times. -/
def Inv (L : ℕ) (s : St) : Prop :=
  s.inp.length + s.outr.length ≤ L ∧ s.cnt.length ≤ s.outr.length ∧
    s.dig.length ≤ s.outr.length ∧
    s.una.length + s.rest.length + s.t1.length + s.t2.length ≤ L

theorem iter_una {f : St → St} (h : ∀ s, (f s).una = s.una) (n : ℕ) (s : St) :
    (f^[n] s).una = s.una := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, h]

/-- The number of leading `true`s. -/
def lead : List Bool → ℕ
  | true :: l => lead l + 1
  | _ => 0

theorem lead_le_length (l : List Bool) : lead l ≤ l.length := by
  induction l with
  | nil => simp [lead]
  | cons b l ih => cases b <;> simp [lead]; omega

theorem lead_replicate_append (a : ℕ) (x : List Bool) (hx : x.head? ≠ some true) :
    lead (List.replicate a true ++ x) = a := by
  induction a with
  | zero =>
    cases x with
    | nil => rfl
    | cons b x =>
      cases b with
      | false => rfl
      | true => simp at hx
  | succ a ih => simp [List.replicate_succ, lead, ih]

/-! ### The unary prefix -/

def onesAct (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .inp => .pop
  | .outr => .push true
  | .cnt => .push true
  | _ => .keep

def topTrue (h : Stk → Option Bool) : Bool := h .inp == some true

def onesStep (s : St) : St :=
  { s with inp := s.inp.tail, outr := true :: s.outr, cnt := true :: s.cnt }

def onesLoop : StackProg Stk Bool := .loop topTrue (.act onesAct)

def onesSem (s : St) : St := onesStep^[lead s.inp] s

theorem topTrue_eq (s : St) : topTrue (fun k => (s.store k).head?) = decide (0 < lead s.inp) := by
  simp only [topTrue, St.store]
  cases h : s.inp with
  | nil => simp [lead]
  | cons b l => cases b <;> simp [lead]

theorem onesAct_impl (L : ℕ) :
    Impl (fun s => Inv L s ∧ 0 < lead s.inp) (Inv L) (.act onesAct) onesStep 1 := by
  apply Impl.act
  rintro s ⟨⟨h1, h2, h3, h4⟩, hpos⟩
  constructor
  · funext k
    cases k <;> rfl
  · cases h : s.inp with
    | nil => simp [h, lead] at hpos
    | cons b l =>
      simp only [h, List.length_cons] at h1
      refine ⟨?_, ?_, ?_, h4⟩ <;> simp [onesStep, h] <;> omega

theorem onesLoop_impl (L : ℕ) :
    Impl (Inv L) (Inv L) onesLoop onesSem (L * (1 + 2) + 1) := by
  have h := Impl.loop (P := Inv L) (fun s => lead s.inp) L (fun s _ => topTrue_eq s)
    (fun s _ hpos => by
      cases h : s.inp with
      | nil => simp [h, lead] at hpos
      | cons b l =>
        cases b with
        | false => simp [h, lead] at hpos
        | true => simp [onesStep, h, lead])
    (fun s hs => le_trans (lead_le_length _) (by have := hs.1; omega))
    (onesAct_impl L)
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem onesSem_spec (a : ℕ) (s : St) (x : List Bool) (hinp : s.inp = List.replicate a true ++ x)
    (hx : x.head? ≠ some true) :
    onesSem s = { s with inp := x, outr := List.replicate a true ++ s.outr,
                         cnt := List.replicate a true ++ s.cnt } := by
  unfold onesSem
  rw [hinp, lead_replicate_append a x hx]
  induction a generalizing s with
  | zero =>
    cases s
    simp_all
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    have h1 : (onesStep s).inp = List.replicate a true ++ x := by
      simp [onesStep, hinp, List.replicate_succ]
    rw [ih (onesStep s) h1]
    simp [onesStep, List.replicate_succ']

theorem onesSem_una (s : St) : (onesSem s).una = s.una :=
  iter_una (f := onesStep) (fun s => rfl) _ s

/-! ### Moving one symbol -/

def sepAct (h : Stk → Option Bool) : Stk → StackAct Bool
  | .inp => .pop
  | .outr => match h .inp with
    | some b => .push b
    | none => .keep
  | _ => .keep

def sepStep (s : St) : St :=
  { s with inp := s.inp.tail,
           outr := match s.inp.head? with
             | some b => b :: s.outr
             | none => s.outr }

theorem sepAct_impl (L : ℕ) : Impl (Inv L) (Inv L) (.act sepAct) sepStep 1 := by
  apply Impl.act
  rintro s ⟨h1, h2, h3, h4⟩
  constructor
  · funext k
    cases k <;> simp only [StackProg.applyAct, sepAct, sepStep, St.store] <;>
      first | rfl | (cases s.inp.head? <;> rfl)
  · cases h : s.inp with
    | nil =>
      simp only [h, List.length_nil] at h1
      refine ⟨?_, ?_, ?_, h4⟩ <;> simp [sepStep, h] <;> omega
    | cons b l =>
      simp only [h, List.length_cons] at h1
      refine ⟨?_, ?_, ?_, h4⟩ <;> simp [sepStep, h] <;> omega

theorem sepStep_cons (s : St) (b : Bool) (x : List Bool) (h : s.inp = b :: x) :
    sepStep s = { s with inp := x, outr := b :: s.outr } := by
  simp [sepStep, h]

/-! ### The digits -/

def digAct (h : Stk → Option Bool) : Stk → StackAct Bool
  | .cnt => .pop
  | .inp => .pop
  | .outr => match h .inp with
    | some b => .push b
    | none => .keep
  | .dig => match h .inp with
    | some b => .push b
    | none => .keep
  | _ => .keep

def digTest (h : Stk → Option Bool) : Bool := (h .cnt).isSome && (h .inp).isSome

def digStep (s : St) : St :=
  { s with cnt := s.cnt.tail, inp := s.inp.tail,
           outr := match s.inp.head? with
             | some b => b :: s.outr
             | none => s.outr
           dig := match s.inp.head? with
             | some b => b :: s.dig
             | none => s.dig }

def digRank (s : St) : ℕ := min s.cnt.length s.inp.length

def digLoop : StackProg Stk Bool := .loop digTest (.act digAct)

def digSem (s : St) : St := digStep^[digRank s] s

theorem digTest_eq (s : St) : digTest (fun k => (s.store k).head?) = decide (0 < digRank s) := by
  obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
  simp only [digTest, St.store, digRank]
  cases cnt <;> cases inp <;> simp

theorem digAct_impl (L : ℕ) :
    Impl (fun s => Inv L s ∧ 0 < digRank s) (Inv L) (.act digAct) digStep 1 := by
  apply Impl.act
  rintro s ⟨⟨h1, h2, h3, h4⟩, hpos⟩
  constructor
  · funext k
    cases k <;> simp only [StackProg.applyAct, digAct, digStep, St.store] <;>
      first | rfl | (cases s.inp.head? <;> rfl)
  · cases h : s.inp with
    | nil => simp [digRank, h] at hpos
    | cons b l =>
      cases hc : s.cnt with
      | nil => simp [digRank, hc] at hpos
      | cons c cs =>
        simp only [h, hc, List.length_cons] at h1 h2
        refine ⟨?_, ?_, ?_, h4⟩ <;> simp [digStep, h, hc] <;> omega

theorem digLoop_impl (L : ℕ) : Impl (Inv L) (Inv L) digLoop digSem (L * (1 + 2) + 1) := by
  have h := Impl.loop (P := Inv L) digRank L (fun s _ => digTest_eq s)
    (fun s _ hpos => by
      cases h : s.inp with
      | nil => simp [digRank, h] at hpos
      | cons b l =>
        cases hc : s.cnt with
        | nil => simp [digRank, hc] at hpos
        | cons c cs => simp [digStep, digRank, h, hc])
    (fun s hs => by
      have := hs.1
      simp only [digRank]
      omega)
    (digAct_impl L)
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem digSem_spec (bs : List Bool) (s : St) (x : List Bool) (hinp : s.inp = bs ++ x)
    (hc : s.cnt.length = bs.length) :
    digSem s = { s with cnt := [], inp := x, outr := bs.reverse ++ s.outr,
                        dig := bs.reverse ++ s.dig } := by
  have key : ∀ (bs : List Bool) (s : St), s.inp = bs ++ x → s.cnt.length = bs.length →
      digStep^[bs.length] s = { s with cnt := [], inp := x, outr := bs.reverse ++ s.outr,
                                       dig := bs.reverse ++ s.dig } := by
    intro bs
    induction bs with
    | nil =>
      intro s hinp hc
      have : s.cnt = [] := List.length_eq_zero_iff.mp (by simpa using hc)
      cases s
      simp_all
    | cons b bs ih =>
      intro s hinp hc
      rw [List.length_cons, Function.iterate_succ_apply]
      have h1 : (digStep s).inp = bs ++ x := by simp [digStep, hinp]
      have h2 : (digStep s).cnt.length = bs.length := by
        simp [digStep, hc]
      rw [ih (digStep s) h1 h2]
      simp [digStep, hinp]
  unfold digSem
  have hr : digRank s = bs.length := by
    simp [digRank, hc, hinp]
  rw [hr]
  exact key bs s hinp hc

theorem digSem_una (s : St) : (digSem s).una = s.una :=
  iter_una (f := digStep) (fun s => rfl) _ s

/-! ### Clearing the counter -/

def clearCntAct (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .cnt => .pop
  | _ => .keep

def cntTest (h : Stk → Option Bool) : Bool := (h .cnt).isSome

def clearCntStep (s : St) : St := { s with cnt := s.cnt.tail }

def clearCnt : StackProg Stk Bool := .loop cntTest (.act clearCntAct)

def clearCntSem (s : St) : St := clearCntStep^[s.cnt.length] s

theorem clearCnt_impl (L : ℕ) : Impl (Inv L) (Inv L) clearCnt clearCntSem (L * (1 + 2) + 1) := by
  have hact : Impl (fun s => Inv L s ∧ 0 < s.cnt.length) (Inv L) (.act clearCntAct)
      clearCntStep 1 := by
    apply Impl.act
    rintro s ⟨⟨h1, h2, h3, h4⟩, hpos⟩
    constructor
    · funext k
      cases k <;> rfl
    · refine ⟨h1, ?_, h3, h4⟩
      simp [clearCntStep]
      omega
  have h := Impl.loop (P := Inv L) (test := cntTest) (fun s => s.cnt.length) L
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      simp only [cntTest, St.store]
      cases cnt <;> simp)
    (fun s _ hpos => by
      simp [clearCntStep]
      omega)
    (fun s hs => by
      have := hs.1
      have := hs.2.1
      omega)
    hact
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem clearCntSem_spec (s : St) : clearCntSem s = { s with cnt := [] } := by
  unfold clearCntSem
  generalize hn : s.cnt.length = n
  induction n generalizing s with
  | zero =>
    have : s.cnt = [] := List.length_eq_zero_iff.mp hn
    cases s
    simp_all
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (clearCntStep s) (by simp [clearCntStep, hn])]
    simp [clearCntStep]

/-! ### The block `skipNat` -/

def skipNat : StackProg Stk Bool := .seq onesLoop (.seq (.act sepAct) (.seq digLoop clearCnt))

def skipNatSem (s : St) : St := clearCntSem (digSem (sepStep (onesSem s)))

/-- Step bound of `skipNat`. -/
def bSkip (L : ℕ) : ℕ := (L * (1 + 2) + 1) + 1 + (1 + 1 + ((L * (1 + 2) + 1) + 1 + (L * (1 + 2) + 1)))

theorem skipNat_impl (L : ℕ) : Impl (Inv L) (Inv L) skipNat skipNatSem (bSkip L) :=
  (onesLoop_impl L).seq ((sepAct_impl L).seq ((digLoop_impl L).seq (clearCnt_impl L)))

theorem skipNatSem_una (s : St) : (skipNatSem s).una = s.una := by
  unfold skipNatSem
  rw [clearCntSem_spec]
  show (digSem (sepStep (onesSem s))).una = s.una
  rw [digSem_una]
  show (onesSem s).una = s.una
  exact onesSem_una s

/-- `skipNat` on a block `1^a 0 bs` with `|bs| = a + |cnt|`. -/
theorem skipNatSem_spec (a : ℕ) (bs x : List Bool) (s : St)
    (hinp : s.inp = List.replicate a true ++ false :: (bs ++ x))
    (hlen : bs.length = a + s.cnt.length) :
    skipNatSem s = { s with inp := x, outr := bs.reverse ++ false :: (List.replicate a true ++ s.outr),
                            cnt := [], dig := bs.reverse ++ s.dig } := by
  unfold skipNatSem
  rw [onesSem_spec a s (false :: (bs ++ x)) hinp (by simp)]
  rw [sepStep_cons _ false (bs ++ x) rfl]
  rw [digSem_spec bs _ x rfl (by simp [hlen])]
  rw [clearCntSem_spec]

open NetworkEquilibriumCLS.LinearNash in
/-- `skipNat` on the code of a natural number. -/
theorem skipNatSem_encNat (m : ℕ) (x : List Bool) (s : St) (hinp : s.inp = encNat m ++ x)
    (hc : s.cnt = []) :
    skipNatSem s = { s with inp := x, outr := (encNat m).reverse ++ s.outr,
                            dig := m.bits.reverse ++ s.dig } := by
  have h := skipNatSem_spec m.bits.length m.bits x s (by simpa [encNat] using hinp) (by simp [hc])
  rw [h]
  cases s
  simp_all [encNat]

end ScaleLam

namespace ScaleLam

open CookPvsNP NetworkEquilibriumCLS.LinearNash

theorem Impl.pre {P P' Q : St → Prop} {p : StackProg Stk Bool} {f : St → St} {B : ℕ}
    (h : Impl P Q p f B) (hP : ∀ s, P' s → P s) : Impl P' Q p f B :=
  h.conseq hP (fun _ _ hq => hq) (le_refl _)

/-! ### `skipNat` on explicit states -/

theorem skipNatSem_mk (a : ℕ) (bs x outr cnt dig una rest t1 t2 out : List Bool)
    (hlen : bs.length = a + cnt.length) :
    skipNatSem ⟨List.replicate a true ++ false :: (bs ++ x), outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨x, bs.reverse ++ false :: (List.replicate a true ++ outr), [], bs.reverse ++ dig, una, rest,
        t1, t2, out⟩ :=
  skipNatSem_spec a bs x ⟨_, outr, cnt, dig, una, rest, t1, t2, out⟩ rfl hlen

theorem skipNatSem_encNat_mk (m : ℕ) (x outr dig una rest t1 t2 out : List Bool) :
    skipNatSem ⟨encNat m ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
      ⟨x, (encNat m).reverse ++ outr, [], m.bits.reverse ++ dig, una, rest, t1, t2, out⟩ := by
  have h := skipNatSem_mk m.bits.length m.bits x outr [] dig una rest t1 t2 out (by simp)
  simp only [encNat, List.append_assoc, List.cons_append] at h ⊢
  rw [h]
  simp

/-! ### A rational number -/

def ratP : StackProg Stk Bool := .seq (.act sepAct) (.seq skipNat skipNat)

def ratSem (s : St) : St := skipNatSem (skipNatSem (sepStep s))

def bRat (L : ℕ) : ℕ := 1 + 1 + (bSkip L + 1 + bSkip L)

theorem rat_impl (L : ℕ) : Impl (Inv L) (Inv L) ratP ratSem (bRat L) := by
  have h := (sepAct_impl L).seq ((skipNat_impl L).seq (skipNat_impl L))
  exact h

theorem ratSem_una (s : St) : (ratSem s).una = s.una := by
  unfold ratSem
  rw [skipNatSem_una, skipNatSem_una]
  rfl

theorem sepStep_mk (b : Bool) (x outr cnt dig una rest t1 t2 out : List Bool) :
    sepStep ⟨b :: x, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨x, b :: outr, cnt, dig, una, rest, t1, t2, out⟩ := rfl

theorem ratSem_mk (r : ℚ) (x outr dig una rest t1 t2 out : List Bool) :
    ratSem ⟨encRat r ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
      ⟨x, (encRat r).reverse ++ outr, [], r.den.bits.reverse ++ (r.num.natAbs.bits.reverse ++ dig),
        una, rest, t1, t2, out⟩ := by
  unfold ratSem
  simp only [encRat, encInt, List.append_assoc, List.cons_append]
  rw [sepStep_mk, skipNatSem_encNat_mk, skipNatSem_encNat_mk]
  simp

/-! ### One gate -/

def gateP : StackProg Stk Bool :=
  .branch topTrue
    (.seq (.act onesAct)
      (.branch topTrue (.seq skipNat (.seq skipNat skipNat)) (.seq skipNat ratP)))
    (.seq skipNat skipNat)

def isTop (s : St) : Bool := decide (0 < lead s.inp)

def gateSem (s : St) : St :=
  if isTop s = true then
    (fun s1 => if isTop s1 = true then skipNatSem (skipNatSem (skipNatSem s1))
      else ratSem (skipNatSem s1)) (onesStep s)
  else skipNatSem (skipNatSem s)

def bGate (L : ℕ) : ℕ :=
  1 + max (1 + 1 + (1 + max (bSkip L + 1 + (bSkip L + 1 + bSkip L)) (bSkip L + 1 + bRat L)))
    (bSkip L + 1 + bSkip L)

theorem gate_impl (L : ℕ) : Impl (Inv L) (Inv L) gateP gateSem (bGate L) := by
  have h3 := (skipNat_impl L).seq ((skipNat_impl L).seq (skipNat_impl L))
  have hr := (skipNat_impl L).seq (rat_impl L)
  have h2 := (skipNat_impl L).seq (skipNat_impl L)
  have inner := Impl.branch (P := Inv L) (test := topTrue) isTop (fun s _ => topTrue_eq s)
    (h3.pre (fun s hs => hs.1)) (hr.pre (fun s hs => hs.1))
  have thenB := ((onesAct_impl L).pre (P' := fun s => Inv L s ∧ isTop s = true)
    (fun s hs => ⟨hs.1, of_decide_eq_true hs.2⟩)).seq inner
  have h := Impl.branch (P := Inv L) (test := topTrue) isTop (fun s _ => topTrue_eq s) thenB
    (h2.pre (fun s hs => hs.1))
  exact h

theorem gateSem_una (s : St) : (gateSem s).una = s.una := by
  have h1 : ∀ s1 : St, (if isTop s1 = true then skipNatSem (skipNatSem (skipNatSem s1))
      else ratSem (skipNatSem s1)).una = s1.una := by
    intro s1
    split_ifs
    · rw [skipNatSem_una, skipNatSem_una, skipNatSem_una]
    · rw [ratSem_una, skipNatSem_una]
  unfold gateSem
  split_ifs
  · exact (h1 (onesStep s)).trans rfl
  · rw [skipNatSem_una, skipNatSem_una]

theorem rep_cons (k : ℕ) (l : List Bool) :
    List.replicate k true ++ true :: l = true :: (List.replicate k true ++ l) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem isTop_false (x outr cnt dig una rest t1 t2 out : List Bool) :
    isTop ⟨false :: x, outr, cnt, dig, una, rest, t1, t2, out⟩ = false := by
  simp [isTop, lead]

theorem isTop_true (x outr cnt dig una rest t1 t2 out : List Bool) :
    isTop ⟨true :: x, outr, cnt, dig, una, rest, t1, t2, out⟩ = true := by
  simp [isTop, lead]

theorem onesStep_mk (x outr cnt dig una rest t1 t2 out : List Bool) :
    onesStep ⟨true :: x, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨x, true :: outr, true :: cnt, dig, una, rest, t1, t2, out⟩ := rfl

/-- A gate with two gate indices: tag `t ≥ 2`. -/
theorem gateSem_bin (t a b : ℕ) (ht : 2 ≤ t) (x outr dig una rest t1 t2 out : List Bool) :
    gateSem ⟨encNat t ++ encNat a ++ encNat b ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
      ⟨x, (encNat t ++ encNat a ++ encNat b).reverse ++ outr, [],
        b.bits.reverse ++ (a.bits.reverse ++ (t.bits.reverse ++ dig)), una, rest, t1, t2, out⟩ := by
  have hsize : 2 ≤ t.bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.lt_size.mpr (by simpa using ht)
  obtain ⟨k, hk⟩ : ∃ k, t.bits.length = k + 2 := ⟨t.bits.length - 2, by omega⟩
  have e : encNat t ++ encNat a ++ encNat b ++ x =
      true :: (List.replicate (k + 1) true ++ false :: (t.bits ++ (encNat a ++ (encNat b ++ x)))) := by
    simp [encNat, hk, List.replicate_succ]
  rw [e]
  unfold gateSem
  rw [isTop_true]
  simp only [if_true]
  rw [onesStep_mk]
  have e2 : isTop ⟨List.replicate (k + 1) true ++ false :: (t.bits ++ (encNat a ++ (encNat b ++ x))),
      true :: outr, [true], dig, una, rest, t1, t2, out⟩ = true := by
    simp [isTop, lead, List.replicate_succ]
  rw [e2]
  simp only [if_true]
  rw [skipNatSem_mk (k + 1) t.bits _ _ _ _ _ _ _ _ _ (by simp [hk]), skipNatSem_encNat_mk,
    skipNatSem_encNat_mk]
  simp [encNat, hk, List.replicate_succ']
  simp only [rep_cons]

/-- `gateP` moves exactly one gate code. -/
theorem gateSem_mk (g : ArithmeticGate) (x outr dig una rest t1 t2 out : List Bool) :
    ∃ d, gateSem ⟨gateCode g ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
      ⟨x, (gateCode g).reverse ++ outr, [], d, una, rest, t1, t2, out⟩ := by
  cases g with
  | input i =>
    have h : gateSem ⟨gateCode (.input i) ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
        ⟨x, (gateCode (.input i)).reverse ++ outr, [], i.bits.reverse ++ dig, una, rest, t1, t2,
          out⟩ := by
      have e : gateCode (.input i) ++ x = false :: (encNat i ++ x) := by
        simp [gateCode, encNat]
      rw [e]
      unfold gateSem
      rw [isTop_false]
      simp only [Bool.false_eq_true, if_false]
      have h0 := skipNatSem_encNat_mk 0 (encNat i ++ x) outr dig una rest t1 t2 out
      simp only [encNat, Nat.zero_bits, List.length_nil, List.replicate_zero, List.nil_append,
        List.cons_append, List.reverse_cons, List.reverse_nil] at h0
      simp only [encNat] at *
      rw [h0]
      have h1 := skipNatSem_encNat_mk i x (false :: outr) dig una rest t1 t2 out
      simp only [encNat] at h1
      rw [h1]
      simp [gateCode, encNat]
    exact ⟨_, h⟩
  | constant r =>
    have h : gateSem ⟨gateCode (.constant r) ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
        ⟨x, (gateCode (.constant r)).reverse ++ outr, [],
          r.den.bits.reverse ++ (r.num.natAbs.bits.reverse ++ (true :: dig)), una, rest, t1, t2,
          out⟩ := by
      have e : gateCode (.constant r) ++ x = true :: false :: true :: (encRat r ++ x) := by
        simp [gateCode, encNat]
      rw [e]
      unfold gateSem
      rw [isTop_true]
      simp only [if_true]
      rw [onesStep_mk, isTop_false]
      simp only [Bool.false_eq_true, if_false]
      have h1 := skipNatSem_mk 0 [true] (encRat r ++ x) (true :: outr) [true] dig una rest t1 t2 out
        (by simp)
      simp only [List.replicate_zero, List.nil_append, List.cons_append, List.reverse_cons,
        List.reverse_nil] at h1
      rw [h1, ratSem_mk]
      simp [gateCode, encNat]
    exact ⟨_, h⟩
  | add a b => exact ⟨_, gateSem_bin 2 a b (by norm_num) x outr dig una rest t1 t2 out⟩
  | sub a b => exact ⟨_, gateSem_bin 3 a b (by norm_num) x outr dig una rest t1 t2 out⟩
  | mul a b => exact ⟨_, gateSem_bin 4 a b (by norm_num) x outr dig una rest t1 t2 out⟩
  | minimum a b => exact ⟨_, gateSem_bin 5 a b (by norm_num) x outr dig una rest t1 t2 out⟩
  | maximum a b => exact ⟨_, gateSem_bin 6 a b (by norm_num) x outr dig una rest t1 t2 out⟩
  | test a b => exact ⟨_, gateSem_bin 7 a b (by norm_num) x outr dig una rest t1 t2 out⟩

end ScaleLam

namespace ScaleLam

open CookPvsNP NetworkEquilibriumCLS.LinearNash

theorem iter_proj {α : Type} (π : St → α) {f : St → St} (h : ∀ s, π (f s) = π s) (n : ℕ)
    (s : St) : π (f^[n] s) = π s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, h]

/-! ### Loop A: empty `una` into `t1`, taking as many fuel symbols into `t2` -/

def aAct (h : Stk → Option Bool) : Stk → StackAct Bool
  | .una => .pop
  | .t1 => .push true
  | .rest => .pop
  | .t2 => match h .rest with
    | some _ => .push true
    | none => .keep
  | _ => .keep

def unaTest (h : Stk → Option Bool) : Bool := (h .una).isSome

def aStep (s : St) : St :=
  { s with una := s.una.tail, t1 := true :: s.t1, rest := s.rest.tail,
           t2 := match s.rest.head? with
             | some _ => true :: s.t2
             | none => s.t2 }

def aLoop : StackProg Stk Bool := .loop unaTest (.act aAct)

def aSem (s : St) : St := aStep^[s.una.length] s

theorem unaTest_eq (s : St) : unaTest (fun k => (s.store k).head?) = decide (0 < s.una.length) := by
  obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
  simp only [unaTest, St.store]
  cases una <;> simp

theorem aLoop_impl (L : ℕ) : Impl (Inv L) (Inv L) aLoop aSem (L * (1 + 2) + 1) := by
  have hact : Impl (fun s => Inv L s ∧ 0 < s.una.length) (Inv L) (.act aAct) aStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4⟩, hpos⟩
    constructor
    · funext k
      cases k <;> simp only [StackProg.applyAct, aAct, aStep, St.store] <;>
        first | rfl | (cases rest <;> rfl)
    · cases una with
      | nil => simp at hpos
      | cons u us =>
        cases rest with
        | nil =>
          refine ⟨h1, h2, h3, ?_⟩
          simp [aStep] at h4 ⊢
          omega
        | cons r rs =>
          refine ⟨h1, h2, h3, ?_⟩
          simp [aStep] at h4 ⊢
          omega
  have h := Impl.loop (P := Inv L) (test := unaTest) (fun s => s.una.length) L
    (fun s _ => unaTest_eq s)
    (fun s _ hpos => by
      simp [aStep]
      omega)
    (fun s hs => by
      have := hs.2.2.2
      omega)
    hact
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem aSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    aSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, outr, cnt, dig, [], rest.drop una.length, List.replicate una.length true ++ t1,
        List.replicate (min una.length rest.length) true ++ t2, out⟩ := by
  show aStep^[una.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction una generalizing rest t1 t2 with
  | nil => simp
  | cons u us ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    cases rest with
    | nil =>
      have e : aStep ⟨inp, outr, cnt, dig, u :: us, [], t1, t2, out⟩ =
          ⟨inp, outr, cnt, dig, us, [], true :: t1, t2, out⟩ := rfl
      rw [e, ih]
      simp [rep_cons, List.replicate_succ]
    | cons r rs =>
      have e : aStep ⟨inp, outr, cnt, dig, u :: us, r :: rs, t1, t2, out⟩ =
          ⟨inp, outr, cnt, dig, us, rs, true :: t1, true :: t2, out⟩ := rfl
      rw [e, ih]
      simp [rep_cons, Nat.succ_min_succ, List.replicate_succ]

/-! ### Moving `t1` and `t2` back onto `una` -/

def m1Act (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .t1 => .pop
  | .una => .push true
  | _ => .keep

def t1Test (h : Stk → Option Bool) : Bool := (h .t1).isSome

def m1Step (s : St) : St := { s with t1 := s.t1.tail, una := true :: s.una }

def m1Loop : StackProg Stk Bool := .loop t1Test (.act m1Act)

def m1Sem (s : St) : St := m1Step^[s.t1.length] s

theorem m1Loop_impl (L : ℕ) : Impl (Inv L) (Inv L) m1Loop m1Sem (L * (1 + 2) + 1) := by
  have hact : Impl (fun s => Inv L s ∧ 0 < s.t1.length) (Inv L) (.act m1Act) m1Step 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4⟩, hpos⟩
    constructor
    · funext k
      cases k <;> rfl
    · cases t1 with
      | nil => simp at hpos
      | cons u us =>
        refine ⟨h1, h2, h3, ?_⟩
        simp [m1Step] at h4 ⊢
        omega
  have h := Impl.loop (P := Inv L) (test := t1Test) (fun s => s.t1.length) L
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      simp only [t1Test, St.store]
      cases t1 <;> simp)
    (fun s _ hpos => by
      simp [m1Step]
      omega)
    (fun s hs => by
      have := hs.2.2.2
      omega)
    hact
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem m1Sem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    m1Sem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, outr, cnt, dig, List.replicate t1.length true ++ una, rest, [], t2, out⟩ := by
  show m1Step^[t1.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction t1 generalizing una with
  | nil => simp
  | cons u us ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : m1Step ⟨inp, outr, cnt, dig, una, rest, u :: us, t2, out⟩ =
        ⟨inp, outr, cnt, dig, true :: una, rest, us, t2, out⟩ := rfl
    rw [e, ih]
    simp [rep_cons, List.replicate_succ]

def m2Act (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .t2 => .pop
  | .una => .push true
  | _ => .keep

def t2Test (h : Stk → Option Bool) : Bool := (h .t2).isSome

def m2Step (s : St) : St := { s with t2 := s.t2.tail, una := true :: s.una }

def m2Loop : StackProg Stk Bool := .loop t2Test (.act m2Act)

def m2Sem (s : St) : St := m2Step^[s.t2.length] s

theorem m2Loop_impl (L : ℕ) : Impl (Inv L) (Inv L) m2Loop m2Sem (L * (1 + 2) + 1) := by
  have hact : Impl (fun s => Inv L s ∧ 0 < s.t2.length) (Inv L) (.act m2Act) m2Step 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4⟩, hpos⟩
    constructor
    · funext k
      cases k <;> rfl
    · cases t2 with
      | nil => simp at hpos
      | cons u us =>
        refine ⟨h1, h2, h3, ?_⟩
        simp [m2Step] at h4 ⊢
        omega
  have h := Impl.loop (P := Inv L) (test := t2Test) (fun s => s.t2.length) L
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      simp only [t2Test, St.store]
      cases t2 <;> simp)
    (fun s _ hpos => by
      simp [m2Step]
      omega)
    (fun s hs => by
      have := hs.2.2.2
      omega)
    hact
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem m2Sem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    m2Sem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, outr, cnt, dig, List.replicate t2.length true ++ una, rest, t1, [], out⟩ := by
  show m2Step^[t2.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction t2 generalizing una with
  | nil => simp
  | cons u us ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : m2Step ⟨inp, outr, cnt, dig, una, rest, t1, u :: us, out⟩ =
        ⟨inp, outr, cnt, dig, true :: una, rest, t1, us, out⟩ := rfl
    rw [e, ih]
    simp [rep_cons, List.replicate_succ]

/-! ### Doubling the counter (capped by the fuel) -/

def dblP : StackProg Stk Bool := .seq aLoop (.seq m1Loop m2Loop)

def dblSem (s : St) : St := m2Sem (m1Sem (aSem s))

def bDbl (L : ℕ) : ℕ := (L * (1 + 2) + 1) + 1 + ((L * (1 + 2) + 1) + 1 + (L * (1 + 2) + 1))

theorem dbl_impl (L : ℕ) : Impl (Inv L) (Inv L) dblP dblSem (bDbl L) := by
  have h := (aLoop_impl L).seq ((m1Loop_impl L).seq (m2Loop_impl L))
  exact h

theorem dblSem_dig (s : St) : (dblSem s).dig = s.dig := by
  unfold dblSem m2Sem m1Sem aSem
  rw [iter_proj (fun s => s.dig) (f := m2Step) (fun s => rfl),
    iter_proj (fun s => s.dig) (f := m1Step) (fun s => rfl),
    iter_proj (fun s => s.dig) (f := aStep) (fun s => rfl)]

theorem dblSem_mk (inp outr cnt dig una rest out : List Bool) :
    dblSem ⟨inp, outr, cnt, dig, una, rest, [], [], out⟩ =
      ⟨inp, outr, cnt, dig, List.replicate (una.length + min una.length rest.length) true,
        rest.drop una.length, [], [], out⟩ := by
  unfold dblSem
  rw [aSem_mk, m1Sem_mk, m2Sem_mk]
  simp [List.replicate_append_replicate, Nat.add_comm]

/-! ### One Horner step -/

def digTop (h : Stk → Option Bool) : Bool := h .dig == some true

def isOne (s : St) : Bool := s.dig.head? == some true

def incAct (h : Stk → Option Bool) : Stk → StackAct Bool
  | .rest => .pop
  | .una => match h .rest with
    | some _ => .push true
    | none => .keep
  | _ => .keep

def incStep (s : St) : St :=
  { s with rest := s.rest.tail,
           una := match s.rest.head? with
             | some _ => true :: s.una
             | none => s.una }

def nopAct (_h : Stk → Option Bool) (_k : Stk) : StackAct Bool := .keep

def popDigAct (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .dig => .pop
  | _ => .keep

def popDigStep (s : St) : St := { s with dig := s.dig.tail }

def hornerP : StackProg Stk Bool :=
  .seq dblP (.seq (.branch digTop (.act incAct) (.act nopAct)) (.act popDigAct))

def hornerSem (s : St) : St :=
  (fun s => popDigStep ((fun s => if isOne s = true then incStep s else (fun s => s) s) s))
    (dblSem s)

def bHorner (L : ℕ) : ℕ := bDbl L + 1 + ((1 + max 1 1) + 1 + 1)

theorem horner_impl (L : ℕ) : Impl (Inv L) (Inv L) hornerP hornerSem (bHorner L) := by
  have hinc : Impl (fun s => Inv L s ∧ isOne s = true) (Inv L) (.act incAct) incStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4⟩, -⟩
    constructor
    · funext k
      cases k <;> simp only [StackProg.applyAct, incAct, incStep, St.store] <;>
        first | rfl | (cases rest <;> rfl)
    · cases rest with
      | nil =>
        refine ⟨h1, h2, h3, ?_⟩
        simp [incStep] at h4 ⊢
        omega
      | cons r rs =>
        refine ⟨h1, h2, h3, ?_⟩
        simp [incStep] at h4 ⊢
        omega
  have hnop : Impl (fun s => Inv L s ∧ isOne s = false) (Inv L) (.act nopAct) (fun s => s) 1 := by
    apply Impl.act
    rintro s ⟨hs, -⟩
    constructor
    · funext k
      cases k <;> rfl
    · exact hs
  have hbr := Impl.branch (P := Inv L) (test := digTop) isOne
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      rfl)
    hinc hnop
  have hpop : Impl (Inv L) (Inv L) (.act popDigAct) popDigStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨h1, h2, h3, h4⟩
    constructor
    · funext k
      cases k <;> rfl
    · refine ⟨h1, h2, ?_, h4⟩
      simp [popDigStep] at h3 ⊢
      omega
  have h := (dbl_impl L).seq (hbr.seq hpop)
  exact h

theorem hornerSem_dig (s : St) : (hornerSem s).dig = s.dig.tail := by
  have e : (hornerSem s).dig = (dblSem s).dig.tail := by
    unfold hornerSem
    by_cases h : isOne (dblSem s) = true
    · simp only [h, if_true]
      rfl
    · simp only [h, if_false]
      rfl
  rw [e, dblSem_dig]

/-- A Horner step with digit `d` when the fuel suffices. -/
theorem hornerSem_mk (d : Bool) (v : ℕ) (inp outr cnt ds rest out : List Bool)
    (hfit : v + d.toNat ≤ rest.length) :
    hornerSem ⟨inp, outr, cnt, d :: ds, List.replicate v true, rest, [], [], out⟩ =
      ⟨inp, outr, cnt, ds, List.replicate (2 * v + d.toNat) true, rest.drop (v + d.toNat), [], [],
        out⟩ := by
  unfold hornerSem
  simp only []
  rw [dblSem_mk]
  have hv : v ≤ rest.length := by omega
  cases d with
  | false =>
    have e : isOne ⟨inp, outr, cnt, false :: ds,
        List.replicate ((List.replicate v true).length + min (List.replicate v true).length rest.length) true,
        rest.drop (List.replicate v true).length, [], [], out⟩ = false := rfl
    rw [e]
    simp only [Bool.false_eq_true, if_false]
    simp [popDigStep, Nat.min_eq_left hv, two_mul]
  | true =>
    have e : isOne ⟨inp, outr, cnt, true :: ds,
        List.replicate ((List.replicate v true).length + min (List.replicate v true).length rest.length) true,
        rest.drop (List.replicate v true).length, [], [], out⟩ = true := rfl
    rw [e]
    simp only [if_true]
    have hne : ∃ r rs, rest.drop v = r :: rs := by
      cases h : rest.drop v with
      | nil =>
        have := congrArg List.length h
        simp at this hfit
        omega
      | cons r rs => exact ⟨r, rs, rfl⟩
    obtain ⟨r, rs, hr⟩ := hne
    have hrs : rest.drop (v + 1) = rs := by
      have : rest.drop (v + 1) = (rest.drop v).tail := by
        rw [List.tail_drop]
      rw [this, hr]
      rfl
    simp only [List.length_replicate, Nat.min_eq_left hv, Bool.toNat_true, hr, hrs]
    simp [popDigStep, incStep, two_mul, List.replicate_succ]

/-! ### The conversion loop -/

def digSome (h : Stk → Option Bool) : Bool := (h .dig).isSome

def toUnaP : StackProg Stk Bool := .loop digSome hornerP

def toUnaSem (s : St) : St := hornerSem^[s.dig.length] s

def bUna (L : ℕ) : ℕ := L * (bHorner L + 2) + 1

theorem toUna_impl (L : ℕ) : Impl (Inv L) (Inv L) toUnaP toUnaSem (bUna L) := by
  have h := Impl.loop (P := Inv L) (test := digSome) (fun s => s.dig.length) L
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      simp only [digSome, St.store]
      cases dig <;> simp)
    (fun s _ hpos => by
      rw [hornerSem_dig]
      simp
      omega)
    (fun s hs => by
      have := hs.1
      have := hs.2.2.1
      omega)
    ((horner_impl L).pre (fun s hs => hs.1))
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

/-- The value of a digit list read from the most significant digit, starting from `v`. -/
def hval (ds : List Bool) (v : ℕ) : ℕ := ds.foldl (fun v d => 2 * v + d.toNat) v

theorem hval_ge (ds : List Bool) (v : ℕ) : v ≤ hval ds v := by
  induction ds generalizing v with
  | nil => simp [hval]
  | cons d ds ih =>
    have := ih (2 * v + d.toNat)
    simp only [hval, List.foldl_cons] at this ⊢
    omega

theorem foldr_bits (n : ℕ) : n.bits.foldr (fun d v => 2 * v + d.toNat) 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp [ih, Nat.bit_val]

theorem hval_bits (n : ℕ) : hval n.bits.reverse 0 = n := by
  unfold hval
  rw [List.foldl_reverse]
  exact foldr_bits n

theorem toUnaSem_mk (ds : List Bool) (v : ℕ) (inp outr cnt rest out : List Bool)
    (hfit : hval ds v ≤ v + rest.length) :
    toUnaSem ⟨inp, outr, cnt, ds, List.replicate v true, rest, [], [], out⟩ =
      ⟨inp, outr, cnt, [], List.replicate (hval ds v) true, rest.drop (hval ds v - v), [], [],
        out⟩ := by
  show hornerSem^[ds.length] (St.mk inp outr cnt ds (List.replicate v true) rest [] [] out) = _
  induction ds generalizing v rest with
  | nil => simp [hval]
  | cons d ds ih =>
    have hge := hval_ge ds (2 * v + d.toNat)
    have hfit' : hval ds (2 * v + d.toNat) ≤ v + rest.length := by
      simpa [hval] using hfit
    have h1 : v + d.toNat ≤ rest.length := by omega
    rw [List.length_cons, Function.iterate_succ_apply, hornerSem_mk d v inp outr cnt ds rest out h1]
    rw [ih (2 * v + d.toNat) (rest.drop (v + d.toNat)) (by
      simp only [List.length_drop]
      omega)]
    have e : hval (d :: ds) v = hval ds (2 * v + d.toNat) := by simp [hval]
    rw [e, List.drop_drop]
    congr 2
    omega

/-- Reading a count `c ≤ |rest|` from its binary digits. -/
theorem toUnaSem_bits (c : ℕ) (inp outr cnt rest out : List Bool) (hc : c ≤ rest.length) :
    toUnaSem ⟨inp, outr, cnt, c.bits.reverse, [], rest, [], [], out⟩ =
      ⟨inp, outr, cnt, [], List.replicate c true, rest.drop c, [], [], out⟩ := by
  have h := toUnaSem_mk c.bits.reverse 0 inp outr cnt rest out (by simpa [hval_bits] using hc)
  simpa [hval_bits] using h

end ScaleLam

namespace ScaleLam

open CookPvsNP NetworkEquilibriumCLS.LinearNash NadlerCLS

/-! ### Counted loops -/

def tickAct (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .una => .pop
  | .rest => .push true
  | _ => .keep

def tickStep (s : St) : St := { s with una := s.una.tail, rest := true :: s.rest }

/-- Run `body` once for every symbol of the counter `una`, returning the symbols to the fuel. -/
def cloopP (body : StackProg Stk Bool) : StackProg Stk Bool :=
  .loop unaTest (.seq (.act tickAct) body)

def cloopSem (bsem : St → St) (s : St) : St := (fun s => bsem (tickStep s))^[s.una.length] s

theorem cloop_impl (L : ℕ) {body : StackProg Stk Bool} {bsem : St → St} {B : ℕ}
    (hb : Impl (Inv L) (Inv L) body bsem B) (hu : ∀ s, (bsem s).una = s.una) :
    Impl (Inv L) (Inv L) (cloopP body) (cloopSem bsem) (L * ((1 + 1 + B) + 2) + 1) := by
  have htick : Impl (fun s => Inv L s ∧ 0 < s.una.length) (Inv L) (.act tickAct) tickStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4⟩, hpos⟩
    constructor
    · funext k
      cases k <;> rfl
    · cases una with
      | nil => simp at hpos
      | cons u us =>
        refine ⟨h1, h2, h3, ?_⟩
        simp [tickStep] at h4 ⊢
        omega
  have h := Impl.loop (P := Inv L) (test := unaTest) (fun s => s.una.length) L
    (fun s _ => unaTest_eq s)
    (fun s _ hpos => by
      show (bsem (tickStep s)).una.length + 1 = s.una.length
      rw [hu]
      simp [tickStep]
      omega)
    (fun s hs => by
      have := hs.2.2.2
      omega)
    (htick.seq hb)
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem cloopSem_una (bsem : St → St) (hu : ∀ s, (bsem s).una = s.una) (s : St) :
    (cloopSem bsem s).una.length = 0 := by
  unfold cloopSem
  generalize hn : s.una.length = n
  induction n generalizing s with
  | zero => simpa using hn
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    rw [hu]
    simp [tickStep, hn]

/-- A counted loop over the codes of the items of a list. -/
theorem cloopSem_mk {α : Type} (c : α → List Bool) (bsem : St → St)
    (hspec : ∀ (a : α) (x outr dig una rest t1 t2 out : List Bool),
      ∃ d, bsem ⟨c a ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
        ⟨x, (c a).reverse ++ outr, [], d, una, rest, t1, t2, out⟩)
    (xs : List α) (x outr dig rest t1 t2 out : List Bool) :
    ∃ d, cloopSem bsem
        ⟨xs.flatMap c ++ x, outr, [], dig, List.replicate xs.length true, rest, t1, t2, out⟩ =
      ⟨x, (xs.flatMap c).reverse ++ outr, [], d, [], List.replicate xs.length true ++ rest, t1, t2,
        out⟩ := by
  induction xs generalizing outr dig rest with
  | nil => exact ⟨dig, by simp [cloopSem]⟩
  | cons a xs ih =>
    obtain ⟨d1, h1⟩ := hspec a (xs.flatMap c ++ x) outr dig (List.replicate xs.length true)
      (true :: rest) t1 t2 out
    obtain ⟨d2, h2⟩ := ih ((c a).reverse ++ outr) d1 (true :: rest)
    refine ⟨d2, ?_⟩
    rw [List.length_cons]
    have e : cloopSem bsem ⟨(a :: xs).flatMap c ++ x, outr, [], dig,
          List.replicate (xs.length + 1) true, rest, t1, t2, out⟩ =
        cloopSem bsem ⟨xs.flatMap c ++ x, (c a).reverse ++ outr, [], d1,
          List.replicate xs.length true, true :: rest, t1, t2, out⟩ := by
      have ht : tickStep ⟨(a :: xs).flatMap c ++ x, outr, [], dig,
            List.replicate (xs.length + 1) true, rest, t1, t2, out⟩ =
          ⟨c a ++ (xs.flatMap c ++ x), outr, [], dig, List.replicate xs.length true, true :: rest,
            t1, t2, out⟩ := by
        simp [tickStep, List.replicate_succ]
      show (fun s => bsem (tickStep s))^[(List.replicate (xs.length + 1) true).length] _ =
        (fun s => bsem (tickStep s))^[(List.replicate xs.length true).length] _
      rw [List.length_replicate, List.length_replicate, Function.iterate_succ_apply]
      show (fun s => bsem (tickStep s))^[xs.length] (bsem (tickStep _)) = _
      rw [ht, h1]
    rw [e, h2]
    simp [rep_cons, List.replicate_succ]

/-! ### Clearing the digit stack -/

def clearDig : StackProg Stk Bool := .loop digSome (.act popDigAct)

def clearDigSem (s : St) : St := popDigStep^[s.dig.length] s

theorem clearDig_impl (L : ℕ) : Impl (Inv L) (Inv L) clearDig clearDigSem (L * (1 + 2) + 1) := by
  have hact : Impl (fun s => Inv L s ∧ 0 < s.dig.length) (Inv L) (.act popDigAct) popDigStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4⟩, hpos⟩
    constructor
    · funext k
      cases k <;> rfl
    · refine ⟨h1, h2, ?_, h4⟩
      simp [popDigStep] at h3 ⊢
      omega
  have h := Impl.loop (P := Inv L) (test := digSome) (fun s => s.dig.length) L
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      simp only [digSome, St.store]
      cases dig <;> simp)
    (fun s _ hpos => by
      simp [popDigStep]
      omega)
    (fun s hs => by
      have := hs.1
      have := hs.2.2.1
      omega)
    hact
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem clearDigSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    clearDigSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, outr, cnt, [], una, rest, t1, t2, out⟩ := by
  show popDigStep^[dig.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction dig with
  | nil => rfl
  | cons d ds ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    exact ih

/-! ### A length-prefixed list -/

def listP (body : StackProg Stk Bool) : StackProg Stk Bool :=
  .seq clearDig (.seq skipNat (.seq toUnaP (cloopP body)))

def listSem (bsem : St → St) (s : St) : St :=
  cloopSem bsem (toUnaSem (skipNatSem (clearDigSem s)))

def bList (L B : ℕ) : ℕ :=
  (L * (1 + 2) + 1) + 1 + (bSkip L + 1 + (bUna L + 1 + (L * ((1 + 1 + B) + 2) + 1)))

theorem list_impl (L : ℕ) {body : StackProg Stk Bool} {bsem : St → St} {B : ℕ}
    (hb : Impl (Inv L) (Inv L) body bsem B) (hu : ∀ s, (bsem s).una = s.una) :
    Impl (Inv L) (Inv L) (listP body) (listSem bsem) (bList L B) := by
  have h := (clearDig_impl L).seq ((skipNat_impl L).seq ((toUna_impl L).seq (cloop_impl L hb hu)))
  exact h

theorem listSem_mk {α : Type} (c : α → List Bool) (bsem : St → St)
    (hspec : ∀ (a : α) (x outr dig una rest t1 t2 out : List Bool),
      ∃ d, bsem ⟨c a ++ x, outr, [], dig, una, rest, t1, t2, out⟩ =
        ⟨x, (c a).reverse ++ outr, [], d, una, rest, t1, t2, out⟩)
    (L : ℕ) (xs : List α) (hlen : xs.length ≤ L) (x outr dig out : List Bool) :
    ∃ d, listSem bsem ⟨encList c xs ++ x, outr, [], dig, [], List.replicate L true, [], [], out⟩ =
      ⟨x, (encList c xs).reverse ++ outr, [], d, [], List.replicate L true, [], [], out⟩ := by
  obtain ⟨d, hd⟩ := cloopSem_mk c bsem hspec xs x ((encNat xs.length).reverse ++ outr) []
    ((List.replicate L true).drop xs.length) [] [] out
  refine ⟨d, ?_⟩
  unfold listSem
  have e : encList c xs ++ x = encNat xs.length ++ (xs.flatMap c ++ x) := by
    simp [encList]
  rw [e, clearDigSem_mk, skipNatSem_encNat_mk]
  simp only [List.append_nil]
  rw [toUnaSem_bits xs.length _ _ _ _ _ (by simpa using hlen), hd]
  have e2 : List.replicate xs.length true ++ (List.replicate L true).drop xs.length =
      List.replicate L true := by
    rw [List.drop_replicate, List.replicate_append_replicate]
    congr 1
    omega
  rw [e2]
  simp [encList]

/-! ### A circuit -/

def circP : StackProg Stk Bool := .seq (listP gateP) (listP skipNat)

def circSem (s : St) : St := listSem skipNatSem (listSem gateSem s)

def bCirc (L : ℕ) : ℕ := bList L (bGate L) + 1 + bList L (bSkip L)

theorem circ_impl (L : ℕ) : Impl (Inv L) (Inv L) circP circSem (bCirc L) := by
  have h := (list_impl L (gate_impl L) gateSem_una).seq (list_impl L (skipNat_impl L) skipNatSem_una)
  exact h

theorem circSem_mk (L : ℕ) (C : Circ) (hg : C.gates.length ≤ L) (ho : C.outputs.length ≤ L)
    (x outr dig out : List Bool) :
    ∃ d, circSem ⟨encCirc C ++ x, outr, [], dig, [], List.replicate L true, [], [], out⟩ =
      ⟨x, (encCirc C).reverse ++ outr, [], d, [], List.replicate L true, [], [], out⟩ := by
  obtain ⟨d1, h1⟩ := listSem_mk gateCode gateSem gateSem_mk L C.gates hg
    (encList encNat C.outputs ++ x) outr dig out
  obtain ⟨d2, h2⟩ := listSem_mk encNat skipNatSem
    (fun a x outr dig una rest t1 t2 out => ⟨_, skipNatSem_encNat_mk a x outr dig una rest t1 t2 out⟩)
    L C.outputs ho x ((encList gateCode C.gates).reverse ++ outr) d1 out
  refine ⟨d2, ?_⟩
  unfold circSem
  have e : encCirc C ++ x = encList gateCode C.gates ++ (encList encNat C.outputs ++ x) := by
    simp [encCirc]
  rw [e, h1, h2]
  simp [encCirc]

/-! ### The parse of two circuits and a rational -/

def parseP : StackProg Stk Bool := .seq circP (.seq circP ratP)

def parseSem (s : St) : St := ratSem (circSem (circSem s))

def bParse (L : ℕ) : ℕ := bCirc L + 1 + (bCirc L + 1 + bRat L)

theorem parse_impl (L : ℕ) : Impl (Inv L) (Inv L) parseP parseSem (bParse L) := by
  have h := (circ_impl L).seq ((circ_impl L).seq (rat_impl L))
  exact h

theorem parseSem_mk (L : ℕ) (f p : Circ) (δ : ℚ) (hf1 : f.gates.length ≤ L)
    (hf2 : f.outputs.length ≤ L) (hp1 : p.gates.length ≤ L) (hp2 : p.outputs.length ≤ L)
    (x out : List Bool) :
    ∃ d, parseSem ⟨encCirc f ++ encCirc p ++ encRat δ ++ x, [], [], [], [], List.replicate L true,
        [], [], out⟩ =
      ⟨x, (encCirc f ++ encCirc p ++ encRat δ).reverse, [], d, [], List.replicate L true, [], [],
        out⟩ := by
  obtain ⟨d1, h1⟩ := circSem_mk L f hf1 hf2 (encCirc p ++ (encRat δ ++ x)) [] [] out
  obtain ⟨d2, h2⟩ := circSem_mk L p hp1 hp2 (encRat δ ++ x) ((encCirc f).reverse ++ []) d1 out
  refine ⟨δ.den.bits.reverse ++ (δ.num.natAbs.bits.reverse ++ d2), ?_⟩
  unfold parseSem
  simp only [List.append_assoc]
  rw [h1, h2, ratSem_mk]
  simp

end ScaleLam

namespace ScaleLam

open CookPvsNP NetworkEquilibriumCLS.LinearNash NadlerCLS

/-- The initial state on input `w`. -/
def St.init (w : List Bool) : St := ⟨w, [], [], [], [], [], [], [], []⟩

theorem rep_cons_b (b : Bool) (k : ℕ) (l : List Bool) :
    List.replicate k b ++ b :: l = b :: (List.replicate k b ++ l) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-! ### Start-up: `rest := 1^|w|` -/

def inpSome (h : Stk → Option Bool) : Bool := (h .inp).isSome

def iaAct (h : Stk → Option Bool) : Stk → StackAct Bool
  | .inp => .pop
  | .t1 => match h .inp with
    | some b => .push b
    | none => .keep
  | _ => .keep

def iaStep (s : St) : St :=
  { s with inp := s.inp.tail,
           t1 := match s.inp.head? with
             | some b => b :: s.t1
             | none => s.t1 }

def iaLoop : StackProg Stk Bool := .loop inpSome (.act iaAct)

def iaSem (s : St) : St := iaStep^[s.inp.length] s

def PA (L : ℕ) (s : St) : Prop :=
  s.inp.length + s.t1.length ≤ L ∧ s.rest = [] ∧ s.outr = [] ∧ s.cnt = [] ∧ s.dig = [] ∧
    s.una = [] ∧ s.t2 = []

def PB (L : ℕ) (s : St) : Prop :=
  s.inp.length + s.t1.length ≤ L ∧ s.rest.length + s.t1.length ≤ L ∧ s.outr = [] ∧ s.cnt = [] ∧
    s.dig = [] ∧ s.una = [] ∧ s.t2 = []

theorem inpSome_eq (s : St) : inpSome (fun k => (s.store k).head?) = decide (0 < s.inp.length) := by
  obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
  simp only [inpSome, St.store]
  cases inp <;> simp

theorem iaLoop_impl (L : ℕ) : Impl (PA L) (PB L) iaLoop iaSem (L * (1 + 2) + 1) := by
  have hact : Impl (fun s => PA L s ∧ 0 < s.inp.length) (PA L) (.act iaAct) iaStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hpos⟩
    cases inp with
    | nil => simp at hpos
    | cons b l =>
      constructor
      · funext k
        cases k <;> rfl
      · refine ⟨?_, h2, h3, h4, h5, h6, h7⟩
        simp [iaStep] at h1 ⊢
        omega
  have h := Impl.loop (P := PA L) (test := inpSome) (fun s => s.inp.length) L
    (fun s _ => inpSome_eq s)
    (fun s _ hpos => by
      simp [iaStep]
      omega)
    (fun s hs => by
      have := hs.1
      omega)
    hact
  refine h.conseq (fun s hs => hs) (fun s _ hq => ?_) (le_refl _)
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, -⟩ := hq
  refine ⟨h1, ?_, h3, h4, h5, h6, h7⟩
  rw [h2]
  simp only [List.length_nil]
  omega

theorem iaSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    iaSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨[], outr, cnt, dig, una, rest, inp.reverse ++ t1, t2, out⟩ := by
  show iaStep^[inp.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction inp generalizing t1 with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : iaStep ⟨b :: l, outr, cnt, dig, una, rest, t1, t2, out⟩ =
        ⟨l, outr, cnt, dig, una, rest, b :: t1, t2, out⟩ := rfl
    rw [e, ih]
    simp

def ibAct (h : Stk → Option Bool) : Stk → StackAct Bool
  | .t1 => .pop
  | .inp => match h .t1 with
    | some b => .push b
    | none => .keep
  | .rest => .push true
  | _ => .keep

def ibStep (s : St) : St :=
  { s with t1 := s.t1.tail,
           inp := match s.t1.head? with
             | some b => b :: s.inp
             | none => s.inp
           rest := true :: s.rest }

def ibLoop : StackProg Stk Bool := .loop t1Test (.act ibAct)

def ibSem (s : St) : St := ibStep^[s.t1.length] s

theorem t1Test_eq (s : St) : t1Test (fun k => (s.store k).head?) = decide (0 < s.t1.length) := by
  obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
  simp only [t1Test, St.store]
  cases t1 <;> simp

theorem ibLoop_impl (L : ℕ) : Impl (PB L) (Inv L) ibLoop ibSem (L * (1 + 2) + 1) := by
  have hact : Impl (fun s => PB L s ∧ 0 < s.t1.length) (PB L) (.act ibAct) ibStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hpos⟩
    cases t1 with
    | nil => simp at hpos
    | cons b l =>
      constructor
      · funext k
        cases k <;> rfl
      · refine ⟨?_, ?_, h3, h4, h5, h6, h7⟩
        · simp [ibStep] at h1 ⊢
          omega
        · simp [ibStep] at h2 ⊢
          omega
  have h := Impl.loop (P := PB L) (test := t1Test) (fun s => s.t1.length) L
    (fun s _ => t1Test_eq s)
    (fun s _ hpos => by
      simp [ibStep]
      omega)
    (fun s hs => by
      have := hs.1
      omega)
    hact
  refine h.conseq (fun s hs => hs) (fun s _ hq => ?_) (le_refl _)
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h0⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h3]
    simp only [List.length_nil]
    omega
  · rw [h3, h4]
  · rw [h3, h5]
  · rw [h6, h7]
    simp only [List.length_nil]
    omega

theorem ibSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    ibSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨t1.reverse ++ inp, outr, cnt, dig, una, List.replicate t1.length true ++ rest, [], t2,
        out⟩ := by
  show ibStep^[t1.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction t1 generalizing inp rest with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : ibStep ⟨inp, outr, cnt, dig, una, rest, b :: l, t2, out⟩ =
        ⟨b :: inp, outr, cnt, dig, una, true :: rest, l, t2, out⟩ := rfl
    rw [e, ih]
    simp [rep_cons, List.replicate_succ]

def initP : StackProg Stk Bool := .seq iaLoop ibLoop

def initSem (s : St) : St := ibSem (iaSem s)

def bInit (L : ℕ) : ℕ := (L * (1 + 2) + 1) + 1 + (L * (1 + 2) + 1)

theorem init_impl (L : ℕ) : Impl (PA L) (Inv L) initP initSem (bInit L) := by
  have h := (iaLoop_impl L).seq (ibLoop_impl L)
  exact h

theorem initSem_init (w : List Bool) :
    initSem (St.init w) = ⟨w, [], [], [], [], List.replicate w.length true, [], [], []⟩ := by
  unfold initSem St.init
  rw [iaSem_mk, ibSem_mk]
  simp

/-! ### The final block -/

/-- Size invariant of the final block. -/
def Tl (M : ℕ) (s : St) : Prop :=
  s.inp.length ≤ M ∧ s.outr.length ≤ M ∧ s.rest.length ≤ M ∧ s.t1.length ≤ M

def popInpAct (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .inp => .pop
  | _ => .keep

def popInpStep (s : St) : St := { s with inp := s.inp.tail }

def clearInp : StackProg Stk Bool := .loop inpSome (.act popInpAct)

def clearInpSem (s : St) : St := popInpStep^[s.inp.length] s

theorem clearInp_impl (M : ℕ) : Impl (Tl M) (Tl M) clearInp clearInpSem (M * (1 + 2) + 1) := by
  have hact : Impl (fun s => Tl M s ∧ 0 < s.inp.length) (Tl M) (.act popInpAct) popInpStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3, h4⟩, hpos⟩
    constructor
    · funext k
      cases k <;> rfl
    · refine ⟨?_, h2, h3, h4⟩
      simp [popInpStep] at h1 ⊢
      omega
  have h := Impl.loop (P := Tl M) (test := inpSome) (fun s => s.inp.length) M
    (fun s _ => inpSome_eq s)
    (fun s _ hpos => by
      simp [popInpStep]
      omega)
    (fun s hs => hs.1)
    hact
  exact h.conseq (fun s hs => hs) (fun s _ hq => hq.1) (le_refl _)

theorem clearInpSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    clearInpSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨[], outr, cnt, dig, una, rest, t1, t2, out⟩ := by
  show popInpStep^[inp.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction inp with
  | nil => rfl
  | cons d ds ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    exact ih

def pushAct (b : Bool) (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .outr => .push b
  | _ => .keep

def pushStep (b : Bool) (s : St) : St := { s with outr := b :: s.outr }

theorem push_impl (b : Bool) (M : ℕ) :
    Impl (Tl M) (Tl (M + 1)) (.act (pushAct b)) (pushStep b) 1 := by
  apply Impl.act
  rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨h1, h2, h3, h4⟩
  constructor
  · funext k
    cases k <;> rfl
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [pushStep] at * <;> omega

def pushN (b : Bool) : ℕ → StackProg Stk Bool
  | 0 => .act nopAct
  | m + 1 => .seq (.act (pushAct b)) (pushN b m)

def pushNSem (b : Bool) : ℕ → St → St
  | 0, s => s
  | m + 1, s => pushNSem b m (pushStep b s)

theorem pushN_impl (b : Bool) (m M : ℕ) :
    Impl (Tl M) (Tl (M + m)) (pushN b m) (pushNSem b m) (2 * m + 1) := by
  induction m generalizing M with
  | zero =>
    apply Impl.act
    intro s hs
    constructor
    · funext k
      cases k <;> rfl
    · exact hs
  | succ m ih =>
    have h := (push_impl b M).seq (ih (M + 1))
    refine h.conseq (fun s hs => hs) (fun s _ hq => ?_) (by omega)
    have e : M + 1 + m = M + (m + 1) := by omega
    rw [← e]
    exact hq

theorem pushNSem_mk (b : Bool) (m : ℕ) (inp outr cnt dig una rest t1 t2 out : List Bool) :
    pushNSem b m ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, List.replicate m b ++ outr, cnt, dig, una, rest, t1, t2, out⟩ := by
  induction m generalizing outr with
  | zero => rfl
  | succ m ih =>
    show pushNSem b m (pushStep b ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩) = _
    have e : pushStep b ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
        ⟨inp, b :: outr, cnt, dig, una, rest, t1, t2, out⟩ := rfl
    rw [e, ih]
    simp [rep_cons_b, List.replicate_succ]

/-! Fuel to the output: `|rest|` ones, with a copy on `t1`. -/

def fAct (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .rest => .pop
  | .outr => .push true
  | .t1 => .push true
  | _ => .keep

def fStep (s : St) : St := { s with rest := s.rest.tail, outr := true :: s.outr, t1 := true :: s.t1 }

def restSome (h : Stk → Option Bool) : Bool := (h .rest).isSome

def fLoop : StackProg Stk Bool := .loop restSome (.act fAct)

def fSem (s : St) : St := fStep^[s.rest.length] s

theorem fLoop_impl (M : ℕ) : Impl (Tl M) (Tl (2 * M)) fLoop fSem ((2 * M) * (1 + 2) + 1) := by
  let P : St → Prop := fun s =>
    s.inp.length ≤ M ∧ s.outr.length + s.rest.length ≤ 2 * M ∧ s.t1.length + s.rest.length ≤ 2 * M
  have hact : Impl (fun s => P s ∧ 0 < s.rest.length) P (.act fAct) fStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3⟩, hpos⟩
    cases rest with
    | nil => simp at hpos
    | cons r rs =>
      constructor
      · funext k
        cases k <;> rfl
      · refine ⟨h1, ?_, ?_⟩ <;> simp [fStep] at * <;> omega
  have h := Impl.loop (P := P) (test := restSome) (fun s => s.rest.length) (2 * M)
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      simp only [restSome, St.store]
      cases rest <;> simp)
    (fun s _ hpos => by
      simp [fStep]
      omega)
    (fun s hs => by
      have := hs.2.1
      omega)
    hact
  refine h.conseq (fun s hs => ⟨hs.1, by have := hs.2.1; have := hs.2.2.1; omega,
    by have := hs.2.2.1; have := hs.2.2.2; omega⟩) (fun s _ hq => ?_) (le_refl _)
  obtain ⟨⟨h1, h2, h3⟩, h0⟩ := hq
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem fSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    fSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, List.replicate rest.length true ++ outr, cnt, dig, una, [],
        List.replicate rest.length true ++ t1, t2, out⟩ := by
  show fStep^[rest.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction rest generalizing outr t1 with
  | nil => rfl
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : fStep ⟨inp, outr, cnt, dig, una, r :: rs, t1, t2, out⟩ =
        ⟨inp, true :: outr, cnt, dig, una, rs, true :: t1, t2, out⟩ := rfl
    rw [e, ih]
    simp [rep_cons, List.replicate_succ]

/-! Zeros to the output: `|t1|` zeros. -/

def zAct (_h : Stk → Option Bool) : Stk → StackAct Bool
  | .t1 => .pop
  | .outr => .push false
  | _ => .keep

def zStep (s : St) : St := { s with t1 := s.t1.tail, outr := false :: s.outr }

def zLoop : StackProg Stk Bool := .loop t1Test (.act zAct)

def zSem (s : St) : St := zStep^[s.t1.length] s

theorem zLoop_impl (M : ℕ) : Impl (Tl M) (Tl (2 * M)) zLoop zSem ((2 * M) * (1 + 2) + 1) := by
  let P : St → Prop := fun s =>
    s.inp.length ≤ M ∧ s.rest.length ≤ M ∧ s.outr.length + s.t1.length ≤ 2 * M
  have hact : Impl (fun s => P s ∧ 0 < s.t1.length) P (.act zAct) zStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨⟨h1, h2, h3⟩, hpos⟩
    cases t1 with
    | nil => simp at hpos
    | cons r rs =>
      constructor
      · funext k
        cases k <;> rfl
      · refine ⟨h1, h2, ?_⟩
        simp [zStep] at *
        omega
  have h := Impl.loop (P := P) (test := t1Test) (fun s => s.t1.length) (2 * M)
    (fun s _ => t1Test_eq s)
    (fun s _ hpos => by
      simp [zStep]
      omega)
    (fun s hs => by
      have := hs.2.2
      omega)
    hact
  refine h.conseq (fun s hs => ⟨hs.1, hs.2.2.1, by have := hs.2.1; have := hs.2.2.2; omega⟩)
    (fun s _ hq => ?_) (le_refl _)
  obtain ⟨⟨h1, h2, h3⟩, h0⟩ := hq
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem zSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    zSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, List.replicate t1.length false ++ outr, cnt, dig, una, rest, [], t2, out⟩ := by
  show zStep^[t1.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction t1 generalizing outr with
  | nil => rfl
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : zStep ⟨inp, outr, cnt, dig, una, rest, r :: rs, t2, out⟩ =
        ⟨inp, false :: outr, cnt, dig, una, rest, rs, t2, out⟩ := rfl
    rw [e, ih]
    simp [rep_cons_b, List.replicate_succ]

/-! Reversing the output. -/

def oAct (h : Stk → Option Bool) : Stk → StackAct Bool
  | .outr => .pop
  | .out => match h .outr with
    | some b => .push b
    | none => .keep
  | _ => .keep

def oStep (s : St) : St :=
  { s with outr := s.outr.tail,
           out := match s.outr.head? with
             | some b => b :: s.out
             | none => s.out }

def outrSome (h : Stk → Option Bool) : Bool := (h .outr).isSome

def oLoop : StackProg Stk Bool := .loop outrSome (.act oAct)

def oSem (s : St) : St := oStep^[s.outr.length] s

theorem oLoop_impl (M : ℕ) : Impl (Tl M) (fun _ => True) oLoop oSem (M * (1 + 2) + 1) := by
  let P : St → Prop := fun s => s.outr.length ≤ M
  have hact : Impl (fun s => P s ∧ 0 < s.outr.length) P (.act oAct) oStep 1 := by
    apply Impl.act
    rintro ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ ⟨h1, hpos⟩
    cases outr with
    | nil => simp at hpos
    | cons r rs =>
      constructor
      · funext k
        cases k <;> rfl
      · simp [P, oStep] at *
        omega
  have h := Impl.loop (P := P) (test := outrSome) (fun s => s.outr.length) M
    (fun s _ => by
      obtain ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ := s
      simp only [outrSome, St.store]
      cases outr <;> simp)
    (fun s _ hpos => by
      simp [oStep]
      omega)
    (fun s hs => hs)
    hact
  exact h.conseq (fun s hs => hs.2.1) (fun s _ _ => trivial) (le_refl _)

theorem oSem_mk (inp outr cnt dig una rest t1 t2 out : List Bool) :
    oSem ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
      ⟨inp, [], cnt, dig, una, rest, t1, t2, outr.reverse ++ out⟩ := by
  show oStep^[outr.length] (St.mk inp outr cnt dig una rest t1 t2 out) = _
  induction outr generalizing out with
  | nil => rfl
  | cons r rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : oStep ⟨inp, r :: rs, cnt, dig, una, rest, t1, t2, out⟩ =
        ⟨inp, rs, cnt, dig, una, rest, t1, t2, r :: out⟩ := rfl
    rw [e, ih]
    simp

/-! The final block. -/

def tailP (n : ℕ) : StackProg Stk Bool :=
  .seq clearInp (.seq (.act (pushAct false)) (.seq fLoop (.seq (pushN true (n + 1))
    (.seq (.act (pushAct false)) (.seq zLoop (.seq (pushN false n)
      (.seq (.act (pushAct true)) (.seq (.act (pushAct true)) (.seq (.act (pushAct false))
        (.seq (.act (pushAct true)) oLoop))))))))))

def tailSem (n : ℕ) (s : St) : St :=
  oSem (pushStep true (pushStep false (pushStep true (pushStep true (pushNSem false n
    (zSem (pushStep false (pushNSem true (n + 1) (fSem (pushStep false (clearInpSem s)))))))))))

def bTail (n L : ℕ) : ℕ := 40 * L + 30 * n + 200

theorem tail_impl (n L : ℕ) : Impl (Tl L) (fun _ => True) (tailP n) (tailSem n) (bTail n L) := by
  have h := (clearInp_impl L).seq ((push_impl false L).seq ((fLoop_impl (L + 1)).seq
    ((pushN_impl true (n + 1) (2 * (L + 1))).seq ((push_impl false (2 * (L + 1) + (n + 1))).seq
      ((zLoop_impl (2 * (L + 1) + (n + 1) + 1)).seq
        ((pushN_impl false n (2 * (2 * (L + 1) + (n + 1) + 1))).seq
          ((push_impl true (2 * (2 * (L + 1) + (n + 1) + 1) + n)).seq
            ((push_impl true (2 * (2 * (L + 1) + (n + 1) + 1) + n + 1)).seq
              ((push_impl false (2 * (2 * (L + 1) + (n + 1) + 1) + n + 1 + 1)).seq
                ((push_impl true (2 * (2 * (L + 1) + (n + 1) + 1) + n + 1 + 1 + 1)).seq
                  (oLoop_impl (2 * (2 * (L + 1) + (n + 1) + 1) + n + 1 + 1 + 1 + 1))))))))))))
  refine h.conseq (fun s hs => hs) (fun s _ hq => hq) ?_
  unfold bTail
  omega

theorem tailSem_mk (n L : ℕ) (inp outr cnt dig una t2 : List Bool) :
    tailSem n ⟨inp, outr, cnt, dig, una, List.replicate L true, [], t2, []⟩ =
      ⟨[], [], cnt, dig, una, [], [], t2,
        outr.reverse ++ (false :: (List.replicate L true ++ (List.replicate (n + 1) true ++
          (false :: (List.replicate L false ++ (List.replicate n false ++
            [true, true, false, true]))))))⟩ := by
  unfold tailSem
  have p : ∀ (b : Bool) (inp outr cnt dig una rest t1 t2 out : List Bool),
      pushStep b ⟨inp, outr, cnt, dig, una, rest, t1, t2, out⟩ =
        ⟨inp, b :: outr, cnt, dig, una, rest, t1, t2, out⟩ := fun _ _ _ _ _ _ _ _ _ _ => rfl
  rw [clearInpSem_mk, p, fSem_mk, pushNSem_mk, p, zSem_mk, pushNSem_mk, p, p, p, p, oSem_mk]
  simp
  simp only [List.replicate_add, List.append_assoc, List.cons_append]

end ScaleLam

namespace ScaleLam

open CookPvsNP NetworkEquilibriumCLS.LinearNash NadlerCLS

/-! ### The program -/

def totalP (n : ℕ) : StackProg Stk Bool := .seq initP (.seq parseP (tailP n))

def totalSem (n : ℕ) (s : St) : St := tailSem n (parseSem (initSem s))

def bTotal (n L : ℕ) : ℕ := bInit L + 1 + (bParse L + 1 + bTail n L)

theorem total_impl (n L : ℕ) :
    Impl (PA L) (fun _ => True) (totalP n) (totalSem n) (bTotal n L) := by
  have ht : Impl (Inv L) (fun _ => True) (tailP n) (tailSem n) (bTail n L) :=
    (tail_impl n L).pre (fun s hs => by
      obtain ⟨h1, h2, h3, h4⟩ := hs
      exact ⟨by omega, by omega, by omega, by omega⟩)
  have h := (init_impl L).seq ((parse_impl L).seq ht)
  exact h

/-! ### The step bound is polynomial -/

theorem PolyB.maxb {b c : ℕ → ℕ} (hb : PolyB b) (hc : PolyB c) :
    PolyB (fun L => max (b L) (c L)) :=
  (hb.add hc).mono (fun L => by
    show max (b L) (c L) ≤ b L + c L
    omega)

theorem hL_poly : PolyB (fun L => L * (1 + 2) + 1) :=
  (PolyB.id.mul (PolyB.const (1 + 2))).add (PolyB.const 1)

theorem bSkip_poly : PolyB bSkip := by
  have c1 := PolyB.const 1
  have hL := hL_poly
  exact (hL.add c1).add ((c1.add c1).add ((hL.add c1).add hL))

theorem bRat_poly : PolyB bRat := by
  have c1 := PolyB.const 1
  have S := bSkip_poly
  exact (c1.add c1).add ((S.add c1).add S)

theorem bGate_poly : PolyB bGate := by
  have c1 := PolyB.const 1
  have S := bSkip_poly
  have R := bRat_poly
  exact c1.add (((c1.add c1).add (c1.add (((S.add c1).add ((S.add c1).add S)).maxb
    ((S.add c1).add R)))).maxb ((S.add c1).add S))

theorem bDbl_poly : PolyB bDbl := by
  have c1 := PolyB.const 1
  have hL := hL_poly
  exact (hL.add c1).add ((hL.add c1).add hL)

theorem bHorner_poly : PolyB bHorner := by
  have c1 := PolyB.const 1
  exact (bDbl_poly.add c1).add (PolyB.const ((1 + max 1 1) + 1 + 1))

theorem bUna_poly : PolyB bUna := by
  have c1 := PolyB.const 1
  exact (PolyB.id.mul (bHorner_poly.add (PolyB.const 2))).add c1

theorem bList_poly {b : ℕ → ℕ} (hb : PolyB b) : PolyB (fun L => bList L (b L)) := by
  have c1 := PolyB.const 1
  have hL := hL_poly
  exact (hL.add c1).add ((bSkip_poly.add c1).add ((bUna_poly.add c1).add
    ((PolyB.id.mul (((c1.add c1).add hb).add (PolyB.const 2))).add c1)))

theorem bCirc_poly : PolyB bCirc := by
  have c1 := PolyB.const 1
  exact ((bList_poly bGate_poly).add c1).add (bList_poly bSkip_poly)

theorem bParse_poly : PolyB bParse := by
  have c1 := PolyB.const 1
  exact (bCirc_poly.add c1).add ((bCirc_poly.add c1).add bRat_poly)

theorem bInit_poly : PolyB bInit := by
  have c1 := PolyB.const 1
  have hL := hL_poly
  exact (hL.add c1).add hL

theorem bTail_poly (n : ℕ) : PolyB (bTail n) :=
  (((PolyB.const 40).mul PolyB.id).add (PolyB.const (30 * n))).add (PolyB.const 200)

theorem bTotal_poly (n : ℕ) : PolyB (bTotal n) := by
  have c1 := PolyB.const 1
  exact (bInit_poly.add c1).add ((bParse_poly.add c1).add (bTail_poly n))

/-! ### The output on instance codes -/

theorem bits_two_pow (m : ℕ) : (2 ^ m).bits = List.replicate m false ++ [true] := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : 2 ^ (m + 1) = Nat.bit false (2 ^ m) := by
      rw [Nat.bit_false, pow_succ]
      ring
    rw [e, Nat.bits_append_bit _ _ (fun h => absurd h (by positivity)), ih]
    simp [List.replicate_succ]

theorem encRat_natCast (N : ℕ) : encRat (N : ℚ) = false :: (encNat N ++ [true, false, true]) := by
  have h : ¬ ((N : ℤ) < 0) := by omega
  simp [encRat, encInt, encNat, h]

theorem encRat_two_pow (m : ℕ) :
    encRat ((2 ^ m : ℕ) : ℚ) =
      false :: (List.replicate (m + 1) true ++
        false :: (List.replicate m false ++ [true, true, false, true])) := by
  rw [encRat_natCast]
  simp [encNat, bits_two_pow]

theorem length_le_flatMap {α : Type} (c : α → List Bool) (hc : ∀ a, 1 ≤ (c a).length)
    (xs : List α) : xs.length ≤ (xs.flatMap c).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have := hc a
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

theorem length_le_encList {α : Type} (c : α → List Bool) (hc : ∀ a, 1 ≤ (c a).length)
    (xs : List α) : xs.length ≤ (encList c xs).length := by
  have := length_le_flatMap c hc xs
  simp only [encList, List.length_append]
  omega

theorem one_le_encNat (m : ℕ) : 1 ≤ (encNat m).length := by
  simp [encNat]
  omega

theorem one_le_gateCode (g : ArithmeticGate) : 1 ≤ (gateCode g).length := by
  cases g <;> simp [gateCode, encNat] <;> omega

theorem total_valid (n m : ℕ) (I : COInstance m) :
    (totalSem n (St.init (encCO I))).out =
      encCO ({ f := I.f, p := I.p, δ := I.δ,
               lam := ((2 ^ ((encCO I).length + n) : ℕ) : ℚ) } : COInstance m) := by
  have hlen : (encCO I).length = (encCirc I.f).length + (encCirc I.p).length +
      (encRat I.δ).length + (encRat I.lam).length := by
    simp [encCO]
    omega
  have hf : (encCirc I.f).length = (encList gateCode I.f.gates).length +
      (encList encNat I.f.outputs).length := by simp [encCirc]
  have hp : (encCirc I.p).length = (encList gateCode I.p.gates).length +
      (encList encNat I.p.outputs).length := by simp [encCirc]
  have b1 := length_le_encList gateCode one_le_gateCode I.f.gates
  have b2 := length_le_encList encNat one_le_encNat I.f.outputs
  have b3 := length_le_encList gateCode one_le_gateCode I.p.gates
  have b4 := length_le_encList encNat one_le_encNat I.p.outputs
  obtain ⟨d, hd⟩ := parseSem_mk (encCO I).length I.f I.p I.δ (by omega) (by omega) (by omega)
    (by omega) (encRat I.lam) []
  unfold totalSem
  rw [initSem_init]
  have e : encCO I = encCirc I.f ++ encCirc I.p ++ encRat I.δ ++ encRat I.lam := rfl
  rw [e] at hd ⊢
  rw [hd, tailSem_mk]
  simp only [encCO, List.reverse_reverse, encRat_two_pow]
  simp only [List.replicate_add, List.append_assoc, List.cons_append, List.length_append]

theorem lam_bound (n m : ℕ) (I : COInstance m) (hlam : 0 < I.lam) :
    (n : ℚ) * I.lam ≤ ((2 ^ ((encCO I).length + n) : ℕ) : ℚ) := by
  set a := I.lam.num.natAbs with ha
  have hnum : 0 < I.lam.num := Rat.num_pos.mpr hlam
  have h1 : I.lam ≤ (a : ℚ) := by
    have hden : (1 : ℚ) ≤ (I.lam.den : ℚ) := by
      exact_mod_cast I.lam.den_pos
    have e1 : I.lam * (I.lam.den : ℚ) = (I.lam.num : ℚ) := Rat.mul_den_eq_num I.lam
    have e2 : (I.lam.num : ℚ) = (a : ℚ) := by
      have : (a : ℤ) = I.lam.num := Int.natAbs_of_nonneg hnum.le
      rw [← this]
      simp
    calc I.lam ≤ I.lam * (I.lam.den : ℚ) := le_mul_of_one_le_right hlam.le hden
      _ = (a : ℚ) := by rw [e1, e2]
  have h2 : a.bits.length ≤ (encCO I).length := by
    have : (encRat I.lam).length ≤ (encCO I).length := by
      simp [encCO]
      omega
    have : a.bits.length ≤ (encRat I.lam).length := by
      simp [encRat, encInt, encNat, ha]
      omega
    omega
  have h3 : a < 2 ^ (encCO I).length := by
    have := Nat.lt_size_self a
    rw [Nat.size_eq_bits_len] at h2
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) h2)
  have h4 : n * a ≤ 2 ^ ((encCO I).length + n) := by
    have hn : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
    calc n * a ≤ 2 ^ n * 2 ^ (encCO I).length := Nat.mul_le_mul hn h3.le
      _ = 2 ^ ((encCO I).length + n) := by rw [pow_add, mul_comm]
  calc (n : ℚ) * I.lam ≤ (n : ℚ) * (a : ℚ) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
    _ = ((n * a : ℕ) : ℚ) := by push_cast; ring
    _ ≤ ((2 ^ ((encCO I).length + n) : ℕ) : ℚ) := by exact_mod_cast h4

end ScaleLam

open NetworkEquilibriumCLS.LinearNash NadlerCLS in
theorem solution (n : ℕ) :
    ∃ F : List Bool → List Bool, PolyTime F ∧
      ∀ I : COInstance n, I.Valid →
        ∃ lam' : ℚ, (n : ℚ) * I.lam ≤ lam' ∧
          F (encCO I) =
            encCO ({ f := I.f, p := I.p, δ := I.δ, lam := lam' } : COInstance n) := by
  refine ⟨fun w => (ScaleLam.totalSem n (ScaleLam.St.init w)).out, ?_, ?_⟩
  · obtain ⟨A, d, hAd⟩ := ScaleLam.bTotal_poly n
    obtain ⟨k, hk⟩ := CookPvsNP.polynomial_absorb A d 0
    apply CookPvsNP.stack_program_polytime (ScaleLam.totalP n) ScaleLam.Stk.inp ScaleLam.Stk.out _ k
    intro w
    have hPA : ScaleLam.PA w.length (ScaleLam.St.init w) :=
      ⟨by simp [ScaleLam.St.init], rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨-, t, ht, hexec⟩ := ScaleLam.total_impl n w.length (ScaleLam.St.init w) hPA
    refine ⟨(ScaleLam.totalSem n (ScaleLam.St.init w)).store, t, ?_, ?_, rfl⟩
    · have h1 := hAd w.length
      have h2 := hk w.length
      exact le_trans ht (le_trans h1 (by simpa using h2))
    · have e : (fun j => if j = ScaleLam.Stk.inp then w else []) = (ScaleLam.St.init w).store := by
        funext j
        cases j <;> rfl
      rw [e]
      exact hexec
  · intro I hI
    exact ⟨_, ScaleLam.lam_bound n n I hI.2.2.2, ScaleLam.total_valid n n I⟩
