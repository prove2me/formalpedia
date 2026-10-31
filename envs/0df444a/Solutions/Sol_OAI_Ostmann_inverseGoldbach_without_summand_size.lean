-- Prove2me | solution 1 for OAI.Ostmann.inverseGoldbach_without_summand_size
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:43:08.456837+00:00
-- url     : https://prove2.me/submissions/622f5953-296f-471a-8459-dad24545fa9d

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D006
import Theorems.Thm_OAI_Ostmann_inverseGoldbach_of_published
import Theorems.Thm_OAI_Ostmann_publishedSummandSizeBound

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiTwoPoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary two-point estimate for the required Bonami bound -/

namespace Ostmann

open Finset
open scoped BigOperators

theorem bonami_choose_bound (l j : ℕ) (hl : 0 < l) :
    (2 * l).choose (2 * j) ≤ l.choose j * (2 * l - 1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hj : j + 1 ≤ l
    · have hstep1 := Nat.choose_succ_right_eq (2 * l) (2 * j + 1)
      have hstep2 := Nat.choose_succ_right_eq (2 * l) (2 * j)
      have hsmall := Nat.choose_succ_right_eq l j
      have heven : 2 * l - 2 * j = 2 * (l - j) := by omega
      have hodd : 2 * l - (2 * j + 1) ≤ (2 * l - 1) * (2 * j + 1) := by
        have hone : 1 ≤ 2 * j + 1 := by omega
        have hmono := Nat.mul_le_mul_left (2 * l - 1) hone
        omega
      have hid : (2 * l).choose (2 * (j + 1)) * (2 * j + 2) * (2 * j + 1) =
          (2 * l).choose (2 * j) * (2 * (l - j)) * (2 * l - (2 * j + 1)) := by
        calc
          _ = ((2 * l).choose (2 * j + 1) * (2 * l - (2 * j + 1))) *
              (2 * j + 1) := by rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, hstep1]
          _ = ((2 * l).choose (2 * j + 1) * (2 * j + 1)) *
              (2 * l - (2 * j + 1)) := by ring
          _ = _ := by rw [hstep2, heven]
      have hbound : (2 * l).choose (2 * (j + 1)) * ((2 * j + 2) * (2 * j + 1)) ≤
          (l.choose (j + 1) * (2 * l - 1) ^ (j + 1)) *
            ((2 * j + 2) * (2 * j + 1)) := by
        calc
          _ = (2 * l).choose (2 * j) * (2 * (l - j)) *
              (2 * l - (2 * j + 1)) := by rw [← Nat.mul_assoc, hid]
          _ ≤ (l.choose j * (2 * l - 1) ^ j) * (2 * (l - j)) *
              ((2 * l - 1) * (2 * j + 1)) := by gcongr
          _ = (l.choose j * (l - j)) * (2 * l - 1) ^ (j + 1) *
              (2 * (2 * j + 1)) := by rw [pow_succ]; ring
          _ = _ := by rw [← hsmall]; ring
      exact Nat.le_of_mul_le_mul_right hbound (by positivity)
    · rw [Nat.choose_eq_zero_of_lt (by omega : 2 * l < 2 * (j + 1))]
      exact Nat.zero_le _

private theorem sum_range_double (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range (2 * n), f i) = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

private theorem even_power_binomial (x y : ℝ) (l : ℕ) :
    ((x + y) ^ (2 * l) + (x - y) ^ (2 * l)) / 2 =
      ∑ j ∈ range (l + 1), y ^ (2 * j) * x ^ (2 * (l - j)) *
        ((2 * l).choose (2 * j) : ℝ) := by
  have hsum : (x + y) ^ (2 * l) + (x - y) ^ (2 * l) =
      ∑ i ∈ range (2 * l + 1),
        (y ^ i + (-y) ^ i) * x ^ (2 * l - i) * ((2 * l).choose i : ℝ) := by
    rw [show x + y = y + x by ring, show x - y = -y + x by ring,
      add_pow, add_pow, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum, sum_range_succ, sum_range_double, sum_range_succ]
  have heven (j : ℕ) : (-y) ^ (2 * j) = y ^ (2 * j) := by
    rw [pow_mul, neg_sq, ← pow_mul]
  have hodd (j : ℕ) : (-y) ^ (2 * j + 1) = -(y ^ (2 * j + 1)) := by
    rw [pow_succ, pow_succ, heven]
    ring
  simp_rw [heven, hodd, add_neg_cancel, zero_mul, add_zero]
  have hsub : ∀ j ∈ range l, 2 * l - 2 * j = 2 * (l - j) := by
    intro j hj
    omega
  have hrew : (∑ j ∈ range l,
      (y ^ (2 * j) + y ^ (2 * j)) * x ^ (2 * l - 2 * j) *
        ((2 * l).choose (2 * j) : ℝ)) =
      2 * ∑ j ∈ range l, y ^ (2 * j) * x ^ (2 * (l - j)) *
        ((2 * l).choose (2 * j) : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hsub j hj]
    ring
  rw [hrew]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
  ring

/-- Bonami's required even-moment inequality on one Boolean coordinate. -/
theorem bonami_two_point (x y : ℝ) (l : ℕ) (hl : 0 < l) :
    (|x + y| ^ (2 * l) + |x - y| ^ (2 * l)) / 2 ≤
      (x ^ 2 + (2 * l - 1 : ℕ) * y ^ 2) ^ l := by
  have he (z : ℝ) (n : ℕ) : 0 ≤ z ^ (2 * n) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  rw [← abs_pow, ← abs_pow, abs_of_nonneg (he _ _),
    abs_of_nonneg (he _ _), even_power_binomial]
  rw [show x ^ 2 + ((2 * l - 1 : ℕ) : ℝ) * y ^ 2 =
    ((2 * l - 1 : ℕ) : ℝ) * y ^ 2 + x ^ 2 by ring, add_pow]
  apply sum_le_sum
  intro j hj
  have hc : ((2 * l).choose (2 * j) : ℝ) ≤
      (l.choose j : ℝ) * ((2 * l - 1 : ℕ) : ℝ) ^ j := by
    exact_mod_cast bonami_choose_bound l j hl
  calc
    _ ≤ y ^ (2 * j) * x ^ (2 * (l - j)) *
        ((l.choose j : ℝ) * ((2 * l - 1 : ℕ) : ℝ) ^ j) := by
      exact mul_le_mul_of_nonneg_left hc (mul_nonneg (he _ _) (he _ _))
    _ = _ := by simp only [mul_pow, pow_mul]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite moment interpolation for the Boolean-cube induction -/

namespace Ostmann

open Finset
open scoped BigOperators

private theorem sum_add_pow_bound_pos {ι : Type*} (s : Finset ι)
    (u v : ι → ℝ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) (l : ℕ)
    (hU : (∑ i ∈ s, u i ^ l) ≤ s.card * A ^ l)
    (hV : (∑ i ∈ s, v i ^ l) ≤ s.card * B ^ l) :
    (∑ i ∈ s, (u i + v i) ^ l) ≤ s.card * (A + B) ^ l := by
  have hAB : 0 < A + B := add_pos hA hB
  have hweights : A / (A + B) + B / (A + B) = 1 := by field_simp
  have hpoint (i : ι) (hi : i ∈ s) :
      ((u i + v i) / (A + B)) ^ l ≤
        A / (A + B) * (u i / A) ^ l + B / (A + B) * (v i / B) ^ l := by
    have h := (convexOn_pow l).2 (div_nonneg (hu i hi) hA.le)
      (div_nonneg (hv i hi) hB.le)
      (div_nonneg hA.le hAB.le) (div_nonneg hB.le hAB.le) hweights
    dsimp only [smul_eq_mul] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    field_simp
  have hsum : (∑ i ∈ s, (u i + v i) ^ l) / (A + B) ^ l ≤
      A / (A + B) * ((∑ i ∈ s, u i ^ l) / A ^ l) +
        B / (A + B) * ((∑ i ∈ s, v i ^ l) / B ^ l) := by
    calc
      _ = ∑ i ∈ s, ((u i + v i) / (A + B)) ^ l := by
        simp only [div_pow, sum_div]
      _ ≤ ∑ i ∈ s, (A / (A + B) * (u i / A) ^ l +
          B / (A + B) * (v i / B) ^ l) := sum_le_sum hpoint
      _ = _ := by simp only [div_pow, sum_add_distrib, ← mul_sum, sum_div]
  have hUA : (∑ i ∈ s, u i ^ l) / A ^ l ≤ s.card :=
    (div_le_iff₀ (pow_pos hA l)).mpr hU
  have hVB : (∑ i ∈ s, v i ^ l) / B ^ l ≤ s.card :=
    (div_le_iff₀ (pow_pos hB l)).mpr hV
  apply (div_le_iff₀ (pow_pos hAB l)).mp
  calc
    _ ≤ A / (A + B) * ((∑ i ∈ s, u i ^ l) / A ^ l) +
        B / (A + B) * ((∑ i ∈ s, v i ^ l) / B ^ l) := hsum
    _ ≤ A / (A + B) * s.card + B / (A + B) * s.card := by
      exact add_le_add (mul_le_mul_of_nonneg_left hUA (div_nonneg hA.le hAB.le))
        (mul_le_mul_of_nonneg_left hVB (div_nonneg hB.le hAB.le))
    _ = s.card := by rw [← add_mul, hweights, one_mul]

private theorem eq_zero_of_sum_pow_le_zero {ι : Type*} (s : Finset ι)
    (u : ι → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i) (l : ℕ)
    (hU : (∑ i ∈ s, u i ^ l) ≤ 0) : ∀ i ∈ s, u i = 0 := by
  intro i hi
  have hterm := (single_le_sum (fun j hj => pow_nonneg (hu j hj) l) hi).trans hU
  by_contra hn
  exact (not_le_of_gt (pow_pos (lt_of_le_of_ne (hu i hi) (Ne.symm hn)) l)) hterm

/-- The finite-sum form needed for tensorization, with no analytic limits. -/
theorem sum_add_pow_bound {ι : Type*} (s : Finset ι)
    (u v : ι → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) (l : ℕ) (hl : 0 < l)
    (hU : (∑ i ∈ s, u i ^ l) ≤ s.card * A ^ l)
    (hV : (∑ i ∈ s, v i ^ l) ≤ s.card * B ^ l) :
    (∑ i ∈ s, (u i + v i) ^ l) ≤ s.card * (A + B) ^ l := by
  rcases eq_or_lt_of_le hA with hA | hA
  · subst A
    have hzero : ∀ i ∈ s, u i = 0 := eq_zero_of_sum_pow_le_zero s u hu l (by
      simpa only [zero_pow (Nat.ne_of_gt hl), mul_zero] using hU)
    have hid : (∑ i ∈ s, (u i + v i) ^ l) = ∑ i ∈ s, v i ^ l := by
      apply sum_congr rfl
      intro i hi
      rw [hzero i hi, zero_add]
    rw [hid, zero_add]
    exact hV
  rcases eq_or_lt_of_le hB with hB | hB
  · subst B
    have hzero : ∀ i ∈ s, v i = 0 := eq_zero_of_sum_pow_le_zero s v hv l (by
      simpa only [zero_pow (Nat.ne_of_gt hl), mul_zero] using hV)
    have hid : (∑ i ∈ s, (u i + v i) ^ l) = ∑ i ∈ s, u i ^ l := by
      apply sum_congr rfl
      intro i hi
      rw [hzero i hi, add_zero]
    rw [hid, add_zero]
    exact hU
  exact sum_add_pow_bound_pos s u v A B hA hB hu hv l hU hV

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiCube
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete finite Boolean polynomials for Bonami's inequality -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

theorem booleanEnergy_nonneg {α : Type*} [Fintype α]
    (r : ℝ) (hr : 0 ≤ r) (a : (α → Bool) → ℝ) : 0 ≤ booleanEnergy r a := by
  apply sum_nonneg
  intro b hb
  apply mul_nonneg _ (sq_nonneg _)
  exact prod_nonneg (fun i hi => by split <;> positivity)

theorem booleanPolynomial_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (a : (β → Bool) → ℝ) (ε : β → Bool) :
    booleanPolynomial a ε =
      booleanPolynomial (fun b : α → Bool => a (fun i => b (e.symm i)))
        (fun i => ε (e i)) := by
  unfold booleanPolynomial
  rw [← (Equiv.arrowCongr e (Equiv.refl Bool)).sum_comp]
  apply sum_congr rfl
  intro b hb
  congr 1
  rw [← e.prod_comp]
  simp [Equiv.arrowCongr]

theorem booleanEnergy_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (r : ℝ) (a : (β → Bool) → ℝ) :
    booleanEnergy r a =
      booleanEnergy r (fun b : α → Bool => a (fun i => b (e.symm i))) := by
  unfold booleanEnergy
  rw [← (Equiv.arrowCongr e (Equiv.refl Bool)).sum_comp]
  apply sum_congr rfl
  intro b hb
  congr 1
  rw [← e.prod_comp]
  simp [Equiv.arrowCongr]

theorem sum_option_cube {α : Type*} [Fintype α] (f : (Option α → Bool) → ℝ) :
    (∑ b : Option α → Bool, f b) =
      (∑ b : α → Bool, f (fun i => i.elim true b)) +
        ∑ b : α → Bool, f (fun i => i.elim false b) := by
  calc
    _ = ∑ z : Bool × (α → Bool),
        f ((Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)).symm z) :=
      ((Equiv.piOptionEquivProd (β := fun _ : Option α => Bool)).symm.sum_comp f).symm
    _ = ∑ x : Bool, ∑ b : α → Bool, f (fun i => i.elim x b) := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro b hb
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := Fintype.sum_bool _

theorem booleanPolynomial_option {α : Type*} [Fintype α]
    (a : (Option α → Bool) → ℝ) (ε : Option α → Bool) :
    booleanPolynomial a ε =
      booleanPolynomial (fun b => a (fun i => i.elim false b)) (fun i => ε (some i)) +
        (if ε none then 1 else -1) *
          booleanPolynomial (fun b => a (fun i => i.elim true b)) (fun i => ε (some i)) := by
  unfold booleanPolynomial
  have hs := sum_option_cube (fun b : Option α → Bool =>
    a b * ∏ i : Option α, if b i then (if ε i then 1 else -1) else 1)
  have hp : ∀ f : Option α → ℝ, (∏ i, f i) = f none * ∏ i : α, f (some i) :=
    fun f => Fintype.prod_option f
  simp only [finite_univ_canonical] at hs ⊢
  simp only [finite_univ_canonical] at hp
  rw [hs]
  simp only [hp, Option.elim, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  ac_rfl

theorem booleanEnergy_option {α : Type*} [Fintype α]
    (r : ℝ) (a : (Option α → Bool) → ℝ) :
    booleanEnergy r a =
      booleanEnergy r (fun b => a (fun i => i.elim false b)) +
        r * booleanEnergy r (fun b => a (fun i => i.elim true b)) := by
  unfold booleanEnergy
  have hs := sum_option_cube (fun b : Option α → Bool =>
    (∏ i : Option α, if b i then r else 1) * (a b) ^ 2)
  have hp : ∀ f : Option α → ℝ, (∏ i, f i) = f none * ∏ i : α, f (some i) :=
    fun f => Fintype.prod_option f
  simp only [finite_univ_canonical] at hs ⊢
  simp only [finite_univ_canonical] at hp
  rw [hs]
  simp only [hp, Option.elim, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  simp only [mul_assoc]
  rw [add_comm]
  congr 3

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiTensor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensorizing the two-point Bonami estimate on a finite cube -/

namespace Ostmann

open Finset
open scoped Classical BigOperators

universe u

theorem booleanMoment_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (l : ℕ) (a : (β → Bool) → ℝ) :
    booleanMoment l a =
      booleanMoment l (fun b : α → Bool => a (fun i => b (e.symm i))) := by
  unfold booleanMoment
  rw [← (Equiv.arrowCongr e (Equiv.refl Bool)).sum_comp]
  apply sum_congr rfl
  intro ε hε
  rw [booleanPolynomial_reindex e]
  simp [Equiv.arrowCongr]

theorem booleanMoment_option {α : Type*} [Fintype α]
    (l : ℕ) (a : (Option α → Bool) → ℝ) :
    booleanMoment l a =
      ∑ ε : α → Bool,
        (|booleanPolynomial (fun b => a (fun i => i.elim false b)) ε +
          booleanPolynomial (fun b => a (fun i => i.elim true b)) ε| ^ (2 * l) +
        |booleanPolynomial (fun b => a (fun i => i.elim false b)) ε -
          booleanPolynomial (fun b => a (fun i => i.elim true b)) ε| ^ (2 * l)) := by
  unfold booleanMoment
  have hs := sum_option_cube (fun ε : Option α → Bool =>
    |booleanPolynomial a ε| ^ (2 * l))
  simp only [finite_univ_canonical] at hs ⊢
  rw [hs, ← sum_add_distrib]
  apply sum_congr rfl
  intro ε hε
  simp only [booleanPolynomial_option, Option.elim, Bool.false_eq_true,
    ↓reduceIte, one_mul, neg_one_mul, sub_eq_add_neg]

/-- The exact weighted even-moment bound for arbitrary finite Boolean cubes. -/
theorem booleanPolynomial_moment (l : ℕ) (hl : 0 < l)
    (α : Type u) [Fintype α] (a : (α → Bool) → ℝ) :
    booleanMoment l a ≤ (Fintype.card (α → Bool) : ℝ) *
      booleanEnergy ((2 * l - 1 : ℕ) : ℝ) a ^ l := by
  let r : ℝ := ((2 * l - 1 : ℕ) : ℝ)
  have hr : 0 ≤ r := Nat.cast_nonneg _
  revert a
  refine Fintype.induction_empty_option
    (P := fun β _ => ∀ a : (β → Bool) → ℝ,
      booleanMoment l a ≤ (Fintype.card (β → Bool) : ℝ) * booleanEnergy r a ^ l)
    ?_ ?_ ?_ α
  · intro β γ instγ e ih a
    let : Fintype β := Fintype.ofEquiv γ e.symm
    rw [booleanMoment_reindex e, booleanEnergy_reindex e]
    rw [← Fintype.card_congr (Equiv.arrowCongr e (Equiv.refl Bool))]
    exact ih _
  · intro a
    simp [booleanMoment, booleanPolynomial, booleanEnergy, pow_mul, sq_abs]
  · intro β instβ ih a
    let a0 : (β → Bool) → ℝ := fun b => a (fun i => i.elim false b)
    let a1 : (β → Bool) → ℝ := fun b => a (fun i => i.elim true b)
    let E0 := booleanEnergy r a0
    let E1 := booleanEnergy r a1
    have hE0 : 0 ≤ E0 := booleanEnergy_nonneg r hr a0
    have hE1 : 0 ≤ E1 := booleanEnergy_nonneg r hr a1
    have h0 : (∑ ε : β → Bool, (booleanPolynomial a0 ε ^ 2) ^ l) ≤
        (Fintype.card (β → Bool) : ℝ) * E0 ^ l := by
      simpa only [booleanMoment, pow_mul, sq_abs] using ih a0
    have h1 : (∑ ε : β → Bool, (r * booleanPolynomial a1 ε ^ 2) ^ l) ≤
        (Fintype.card (β → Bool) : ℝ) * (r * E1) ^ l := by
      have hi1 : (∑ ε : β → Bool, (booleanPolynomial a1 ε ^ 2) ^ l) ≤
          (Fintype.card (β → Bool) : ℝ) * E1 ^ l := by
        simpa only [booleanMoment, pow_mul, sq_abs] using ih a1
      have hh := mul_le_mul_of_nonneg_left hi1 (pow_nonneg hr l)
      simpa only [mul_pow, ← mul_sum, mul_assoc, mul_left_comm] using hh
    have hmean := sum_add_pow_bound (univ : Finset (β → Bool))
      (fun ε => booleanPolynomial a0 ε ^ 2)
      (fun ε => r * booleanPolynomial a1 ε ^ 2) E0 (r * E1)
      hE0 (mul_nonneg hr hE1) (fun _ _ => sq_nonneg _)
      (fun _ _ => mul_nonneg hr (sq_nonneg _)) l hl h0 h1
    have hpoint (ε : β → Bool) :
        |booleanPolynomial a0 ε + booleanPolynomial a1 ε| ^ (2 * l) +
          |booleanPolynomial a0 ε - booleanPolynomial a1 ε| ^ (2 * l) ≤
        2 * (booleanPolynomial a0 ε ^ 2 + r * booleanPolynomial a1 ε ^ 2) ^ l := by
      have hh := bonami_two_point (booleanPolynomial a0 ε) (booleanPolynomial a1 ε) l hl
      dsimp only [r]
      linarith
    calc
      booleanMoment l a = ∑ ε : β → Bool,
          (|booleanPolynomial a0 ε + booleanPolynomial a1 ε| ^ (2 * l) +
          |booleanPolynomial a0 ε - booleanPolynomial a1 ε| ^ (2 * l)) :=
        booleanMoment_option l a
      _ ≤ ∑ ε : β → Bool,
          2 * (booleanPolynomial a0 ε ^ 2 + r * booleanPolynomial a1 ε ^ 2) ^ l :=
        sum_le_sum (fun ε _ => hpoint ε)
      _ = 2 * ∑ ε : β → Bool,
          (booleanPolynomial a0 ε ^ 2 + r * booleanPolynomial a1 ε ^ 2) ^ l :=
        (mul_sum ..).symm
      _ ≤ 2 * ((Fintype.card (β → Bool) : ℝ) * (E0 + r * E1) ^ l) := by
        exact mul_le_mul_of_nonneg_left hmean (by norm_num)
      _ = (Fintype.card (Option β → Bool) : ℝ) * booleanEnergy r a ^ l := by
        rw [booleanEnergy_option]
        have hcard := Fintype.card_congr
          (Equiv.piOptionEquivProd (β := fun _ : Option β => Bool))
        rw [Fintype.card_prod, Fintype.card_bool] at hcard
        rw [hcard, Nat.cast_mul, Nat.cast_ofNat]
        change 2 * ((Fintype.card (β → Bool) : ℝ) * (E0 + r * E1) ^ l) =
          2 * (Fintype.card (β → Bool) : ℝ) * (E0 + r * E1) ^ l
        ring
    simp only [Fintype.card, finite_univ_canonical, le_refl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiInput
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharge of the published Bonami input

The finite even-moment specialization is proved here from the elementary
two-point inequality and finite convexity. No infinite-product theorem is
needed for the application.
-/

namespace Ostmann

open Finset
open scoped Classical BigOperators

theorem booleanPolynomial_eq_rademacher {P : Finset ℕ}
    (a : Finset P → ℝ) (ε : P → Bool) :
    booleanPolynomial (fun b => a (boolFinsetEquiv P b)) ε =
      ∑ Q : Finset P, a Q * rademacherMonomial Q ε := by
  unfold booleanPolynomial
  calc
    _ = ∑ b : P → Bool, a (boolFinsetEquiv P b) *
        rademacherMonomial (boolFinsetEquiv P b) ε := by
      simp only [finite_univ_canonical]
      apply sum_congr rfl
      intro b hb
      congr 1
      simp only [boolFinsetEquiv, Equiv.coe_fn_mk, rademacherMonomial, prod_filter]
      simp only [finite_univ_canonical]
    _ = _ := by
      simpa only [finite_univ_canonical] using
        (boolFinsetEquiv P).sum_comp (fun Q => a Q * rademacherMonomial Q ε)

theorem booleanEnergy_eq_finset {α : Type*} [Fintype α]
    (r : ℝ) (a : Finset α → ℝ) :
    booleanEnergy r (fun b => a (boolFinsetEquiv α b)) =
      ∑ Q : Finset α, r ^ Q.card * (a Q) ^ 2 := by
  unfold booleanEnergy
  calc
    _ = ∑ b : α → Bool, r ^ (boolFinsetEquiv α b).card *
        (a (boolFinsetEquiv α b)) ^ 2 := by
      apply sum_congr rfl
      intro b hb
      congr 1
      rw [← prod_const]
      simp only [boolFinsetEquiv, Equiv.coe_fn_mk, prod_filter]
    _ = _ := by
      simpa only [finite_univ_canonical] using
        (boolFinsetEquiv α).sum_comp (fun Q => r ^ Q.card * (a Q) ^ 2)

/-- The exact `p=2`, `q=2l` finite-cube specialization of Bonami is proved. -/
theorem publishedBonamiBound : PublishedBonamiBound := by
  intro P l hl a
  have h := booleanPolynomial_moment l hl P (fun b => a (boolFinsetEquiv P b))
  simp only [booleanMoment, booleanPolynomial_eq_rademacher, booleanEnergy_eq_finset] at h
  have hc : 0 < (Fintype.card (P → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [Fintype.card, finite_univ_canonical] at h hc ⊢
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SkewKernelSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite algebraic identity for the large-sieve kernel

This is the cancellation underlying Montgomery--Vaughan's equation (3.6).
The diagonal correction is retained explicitly before any norm estimate.
-/

namespace Ostmann

open scoped BigOperators

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

 theorem skew_kernel_square_entry (h k : ι → ι → K)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (∑ r, h r s * h r t) =
      (if s = t then ∑ r, h r s ^ 2 else 0) +
        h s t * ((∑ r, k r s) - ∑ r, k r t) + 2 * h s t * k s t := by
  by_cases hst : s = t
  · subst t
    simp [hdiag, sq]
  · have he (r : ι) : h r s * h r t = h s t * (k r s - k r t) +
        (if r = s then h s t * k s t else 0) +
        (if r = t then h s t * k s t else 0) := by
      by_cases hrs : r = s
      · subst r
        simp [hdiag, kdiag, hst]
      · by_cases hrt : r = t
        · subst r
          rw [hdiag, kdiag, kskew t s]
          simp only [hrs, ↓reduceIte]
          ring
        · simp only [hrs, hrt, ↓reduceIte, add_zero]
          exact htriple r s t hrs hrt hst
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hst, ↓reduceIte, zero_add, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OrdinaryPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary prime interval and its normalization

The conductor-one character is trivial, so the ordinary prime prior has
no Page correction. Its logarithmic interval mass and inverse bound are
derived from the same published theta input.
-/

namespace Ostmann

open Filter MeasureTheory

theorem PublishedProgressionInput.localZero_one (P : PublishedProgressionInput) :
    P.localZero 1 = none := by
  cases he : P.localZero 1 with
  | none => rfl
  | some e => exact False.elim (e.modulus_ne_one (Nat.dvd_one.mp (P.divides 1 e he)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrimePowerRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing higher prime powers from the fixed smooth mean -/
namespace Ostmann
open scoped Classical BigOperators

 theorem primeMeanTest_nat_support (X : ℝ) (hX : 0 < X) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) : primeMeanTest (n / X) = 0 := by
  apply primeMeanTest_zero_outside
  intro h
  apply hn
  rw [Finset.mem_Ioc]
  constructor
  · by_contra hz
    have : n = 0 := by omega
    subst n
    norm_num at h
  · apply (Nat.le_floor_iff hX.le).mpr
    have hh := (div_le_iff₀ hX).mp h.2
    linarith

 theorem smoothMangoldtMean_eq_sum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean q χ X = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * primeMeanTest (n / X) := by
  apply tsum_eq_sum
  intro n hn
  rw [primeMeanTest_nat_support X hX n hn, Complex.ofReal_zero, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensFromFirst
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded second Mertens estimate from the first

Only bounded error is needed in the Ostmann application. Partial summation
therefore makes the second prime-sum input a consequence of the first.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

theorem MertensEstimate.floor_error {C : ℝ} (hM : MertensEstimate C)
    {t : ℝ} (ht : 2 ≤ t) :
    |(∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t| ≤
      C + Real.log 2 := by
  have hf : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hf0 : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
  have ht0 : 0 < t := by linarith
  have hhalf : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor t
    linarith
  have hlo := Real.log_le_log (show 0 < t / 2 by positivity) hhalf
  rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlo
  have hhi := Real.log_le_log hf0 (Nat.floor_le ht0.le)
  have hM' := abs_le.mp (hM _ hf)
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

private theorem sum_logPrimeCoefficient (Q : ℕ) :
    (∑ n ∈ Icc 0 Q, logPrimeCoefficient n) =
      ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p := by
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  rfl

private theorem sum_inv_log_mul_logPrimeCoefficient (Q : ℕ) :
    (∑ n ∈ Icc 0 Q, (Real.log (n : ℝ))⁻¹ * logPrimeCoefficient n) =
      ∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹ := by
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  apply sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [logPrimeCoefficient, hp, ↓reduceIte]
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    field_simp
  · simp [logPrimeCoefficient, hp]

private theorem inv_log_differentiable {t : ℝ} (ht : 1 < t) :
    DifferentiableAt ℝ (fun x : ℝ => (Real.log x)⁻¹) t := by
  exact (Real.differentiableAt_log (by linarith)).inv (Real.log_pos ht).ne'

private theorem inv_log_deriv_continuous (Q : ℕ) :
    ContinuousOn (deriv (fun x : ℝ => (Real.log x)⁻¹)) (Set.Icc 2 Q) := by
  simp only [Real.deriv_inv_log]
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

/-- Partial summation for precisely the two prime weights used downstream. -/
theorem prime_reciprocal_partial_summation (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) =
      (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) / Real.log Q +
      ∫ t in (2 : ℝ)..Q,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
          (t⁻¹ / Real.log t ^ 2) := by
  have hid := sum_mul_eq_sub_integral_mul₁ logPrimeCoefficient
    (by norm_num [logPrimeCoefficient]) (by norm_num [logPrimeCoefficient]) (Q : ℝ)
    (f := fun x : ℝ => (Real.log x)⁻¹)
    (fun t ht => inv_log_differentiable (by linarith [ht.1]))
    (inv_log_deriv_continuous Q).integrableOn_Icc
  rw [Nat.floor_natCast, sum_inv_log_mul_logPrimeCoefficient,
    sum_logPrimeCoefficient] at hid
  simp_rw [Real.deriv_inv_log, sum_logPrimeCoefficient] at hid
  rw [← intervalIntegral.integral_of_le (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)] at hid
  have hfun : (fun t : ℝ => -t⁻¹ / Real.log t ^ 2 *
      ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) =
      fun t : ℝ => -((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
        (t⁻¹ / Real.log t ^ 2)) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_neg] at hid
  simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hid

private theorem mertens_kernel_continuous (Q : ℕ) :
    ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.Icc 2 Q) := by
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

private theorem mertens_weighted_sum_integrable (Q : ℕ) (hQ : 2 ≤ Q) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
        (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)]
  have h := integrableOn_mul_sum_Icc logPrimeCoefficient (m := 0)
    (show (0 : ℝ) ≤ 2 by norm_num) (mertens_kernel_continuous Q).integrableOn_Icc
  simpa only [sum_logPrimeCoefficient, mul_comm] using h

private theorem mertens_log_kernel_continuous (Q : ℕ) :
    ContinuousOn (fun t : ℝ => Real.log t * (t⁻¹ / Real.log t ^ 2))
      (Set.Icc 2 Q) := by
  fun_prop (disch := grind [Real.log_pos, ne_of_gt])

private theorem mertens_log_kernel_integral (Q : ℕ) (hQ : 2 ≤ Q) :
    (∫ t in (2 : ℝ)..Q, Real.log t * (t⁻¹ / Real.log t ^ 2)) =
      Real.log (Real.log Q) - Real.log (Real.log 2) := by
  rw [← integral_inv_div_log (by norm_num : (1 : ℝ) < 2)
    (show (1 : ℝ) < Q by exact_mod_cast (show 1 < Q by omega))]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht2 : 2 ≤ t := (Set.uIcc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ) ▸ ht).1
  have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp

private theorem mertens_error_integral_bound {C : ℝ} (hM : MertensEstimate C)
    (Q : ℕ) (hQ : 2 ≤ Q) :
    |∫ t in (2 : ℝ)..Q,
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)| ≤ (C + Real.log 2) / Real.log 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hM 1 le_rfl)
  have hD : 0 ≤ C + Real.log 2 := add_nonneg hC (Real.log_nonneg (by norm_num))
  have hk : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_kernel_continuous Q).integrableOn_Icc
  have hl : IntervalIntegrable (fun t : ℝ => Real.log t *
      (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_log_kernel_continuous Q).integrableOn_Icc
  have he : IntervalIntegrable (fun t : ℝ =>
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    simpa only [sub_mul] using (mertens_weighted_sum_integrable Q hQ).sub hl
  calc
    _ ≤ ∫ t in (2 : ℝ)..Q,
        |((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
          (t⁻¹ / Real.log t ^ 2)| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm hQR (f := fun t : ℝ =>
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)))
    _ ≤ ∫ t in (2 : ℝ)..Q, (C + Real.log 2) * (t⁻¹ / Real.log t ^ 2) := by
      apply intervalIntegral.integral_mono_on hQR he.norm (hk.const_mul _)
      intro t ht
      have hk0 : 0 ≤ t⁻¹ / Real.log t ^ 2 :=
        div_nonneg (inv_nonneg.mpr (by linarith [ht.1])) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
      exact mul_le_mul_of_nonneg_right (hM.floor_error ht.1) hk0
    _ = (C + Real.log 2) * ((Real.log 2)⁻¹ - (Real.log Q)⁻¹) := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_div_log_sq (by norm_num : (1 : ℝ) < 2)
          (show (1 : ℝ) < Q by exact_mod_cast (show 1 < Q by omega))]
    _ ≤ (C + Real.log 2) / Real.log 2 := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ hD
      have : 0 ≤ (Real.log (Q : ℝ))⁻¹ :=
        inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega)))
      linarith

/-- The bounded-error second theorem follows from the first; no second
independent Mertens hypothesis is needed by the conditional main theorem. -/
theorem MertensEstimate.harmonic {C : ℝ} (hM : MertensEstimate C) :
    MertensHarmonicEstimate
      (|1 - Real.log (Real.log 2)| + (2 * C + Real.log 2) / Real.log 2) := by
  intro Q hQ
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hlogle : Real.log 2 ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by norm_num) hQR
  have hC : 0 ≤ C := (abs_nonneg _).trans (hM 1 le_rfl)
  have hl : IntervalIntegrable (fun t : ℝ => Real.log t *
      (t⁻¹ / Real.log t ^ 2)) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    exact (mertens_log_kernel_continuous Q).integrableOn_Icc
  have hei : (∫ t in (2 : ℝ)..Q,
      ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
        (t⁻¹ / Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..Q,
        (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) *
          (t⁻¹ / Real.log t ^ 2)) -
        (Real.log (Real.log Q) - Real.log (Real.log 2)) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (mertens_weighted_sum_integrable Q hQ) hl,
      mertens_log_kernel_integral Q hQ]
  have hid : (∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) - Real.log (Real.log Q) =
      (1 - Real.log (Real.log 2)) +
        ((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q) / Real.log Q +
        (∫ t in (2 : ℝ)..Q,
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)) := by
    rw [hei, prime_reciprocal_partial_summation Q hQ]
    field_simp
    ring
  have hendpoint : |((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) -
      Real.log Q) / Real.log Q| ≤ C / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogQ]
    exact (div_le_div_of_nonneg_right (hM Q (by omega)) hlogQ.le).trans
      (div_le_div_of_nonneg_left hC hlog2 hlogle)
  rw [hid]
  calc
    _ ≤ |1 - Real.log (Real.log 2)| +
        |((∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q) / Real.log Q| +
        |∫ t in (2 : ℝ)..Q,
          ((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ) / p) - Real.log t) *
            (t⁻¹ / Real.log t ^ 2)| := (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |1 - Real.log (Real.log 2)| + C / Real.log 2 +
        (C + Real.log 2) / Real.log 2 := by
      exact add_le_add (add_le_add le_rfl hendpoint)
        (mertens_error_integral_bound hM Q hQ)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightArchimedean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Gamma and zeta-pole errors in the low-height rectangle -/

namespace Ostmann

open Complex Set

/-- The pole remainder is uniformly bounded even when the evaluation point
approaches one through the complex low-height rectangle. -/
theorem vonMangoldt_low_height_pole_error : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s - (s - 1)⁻¹‖ ≤ C := by
  let F := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (0 : ZMod 1)
  let K : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Icc (-2 : ℝ) 2
  have hc : ContinuousOn F K :=
    (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (0 : ZMod 1)).mono
      (fun _ hs => hs.1.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro s hs hs' hi
  have hunit : IsUnit (0 : ZMod 1) := by
    rw [Subsingleton.elim (0 : ZMod 1) 1]
    exact isUnit_one
  have he := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux hunit hs
  rw [residue_one_eq_vonMangoldt] at he
  simp only [Nat.totient_one, Nat.cast_one, inv_one, one_div] at he
  change F s = _ at he
  rw [← he]
  exact (hC s ⟨⟨hs.le, hs'⟩, abs_le.mp hi⟩).trans (by linarith [le_abs_self C])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightZeroBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual zero sums and bounded low-height errors -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem exists_low_height_vonMangoldt_upper : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤
        realZeroKernel (s.re - 1) s.im + C := by
  obtain ⟨C, hC, hb⟩ := vonMangoldt_low_height_pole_error
  refine ⟨C, hC, ?_⟩
  intro s hs hs2 hi
  have hh := (Complex.re_le_norm _).trans (hb s hs hs2 hi)
  rw [Complex.sub_re] at hh
  have he : ((s - 1)⁻¹).re = realZeroKernel (s.re - 1) s.im := by
    simpa using realZeroKernel_complex_sub s 1
  rw [he] at hh
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightShiftedBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The shifted zero-sum bound from trigonometric positivity -/

namespace Ostmann

open Complex

/-- The coefficient three on the real pole, and the separate doubled-height
pole, give the strict inequality needed to exclude a nonreal exceptional zero. -/
theorem exists_low_height_shifted_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (σ t : ℝ), 1 < σ → σ ≤ 2 → |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ ((σ : ℂ) + (t : ℂ) * I) ≤
        3 / (σ - 1) + realZeroKernel (σ - 1) (2 * t) +
          2 * Real.log χ.modulus + C := by
  obtain ⟨G, hG, hg⟩ := exists_low_height_zero_sum_error
  obtain ⟨V, hV, hv⟩ := exists_low_height_vonMangoldt_upper
  refine ⟨4 * G + 4 * V, by positivity, ?_⟩
  intro χ σ t hσ hσ2 ht
  have ht2 : |2 * t| ≤ 2 := by rw [abs_mul]; norm_num; linarith
  have hzero := hg χ ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
    (by simpa using hσ2) (by simpa using ht.trans (by norm_num : (1 : ℝ) ≤ 2))
  have hreal := hv (σ : ℂ) hσ hσ2 (by simp)
  have hdouble := hv ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ)
    (by simpa using hσ2) (by simpa using ht2)
  have hp := real_character_trigonometric_sum_nonneg χ σ t hσ
  have he := χ.asComplex.mangoldt_LSeries_eq ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeries (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ)) _ = _ at he
  rw [PrimitiveRealCharacter.asComplex_L] at he
  rw [he, neg_div, Complex.neg_re] at hp
  have hk : realZeroKernel (σ - 1) 0 = 1 / (σ - 1) := by
    unfold realZeroKernel
    field_simp [sub_ne_zero.mpr hσ.ne']
    ring
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero, sub_zero] at hdouble hreal
  rw [hk] at hreal
  rw [logDeriv_apply] at hzero
  simp only [div_eq_mul_inv] at *
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightZeroExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local exceptional-zero argument with explicit margins -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

theorem near_zero_small_height (χ : PrimitiveRealCharacter) (δ S : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : δ * (2 * Real.log χ.modulus + S) ≤ 1 / 10)
    (hupper : ∀ t : ℝ, |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + 2 * Real.log χ.modulus + S)
    (i : ℕ) (hi : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re)
    (hiy : |((realCharacterActualZeros χ).zeros i).im| ≤ 1) :
    |((realCharacterActualZeros χ).zeros i).im| < δ / 2 := by
  by_contra hy
  let ρ := (realCharacterActualZeros χ).zeros i
  let a : ℝ := 1 + δ - ρ.re
  let s : ℂ := ((1 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I
  have ha : δ ≤ a := by dsimp [a, ρ]; linarith [((realCharacterActualZeros χ).in_strip i).2]
  have ha' : a ≤ (21 / 20) * δ := by dsimp [a, ρ]; linarith
  have hterm := shifted_real_zero_term_le χ s (by dsimp [s]; simp; linarith)
    (by dsimp [s]; simp; linarith) i
  have hdiff : s - (realCharacterActualZeros χ).zeros i = (a : ℂ) := by
    apply Complex.ext <;> simp [s, a, ρ]
  rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re] at hterm
  have hb := (mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 4)).trans (hupper ρ.im hiy)
  have hp := mul_le_mul_of_nonneg_left hb hδ.le
  have he : δ * (3 / δ + realZeroKernel δ (2 * ρ.im) + 2 * Real.log χ.modulus + S) =
      3 + δ * realZeroKernel δ (2 * ρ.im) + δ * (2 * Real.log χ.modulus + S) := by
    field_simp; ring
  rw [he] at hp
  have hm := real_zero_shifted_mass δ a hδ ha ha'
  have hk := real_zero_double_height_mass δ ρ.im hδ (le_of_not_gt hy)
  simp only [div_eq_mul_inv] at hm
  linarith

/-- The local inequalities force every exceptional low-height zero to be real,
and count multiplicities: two distinct indices are impossible. -/
theorem near_low_height_zeros_real_unique (χ : PrimitiveRealCharacter) (δ R S : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10)
    (hS : δ * (2 * Real.log χ.modulus + S) ≤ 1 / 10)
    (hreal : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (hshift : ∀ t : ℝ, |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + 2 * Real.log χ.modulus + S) :
    (∀ i, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ 1 →
      ((realCharacterActualZeros χ).zeros i).im = 0) ∧
    (∀ i j, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ 1 →
      |((realCharacterActualZeros χ).zeros j).im| ≤ 1 → i = j) := by
  have hsmall := near_zero_small_height χ δ S hδ hδ1 hS hshift
  have huniq := near_axis_zero_indices_unique χ δ R hδ hδ1 hR hreal
  constructor
  · intro i hi hiy
    obtain ⟨j, hj⟩ := realCharacterActualZeros_conjugate χ i
    have hjre : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re := by simpa [hj] using hi
    have hjim : |((realCharacterActualZeros χ).zeros j).im| ≤ δ / 2 := by
      simpa [hj] using (hsmall i hi hiy).le
    have hij := huniq i j hi hjre (hsmall i hi hiy).le hjim
    rw [← hij] at hj
    have hh := congrArg Complex.im hj
    simp only [Complex.conj_im] at hh
    linarith
  · intro i j hi hj hiy hjy
    exact huniq i j hi hj (hsmall i hi hiy).le (hsmall j hj hjy).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualRealZeroRegion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual low-height real-character zero-free region -/

namespace Ostmann

open Complex
open scoped Classical

/-- A single absolute zero-free constant works for every real primitive
character. Shrinking the progression constant will align the two inputs. -/
theorem exists_actual_real_low_height_region : ∃ κ : ℝ, 0 < κ ∧
    ∀ P : PublishedProgressionInput, P.kappa ≤ κ → ActualRealLowHeightRegion P := by
  obtain ⟨R, hR, hreal⟩ := exists_real_zero_sum_upper
  obtain ⟨S, hS, hshift⟩ := exists_low_height_shifted_bound
  let D : ℝ := R + S + 4
  have hD : 0 < D := by dsimp [D]; positivity
  let κ : ℝ := 1 / (2000 * D)
  refine ⟨κ, by dsimp [κ]; positivity, ?_⟩
  intro P hP χ Q hQ hq
  let H : ℝ := Real.log (4 * (Q : ℝ))
  have hQr : 2 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hH : 1 ≤ H := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 4 * (Q : ℝ))).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hHpos : 0 < H := by linarith
  have hlog : Real.log χ.modulus ≤ H := by
    apply Real.log_le_log (by exact_mod_cast χ.positive)
    have hh : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hq
    linarith
  let δ : ℝ := 1 / (100 * D * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity : 0 < 100 * D * H)).mpr
    have hh := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ D)
    dsimp [D] at *
    nlinarith
  have hRerr : δ * ((1 / 2) * Real.log χ.modulus + R) ≤ 1 / 10 := by
    rw [show δ * ((1 / 2) * Real.log χ.modulus + R) =
      ((1 / 2) * Real.log χ.modulus + R) / (100 * D * H) by dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hrh := mul_le_mul_of_nonneg_left hH hR.le
    have hsh := mul_nonneg hS.le hHpos.le
    dsimp [D]
    nlinarith
  have hSerr : δ * (2 * Real.log χ.modulus + S) ≤ 1 / 10 := by
    rw [show δ * (2 * Real.log χ.modulus + S) =
      (2 * Real.log χ.modulus + S) / (100 * D * H) by dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hsh := mul_le_mul_of_nonneg_left hH hS.le
    have hrh := mul_nonneg hR.le hHpos.le
    dsimp [D]
    nlinarith
  have hr : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤
      1 / δ + ((1 / 2) * Real.log χ.modulus + R) := by
    simpa only [add_sub_cancel_left, add_assoc] using
      hreal χ (1 + δ) (by linarith) (by linarith)
  have hs : ∀ t : ℝ, |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + 2 * Real.log χ.modulus + S := by
    intro t ht
    simpa only [add_sub_cancel_left] using
      hshift χ (1 + δ) t (by linarith) (by linarith) ht
  obtain ⟨hrealzero, huniq⟩ := near_low_height_zeros_real_unique χ δ
    ((1 / 2) * Real.log χ.modulus + R) S hδ hδ1 hRerr hSerr hr hs
  have hgap : P.kappa / H ≤ δ / 20 := by
    apply (div_le_div_of_nonneg_right hP hHpos.le).trans
    have he : κ / H = δ / 20 := by
      dsimp [κ, δ]
      field_simp
      ring
    exact he.le
  let E := ((realCharacterActualZeros χ).heightIndices 1).filter
    (fun i => 1 - P.kappa / H < ((realCharacterActualZeros χ).zeros i).re)
  have hmem (i : ℕ) : i ∈ E ↔ |((realCharacterActualZeros χ).zeros i).im| ≤ 1 ∧
      1 - P.kappa / H < ((realCharacterActualZeros χ).zeros i).re := by
    simp [E]
  refine ⟨E, Finset.card_le_one.mpr ?_, ?_, ?_⟩
  · intro i hi j hj
    have hi' := (hmem i).mp hi
    have hj' := (hmem j).mp hj
    exact huniq i j (by linarith [hi'.2]) (by linarith [hj'.2]) hi'.1 hj'.1
  · intro i hi
    have hi' := (hmem i).mp hi
    exact ⟨hrealzero i (by linarith [hi'.2]) hi'.1, hi'.2.le⟩
  · intro i hi him
    by_contra hb
    have him' : |((realCharacterActualZeros χ).zeros i).im| ≤ 1 := by
      nlinarith [sq_abs ((realCharacterActualZeros χ).zeros i).im,
        abs_nonneg ((realCharacterActualZeros χ).zeros i).im]
    exact hi ((hmem i).mpr ⟨him', lt_of_not_ge hb⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FullHeightRegionComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the conductor-height cutoffs with the published Page cutoff -/

namespace Ostmann

theorem conductor_height_log_ge_one (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    1 ≤ Real.log (2 * (Q : ℝ) * T) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 2 * (Q : ℝ) * T)).mpr
  have hh := mul_le_mul_of_nonneg_right hQr (by linarith : 0 ≤ T)
  exact Real.exp_one_lt_three.le.trans (by nlinarith)

theorem local_height_log_le (q Q : ℕ) (hq : 0 < q) (hqQ : q ≤ Q)
    (T : ℝ) (hT : 2 ≤ T) :
    Real.log q + Real.log (T + 2) + 1 ≤ 2 * Real.log (2 * (Q : ℝ) * T) := by
  have hQr : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ1 : 1 ≤ Q := (Nat.succ_le_iff.mpr hq).trans hqQ
  have hH := conductor_height_log_ge_one Q hQ1 T hT
  have hp : (q : ℝ) * (T + 2) ≤ 2 * (Q : ℝ) * T := by
    have hQpos : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_right hQr (by linarith : 0 ≤ T + 2)
    nlinarith
  have hl := Real.log_le_log (mul_pos hqp (by linarith : 0 < T + 2)) hp
  rw [Real.log_mul hqp.ne' (by linarith : T + 2 ≠ 0)] at hl
  linarith

theorem small_cutoff_fraction (a b U V : ℝ) (ha : 0 ≤ a) (hU : 0 < U) (hV : 0 < V)
    (hab : a ≤ b / 4) (hUV : U ≤ 2 * V) : a / V ≤ b / (2 * U) := by
  apply (div_le_div_iff₀ hV (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hUV (by positivity : 0 ≤ 2 * a)
  have hh' := mul_le_mul_of_nonneg_right hab hV.le
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexRegionFromPage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complex zero-free input follows from the retained real Page input -/

namespace Ostmann

theorem complexZeroRegion_of_page (κ : ℝ) (hκ : 0 < κ)
    (hunique : ∀ Q : ℕ, 2 ≤ Q → ∀ e f : PrimitiveRealZero,
      e.modulus ≤ Q → f.modulus ≤ Q →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ e.beta →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ f.beta → e = f) :
    PublishedComplexZeroRegion actualCharacterZeros := by
  classical
  obtain ⟨cn, hcn, hn⟩ := exists_nonquadratic_zero_free_region
  obtain ⟨cr, hcr, hr⟩ := exists_full_height_real_region
  let c := min (cn / 4) (min (cr / 4) κ)
  have hc : 0 < c := lt_min (by positivity) (lt_min (by positivity) hκ)
  have hcnc : c ≤ cn / 4 := min_le_left _ _
  have hcrc : c ≤ cr / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcP : c ≤ κ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro Q hQ T hT
  let H := Real.log (2 * (Q : ℝ) * T)
  have hQ1 : 1 ≤ Q := by omega
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one (conductor_height_log_ge_one Q hQ1 T hT)
  have hconvert : ∀ (χ : PrimitiveComplexCharacter), χ.modulus ≤ Q → ∀ i : ℕ,
      |((actualCharacterZeros χ).zeros i).im| ≤ T →
      1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
      ∃ e : PrimitiveRealZero, e.modulus = χ.modulus ∧
        e.beta = ((actualCharacterZeros χ).zeros i).re ∧ e.asRealCharacter.asComplex = χ := by
    intro χ hχ i hi hnear
    let U := Real.log χ.modulus + Real.log (T + 2) + 1
    have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
    have ht : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    have hUp : 0 < U := by dsimp [U]; linarith
    have hUH : U ≤ 2 * H := local_height_log_le χ.modulus Q χ.positive hχ T hT
    have hsq : χ.character ^ 2 = 1 := by
      by_contra hsq
      let V := Real.log χ.modulus + Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) + 1
      have hVp : 0 < V := by
        have hl : 0 ≤ Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) :=
          Real.log_nonneg (by linarith [abs_nonneg ((actualCharacterZeros χ).zeros i).im])
        dsimp [V]
        linarith
      have hVU : V ≤ U := by
        have hl := Real.log_le_log (by positivity : 0 < |((actualCharacterZeros χ).zeros i).im| + 2)
          (show |((actualCharacterZeros χ).zeros i).im| + 2 ≤ T + 2 by linarith)
        dsimp [V, U]
        linarith
      have hcut := small_cutoff_fraction c cn U H hc.le hUp hHp hcnc hUH
      have hhalf : cn / (2 * U) < cn / U := by
        apply (div_lt_div_iff₀ (by positivity) hUp).mpr
        nlinarith
      have hmono : cn / U ≤ cn / V := by
        apply (div_le_div_iff₀ hUp hVp).mpr
        exact mul_le_mul_of_nonneg_left hVU hcn.le
      have hzero := hn χ hsq i
      change cn / V ≤ _ at hzero
      linarith
    have hcut := small_cutoff_fraction c cr U H hc.le hUp hHp hcrc hUH
    have hhalf : cr / (2 * U) ≤ cr / U := by
      apply (div_le_div_iff₀ (by positivity) hUp).mpr
      nlinarith
    have hnearR : 1 - cr / U ≤ ((actualCharacterZeros χ).zeros i).re := by linarith
    have him : ((realCharacterActualZeros (χ.asReal hsq)).zeros i).im = 0 :=
      (hr (χ.asReal hsq) T hT).1 i
        (by rw [realCharacterActualZeros, χ.asReal_asComplex hsq]; exact hi)
        (by
          change 1 - cr / U ≤ ((actualCharacterZeros (χ.asReal hsq).asComplex).zeros i).re
          rw [χ.asReal_asComplex hsq]
          exact hnearR)
    let e := (actualRealCharacterZeroExpansion (χ.asReal hsq)).realZero i him
    refine ⟨e, rfl, ?_, ?_⟩
    · change ((realCharacterActualZeros (χ.asReal hsq)).zeros i).re = _
      rw [realCharacterActualZeros, χ.asReal_asComplex hsq]
    · change ((actualRealCharacterZeroExpansion (χ.asReal hsq)).realZero i him).asRealCharacter.asComplex = χ
      rw [actualRealZero_asCharacter, PrimitiveComplexCharacter.asReal_asComplex]
  have hlog4 : 0 < Real.log (4 * (Q : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * Q))
  have hlogH : Real.log (4 * (Q : ℝ)) ≤ H := by
    apply Real.log_le_log (by positivity)
    have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
    nlinarith
  have hPage : c / H ≤ κ / Real.log (4 * (Q : ℝ)) := by
    apply (div_le_div_iff₀ hHp hlog4).mpr
    exact (mul_le_mul_of_nonneg_left hlogH hc.le).trans
      (mul_le_mul_of_nonneg_right hcP hHp.le)
  have huniq (χ ψ : PrimitiveComplexCharacter) (hχ : χ.modulus ≤ Q) (hψ : ψ.modulus ≤ Q)
      (i j : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T)
      (hj : |((actualCharacterZeros ψ).zeros j).im| ≤ T)
      (hni : 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re)
      (hnj : 1 - c / H ≤ ((actualCharacterZeros ψ).zeros j).re) : χ = ψ := by
    obtain ⟨e, heq, heb, heχ⟩ := hconvert χ hχ i hi hni
    obtain ⟨f, hfq, hfb, hfψ⟩ := hconvert ψ hψ j hj hnj
    have hef := hunique Q (by omega) e f (by simpa [heq] using hχ)
      (by simpa [hfq] using hψ) (by rw [heb]; linarith) (by rw [hfb]; linarith)
    exact heχ.symm.trans ((congrArg (fun e : PrimitiveRealZero => e.asRealCharacter.asComplex) hef).trans hfψ)
  by_cases hex : ∃ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q ∧ ∃ i : ℕ,
      |((actualCharacterZeros χ).zeros i).im| ≤ T ∧ 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re
  · obtain ⟨χ₀, hχ₀, i₀, hi₀, hn₀⟩ := hex
    refine ⟨some χ₀, ?_⟩
    intro χ hχ hne i hi
    by_contra hbad
    have hn : 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re := by linarith [lt_of_not_ge hbad]
    exact hne (congrArg some (huniq χ χ₀ hχ hχ₀ i i₀ hi hi₀ hn hn₀))
  · refine ⟨none, ?_⟩
    intro χ hχ _ i hi
    by_contra hbad
    exact hex ⟨χ, hχ, i, hi, by linarith [lt_of_not_ge hbad]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrincipalPartialSummation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed principal-character mean by partial summation

This identifies the literal smooth mean with a compactly supported integral
of the Chebyshev function, for use with the quantitative PNT.
-/

namespace Ostmann

open MeasureTheory Finset
open scoped Classical BigOperators Interval

theorem primeMeanTest_deriv_continuous : Continuous (deriv primeMeanTest) :=
  (primeMeanTest_contDiff (n := 1)).continuous_deriv_one

theorem primeMeanTest_deriv_zero_outside (t : ℝ)
    (ht : t ∉ Set.Icc (5 / 8 : ℝ) (7 / 8)) : deriv primeMeanTest t = 0 := by
  have hs : tsupport primeMeanTest ⊆ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    exact hx (primeMeanTest_zero_outside x hn)
  exact deriv_of_notMem_tsupport (fun h => ht (hs h))

theorem primeMeanTest_deriv_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, |deriv primeMeanTest t| ≤ D := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    primeMeanTest_deriv_continuous.continuousOn
  refine ⟨|D| + 1, by positivity, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8)
  · have h := hD t ht
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self D]
  · rw [primeMeanTest_deriv_zero_outside t ht, abs_zero]
    positivity

theorem scaledPrimeMeanTest_hasDerivAt (X t : ℝ) :
    HasDerivAt (fun s : ℝ => primeMeanTest (s / X))
      (deriv primeMeanTest (t / X) / X) t := by
  have h := (((primeMeanTest_contDiff (n := 1)).differentiable
      (by norm_num)) (t / X)).hasDerivAt |>.comp t ((hasDerivAt_id t).div_const X)
  simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using h

theorem smoothPrincipalMean_eq_real_sum (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean 1 1 X =
      ((∑ n ∈ Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n *
        primeMeanTest (n / X) : ℝ) : ℂ) := by
  rw [smoothMangoldtMean_eq_sum 1 1 X hX]
  have heq : (∑ n ∈ Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n *
      primeMeanTest (n / X)) =
      ∑ n ∈ Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * primeMeanTest (n / X) := by
    rw [← sum_Ioc_add_eq_sum_Icc (Nat.zero_le ⌊X⌋₊)]
    simp
  rw [← heq]
  push_cast
  apply sum_congr rfl
  intro n hn
  have hn1 : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [hn1]
  simp

theorem smoothPrincipalMean_partial_summation (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean 1 1 X =
      ((-(∫ t in (0 : ℝ)..X,
        deriv primeMeanTest (t / X) / X * Chebyshev.psi t) : ℝ) : ℂ) := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X) :=
    (primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X
  have hd : deriv (fun t : ℝ => primeMeanTest (t / X)) =
      fun t : ℝ => deriv primeMeanTest (t / X) / X := by
    funext t
    exact (scaledPrimeMeanTest_hasDerivAt X t).deriv
  have hi : IntegrableOn (deriv (fun t : ℝ => primeMeanTest (t / X)))
      (Set.Icc 0 X) := by rw [hd]; exact hf.continuousOn.integrableOn_Icc
  have hs := sum_mul_eq_sub_integral_mul ArithmeticFunction.vonMangoldt hX.le
    (f := fun t : ℝ => primeMeanTest (t / X))
    (fun t _ => (scaledPrimeMeanTest_hasDerivAt X t).differentiableAt) hi
  rw [hd] at hs
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hs
  rw [show primeMeanTest (X / X) = 0 by
    rw [div_self hX.ne']; exact primeMeanTest_zero_outside 1 (by norm_num), zero_mul,
    zero_sub, ← intervalIntegral.integral_of_le hX.le] at hs
  rw [smoothPrincipalMean_eq_real_sum X hX]
  congr 1
  simpa only [mul_comm] using hs

theorem primeMeanTest_integral_unit :
    (∫ t in (0 : ℝ)..1, primeMeanTest t) = ∫ t : ℝ, primeMeanTest t := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hmem : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
    by_contra hn
    exact ht (primeMeanTest_zero_outside t hn)
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem scaledPrimeMean_main_integral (X : ℝ) (hX : 0 < X) :
    (∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X * t) =
      -(X * ∫ t : ℝ, primeMeanTest t) := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X) :=
    (primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X
  have hs := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ : ℝ => 1)
    (v := fun t : ℝ => primeMeanTest (t / X))
    (v' := fun t : ℝ => deriv primeMeanTest (t / X) / X)
    (fun t _ => hasDerivAt_id t) (fun t _ => scaledPrimeMeanTest_hasDerivAt X t)
    (intervalIntegrable_const) (hf.intervalIntegrable 0 X)
  have hzero : primeMeanTest (X / X) = 0 := by
    rw [div_self hX.ne']
    exact primeMeanTest_zero_outside 1 (by norm_num)
  simp only [hzero, one_mul, zero_mul, mul_zero, sub_zero, zero_sub] at hs
  rw [intervalIntegral.integral_comp_div primeMeanTest hX.ne'] at hs
  simpa only [mul_comm, zero_div, div_self hX.ne', smul_eq_mul,
    primeMeanTest_integral_unit] using hs

private theorem scaledPrimeMean_psi_integrable (X : ℝ) (hX : 0 < X) :
    IntervalIntegrable (fun t : ℝ => deriv primeMeanTest (t / X) / X *
      Chebyshev.psi t) volume 0 X := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X) :=
    (primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX.le]
  simpa only [Chebyshev.psi_eq_sum_Icc] using
    (integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0)
      (show (0 : ℝ) ≤ 0 by rfl) hf.continuousOn.integrableOn_Icc)

/-- The exact principal error is the integral of the unsmoothed PNT error. -/
theorem smoothPrincipalError_integral (X : ℝ) (hX : 0 < X) :
    smoothPrincipalError X =
      |∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X *
        (Chebyshev.psi t - t)| := by
  have hf : Continuous (fun t : ℝ => deriv primeMeanTest (t / X) / X * t) :=
    ((primeMeanTest_deriv_continuous.comp (continuous_id.div_const X)).div_const X).mul
      continuous_id
  have hi : (∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X *
      (Chebyshev.psi t - t)) =
      (∫ t in (0 : ℝ)..X, deriv primeMeanTest (t / X) / X * Chebyshev.psi t) +
        X * ∫ t : ℝ, primeMeanTest t := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (scaledPrimeMean_psi_integrable X hX)
      (hf.intervalIntegrable 0 X), scaledPrimeMean_main_integral X hX, sub_neg_eq_add]
  rw [smoothPrincipalError, smoothPrincipalMean_partial_summation X hX,
    smoothPrincipalMain, ← Complex.ofReal_sub, Complex.norm_real]
  rw [hi]
  rw [Real.norm_eq_abs, sub_eq_add_neg, ← neg_add, abs_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrincipalPNTBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative PNT for the fixed smooth principal test

Only the classical quantitative Chebyshev estimate is used here. The
smoothing bounds are proved for the concrete test retained in the main proof.
-/

namespace Ostmann

open Filter MeasureTheory
open scoped BigOperators Interval

theorem smoothPrincipalError_rough_bound (D X : ℝ) (hD : 0 ≤ D) (hX : 0 < X)
    (hd : ∀ t : ℝ, |deriv primeMeanTest t| ≤ D) :
    smoothPrincipalError X ≤ D * (Real.log 4 + 5) * X := by
  rw [smoothPrincipalError_integral X hX]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := X) (C := D * (Real.log 4 + 5))
    (f := fun t : ℝ => deriv primeMeanTest (t / X) / X * (Chebyshev.psi t - t))
    (fun t ht => ?_)
  · simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hX] using hi
  rw [Set.uIoc_of_le hX.le] at ht
  have ht0 : 0 ≤ t := ht.1.le
  have hpsi : |Chebyshev.psi t - t| ≤ (Real.log 4 + 5) * t := by
    have hh := abs_sub_le (Chebyshev.psi t) 0 t
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (Chebyshev.psi_nonneg t),
      abs_of_nonneg ht0] at hh
    linarith [Chebyshev.psi_le_const_mul_self ht0]
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hX]
  calc
    _ ≤ D / X * ((Real.log 4 + 5) * t) :=
      mul_le_mul (div_le_div_of_nonneg_right (hd _) hX.le) hpsi (abs_nonneg _)
        (div_nonneg hD hX.le)
    _ ≤ D / X * ((Real.log 4 + 5) * X) := by
      gcongr
      exact ht.2
    _ = _ := by field_simp

theorem smoothPrincipalError_of_psi_bound (C c D x0 X : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) (hD : 0 ≤ D)
    (hd : ∀ t : ℝ, |deriv primeMeanTest t| ≤ D)
    (hpsi : ∀ t : ℝ, x0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)))
    (hX : 4 ≤ X) (hx0 : 2 * x0 ≤ X) :
    smoothPrincipalError X ≤ C * D * X *
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  have hX0 : 0 < X := by linarith
  rw [smoothPrincipalError_integral X hX0]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := X)
    (C := C * D * Real.exp (-(c / 2) * Real.sqrt (Real.log X)))
    (f := fun t : ℝ => deriv primeMeanTest (t / X) / X * (Chebyshev.psi t - t))
    (fun t ht => ?_)
  · have hh : |X - 0| = X := by simpa using abs_of_pos hX0
    rw [hh, Real.norm_eq_abs] at hi
    calc
      _ ≤ C * D * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) * X := hi
      _ = _ := by ring
  rw [Set.uIoc_of_le hX0.le] at ht
  by_cases hsmall : t < X / 2
  · have hz : deriv primeMeanTest (t / X) = 0 := by
      apply primeMeanTest_deriv_zero_outside
      intro hmem
      have hh := (le_div_iff₀ hX0).mp hmem.1
      linarith
    rw [hz, zero_div, zero_mul, norm_zero]
    positivity
  have ht0 : 0 < t := ht.1
  have htlo : X / 2 ≤ t := le_of_not_gt hsmall
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hloglarge : 2 * Real.log 2 ≤ Real.log X := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) hX
  have hlogt : Real.log X - Real.log 2 ≤ Real.log t := by
    have h := Real.log_le_log (show 0 < X / 2 by positivity) htlo
    rwa [Real.log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  have hsqrt : Real.sqrt (Real.log X) / 2 ≤ Real.sqrt (Real.log t) := by
    calc
      _ = Real.sqrt (Real.log X / 4) := by rw [Real.sqrt_div hlogX]; norm_num
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hexp : Real.exp (-c * Real.sqrt (Real.log t)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have herr : |Chebyshev.psi t - t| ≤
      C * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    calc
      _ ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) :=
        hpsi t (by linarith)
      _ ≤ _ := by gcongr; exact ht.2
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hX0]
  calc
    _ ≤ D / X * (C * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) :=
      mul_le_mul (div_le_div_of_nonneg_right (hd _) hX0.le) herr (abs_nonneg _)
        (div_nonneg hD hX0.le)
    _ = _ := by field_simp

/-- The fixed-test PNT follows from the classical quantitative Chebyshev PNT. -/
theorem publishedSmoothPrincipalPNT_of_chebyshev
    (hPNT : ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))) :
    PublishedSmoothPrincipalPNT := by
  obtain ⟨c, hc, hp⟩ := hPNT
  obtain ⟨C, hC, hbound⟩ := hp.exists_pos
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hbound.bound
  obtain ⟨D, hD, hd⟩ := primeMeanTest_deriv_bound
  let x1 := max x0 2
  have hpsi : ∀ t : ℝ, x1 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by dsimp only [x1]; positivity) ht
    have hh := hx0 t ((le_max_left _ _).trans ht)
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, Real.sqrt_eq_rpow,
      abs_of_nonneg (mul_nonneg ht0 (Real.exp_nonneg _)), mul_assoc] using hh
  let T : ℝ := max 4 (2 * x1)
  let K0 : ℝ := D * (Real.log 4 + 5)
  let K : ℝ := max (C * D)
    (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T))) + 1
  have hK0 : 0 ≤ K0 := by dsimp only [K0]; positivity
  have hK : 0 < K := by
    dsimp only [K]
    have hh : 0 ≤ C * D := mul_nonneg hC.le hD.le
    linarith [le_max_left (C * D) (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)))]
  refine ⟨K, c / 2, hK, by linarith, ?_⟩
  intro X hX
  have hX0 : 0 < X := by linarith
  by_cases hTX : T ≤ X
  · have hh := smoothPrincipalError_of_psi_bound C c D x1 X hC.le hc hD.le hd hpsi
      ((le_max_left _ _).trans hTX) ((le_max_right _ _).trans hTX)
    refine hh.trans ?_
    have hCK : C * D ≤ K := by
      dsimp only [K]
      have hm := le_max_left (C * D) (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)))
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK hX0.le)
      (Real.exp_nonneg _)
  · have hXT : X ≤ T := le_of_not_ge hTX
    have hsqrt : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log T) :=
      Real.sqrt_le_sqrt (Real.log_le_log hX0 hXT)
    have hscale : K0 * Real.exp ((c / 2) * Real.sqrt (Real.log X)) ≤ K := by
      calc
        _ ≤ K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)) := by gcongr
        _ ≤ _ := by
          dsimp only [K]
          have hm := le_max_right (C * D) (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)))
          linarith
    have hsmall : K0 ≤ K * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
      have hh := mul_le_mul_of_nonneg_right hscale
        (Real.exp_nonneg (-(c / 2) * Real.sqrt (Real.log X)))
      have he : (c / 2) * Real.sqrt (Real.log X) +
          -(c / 2) * Real.sqrt (Real.log X) = 0 := by ring
      simpa only [mul_assoc, ← Real.exp_add, he, Real.exp_zero, mul_one] using hh
    calc
      _ ≤ K0 * X := smoothPrincipalError_rough_bound D X hD.le hX0 hd
      _ ≤ (K * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) * X :=
        mul_le_mul_of_nonneg_right hsmall hX0.le
      _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionPrincipalPNT
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor-one consequence of the progression input

The principal smooth PNT is not an independent input: the conductor-one
theta estimate, elementary prime-power removal and partial summation suffice.
-/

namespace Ostmann

open Filter
open scoped Classical BigOperators

theorem primeProgressionTheta_one (x : ℝ) :
    primeProgressionTheta 1 0 x = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp [primeProgressionTheta, primeProgressionLog, Finset.sum_filter, Nat.ModEq, Nat.mod_one]

theorem PublishedProgressionInput.principal_theta_bound (P : PublishedProgressionInput)
    (x : ℝ) (hx : 2 ≤ x) :
    |Chebyshev.theta x - x| ≤
      P.errorConstant * x * Real.exp (-P.decay * Real.sqrt (Real.log x)) := by
  have h := P.theta 1 le_rfl 0 (by norm_num) x hx
  simpa only [primeProgressionTheta_one, P.localZero_one, pageCoefficient, pageBeta,
    Nat.totient_one, Nat.cast_one, thetaMainTerm, zero_mul, zero_div, sub_zero, div_one]
    using h

private theorem prime_power_error_log_scale (d : ℝ) (hd : 0 < d) :
    ∀ᶠ y : ℝ in atTop,
      2 * Real.sqrt (Real.exp y) * y ≤ Real.exp y * Real.exp (-d * Real.sqrt y) := by
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 1
    (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left (2 : ℝ)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hpoly, eventually_ge_atTop ((4 * d) ^ 2),
    eventually_ge_atTop (0 : ℝ)] with y hy hlarge hy0
  have hpoly' : 2 * y ≤ Real.exp (y / 4) := by
    apply (le_abs_self (2 * y)).trans
    simpa only [pow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul,
      show (1 / 4 : ℝ) * y = y / 4 by ring] using hy
  have hroot : 4 * d ≤ Real.sqrt y := by
    have hs := Real.sqrt_le_sqrt hlarge
    rwa [Real.sqrt_sq (by positivity)] at hs
  have hcost : d * Real.sqrt y ≤ y / 4 := by
    nlinarith [Real.sq_sqrt hy0]
  calc
    _ = Real.exp (y / 2) * (2 * y) := by rw [← Real.exp_half]; ring
    _ ≤ Real.exp (y / 2) * Real.exp (y / 4) :=
      mul_le_mul_of_nonneg_left hpoly' (Real.exp_nonneg _)
    _ = Real.exp (3 * y / 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (y - d * Real.sqrt y) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem PublishedProgressionInput.principal_chebyshev_pnt (P : PublishedProgressionInput) :
    ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2))) := by
  refine ⟨P.decay, P.decay_pos, ?_⟩
  apply Asymptotics.IsBigO.of_bound (P.errorConstant + 1)
  have hsmall := Real.tendsto_log_atTop.eventually
    (prime_power_error_log_scale P.decay P.decay_pos)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hsmall hx
  have hx0 : 0 < x := by linarith
  have hpow : |Chebyshev.psi x - Chebyshev.theta x| ≤
      x * Real.exp (-P.decay * Real.sqrt (Real.log x)) := by
    refine (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)).trans ?_
    simpa only [Real.exp_log hx0] using hsmall
  have htheta := P.principal_theta_bound x hx
  have hh := abs_sub_le (Chebyshev.psi x) (Chebyshev.theta x) x
  have hsum : |Chebyshev.psi x - x| ≤
      (P.errorConstant + 1) * (x * Real.exp (-P.decay * Real.sqrt (Real.log x))) := by
    nlinarith
  simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, Real.sqrt_eq_rpow,
    abs_of_pos (mul_pos hx0 (Real.exp_pos _))] using hsum

theorem PublishedProgressionInput.smoothPrincipalPNT (P : PublishedProgressionInput) :
    PublishedSmoothPrincipalPNT :=
  publishedSmoothPrincipalPNT_of_chebyshev P.principal_chebyshev_pnt

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensThetaKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the conductor-one theta error

The exponential square-root error has a bounded logarithmic integral. This
concrete antiderivative suffices for the first Mertens estimate.
-/

namespace Ostmann

open MeasureTheory
open scoped Interval

theorem hasDerivAt_thetaErrorPrimitive {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt (thetaErrorPrimitive c)
      (Real.exp (-c * Real.sqrt (Real.log t)) / t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  have hs := (Real.hasDerivAt_sqrt hlog.ne').comp t (Real.hasDerivAt_log ht0)
  have hl := ((hs.const_mul c).add_const 1).const_mul (-(2 / c ^ 2))
  have hr := (hs.const_mul (-c)).exp
  refine (hl.mul hr).congr_deriv ?_
  · simp only [Function.comp_apply]
    field_simp
    ring

theorem thetaErrorPrimitive_nonpos {c : ℝ} (hc : 0 < c) (t : ℝ) :
    thetaErrorPrimitive c t ≤ 0 := by
  unfold thetaErrorPrimitive
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
    (Real.exp_nonneg _)

/-- A uniform bound independent of the upper cutoff. -/
theorem theta_error_kernel_integral_bound {c X : ℝ} (hc : 0 < c) (hX : 2 ≤ X) :
    (∫ t in (2 : ℝ)..X, Real.exp (-c * Real.sqrt (Real.log t)) / t) ≤
      -thetaErrorPrimitive c 2 := by
  have hi : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-c * Real.sqrt (Real.log t)) / t) volume 2 X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hX]
    apply ContinuousOn.integrableOn_Icc
    fun_prop (disch := grind)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
    hasDerivAt_thetaErrorPrimitive hc (by
      rw [Set.uIcc_of_le hX] at ht
      linarith [ht.1])) hi]
  linarith [thetaErrorPrimitive_nonpos hc X]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MertensFromProgression
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens estimates from the progression estimate

The conductor-one theta bound implies the first Mertens estimate.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

/-- Abel summation for the logarithmically weighted prime sum. -/
theorem prime_log_div_partial_summation (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) =
      Chebyshev.theta Q / Q + ∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : ContinuousOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc 2 Q) := by
    simp only [deriv_inv']
    exact ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
  have h := sum_mul_eq_sub_integral_mul₁ (primeProgressionLog 1 0)
    (by norm_num [primeProgressionLog]) (by norm_num [primeProgressionLog]) (Q : ℝ)
    (f := fun t : ℝ => t⁻¹)
    (fun t ht => (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt)
    hd.integrableOn_Icc
  have hs : (∑ n ∈ Icc 0 Q, (n : ℝ)⁻¹ * primeProgressionLog 1 0 n) =
      ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p := by
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
    apply sum_congr rfl
    intro n hn
    simp [primeProgressionLog, Nat.ModEq, Nat.mod_one, mul_ite, div_eq_mul_inv, mul_comm]
  change _ = (Q : ℝ)⁻¹ * primeProgressionTheta 1 0 Q -
    ∫ t in Set.Ioc (2 : ℝ) Q, deriv (fun t : ℝ => t⁻¹) t *
      primeProgressionTheta 1 0 t at h
  rw [Nat.floor_natCast, hs] at h
  simp_rw [primeProgressionTheta_one, deriv_inv, neg_mul] at h
  rw [← intervalIntegral.integral_of_le hQR, intervalIntegral.integral_neg,
    sub_neg_eq_add] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

private theorem theta_div_sq_integrable (Q : ℕ) (hQ : 2 ≤ Q) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2) volume 2 Q := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le
    (show (2 : ℝ) ≤ Q by exact_mod_cast hQ)]
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 2 Q) := by
    exact (continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have h := integrableOn_mul_sum_Icc (primeProgressionLog 1 0)
    (m := 0) (show (0 : ℝ) ≤ 2 by norm_num) hc.integrableOn_Icc
  change IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹ * primeProgressionTheta 1 0 t)
    (Set.Icc 2 Q) at h
  simpa only [primeProgressionTheta_one, div_eq_mul_inv, mul_comm] using h

/-- The integrated theta error is bounded independently of the cutoff. -/
theorem PublishedProgressionInput.theta_error_integral (P : PublishedProgressionInput)
    (Q : ℕ) (hQ : 2 ≤ Q) :
    |∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2| ≤
      P.errorConstant * (-thetaErrorPrimitive P.decay 2) := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hk : IntervalIntegrable (fun t : ℝ =>
      Real.exp (-P.decay * Real.sqrt (Real.log t)) / t) volume 2 Q := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
    apply ContinuousOn.integrableOn_Icc
    fun_prop (disch := grind)
  have hi : IntervalIntegrable (fun t : ℝ =>
      (Chebyshev.theta t - t) / t ^ 2) volume 2 Q := by
    have hv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 2 Q := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
      apply ContinuousOn.integrableOn_Icc
      fun_prop (disch := grind)
    apply ((theta_div_sq_integrable Q hQ).sub hv).congr
    intro t ht
    rw [Set.uIoc_of_le hQR] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    field_simp
  calc
    _ ≤ ∫ t in (2 : ℝ)..Q, |(Chebyshev.theta t - t) / t ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm hQR
          (f := fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2))
    _ ≤ ∫ t in (2 : ℝ)..Q,
        P.errorConstant * (Real.exp (-P.decay * Real.sqrt (Real.log t)) / t) := by
      apply intervalIntegral.integral_mono_on hQR hi.norm (hk.const_mul _)
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t)]
      calc
        _ ≤ (P.errorConstant * t * Real.exp (-P.decay * Real.sqrt (Real.log t))) /
            t ^ 2 := div_le_div_of_nonneg_right (P.principal_theta_bound t ht.1)
              (sq_nonneg _)
        _ = _ := by field_simp
    _ = P.errorConstant * ∫ t in (2 : ℝ)..Q,
        Real.exp (-P.decay * Real.sqrt (Real.log t)) / t :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (theta_error_kernel_integral_bound P.decay_pos hQR) P.errorConstant_nonneg

theorem PublishedProgressionInput.mertensConstant_nonneg (P : PublishedProgressionInput) :
    0 ≤ P.mertensConstant := by
  unfold PublishedProgressionInput.mertensConstant
  exact add_nonneg (add_nonneg (abs_nonneg _) P.errorConstant_nonneg)
    (mul_nonneg P.errorConstant_nonneg (neg_nonneg.mpr
      (thetaErrorPrimitive_nonpos P.decay_pos 2)))

/-- First Mertens, with a concrete constant depending on the
progression estimate. -/
theorem PublishedProgressionInput.mertens (P : PublishedProgressionInput) :
    MertensEstimate P.mertensConstant := by
  intro Q hQ
  by_cases hQ2 : 2 ≤ Q
  · have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    have hQ0 : (0 : ℝ) < Q := by linarith
    have hv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 2 Q := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hQR]
      apply ContinuousOn.integrableOn_Icc
      fun_prop (disch := grind)
    have hsplit : (∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2) =
        (∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2) -
          (Real.log Q - Real.log 2) := by
      have he : (∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2) =
          ∫ t in (2 : ℝ)..Q, Chebyshev.theta t / t ^ 2 - t⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hQR] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        field_simp
      rw [he, intervalIntegral.integral_sub (theta_div_sq_integrable Q hQ2) hv,
        integral_inv_of_pos (by norm_num) hQ0,
        Real.log_div hQ0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hid : (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q =
        (1 - Real.log 2) + (Chebyshev.theta Q - Q) / Q +
          ∫ t in (2 : ℝ)..Q, (Chebyshev.theta t - t) / t ^ 2 := by
      rw [hsplit, prime_log_div_partial_summation Q hQ2]
      field_simp
      ring
    have hend : |(Chebyshev.theta Q - Q) / Q| ≤ P.errorConstant := by
      rw [abs_div, abs_of_pos hQ0]
      calc
        _ ≤ (P.errorConstant * Q * Real.exp (-P.decay * Real.sqrt (Real.log Q))) / Q :=
          div_le_div_of_nonneg_right (P.principal_theta_bound Q hQR) hQ0.le
        _ = P.errorConstant * Real.exp (-P.decay * Real.sqrt (Real.log Q)) := by
          field_simp
        _ ≤ P.errorConstant * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr P.decay_pos.le) (Real.sqrt_nonneg _))) P.errorConstant_nonneg
        _ = _ := mul_one _
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add le_rfl hend) (P.theta_error_integral Q hQ2))
  · have hQ1 : Q = 1 := by omega
    subst Q
    simpa only [Nat.primesLE_one, sum_empty, Nat.cast_one, Real.log_one, sub_self,
      abs_zero] using P.mertensConstant_nonneg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_ReducedPublishedInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic hypotheses for the inverse Goldbach theorem

Tensorization gives finite Bonami. The progression estimate gives the two
Mertens estimates and the principal smooth prime number theorem.
Multiplicity-labelled zero enumerations give the fixed-test explicit formula.
-/

namespace Ostmann

theorem inverseGoldbach_of_first_mertens
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM : ℝ) (hM : MertensEstimate CM)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    : InverseGoldbach := by
  exact inverseGoldbach_of_published P0 ls hsize publishedBonamiBound Hreal hSiegel
    sieve CM _ hM hM.harmonic Z hD hR Pexplicit P0.smoothPrincipalPNT

/-- The exact inverse Goldbach conclusion with the same reduced input list. -/
theorem inverseGoldbach_of_reduced_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z) :
    InverseGoldbach :=
  inverseGoldbach_of_first_mertens P0 ls hsize Hreal hSiegel sieve
    P0.mertensConstant P0.mertens Z hD hR Pexplicit

/-- The inverse Goldbach theorem using a faithful numbering of the zeros. -/
theorem inverseGoldbach_of_numbered_zeros
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (e : ∀ χ, ℕ ≃ CharacterZeroCopy χ)
    (hD : PublishedComplexZeroDensity (fun χ => characterZeroEnumeration χ (e χ)))
    (hR : PublishedComplexZeroRegion (fun χ => characterZeroEnumeration χ (e χ))) :
    InverseGoldbach :=
  inverseGoldbach_of_reduced_published P0 ls hsize Hreal hSiegel sieve
    (fun χ => characterZeroEnumeration χ (e χ)) hD hR (actualSmoothExplicitFormula e)

/-- The inverse Goldbach theorem using the Dirichlet L-function zeros. -/
theorem inverseGoldbach_of_remaining_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_of_numbered_zeros P0 ls hsize Hreal hSiegel sieve
    faithfulCharacterZeroEquiv hD hR

/-- The inverse Goldbach theorem using the real low-height zero-free region. -/
theorem inverseGoldbach_of_actual_region
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound)
    (hregion : ActualRealLowHeightRegion P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_of_remaining_published P0 ls hsize
    (actualPublishedRealZeroInput P0 hregion) hSiegel sieve hD hR

/-- The exact inverse Goldbach conclusion, with the real-character Hadamard
and low-height zero-free-region hypotheses both removed. -/
theorem inverseGoldbach_without_real_zero_input
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros)
    (hR : PublishedComplexZeroRegion actualCharacterZeros) :
    InverseGoldbach := by
  obtain ⟨κ, hκ, hregion⟩ := exists_actual_real_low_height_region
  let P := P0.restrictKappa (min P0.kappa κ) (lt_min P0.kappa_pos hκ) (min_le_left _ _)
  exact inverseGoldbach_of_actual_region P ls hsize
    (hregion P (min_le_right _ _)) hSiegel sieve hD hR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualComplexZeroRegion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full-height zero-free region -/

namespace Ostmann

theorem actualComplexZeroRegion : PublishedComplexZeroRegion actualCharacterZeros := by
  obtain ⟨κ, hκ, hpage⟩ := exists_actual_page_uniqueness
  exact complexZeroRegion_of_page κ hκ hpage

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_MainActualProgression
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Main statements with all exceptional-zero data constructed -/

namespace Ostmann

theorem inverseGoldbach_of_actual_progression
    (hP : ActualProgressionTheta) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_real_zero_input
    (progressionInput_of_actual_theta hP) ls hsize hSiegel sieve hD actualComplexZeroRegion

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_MainWithoutProgression
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The main statements after discharging the prime-progression input -/

namespace Ostmann

theorem inverseGoldbach_without_progression_input
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_of_actual_progression actualProgressionTheta ls hsize hSiegel sieve hD

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant kernel in the sharp additive large sieve

The finite-kernel identity is equation (3.6) of Montgomery--Vaughan,
Hilbert's inequality, JLMS (2) 8 (1974), 73--82. The scalar majorant is
Lemma 1 there. Only these concrete trigonometric statements are used.
-/

namespace Ostmann

theorem cosecantKernel_skew (x y : ℝ) : cosecantKernel x y = -cosecantKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cosecantKernel, he]

theorem cotangentKernel_skew (x y : ℝ) : cotangentKernel x y = -cotangentKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cotangentKernel, he, div_neg]

theorem cosecantKernel_triple (x y z : ℝ)
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0)
    (hxz : Real.sin (Real.pi * (x - z)) ≠ 0)
    (hyz : Real.sin (Real.pi * (y - z)) ≠ 0) :
    cosecantKernel x y * cosecantKernel x z =
      cosecantKernel y z * (cotangentKernel x y - cotangentKernel x z) := by
  have he : Real.pi * (y - z) = Real.pi * (x - z) - Real.pi * (x - y) := by ring
  have hs := Real.sin_sub (Real.pi * (x - z)) (Real.pi * (x - y))
  rw [← he] at hs
  unfold cosecantKernel cotangentKernel
  field_simp
  nlinarith

theorem cos_quartic_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    dsimp [f]
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have ht0 : 0 ≤ t := (Set.mem_Ici.mp (interior_subset ht))
    have hs := Real.sin_ge_sub_cube ht0
    linarith
  have hh := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  simpa [f] using hh

theorem sine_cosecant_majorant {x : ℝ} (hx : 0 < x) (hxp : x ≤ Real.pi / 2) :
    1 / (Real.sin x) ^ 2 + 2 * |Real.cos x / (Real.sin x) ^ 2| ≤ 3 / x ^ 2 := by
  have hx2 : x < 2 := by linarith [Real.pi_lt_four]
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxp⟩
  have hxSq : x ^ 2 ≤ 4 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hxSq hx.le
  have hl : 0 ≤ x - x ^ 3 / 6 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hsq := mul_self_le_mul_self hl hsin
  have hcos := mul_le_mul_of_nonneg_left (cos_quartic_upper hx.le) (sq_nonneg x)
  have hpoly : (1 + 2 * Real.cos x) * x ^ 2 ≤ 3 * (Real.sin x) ^ 2 := by nlinarith
  rw [abs_of_nonneg (div_nonneg hc (sq_nonneg _))]
  have he : 1 / (Real.sin x) ^ 2 + 2 * (Real.cos x / (Real.sin x) ^ 2) =
      (1 + 2 * Real.cos x) / (Real.sin x) ^ 2 := by ring
  rw [he]
  exact (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hx)).mpr hpoly

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantDistanceBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cosecant row weight depends only on distance to an integer -/

namespace Ostmann

 theorem cosecantRowWeight_eq (x y : ℝ) :
    cosecantKernel x y ^ 2 + 2 * |cosecantKernel x y * cotangentKernel x y| =
      cosecantRowWeight (x - y) := by
  unfold cosecantKernel cotangentKernel cosecantRowWeight
  congr 1
  · ring
  · congr 2
    ring

 theorem cosecantRowWeight_shift (t : ℝ) (m : ℤ) :
    cosecantRowWeight (t - m) = cosecantRowWeight t := by
  have he : Real.pi * (t - m) = Real.pi * t - (m : ℝ) * Real.pi := by ring
  have hs : |Real.sin (Real.pi * (t - m))| = |Real.sin (Real.pi * t)| := by
    rw [he, Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have hc : |Real.cos (Real.pi * (t - m))| = |Real.cos (Real.pi * t)| := by
    rw [he, Real.cos_sub_int_mul_pi, abs_mul]
    simp
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  simp only [sq_abs] at hs2
  unfold cosecantRowWeight
  rw [hs2, abs_div, abs_div, hc]

 theorem cosecantRowWeight_abs (t : ℝ) : cosecantRowWeight |t| = cosecantRowWeight t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp [cosecantRowWeight, Real.sin_neg, Real.cos_neg]

 theorem cosecantRowWeight_bound (t d : ℝ) (m : ℤ)
    (hd : 0 < d) (hdhalf : d ≤ 1 / 2) (he : |t - m| = d) :
    cosecantRowWeight t ≤ 3 / (Real.pi ^ 2 * d ^ 2) := by
  rw [← cosecantRowWeight_shift t m, ← cosecantRowWeight_abs, he]
  have hp : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  have hh : Real.pi * d ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hb := sine_cosecant_majorant hp hh
  simpa only [cosecantRowWeight, mul_pow] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedInverseSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-sided inverse-square estimate for separated sample points -/

namespace Ostmann

open scoped BigOperators

 theorem ordered_separated_lower {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    ∀ i, δ * (i.val + 1) ≤ x i := by
  have hi : ∀ k : ℕ, ∀ hk : k < n, δ * ((k : ℝ) + 1) ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using hfirst ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hg := hgap ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact hi i.val i.isLt

 theorem finite_positive_inverse_squares (n : ℕ) :
    (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  have he : (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) =
      ∑ j ∈ Finset.range (n + 1), 1 / (j : ℝ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) n,
      Finset.sum_range_succ']
    simp
  rw [he, ← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum _ (fun j _ => by positivity)

 theorem ordered_separated_inverse_squares {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  have hx := ordered_separated_lower x δ hfirst hgap
  have hb (i : Fin n) : 1 / (x i) ^ 2 ≤
      (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := by
    have hi : 0 < (i.val : ℝ) + 1 := by positivity
    have hxi : 0 < x i := lt_of_lt_of_le hδ (hfirst i)
    have hs : (δ * ((i.val : ℝ) + 1)) ^ 2 ≤ (x i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hx i) 2
    calc
      _ ≤ 1 / (δ * ((i.val : ℝ) + 1)) ^ 2 := one_div_le_one_div_of_le (by positivity) hs
      _ = _ := by simp only [mul_pow, one_div, mul_inv]
  calc
    _ ≤ ∑ i : Fin n, (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (δ ^ 2)⁻¹ * ∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (δ ^ 2)⁻¹ * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (finite_positive_inverse_squares n) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedSetSquares
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The inverse-square row sum for a finite separated set -/

namespace Ostmann

open scoped BigOperators

 theorem positive_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  classical
  let e := S.orderEmbOfFin rfl
  have he (i : Fin S.card) : e i ∈ S := S.orderEmbOfFin_mem rfl i
  have hg (i j : Fin S.card) (hij : i < j) : δ ≤ e j - e i := by
    have hij' : e i < e j := e.strictMono hij
    have hh := hsep (e j) (he j) (e i) (he i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at hh
  have hh := ordered_separated_inverse_squares (fun i => e i) δ hδ
    (fun i => hfirst _ (he i)) hg
  have hs : (∑ x ∈ S, 1 / x ^ 2) = ∑ i : Fin S.card, 1 / (e i) ^ 2 := by
    conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  rwa [hs]

 theorem separated_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ |x|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let P := S.filter (fun x => 0 < x)
  let N := S.filter (fun x => ¬0 < x)
  let R := N.image (fun x => -x)
  have hP := positive_set_inverse_squares P δ hδ
    (fun x hx => by
      have h := Finset.mem_filter.mp hx
      simpa only [abs_of_pos h.2] using hfirst x h.1)
    (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  have hRfirst (x : ℝ) (hx : x ∈ R) : δ ≤ x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_filter.mp hy
    simpa only [abs_of_nonpos (le_of_not_gt hy'.2)] using hfirst y hy'.1
  have hRsep (x : ℝ) (hx : x ∈ R) (y : ℝ) (hy : y ∈ R) (hxy : x ≠ y) : δ ≤ |x - y| := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hh := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (fun hab => hxy (congrArg Neg.neg hab))
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hR := positive_set_inverse_squares R δ hδ hRfirst hRsep
  have hsum : (∑ x ∈ P, 1 / x ^ 2) + (∑ x ∈ N, 1 / x ^ 2) = ∑ x ∈ S, 1 / x ^ 2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have he : (∑ x ∈ R, 1 / x ^ 2) = ∑ x ∈ N, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    · simp
    · exact fun _ _ _ _ hab => neg_injective hab
  rw [he] at hR
  rw [← hsum]
  have hid : Real.pi ^ 2 / (3 * δ ^ 2) = 2 * (Real.pi ^ 2 / (6 * δ ^ 2)) := by ring
  rw [hid]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CircleSeparatedPoints
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

 theorem centeredCircleRemainder_bounds (t : ℝ) :
    -(1 / 2) ≤ centeredCircleRemainder t ∧ centeredCircleRemainder t < 1 / 2 := by
  have hl := Int.floor_le (t + 1 / 2)
  have hu := Int.lt_floor_add_one (t + 1 / 2)
  dsimp [centeredCircleRemainder]
  constructor <;> linarith

 theorem circleSeparated_sine_ne_zero {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hx : CircleSeparated x δ) {s t : ι} (hst : s ≠ t) :
    Real.sin (Real.pi * (x s - x t)) ≠ 0 := by
  intro hz
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hz
  have he : x s - x t - (m : ℝ) = 0 := by nlinarith [Real.pi_pos]
  have hh := hx s t hst m
  rw [he, abs_zero] at hh
  linarith

 theorem circleSeparated_remainders {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hx : CircleSeparated x δ) (center s t : ι) (hst : s ≠ t) :
    δ ≤ |centeredCircleRemainder (x s - x center) -
      centeredCircleRemainder (x t - x center)| := by
  have hh := hx s t hst (⌊x s - x center + 1 / 2⌋ - ⌊x t - x center + 1 / 2⌋)
  push_cast at hh
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; dsimp [centeredCircleRemainder]; ring)

 theorem circleSeparated_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s ∈ Finset.univ.erase center,
      1 / centeredCircleRemainder (x s - x center) ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  let S := F.image r
  have hfirst (s : ι) (hs : s ∈ F) : δ ≤ |r s| :=
    hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
  have hinj : Set.InjOn r F := by
    intro s hs t ht he
    by_contra hst
    have hb := circleSeparated_remainders x δ hx center s t hst
    change δ ≤ |r s - r t| at hb
    rw [he, sub_self, abs_zero] at hb
    linarith
  have hb := separated_set_inverse_squares S δ hδ (by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact hfirst s hs) (by
    intro y hy z hz hyz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact circleSeparated_remainders x δ hx center s t (fun hst => hyz (congrArg r hst)))
  have he : (∑ y ∈ S, 1 / y ^ 2) = ∑ s ∈ F, 1 / (r s) ^ 2 := by
    exact Finset.sum_image hinj
  rwa [he] at hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_ReducedFractionSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact circle separation of reduced fractions -/

namespace Ostmann

 theorem reduced_fraction_cross_injective (q r h k : ℕ) (hq : 0 < q)
    (_hr : 0 < r) (hc : h.Coprime q) (kc : k.Coprime r) (he : h * r = k * q) :
    q = r ∧ h = k := by
  have hqr : q ∣ r := hc.symm.dvd_mul_left.mp (by rw [he]; exact dvd_mul_left q k)
  have hrq : r ∣ q := kc.symm.dvd_mul_left.mp (by rw [← he]; exact dvd_mul_left r h)
  have hqeq : q = r := Nat.dvd_antisymm hqr hrq
  refine ⟨hqeq, ?_⟩
  subst r
  exact Nat.eq_of_mul_eq_mul_right hq (by simpa only [mul_comm] using he)

 theorem reduced_fraction_circle_separation (Q q r h k : ℕ)
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hh : h < q) (hk : k < r) (hc : h.Coprime q) (kc : k.Coprime r)
    (hne : (q, h) ≠ (r, k)) (m : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(h : ℝ) / q - (k : ℝ) / r - m| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQR : (0 : ℝ) < Q := lt_of_lt_of_le hqR (by exact_mod_cast hqQ)
  let t : ℝ := (h : ℝ) / q - (k : ℝ) / r - m
  have ht : t ≠ 0 := by
    intro ht0
    have hhlo : 0 ≤ (h : ℝ) / q := by positivity
    have hklo : 0 ≤ (k : ℝ) / r := by positivity
    have hhhi : (h : ℝ) / q < 1 := (div_lt_one hqR).mpr (by exact_mod_cast hh)
    have hkhi : (k : ℝ) / r < 1 := (div_lt_one hrR).mpr (by exact_mod_cast hk)
    have hmlo : (-1 : ℝ) < m := by dsimp [t] at ht0; linarith
    have hmhi : (m : ℝ) < 1 := by dsimp [t] at ht0; linarith
    have hm : m = 0 := by
      have hlo : (-1 : ℤ) < m := by exact_mod_cast hmlo
      have hhi : m < (1 : ℤ) := by exact_mod_cast hmhi
      omega
    have heR : (h : ℝ) * r = (k : ℝ) * q := by
      dsimp [t] at ht0
      rw [hm, Int.cast_zero, sub_zero, sub_eq_zero] at ht0
      exact (div_eq_div_iff hqR.ne' hrR.ne').mp ht0
    have heN : h * r = k * q := by exact_mod_cast heR
    obtain ⟨hqr, hhk⟩ := reduced_fraction_cross_injective q r h k hq hr hc kc heN
    exact hne (Prod.ext hqr hhk)
  let N : ℤ := (h : ℤ) * r - (k : ℤ) * q - m * q * r
  have hN : (N : ℝ) = (q : ℝ) * r * t := by
    dsimp [N, t]
    push_cast
    field_simp
  have hN0 : N ≠ 0 := by
    intro hzero
    rw [hzero, Int.cast_zero] at hN
    exact ht ((mul_eq_zero.mp hN.symm).resolve_left (mul_ne_zero hqR.ne' hrR.ne'))
  have hN1 : (1 : ℤ) ≤ |N| := Int.one_le_abs hN0
  have hN1R : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast hN1
  rw [hN, abs_mul, abs_mul, abs_of_pos hqR, abs_of_pos hrR] at hN1R
  have hprod : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hrQ' : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
    nlinarith
  have hhprod := mul_le_mul_of_nonneg_right hprod (abs_nonneg t)
  change 1 / (Q : ℝ) ^ 2 ≤ |t|
  apply (div_le_iff₀ (sq_pos_of_pos hQR)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_HermitianEigenvector
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hermitian eigenvector cancellation -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem hermitian_eigenvector_left {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) (v : ι → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = (μ : ℂ) * (star u ⬝ᵥ v) := by
  have h : star u ⬝ᵥ (A *ᵥ v) = star (A *ᵥ u) ⬝ᵥ v := by
    rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]
  rw [h, heig, star_smul, smul_dotProduct]
  simp

theorem hermitian_eigenvector_commutator {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (D : Matrix ι ι ℂ) (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) :
    star u ⬝ᵥ ((D * A - A * D) *ᵥ u) = 0 := by
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
    heig, mulVec_smul, dotProduct_smul, hermitian_eigenvector_left hA u μ heig]
  simp only [smul_eq_mul, sub_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantMatrix
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact square of the finite cosecant matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
 theorem imaginaryKernelMatrix_hermitian (h : ι → ι → ℝ)
    (hskew : ∀ s t, h s t = -h t s) : (imaginaryKernelMatrix h).IsHermitian := by
  ext s t
  simp only [imaginaryKernelMatrix, conjTranspose_apply, Matrix.of_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [hskew t s]
  push_cast
  ring

 theorem imaginaryKernelMatrix_square_entry (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (imaginaryKernelMatrix h * imaginaryKernelMatrix h) s t =
      (if s = t then ((∑ r, h r s ^ 2 : ℝ) : ℂ) else 0) +
        (h s t : ℂ) * ((∑ r, k r s : ℝ) - ∑ r, k r t) +
          2 * (h s t : ℂ) * (k s t : ℂ) := by
  have he (r : ι) : imaginaryKernelMatrix h s r * imaginaryKernelMatrix h r t =
      ((h r s * h r t : ℝ) : ℂ) := by
    dsimp [imaginaryKernelMatrix]
    rw [hskew s r]
    push_cast
    calc
      _ = -(Complex.I * Complex.I) * ((h r s : ℂ) * (h r t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [← Complex.ofReal_sum, skew_kernel_square_entry h k hdiag kdiag kskew htriple]
  push_cast
  by_cases hst : s = t <;> simp [hst]

 theorem imaginaryKernelMatrix_square (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) :
    let A : Matrix ι ι ℂ := imaginaryKernelMatrix h
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
    A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
      (Complex.I • (D * A - A * D) : Matrix ι ι ℂ) +
        (2 : ℂ) • Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ)) := by
  dsimp only
  ext s t
  rw [imaginaryKernelMatrix_square_entry h k hdiag kdiag hskew kskew htriple]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    imaginaryKernelMatrix, Matrix.of_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    ]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SymmetricQuadraticBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite quadratic bound for the cosecant row estimate -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem real_symmetric_quadratic_upper (v : ι → ι → ℝ)
    (hv : ∀ s t, v s t = v t s) (u : ι → ℂ) :
    ‖star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u)‖ ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
  have he : star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u) =
      ∑ s, ∑ t, star (u s) * (v s t : ℂ) * u t := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hswap : (∑ s, ∑ t, |v s t| * ‖u t‖ ^ 2) =
      ∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [hv t s]
  have hfactor : (∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul, mul_comm]
  have havg : (∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hswap]
    rw [hfactor]
    ring
  rw [he]
  calc
    _ ≤ ∑ s, ‖∑ t, star (u s) * (v s t : ℂ) * u t‖ := norm_sum_le _ _
    _ ≤ ∑ s, ∑ t, ‖star (u s) * (v s t : ℂ) * u t‖ :=
      Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
    _ = ∑ s, ∑ t, |v s t| * ‖u s‖ * ‖u t‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have hh := mul_le_mul_of_nonneg_left (sq_nonneg (‖u s‖ - ‖u t‖)) (abs_nonneg (v s t))
      nlinarith
    _ = _ := havg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_KernelEigenvalueBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Schur's eigenvalue bound for the concrete finite kernel identity -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_diagonal_quadratic (d : ι → ℝ) (u : ι → ℂ) :
    star u ⬝ᵥ ((Matrix.diagonal (fun s => (d s : ℂ))) *ᵥ u) =
      ((∑ s, d s * ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  rw [show star (u s) * ((d s : ℂ) * u s) = (d s : ℂ) * (star (u s) * u s) by ring,
    Complex.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

 theorem kernel_eigenvalue_bound (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t))
    (B μ : ℝ) (hrow : ∀ s, (∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r| ≤ B)
    (u : ι → ℂ) (hu : 0 < ∑ s, ‖u s‖ ^ 2)
    (heig : imaginaryKernelMatrix h *ᵥ u = (μ : ℂ) • u) : μ ^ 2 ≤ B := by
  let A := imaginaryKernelMatrix h
  let D := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
  let V : Matrix ι ι ℂ := Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ))
  have hA : A.IsHermitian := imaginaryKernelMatrix_hermitian h hskew
  have hcomm := hermitian_eigenvector_commutator hA D u μ heig
  have hsq : star u ⬝ᵥ ((A * A) *ᵥ u) =
      ((μ ^ 2 * ∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mulVec_mulVec, heig, mulVec_smul, heig, smul_smul, dotProduct_smul,
      complex_self_quadratic]
    push_cast
    simp only [smul_eq_mul, pow_two]
  have hidentity := imaginaryKernelMatrix_square h k hdiag kdiag hskew kskew htriple
  change A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
    Complex.I • (D * A - A * D) + (2 : ℂ) • V at hidentity
  rw [hidentity, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, hcomm, smul_zero, sub_zero, smul_mulVec, dotProduct_smul,
    complex_diagonal_quadratic] at hsq
  have hreal := congrArg Complex.re hsq
  have htwo (z : ℂ) : ((2 : ℂ) • z).re = 2 * z.re := by simp [smul_eq_mul, Complex.mul_re]
  simp only [Complex.add_re, Complex.ofReal_re, htwo] at hreal
  have hsym : ∀ s t, h s t * k s t = h t s * k t s := by
    intro s t
    rw [hskew s t, kskew s t]
    ring
  have hv := real_symmetric_quadratic_upper (fun s t => h s t * k s t) hsym u
  have hvr : (star u ⬝ᵥ (V *ᵥ u)).re ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |h s t * k s t| :=
    (Complex.re_le_norm _).trans hv
  have hsum : (∑ s, (∑ r, h r s ^ 2) * ‖u s‖ ^ 2) +
      2 * (∑ s, ‖u s‖ ^ 2 * ∑ r, |h s r * k s r|) ≤
        B * ∑ s, ‖u s‖ ^ 2 := by
    calc
      _ = ∑ s, ‖u s‖ ^ 2 * ((∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r|) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro s _
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ ∑ s, ‖u s‖ ^ 2 * B := Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hfinal : μ ^ 2 * (∑ s, ‖u s‖ ^ 2) ≤ B * (∑ s, ‖u s‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hu).mp hfinal

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMatrixDuality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Hilbert-space duality for the large-sieve phase matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem finite_complex_cauchy_schwarz {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let V : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm v
  have hi : inner ℂ U V = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℂ U V)) (norm_inner_le_norm U V) 2
  rw [hi, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hh
  exact hh

 theorem finite_matrix_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ b : ι → ℂ, (∑ j, ‖(Fᴴ *ᵥ b) j‖ ^ 2) ≤ K * ∑ i, ‖b i‖ ^ 2)
    (c : κ → ℂ) :
    (∑ i, ‖(F *ᵥ c) i‖ ^ 2) ≤ K * ∑ j, ‖c j‖ ^ 2 := by
  let b := F *ᵥ c
  have hE : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hzero : (∑ i, ‖b i‖ ^ 2) = 0
  · change (∑ i, ‖b i‖ ^ 2) ≤ _
    rw [hzero]
    exact mul_nonneg hK hC
  have hEpos : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hE (Ne.symm hzero)
  have hid : star (Fᴴ *ᵥ b) ⬝ᵥ c = star b ⬝ᵥ b := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hcauchy := finite_complex_cauchy_schwarz (Fᴴ *ᵥ b) c
  rw [hid, complex_self_quadratic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE] at hcauchy
  have hmul := mul_le_mul_of_nonneg_right (hdual b) hC
  change (∑ i, ‖b i‖ ^ 2) ≤ _
  have hh : (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) ≤
      (K * ∑ j, ‖c j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ hEpos).mp hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantRowSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp row budget for the cosecant matrix -/

namespace Ostmann

open scoped BigOperators

 theorem cosecant_row_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s, cosecantKernel (x s) (x center) ^ 2) +
        2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| ≤
      1 / δ ^ 2 := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  have he (s : ι) : cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s) =
      cosecantKernel (x s) (x center) * cotangentKernel (x s) (x center) := by
    rw [cosecantKernel_skew (x center) (x s), cotangentKernel_skew (x center) (x s)]
    ring
  have hsum : (∑ s, cosecantKernel (x s) (x center) ^ 2) +
      2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| =
        ∑ s ∈ F, cosecantRowWeight (x s - x center) := by
    simp_rw [he]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp_rw [cosecantRowWeight_eq]
    apply (Finset.sum_erase_add _ _ (Finset.mem_univ center)).symm.trans ?_
    simp [cosecantRowWeight, F]
  have hb (s : ι) (hs : s ∈ F) :
      cosecantRowWeight (x s - x center) ≤ 3 / (Real.pi ^ 2 * (r s) ^ 2) := by
    have hd := hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
    change δ ≤ |r s| at hd
    have hhalf : |r s| ≤ 1 / 2 := abs_le.mpr
      ⟨(centeredCircleRemainder_bounds _).1, (centeredCircleRemainder_bounds _).2.le⟩
    have hh := cosecantRowWeight_bound (x s - x center) |r s|
      ⌊x s - x center + 1 / 2⌋ (lt_of_lt_of_le hδ hd) hhalf rfl
    simpa only [sq_abs] using hh
  rw [hsum]
  calc
    _ ≤ ∑ s ∈ F, 3 / (Real.pi ^ 2 * (r s) ^ 2) := Finset.sum_le_sum hb
    _ = (3 / Real.pi ^ 2) * ∑ s ∈ F, 1 / (r s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left (circleSeparated_inverse_square_row x δ hδ hx center) (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_HermitianNormBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing a finite Hermitian eigenvalue bound to its quadratic form -/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem hermitian_norm_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (B : ℝ) (hB : 0 ≤ B) (heig : ∀ i, |hA.eigenvalues i| ≤ B) : ‖A‖ ≤ B := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real,
    Real.norm_eq_abs] using heig i

 theorem matrix_quadratic_norm_bound (A : Matrix ι ι ℂ) (B : ℝ)
    (hB : ‖A‖ ≤ B) (u : ι → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ B * ∑ i, ‖u i‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let w : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ u)
  have hinner : inner ℂ v w = star u ⬝ᵥ (A *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hv : ‖v‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  have hw : ‖w‖ ≤ B * ‖v‖ := (Matrix.l2_opNorm_mulVec A v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  rw [← hinner]
  calc
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (B * ‖v‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg v)
    _ = B * ∑ i, ‖u i‖ ^ 2 := by rw [← hv]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CosecantHilbertBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Montgomery--Vaughan's finite unweighted Hilbert inequality

This is Theorem 1, inequality (1.2), of Montgomery--Vaughan (1974).
It is derived from the checked finite kernel cancellation and row estimate.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
 theorem cosecantMatrix_hermitian (x : ι → ℝ) : (cosecantMatrix x).IsHermitian :=
  imaginaryKernelMatrix_hermitian _ (fun _ _ => cosecantKernel_skew _ _)

 theorem cosecant_eigenvalue_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (μ : ℝ) (u : ι → ℂ)
    (hu : 0 < ∑ s, ‖u s‖ ^ 2) (heig : cosecantMatrix x *ᵥ u = (μ : ℂ) • u) :
    μ ^ 2 ≤ 1 / δ ^ 2 := by
  exact kernel_eigenvalue_bound
    (fun s t => cosecantKernel (x s) (x t))
    (fun s t => cotangentKernel (x s) (x t))
    (fun _ => cosecantKernel_self _) (fun _ => cotangentKernel_self _)
    (fun _ _ => cosecantKernel_skew _ _) (fun _ _ => cotangentKernel_skew _ _)
    (fun r s t hrs hrt hst => cosecantKernel_triple _ _ _
      (circleSeparated_sine_ne_zero x δ hδ hx hrs)
      (circleSeparated_sine_ne_zero x δ hδ hx hrt)
      (circleSeparated_sine_ne_zero x δ hδ hx hst))
    (1 / δ ^ 2) μ (cosecant_row_sum_bound x δ hδ hx) u hu heig

 theorem cosecantMatrix_norm_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) : ‖cosecantMatrix x‖ ≤ 1 / δ := by
  apply hermitian_norm_bound (cosecantMatrix_hermitian x) (1 / δ) (by positivity)
  intro i
  let hA := cosecantMatrix_hermitian x
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hu : 0 < ∑ s, ‖(hA.eigenvectorBasis i) s‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, hnorm]
    norm_num
  have hb := cosecant_eigenvalue_bound x δ hδ hx (hA.eigenvalues i)
    (hA.eigenvectorBasis i) hu (hA.mulVec_eigenvectorBasis i)
  have hinv : 0 < 1 / δ := by positivity
  have heq : 1 / δ ^ 2 = (1 / δ) ^ 2 := by ring
  rw [heq] at hb
  nlinarith [sq_abs (hA.eigenvalues i), abs_nonneg (hA.eigenvalues i)]

 theorem cosecant_hilbert_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (u : ι → ℂ) :
    ‖∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t‖ ≤
      (1 / δ) * ∑ s, ‖u s‖ ^ 2 := by
  have hb := matrix_quadratic_norm_bound (cosecantMatrix x) (1 / δ)
    (cosecantMatrix_norm_bound x δ hδ hx) u
  have he : star u ⬝ᵥ (cosecantMatrix x *ᵥ u) =
      Complex.I * (∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t) := by
    simp only [dotProduct, mulVec, Pi.star_apply, cosecantMatrix, imaginaryKernelMatrix,
      Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveGeometricKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite exponential kernel for the additive large sieve -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_add (s t : ℝ) :
    sieveHalfPhase (s + t) = sieveHalfPhase s * sieveHalfPhase t := by
  simp only [sieveHalfPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

 theorem sieveHalfPhase_sine (t : ℝ) :
    (2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ) =
      sieveHalfPhase t - sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

 theorem sieveHalfPhase_two_step (s t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) * sieveHalfPhase s =
      sieveHalfPhase (s + t) - sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_sine, sieveHalfPhase_add, sub_eq_add_neg s t, sieveHalfPhase_add]
  ring

 theorem sieve_geometric_kernel_mul (M : ℕ) (J t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) *
      (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
        sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hs := sieveHalfPhase_two_step (2 * (J + M) * t) t
    rw [show 2 * (J + (M : ℝ)) * t + t = (2 * (J + (M + 1 : ℕ)) - 1) * t by
      push_cast; ring,
      show 2 * (J + (M : ℝ)) * t - t = (2 * (J + M) - 1) * t by ring] at hs
    rw [hs]
    ring

 theorem sieve_geometric_kernel (M : ℕ) (J t : ℝ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
      ((sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) /
        ((2 : ℂ) * Complex.I)) * (Real.sin (Real.pi * t) : ℂ)⁻¹ := by
  have hs := sieve_geometric_kernel_mul M J t
  have htC : (Real.sin (Real.pi * t) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hfactor : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero hfactor htC))
  rw [hs, div_eq_mul_inv]
  symm
  calc
    _ = (((2 : ℂ) * Complex.I) * ((2 : ℂ) * Complex.I)⁻¹) *
        ((Real.sin (Real.pi * t) : ℂ) * (Real.sin (Real.pi * t) : ℂ)⁻¹) *
          (sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hfactor, mul_inv_cancel₀ htC]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SievePhaseGram
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite Gram expansion of the large-sieve phase matrix -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_star (t : ℝ) : star (sieveHalfPhase t) = sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

 theorem sieveHalfPhase_difference (s t : ℝ) :
    sieveHalfPhase s * star (sieveHalfPhase t) = sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_star, ← sieveHalfPhase_add, sub_eq_add_neg]

 theorem finite_complex_norm_expansion {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((‖∑ s, f s‖ ^ 2 : ℝ) : ℂ) = ∑ s, ∑ t, f s * star (f t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [← Complex.star_def, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

 theorem sieve_phase_gram {ι : Type*} [Fintype ι] (x : ι → ℝ) (b : ι → ℂ)
    (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, b s * star (b t) *
        ∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t)) := by
  simp only [Complex.ofReal_sum, finite_complex_norm_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [star_mul]
  rw [show 2 * (J + (n : ℝ)) * (x s - x t) =
    2 * (J + (n : ℝ)) * x s - 2 * (J + (n : ℝ)) * x t by ring,
    ← sieveHalfPhase_difference]
  ring

 theorem twisted_cosecant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (b : ι → ℂ) (L : ℝ) :
    ‖∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)‖ ≤ (1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  let u := fun s => star (b s * sieveHalfPhase (L * x s))
  have he : (∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)) =
      ∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    simp only [u, star_star, star_mul]
    rw [show L * (x s - x t) = L * x s - L * x t by ring,
      ← sieveHalfPhase_difference]
    ring
  rw [he]
  have hb := cosecant_hilbert_bound x δ hδ hx u
  simpa only [u, norm_star, norm_mul, sieveHalfPhase_norm, mul_one] using hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SieveDualEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sharp dual large-sieve estimate from the finite Hilbert inequality -/

namespace Ostmann

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
 theorem sieve_pair_kernel (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (s t : ι) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t))) =
      (if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ) := by
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst, zero_add]
    simpa only [cosecantKernel, Complex.ofReal_inv] using
      sieve_geometric_kernel M J (x s - x t) (circleSeparated_sine_ne_zero x δ hδ hx hst)

 theorem sieve_dual_energy_identity (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)) := by
  rw [sieve_phase_gram]
  simp_rw [sieve_pair_kernel x δ hδ hx M J]
  have he (s t : ι) : b s * star (b t) *
      ((if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ)) =
      (if s = t then (M : ℂ) * ((‖b s‖ ^ 2 : ℝ) : ℂ) else 0) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (b s * star (b t) * sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ) -
            b s * star (b t) * sieveHalfPhase ((2 * J - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ)) := by
    by_cases hst : s = t
    · subst t
      simp only [↓reduceIte, sub_self, mul_zero, sieveHalfPhase_zero,
        cosecantKernel_self, Complex.ofReal_zero, mul_one, add_zero]
      rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
      ring
    · simp only [hst, ↓reduceIte, zero_add, div_eq_mul_inv]
      ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_mul, twistedCosecantSum]

 theorem sieve_dual_energy_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    (∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  have hi := sieve_dual_energy_identity x δ hδ hx b M J
  have htop := twisted_cosecant_bound x δ hδ hx b (2 * (J + M) - 1)
  have hbottom := twisted_cosecant_bound x δ hδ hx b (2 * J - 1)
  change ‖twistedCosecantSum x b (2 * (J + M) - 1)‖ ≤ _ at htop
  change ‖twistedCosecantSum x b (2 * J - 1)‖ ≤ _ at hbottom
  have htri := norm_add_le (((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) : ℂ)
    (((2 : ℂ) * Complex.I)⁻¹ *
      (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)))
  have hdiff := norm_sub_le (twistedCosecantSum x b (2 * (J + M) - 1))
    (twistedCosecantSum x b (2 * J - 1))
  rw [← hi] at htri
  have hE : 0 ≤ ∑ s, ‖b s‖ ^ 2 := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hN : 0 ≤ ∑ n ∈ Finset.range M,
      ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hE),
    norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I] at htri
  norm_num at htri
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SeparatedAdditiveSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite additive sieve for circle-separated frequencies -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem sievePhaseMatrix_adjoint {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (J : ℝ) (b : ι → ℂ) (n : Fin M) :
    ((sievePhaseMatrix x M J)ᴴ *ᵥ b) n =
      star (∑ s, star (b s) * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)) := by
  simp only [mulVec, dotProduct, conjTranspose_apply, sievePhaseMatrix, Matrix.of_apply,
    star_sum, star_mul, star_star]

 theorem separated_additive_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (c : Fin M → ℂ) :
    (∑ s, ‖∑ n, c n * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ n, ‖c n‖ ^ 2 := by
  have hdual (b : ι → ℂ) :
      (∑ n, ‖((sievePhaseMatrix x M J)ᴴ *ᵥ b) n‖ ^ 2) ≤
        ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
    simp only [sievePhaseMatrix_adjoint, norm_star]
    have hb := sieve_dual_energy_bound x δ hδ hx (fun s => star (b s)) M J
    rw [← Fin.sum_univ_eq_sum_range] at hb
    simpa only [norm_star] using hb
  have hK : 0 ≤ (M : ℝ) + 1 / δ := by positivity
  have h := finite_matrix_duality (sievePhaseMatrix x M J) ((M : ℝ) + 1 / δ) hK hdual c
  simpa only [mulVec, dotProduct, sievePhaseMatrix, Matrix.of_apply, mul_comm] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProof
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published additive large sieve, with its precise downstream constant

The finite cosecant Hilbert inequality and duality prove the separated-frequency
estimate. Reduced fractions of denominator at most Q are 1/Q²-separated.
This proves the specialization of Montgomery--Vaughan (1973), Theorem 1,
used throughout the conditional development.
-/

namespace Ostmann

open scoped BigOperators

 theorem reducedFractionPoint_separated (Q : ℕ) :
    CircleSeparated (reducedFractionPoint Q) (1 / (Q : ℝ) ^ 2) := by
  intro s t hst m
  rcases s with ⟨⟨q, hq⟩, ⟨h, hh⟩⟩
  rcases t with ⟨⟨r, hr⟩, ⟨k, hk⟩⟩
  simp only [Finset.mem_Icc] at hq hr
  simp only [reducedNumerators, Finset.mem_filter, Finset.mem_range] at hh hk
  have hne : (q, h) ≠ (r, k) := by
    intro he
    have hqr := congrArg Prod.fst he
    have hhk := congrArg Prod.snd he
    dsimp at hqr hhk
    subst r
    subst k
    exact hst rfl
  exact reduced_fraction_circle_separation Q q r h k (by omega) (by omega)
    hq.2 hr.2 hh.1 hk.1 hh.2 hk.2 hne m

 theorem sieveAdditivePhase_eq_half (q h : ℕ) (J : ℤ) (n : ℕ) :
    sieveAdditivePhase q h (J + (n : ℤ)) =
      sieveHalfPhase (2 * ((J : ℝ) + (n : ℝ)) * ((h : ℝ) / q)) := by
  unfold sieveAdditivePhase sieveHalfPhase
  congr 1
  push_cast
  ring

 theorem reducedFraction_sum (Q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ s : ReducedFractionIndex Q, f s.1.val s.2.val) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q, f q h := by
  rw [Fintype.sum_sigma]
  change (∑ q : Finset.Icc 1 Q, ∑ h : reducedNumerators q.val, f q.val h.val) = _
  simp_rw [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort (Finset.Icc 1 Q)
    (fun q : ℕ => ∑ h ∈ reducedNumerators q, f q h)

 theorem publishedAdditiveLargeSieve : PublishedAdditiveLargeSieve := by
  classical
  intro M Q _hM hQ J c
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hδ : 0 < 1 / (Q : ℝ) ^ 2 := by positivity
  have h := separated_additive_sieve (reducedFractionPoint Q) (1 / (Q : ℝ) ^ 2)
    hδ (reducedFractionPoint_separated Q) M (J : ℝ) c
  have hconst : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by field_simp
  rw [hconst] at h
  change (∑ s : ReducedFractionIndex Q,
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((s.2.val : ℝ) / s.1.val))‖ ^ 2) ≤ _ at h
  rw [reducedFraction_sum Q (fun q h =>
    ‖∑ n, c n * sieveHalfPhase (2 * ((J : ℝ) + (n.val : ℝ)) *
      ((h : ℝ) / q))‖ ^ 2)] at h
  simpa only [additiveSieveSum, sieveAdditivePhase_eq_half] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_MainWithoutAdditiveSieve
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both main theorems after discharging the additive large sieve -/

namespace Ostmann

theorem inverseGoldbach_without_additive_sieve
    (hsize : PublishedSummandSizeBound) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_progression_input publishedAdditiveLargeSieve hsize hSiegel sieve hD

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_MainWithoutSummandSize
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both main theorems after proving the required summand-size bounds -/

namespace Ostmann

theorem inverseGoldbach_without_summand_size_oai
    (hSiegel : PublishedSiegelBound) (sieve : PublishedQuadraticLargeSieve)
    (hD : PublishedComplexZeroDensity actualCharacterZeros) :
    InverseGoldbach :=
  inverseGoldbach_without_additive_sieve publishedSummandSizeBound hSiegel sieve hD

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.inverseGoldbach_without_summand_size_oai := @OAI.Ostmann.inverseGoldbach_without_summand_size_oai
