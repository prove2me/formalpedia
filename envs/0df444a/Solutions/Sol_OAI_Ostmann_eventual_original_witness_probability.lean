-- Prove2me | solution 1 for OAI.Ostmann.eventual_original_witness_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:14:49.354126+00:00
-- url     : https://prove2.me/submissions/691eab0b-777a-44f1-aee8-8c8e9b6f61ec

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_eventual_large_kernel_prime_moment
import Theorems.Thm_OAI_Ostmann_eventual_original_outer_first_moment
import Theorems.Thm_OAI_Ostmann_eventual_original_small_second_moment

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem stdAddChar_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [← Complex.inv_eq_conj hn, AddChar.map_neg_eq_inv]

theorem additiveFourier_inversion {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a : ZMod p, additiveFourier f a * ZMod.stdAddChar (a * x) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  calc
    f x = (p : ℂ)⁻¹ * ∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a := by
      simpa only [smul_eq_mul] using hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [additiveFourier]
      ring

theorem additiveFourier_conjugate_coefficient {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x)) =
      (p : ℂ) * conj (additiveFourier f a) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem additiveFourier_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖f x‖ ^ 2) =
      (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2 := by
  have heq : (∑ x : ZMod p, f x * conj (f x)) =
      (p : ℂ) * ∑ a : ZMod p, additiveFourier f a * conj (additiveFourier f a) := by
    calc
      _ = ∑ x : ZMod p, ∑ a : ZMod p,
          additiveFourier f a * ZMod.stdAddChar (a * x) * conj (f x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.sum_mul, ← additiveFourier_inversion]
      _ = ∑ a : ZMod p, additiveFourier f a *
          ∑ x : ZMod p, ZMod.stdAddChar (x * a) * conj (f x) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm x a]
        ring
      _ = _ := by
        simp_rw [additiveFourier_conjugate_coefficient]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at heq
  exact_mod_cast heq

/-- Additive Parseval with the manuscript's probability convention. -/
theorem additiveFourier_parseval {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖additiveFourier f a‖ ^ 2) =
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  rw [additiveFourier_energy f]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RealQuadraticPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real quadratic phases and their linear correlations

These are the concrete exponential sums used in the inverse quadratic step.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem realAdditivePhase_add (x y : ℝ) :
    realAdditivePhase (x + y) = realAdditivePhase x * realAdditivePhase y := by
  unfold realAdditivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realAdditivePhase_nat_mul (n : ℕ) (x : ℝ) :
    realAdditivePhase ((n : ℝ) * x) = realAdditivePhase x ^ n := by
  unfold realAdditivePhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

theorem densityFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [densityFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, additiveFourier_parseval, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem densityFourier_energy_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) ≤ q := by
  rw [densityFourier_energy]
  calc
    _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum (fun x _ => by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCRTProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

/-- The hypotheses of the small-kernel bound hold for the original finite
product of centered density functions. -/
theorem densityCRTList_energy (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (∑ a : ZMod ps.prod, ‖densityFourier (densityCRTList ps hp hc S).value a‖ ^ 2) ≤ ps.prod := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  exact densityFourier_energy_le _ (densityCRTList ps hp hc S).norm_le_one

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCorrelationExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the two finite quadratic sums before the kernel average -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem finite_correlation_expansion {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (F : κ → ι → ℂ) (G : υ → ι → ℂ) :
    (∑ s ∈ S, (∑ w ∈ W, F w s) * conj (∑ v ∈ V, G v s)) =
      ∑ w ∈ W, ∑ v ∈ V, ∑ s ∈ S, F w s * conj (G v s) := by
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_BonamiMonomialFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-cube inequality for a concrete family of distinct monomials -/

namespace Ostmann

open scoped BigOperators

private theorem monomialCoefficients_apply {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (hσ : Function.Injective σ)
    (a : ι → ℝ) (i : ι) : monomialCoefficients σ a (σ i) = a i := by
  classical
  unfold monomialCoefficients
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp only [ite_eq_right_iff]
    exact fun h => (hji (hσ h)).elim
  · simp

private theorem monomialCoefficients_sum {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (a : ι → ℝ) (F : Finset P → ℝ) :
    (∑ Q : Finset P, monomialCoefficients σ a Q * F Q) = ∑ i, a i * F (σ i) := by
  classical
  simp only [monomialCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

private theorem monomialCoefficients_energy {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (hσ : Function.Injective σ)
    (a : ι → ℝ) (F : Finset P → ℝ) :
    (∑ Q : Finset P, F Q * (monomialCoefficients σ a Q) ^ 2) =
      ∑ i, F (σ i) * (a i) ^ 2 := by
  classical
  have he (Q : Finset P) : (monomialCoefficients σ a Q) ^ 2 =
      monomialCoefficients σ (fun i => (a i) ^ 2) Q := by
    by_cases hQ : ∃ i, σ i = Q
    · obtain ⟨i, rfl⟩ := hQ
      rw [monomialCoefficients_apply σ hσ, monomialCoefficients_apply σ hσ]
    · have hne (i : ι) : σ i ≠ Q := fun hi => hQ ⟨i, hi⟩
      simp [monomialCoefficients, hne]
  simp_rw [he, mul_comm (F _)]
  rw [monomialCoefficients_sum]

/-- Apply the published cube bound after inserting the coefficient array
by zero outside the actual monomial family. -/
theorem bonami_monomial_family (hB : PublishedBonamiBound)
    {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) (hσ : Function.Injective σ) (a : ι → ℝ)
    (l : ℕ) (hl : 0 < l) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ i, a i * rademacherMonomial (σ i) ε| ^ (2 * l) ≤
      (∑ i, ((2 * l - 1 : ℕ) : ℝ) ^ (σ i).card * (a i) ^ 2) ^ l := by
  have hb := hB P l hl (monomialCoefficients σ a)
  simp_rw [monomialCoefficients_sum] at hb
  rw [monomialCoefficients_energy σ hσ] at hb
  exact hb

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarefreeBonami
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bonami's inequality for the actual squarefree coefficient indices -/

namespace Ostmann

open scoped BigOperators

theorem mem_primeFactorSubset (P : Finset ℕ) (s : ℕ) (p : P) :
    p ∈ primeFactorSubset P s ↔ p.val ∈ s.primeFactors := by
  simp [primeFactorSubset]

theorem primeFactorSubset_map (P : Finset ℕ) (s : ℕ) (hs : s.primeFactors ⊆ P) :
    (primeFactorSubset P s).map (Function.Embedding.subtype (· ∈ P)) = s.primeFactors := by
  ext p
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, mem_primeFactorSubset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hp
    exact ⟨⟨p, hs hp⟩, hp, rfl⟩

theorem primeFactorSubset_card (P : Finset ℕ) (s : ℕ) (hs : s.primeFactors ⊆ P) :
    (primeFactorSubset P s).card = s.primeFactors.card := by
  rw [← primeFactorSubset_map P s hs, Finset.card_map]

theorem primeFactorSubset_injective (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P) :
    Function.Injective (fun s : S => primeFactorSubset P s.val) := by
  intro s t hst
  apply Subtype.ext
  have hp := congrArg (fun Q : Finset P => Q.map (Function.Embedding.subtype (· ∈ P))) hst
  rw [primeFactorSubset_map P s.val (hP s s.property),
    primeFactorSubset_map P t.val (hP t t.property)] at hp
  have hh := congrArg (fun Q : Finset ℕ => ∏ p ∈ Q, p) hp
  rwa [Nat.prod_primeFactors_of_squarefree (hS s s.property),
    Nat.prod_primeFactors_of_squarefree (hS t t.property)] at hh

/-- This is the even moment bound in the manuscript, indexed by
the squarefree integers themselves. -/
theorem bonami_squarefree_family (hB : PublishedBonamiBound) (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (a : S → ℝ) (l : ℕ) (hl : 0 < l) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool,
        |∑ s : S, a s * rademacherMonomial (primeFactorSubset P s.val) ε| ^ (2 * l) ≤
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * (a s) ^ 2) ^ l := by
  have h := bonami_monomial_family hB P (fun s : S => primeFactorSubset P s.val)
    (primeFactorSubset_injective P S hS hP) a l hl
  simpa only [primeFactorSubset_card P _ (hP _ (Subtype.property _))] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_SquarefreeEulerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted reciprocal squarefree sum in the coefficient estimate -/

namespace Ostmann

open scoped BigOperators

theorem squarefree_weighted_reciprocal_le_product (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      ∏ p ∈ P, (1 + u / (p : ℝ)) := by
  classical
  have hinj : Set.InjOn Nat.primeFactors (↑S : Set ℕ) := by
    intro a ha b hb he
    calc
      a = ∏ p ∈ a.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hS a ha)).symm
      _ = ∏ p ∈ b.primeFactors, p := by rw [he]
      _ = b := Nat.prod_primeFactors_of_squarefree (hS b hb)
  have hterm (s : ℕ) (hs : s ∈ S) :
      u ^ s.primeFactors.card / (s : ℝ) = ∏ p ∈ s.primeFactors, u / (p : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (hS s hs)]
  calc
    _ = ∑ s ∈ S, ∏ p ∈ s.primeFactors, u / (p : ℝ) :=
      Finset.sum_congr rfl hterm
    _ = ∑ Q ∈ S.image Nat.primeFactors, ∏ p ∈ Q, u / (p : ℝ) :=
      (Finset.sum_image (f := fun Q : Finset ℕ => ∏ p ∈ Q, u / (p : ℝ)) hinj).symm
    _ ≤ ∑ Q ∈ P.powerset, ∏ p ∈ Q, u / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro Q hQ
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hQ
        exact Finset.mem_powerset.mpr (hP s hs)
      · intro Q hQ hnot
        exact Finset.prod_nonneg (fun p hp => div_nonneg hu (Nat.cast_nonneg _))
    _ = _ := (Finset.prod_one_add P).symm

theorem squarefree_weighted_reciprocal_le_exp (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      Real.exp (u * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  apply (squarefree_weighted_reciprocal_le_product S P hS hP u hu).trans
  calc
    _ ≤ ∏ p ∈ P, Real.exp (u / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (u / (p : ℝ))
    _ = Real.exp (∑ p ∈ P, u / (p : ℝ)) := (Real.exp_sum P _).symm
    _ = _ := by simp only [div_eq_mul_inv, Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeSumInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem prime_log_weight_le (Q : ℕ) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeReciprocalBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary logarithmic bound for the reciprocal-prime sum -/

namespace Ostmann

open scoped BigOperators

private theorem prime_dyadic_reciprocal_bound (S : Finset ℕ) (j : ℕ) (hj : 1 ≤ j)
    (hS : ∀ p ∈ S, p.Prime ∧ 2 ^ j ≤ p ∧ p ≤ 2 ^ (j + 1)) :
    (∑ p ∈ S, (p : ℝ)⁻¹) ≤ 4 / (j : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hd : 0 < (2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) := by positivity
  have hlogsum : (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log 4 * (2 ^ (j + 1) : ℕ) := by
    apply le_trans _ (prime_log_weight_le (2 ^ (j + 1)))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Nat.mem_primesLE.mpr ⟨(hS p hp).2.2, (hS p hp).1⟩
    · intro p hp hn
      exact Real.log_natCast_nonneg p
  calc
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, hlo, hhi⟩ := hS p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlow : (2 : ℝ) ^ j ≤ p := by exact_mod_cast hlo
      have hlog : (j : ℝ) * Real.log 2 ≤ Real.log p := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hlow
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ hp0 hd).mpr
      simp only [one_mul]
      calc
        _ ≤ (p : ℝ) * Real.log p := mul_le_mul hlow hlog (by positivity) hp0.le
        _ = _ := mul_comm _ _
    _ = (∑ p ∈ S, Real.log (p : ℝ)) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (Real.log 4 * (2 ^ (j + 1) : ℕ)) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2)) :=
      div_le_div_of_nonneg_right hlogsum hd.le
    _ = 4 / (j : ℝ) := by
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [hlog4, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      field_simp
      ring

theorem prime_reciprocal_sum_le_harmonic (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (harmonic (Nat.log 2 N) : ℝ) := by
  classical
  let P := Nat.primesLE N
  let K := Nat.log 2 N
  have hmaps (p : ℕ) (hp : p ∈ P) : Nat.log 2 p ∈ Finset.Icc 1 K := by
    have hprime := Nat.prime_of_mem_primesLE hp
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.log_pos (by decide) hprime.two_le
    · exact Nat.log_mono_right (Nat.le_of_mem_primesLE hp)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 K, 4 / (j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply prime_dyadic_reciprocal_bound _ j (Finset.mem_Icc.mp hj).1
      intro p hp
      obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
      refine ⟨Nat.prime_of_mem_primesLE hp, ?_, ?_⟩
      · rw [← he]
        exact Nat.pow_log_le_self 2 (Nat.prime_of_mem_primesLE hp).ne_zero
      · rw [← he]
        exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p).le
    _ = 4 * (harmonic K : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv, Finset.mul_sum]

theorem prime_reciprocal_sum_le_log (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (1 + Real.log (Nat.log 2 N)) := by
  exact (prime_reciprocal_sum_le_harmonic N).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by norm_num))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquarefreeCoefficientBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential weighted squarefree coefficient budget at the paper's scales -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem prime_reciprocal_exponential_cutoff (C T : ℝ)
    (hT : 1 ≤ T) (N : ℕ) (hN : (N : ℝ) ≤ Real.exp (C * T)) :
    (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤
      4 * (1 + Real.log (max 1 (C / Real.log 2)) + Real.log T) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := max 1 (C / Real.log 2)
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  apply (prime_reciprocal_sum_le_log N).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  by_cases hj : Nat.log 2 N = 0
  · simp only [hj, Nat.cast_zero, Real.log_zero]
    linarith
  · have hNp : 0 < N := by
      by_contra hh
      have : N = 0 := Nat.eq_zero_of_not_pos hh
      simp [this] at hj
    have hjp : (0 : ℝ) < Nat.log 2 N := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 hNp.ne'
    have hl : (Nat.log 2 N : ℝ) * Real.log 2 ≤ C * T := by
      calc
        _ = Real.log ((2 : ℝ) ^ (Nat.log 2 N)) := (Real.log_pow _ _).symm
        _ ≤ Real.log N := Real.log_le_log (by positivity) hpow
        _ ≤ C * T := (Real.log_le_iff_le_exp (by exact_mod_cast hNp)).mpr hN
    have hjbound : (Nat.log 2 N : ℝ) ≤ D * T := by
      have hh : C ≤ D * Real.log 2 := (div_le_iff₀ hl2).mp (le_max_right _ _)
      nlinarith
    have hlog : Real.log (Nat.log 2 N) ≤ Real.log D + Real.log T := by
      calc
        _ ≤ Real.log (D * T) := Real.log_le_log hjp hjbound
        _ = _ := Real.log_mul hD0.ne' (by linarith)
    linarith

/-- The exponent `1/10^6` is the paper's moment scale; the denominator
budget is measured against `T^(1-10^-7)`, the scale of `K`. -/
theorem squarefree_coefficient_budget (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ N) →
      0 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
        Real.exp (ε * T ^ (9999999 / 10000000 : ℝ)) := by
  let μ : ℝ := 1 / 1000000
  let κ : ℝ := 9999999 / 10000000
  let D := max 1 (C / Real.log 2)
  let A := 1 + Real.log D
  have hD : 1 ≤ D := le_max_left _ _
  have hA : 0 ≤ A := by dsimp [A]; linarith [Real.log_nonneg hD]
  have hδ : 0 < κ - μ := by norm_num [κ, μ]
  have hlog := (isLittleO_log_rpow_atTop hδ).bound (show 0 < ε / 32 by positivity)
  have hconst := (tendsto_rpow_atTop hδ).eventually_ge_atTop (32 * A / ε)
  filter_upwards [hlog, hconst, eventually_ge_atTop (1 : ℝ)] with T hl hc hT N S u hN hS hu huU
  have hT0 : 0 < T := by linarith
  have hp := prime_reciprocal_exponential_cutoff C T hT N hN
  have hl' : Real.log T ≤ ε / 32 * T ^ (κ - μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT),
      abs_of_nonneg (Real.rpow_nonneg hT0.le _)] using hl
  have hc' : A ≤ ε / 32 * T ^ (κ - μ) := by
    have hh := (div_le_iff₀ hε).mp hc
    calc
      A = (32 * A) / 32 := by ring
      _ ≤ (T ^ (κ - μ) * ε) / 32 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = ε / 32 * T ^ (κ - μ) := by ring
  have hsum : (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      Real.exp (u * ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) := by
    apply squarefree_weighted_reciprocal_le_exp S (Nat.primesLE N) (fun s hs => (hS s hs).1) _ u hu
    intro s hs p hp
    obtain ⟨hpp, hdiv, hs0⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) hdiv).trans (hS s hs).2, hpp⟩
  apply hsum.trans
  apply Real.exp_le_exp.mpr
  have hbase : (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ≤ 4 * (A + Real.log T) := by
    simpa [A, D, add_assoc] using hp
  have hsmall : A + Real.log T ≤ ε / 16 * T ^ (κ - μ) := by linarith
  calc
    _ ≤ (4 * T ^ μ) * (4 * (A + Real.log T)) :=
      mul_le_mul huU hbase (by positivity) (by positivity)
    _ ≤ (4 * T ^ μ) * (4 * (ε / 16 * T ^ (κ - μ))) := by gcongr
    _ = ε * (T ^ μ * T ^ (κ - μ)) := by ring
    _ = ε * T ^ κ := by
      rw [← Real.rpow_add hT0]
      congr 2
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_PrimeSubsetProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of distinct primes index the amplified coefficient array -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubset_product_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun Q : Finset ℕ => ∏ p ∈ Q, p) {Q | Q ⊆ P} := by
  intro Q hQ R hR heq
  have h := congrArg Nat.primeFactors heq
  rwa [Nat.primeFactors_prod (fun p hp => hP p (hQ hp)),
    Nat.primeFactors_prod (fun p hp => hP p (hR hp))] at h

theorem primeSubsetProducts_card (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) : (primeSubsetProducts P k).card = P.card.choose k := by
  rw [primeSubsetProducts, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard k P
  · intro Q hQ R hR h
    exact primeSubset_product_injective P hP
      (Finset.mem_powersetCard.mp hQ).1 (Finset.mem_powersetCard.mp hR).1 h

theorem primeSubsetProducts_mem_range (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (hZ : ∀ p ∈ P, p ≤ Z) : primeSubsetProducts P k ⊆ oddSquarefreeRange (Z ^ k) := by
  intro s hs
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQ
  have hprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have hsf := primeSubset_product_squarefree Q hprime
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsf.ne_zero, ?_⟩, ?_, hsf⟩
  · simpa only [hcard] using Finset.prod_le_pow_card Q (fun p => p) Z (fun p hp => hZ p (hQP hp))
  · have ho : ∀ p ∈ Q, Odd p := fun p hp => hodd p (hQP hp)
    clear hprime hsf hcard hQP hQ hs
    induction Q using Finset.induction_on with
    | empty => simp
    | @insert p Q hp ih =>
      rw [Finset.prod_insert hp]
      exact (ho p (Finset.mem_insert_self _ _)).mul
        (ih (fun q hq => ho q (Finset.mem_insert_of_mem hq)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_LowWeightEulerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Euler-product constants for the large-kernel coefficient energy -/

namespace Ostmann

open scoped BigOperators

/-- The coarser small-kernel divisor factor is still harmless compared with
its `exp(-.9 K)` loss. -/
theorem small_kernel_divisor_product_bound (K : ℕ) :
    (1 + Real.sqrt 2 / 16) ^ K ≤ Real.exp ((K : ℝ) / 10) := by
  have hs : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hlocal : 1 + Real.sqrt 2 / 16 ≤ Real.exp (1 / 10 : ℝ) := by
    apply le_trans _ (Real.add_one_le_exp (1 / 10 : ℝ))
    linarith
  calc
    _ ≤ (Real.exp (1 / 10 : ℝ)) ^ K := pow_le_pow_left₀ (by positivity) hlocal K
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_WeightedCorrelationEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor sum after the large-kernel pair correlations -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_sum_energy_gram {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ) (G : κ → ι → ℂ) :
    (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) =
      (∑ d ∈ D, ∑ e ∈ D, (c d * conj (c e)) *
        ∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))).re := by
  have hpoint (s : ι) : μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2 =
      ((μ s : ℂ) * ((∑ d ∈ D, c d * G d s) * conj (∑ e ∈ D, c e * G e s))).re := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp_rw [hpoint]
  rw [← Complex.re_sum]
  congr 1
  have hmul (s : ι) : (μ s : ℂ) * ((∑ d ∈ D, c d * G d s) * conj (∑ e ∈ D, c e * G e s)) =
      (∑ d ∈ D, (μ s : ℂ) * (c d * G d s)) * conj (∑ e ∈ D, c e * G e s) := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [hmul]
  rw [finite_correlation_expansion]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [map_mul]
  ring

theorem weighted_sum_energy_le_correlations {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ) (G : κ → ι → ℂ) :
    (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      ∑ d ∈ D, ∑ e ∈ D, (‖c d‖ * ‖c e‖) *
        ‖∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))‖ := by
  rw [weighted_sum_energy_gram, Complex.re_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro e he
  simpa only [norm_mul, Complex.norm_conj] using Complex.re_le_norm
    ((c d * conj (c e)) * ∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SchwartzWeightVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete variation bounds for the quadratic Schwartz weight -/

namespace Ostmann

open scoped SchwartzMap

theorem schwartz_norm_sub_le (Φ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    ‖Φ x - Φ y‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ * |x - y| := by
  have hd (z : ℝ) : ‖fderiv ℝ Φ z‖ ≤ SchwartzMap.seminorm ℝ 0 1 Φ := by
    simpa only [norm_iteratedFDeriv_one] using Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (s := Set.univ) (fun _ _ => Φ.differentiableAt)
    (fun z _ => hd z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetQuadratic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quadratic density sums indexed by prime divisors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

theorem primeSet_prod_le_of_subset (P U : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) : U.toList.prod ≤ P.toList.prod := by
  have he (Q : Finset ℕ) : Q.toList.prod = ∏ p ∈ Q, p := by
    simp
  rw [he, he]
  exact Finset.prod_le_prod_of_subset_of_one_le hU (fun _ _ => Nat.zero_le _)
    (fun p hp _ => (hP p hp).one_lt.le)

theorem primeSet_prod_dvd_of_subset (P U : Finset ℕ) (hU : U ⊆ P) :
    U.toList.prod ∣ P.toList.prod := by
  simpa using Finset.prod_dvd_prod_of_subset U P (fun p : ℕ => p) hU

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCompactCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite cutoffs for compactly supported quadratic transforms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticDensityTerm_mem_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s w : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hw : 0 < w) (hΦ : ∀ x : ℝ, C < x → Φ x = 0)
    (hne : quadraticDensityTerm g a θ Φ R v s w ≠ 0) :
    w ∈ quadraticCompactCutoff q R v C N := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (N : ℝ) ≤ s := Nat.cast_le.mpr hs
  have hsupport : (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) ≤ C := by
    by_contra hh
    have hz := hΦ _ (lt_of_not_ge hh)
    exact hne (by simp only [quadraticDensityTerm, hz, mul_zero])
  have hb : (w : ℝ) ^ 2 ≤ C * R * q / ((N : ℝ) * v) := by
    apply (le_div_iff₀ (mul_pos hNR hv)).mpr
    have hh := (div_le_iff₀ (mul_pos hR hq)).mp hsupport
    have hm := mul_le_mul_of_nonneg_right hsR (show 0 ≤ v * (w : ℝ) ^ 2 by positivity)
    nlinarith only [hh, hm]
  exact Finset.mem_Ioc.mpr ⟨hw, Nat.le_floor (Real.le_sqrt_of_sq_le hb)⟩

/-- Compact support makes the positive quadratic series exactly finite,
with one common cutoff for every index in the dyadic segment. -/
theorem positiveQuadraticSum_eq_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hΦ : ∀ x : ℝ, C < x → Φ x = 0) :
    positiveQuadraticSum g a θ Φ R v s =
      quadraticDensitySum g (quadraticCompactCutoff q R v C N) a θ Φ R v s := by
  classical
  unfold positiveQuadraticSum quadraticDensitySum
  congr 1
  calc
    _ = ∑ w ∈ quadraticCompactCutoff q R v C N,
        if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0 := by
      apply tsum_eq_sum
      intro w hw
      by_cases hw0 : 0 < w
      · simp only [ite_eq_left hw0]
        by_contra hn
        exact hw (quadraticDensityTerm_mem_cutoff g a θ Φ R v C N s w hR hv hN hs hw0 hΦ hn)
      · simp only [ite_eq_right hw0]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact ite_eq_left (Finset.mem_Ioc.mp hw).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_IntegerKernelScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from the real analytic scale to the manuscript's integer K -/

namespace Ostmann

open Filter

theorem integerKernelScale_power (K : ℝ) (hK : 0 ≤ K) :
    integerKernelScale K ^ (9999999 / 10000000 : ℝ) = K := by
  rw [integerKernelScale, ← Real.rpow_mul hK]
  rw [show (10000000 / 9999999 : ℝ) * (9999999 / 10000000) = 1 by norm_num,
    Real.rpow_one]

theorem integerKernelScale_lower (T K : ℝ) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K) :
    T / 1000000 ≤ integerKernelScale K := by
  have hT0 : 0 ≤ T := by linarith
  have hd : (1000 : ℝ) ^ (10000000 / 9999999 : ℝ) ≤ 1000000 := by
    calc
      _ ≤ (1000 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by rw [Real.rpow_two]; norm_num
  calc
    _ ≤ T / (1000 : ℝ) ^ (10000000 / 9999999 : ℝ) :=
      div_le_div_of_nonneg_left hT0 (Real.rpow_pos_of_pos (by norm_num) _) hd
    _ = (T ^ (9999999 / 10000000 : ℝ) / 1000) ^ (10000000 / 9999999 : ℝ) := by
      rw [Real.div_rpow (Real.rpow_nonneg hT0 _) (by norm_num), ← Real.rpow_mul hT0]
      rw [show (9999999 / 10000000 : ℝ) * (10000000 / 9999999) = 1 by norm_num,
        Real.rpow_one]
    _ ≤ integerKernelScale K := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hT0 _) (by norm_num)) hK (by norm_num)

theorem integerKernelScale_moment (T K u : ℝ) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K)
    (hu : u ≤ 2 * T ^ (1 / 1000000 : ℝ)) :
    u ≤ 4 * integerKernelScale K ^ (1 / 1000000 : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hS : 0 < integerKernelScale K := Real.rpow_pos_of_pos hK0 _
  have hlo := integerKernelScale_lower T K hT hK
  have hTS : T ≤ 1000000 * integerKernelScale K := by linarith
  have hc : (1000000 : ℝ) ^ (1 / 1000000 : ℝ) ≤ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ (20 : ℕ)) ^ (1 / 1000000 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = (2 : ℝ) ^ ((20 : ℝ) * (1 / 1000000 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        simp only [Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  apply hu.trans
  calc
    _ ≤ 2 * (1000000 * integerKernelScale K) ^ (1 / 1000000 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT0 hTS (by norm_num)) (by norm_num)
    _ = 2 * ((1000000 : ℝ) ^ (1 / 1000000 : ℝ) *
        integerKernelScale K ^ (1 / 1000000 : ℝ)) := by rw [Real.mul_rpow (by norm_num) hS.le]
    _ ≤ 4 * integerKernelScale K ^ (1 / 1000000 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 2 by norm_num))
        (Real.rpow_nonneg hS.le (1 / 1000000 : ℝ))
      simpa only [show (2 : ℝ) * 2 = 4 by norm_num, mul_assoc] using hh

theorem eventually_at_integerKernelScale (Q : ℝ → Prop) (hQ : ∀ᶠ x : ℝ in atTop, Q x) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ,
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K → Q (integerKernelScale K) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp hQ
  filter_upwards [eventually_ge_atTop (1000000 * max 1 B), eventually_ge_atTop (1 : ℝ)] with T ht hT K hK
  apply hB
  have hh := integerKernelScale_lower T K hT hK
  have hBB := le_max_right (1 : ℝ) B
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SmallPositiveQuadratic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-kernel bound for the original positive quadratic series -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeSet_modulus_primeFactors (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime) :
    U.toList.prod.primeFactors = U := by
  have he : U.toList.prod = ∏ p ∈ U, p := by simp
  rw [he, Nat.primeFactors_prod hU]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SmallDivisorEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-kernel divisor sum and its weighted square norm -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem sum_powerset_power_card (P : Finset ℕ) (x : ℝ) :
    (∑ U ∈ P.powerset, x ^ U.card) = (1 + x) ^ P.card := by
  simpa only [Finset.prod_const] using (Finset.prod_one_add (f := fun _ : ℕ => x) P).symm

theorem small_divisor_combination_bound (P : Finset ℕ) (c G : Finset ℕ → ℂ)
    (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hG : ∀ U ∈ P.powerset, ‖G U‖ ≤ B * (Real.sqrt 2) ^ U.card) :
    ‖∑ U ∈ P.powerset, c U * G U‖ ≤ B * (1 + Real.sqrt 2 / 16) ^ P.card := by
  calc
    _ ≤ ∑ U ∈ P.powerset, ‖c U * G U‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ P.powerset, B * (Real.sqrt 2 / 16) ^ U.card := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      have hh := mul_le_mul (hc U hU) (hG U hU) (norm_nonneg _) (by positivity)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      simp only [div_pow, one_pow]
      ring
    _ = B * (1 + Real.sqrt 2 / 16) ^ P.card := by
      rw [← Finset.mul_sum, sum_powerset_power_card]

theorem sqrt_weighted_energy_le_uniform {ι : Type*} (S : Finset ι) (μ : ι → ℝ)
    (f : ι → ℂ) (B : ℝ) (hB : 0 ≤ B) (hμ : ∀ s ∈ S, 0 ≤ μ s)
    (hf : ∀ s ∈ S, ‖f s‖ ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖f s‖ ^ 2) ≤ B * Real.sqrt (∑ s ∈ S, μ s) := by
  have hh : (∑ s ∈ S, μ s * ‖f s‖ ^ 2) ≤ B ^ 2 * ∑ s ∈ S, μ s := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf s hs) 2) (hμ s hs)).trans_eq (by ring)
  apply (Real.sqrt_le_sqrt hh).trans_eq
  rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OffWitnessEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed off-witness family has exponentially small coefficient norm -/

namespace Ostmann

open Filter
open scoped BigOperators

/-- This is a conditional estimate for the explicitly defined subfamily
where each small-kernel value is below the witness threshold. The pointwise
condition is part of the subfamily, not an additional published input. -/
theorem eventual_off_witness_norm (C₀ ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (M : ℕ) (S : Finset ℕ) (u : ℝ),
      (M : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) → 0 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (c : Finset ℕ → ℂ) (G : Finset ℕ → ℕ → ℂ),
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ s ∈ S, ∀ U ∈ P.powerset,
        ‖G U s‖ ≤ Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ) / 10) * (Real.sqrt 2) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
        Real.exp ((-4 / 5 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [squarefree_coefficient_budget C₀ (2 * ε) (by positivity)] with T hb
  intro P M S u hM hcard hS hu huU c G hc hG
  let K := T ^ (9999999 / 10000000 : ℝ)
  have hpoly : (1 + Real.sqrt 2 / 16) ^ P.card ≤ Real.exp (K / 10) :=
    (small_kernel_divisor_product_bound P.card).trans (Real.exp_le_exp.mpr (by linarith))
  have hpoint (s : ℕ) (hs : s ∈ S) :
      ‖∑ U ∈ P.powerset, c U * G U s‖ ≤ Real.exp (-4 * K / 5) := by
    apply (small_divisor_combination_bound P c (fun U => G U s)
      (Real.exp (-9 * K / 10)) (Real.exp_nonneg _) hc (hG s hs)).trans
    apply (mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤ Real.exp (ε * K) := by
    apply (Real.sqrt_le_sqrt (hb M S u hM hS hu huU)).trans_eq
    rw [← Real.exp_half]
    congr 1
    ring
  apply (sqrt_weighted_energy_le_uniform S (fun s => u ^ s.primeFactors.card / (s : ℝ)) _
    (Real.exp (-4 * K / 5)) (Real.exp_nonneg _) (fun _ _ => by positivity) hpoint).trans
  apply (mul_le_mul_of_nonneg_left hsqrt (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CardinalKernelNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient norms at the actual cardinality of the selected primes -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

private theorem kernelScale_range (C₀ T K : ℝ) (M : ℕ)
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K)
    (hM : (M : ℝ) ≤ Real.exp (C₀ * T)) :
    (M : ℝ) ≤ Real.exp ((1000000 * C₀) * integerKernelScale K) := by
  apply hM.trans
  apply Real.exp_le_exp.mpr
  have hlo := integerKernelScale_lower T K hT hK
  nlinarith

theorem eventual_off_witness_norm_card (C₀ ε : ℝ) (hC₀ : 0 ≤ C₀) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (P.card : ℝ) →
      (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (c : Finset ℕ → ℂ) (G : Finset ℕ → ℕ → ℂ),
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ s ∈ S, ∀ U ∈ P.powerset,
        ‖G U s‖ ≤ Real.exp (-9 * P.card / 10) * (Real.sqrt 2) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
        Real.exp ((-4 / 5 + ε) * P.card) := by
  have hevent := eventual_off_witness_norm (1000000 * C₀) ε hε
  filter_upwards [eventually_at_integerKernelScale _ hevent,
    eventually_ge_atTop (1 : ℝ)] with T hnorm hT
  intro P M S u hK hM hS hu huU c G hc hG
  have hscale := integerKernelScale_power (P.card : ℝ) (by positivity)
  have hn := hnorm (P.card : ℝ) hK P M S u
    (kernelScale_range C₀ T P.card M hC₀ hT hK hM) hscale.ge hS hu
    (integerKernelScale_moment T P.card u hT hK huU) c G hc (by simpa only [hscale] using hG)
  simpa only [hscale] using hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_DivisorReciprocalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reciprocal square-root mass of the selected divisors -/

namespace Ostmann

open scoped BigOperators

theorem sum_reciprocal_sqrt_divisors (Q : Finset ℕ) :
    (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) =
      ∏ p ∈ Q, (1 + (Real.sqrt (p : ℝ))⁻¹) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro V _
  have he : (V.toList.prod : ℝ) = ∏ p ∈ V, (p : ℝ) := by simp
  rw [he, Real.sqrt_prod V (fun p _ => Nat.cast_nonneg p), Finset.prod_inv_distrib]

theorem reciprocal_sqrt_divisor_mass_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, 1000000 ≤ p) :
    (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤
      Real.exp ((Q.card : ℝ) / 1000) := by
  rw [sum_reciprocal_sqrt_divisors]
  calc
    _ ≤ ∏ _p ∈ Q, Real.exp (1 / 1000 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p _; positivity
      · intro p hp
        have hs : (1000 : ℝ) ≤ Real.sqrt (p : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          exact_mod_cast hQ p hp
        have hi : (Real.sqrt (p : ℝ))⁻¹ ≤ (1 / 1000 : ℝ) := by
          simpa only [one_div] using (inv_anti₀ (by norm_num : (0 : ℝ) < 1000) hs)
        have he := Real.add_one_le_exp (1 / 1000 : ℝ)
        linarith
    _ = _ := by rw [Finset.prod_const, ← Real.exp_nat_mul]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedNormTriangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite weighted square norm under divisor summation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_correlation_le_sqrt_energy {ι : Type*} (S : Finset ι)
    (μ : ι → ℝ) (f g : ι → ℂ) (hμ : ∀ s ∈ S, 0 ≤ μ s) :
    ‖∑ s ∈ S, (μ s : ℂ) * (f s * conj (g s))‖ ≤
      Real.sqrt (∑ s ∈ S, μ s * ‖f s‖ ^ 2) *
      Real.sqrt (∑ s ∈ S, μ s * ‖g s‖ ^ 2) := by
  have he (a : ι → ℂ) : (∑ s ∈ S, (Real.sqrt (μ s) * ‖a s‖) ^ 2) =
      ∑ s ∈ S, μ s * ‖a s‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_pow, Real.sq_sqrt (hμ s hs)]
  calc
    _ ≤ ∑ s ∈ S, μ s * (‖f s‖ * ‖g s‖) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro s hs
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hμ s hs), Complex.norm_conj]
    _ = ∑ s ∈ S, (Real.sqrt (μ s) * ‖f s‖) * (Real.sqrt (μ s) * ‖g s‖) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt (hμ s hs)]
    _ ≤ _ := by
      simpa only [he] using Real.sum_mul_le_sqrt_mul_sqrt S
        (fun s => Real.sqrt (μ s) * ‖f s‖) (fun s => Real.sqrt (μ s) * ‖g s‖)

theorem sqrt_weighted_sum_energy_le {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (μ : ι → ℝ) (c : κ → ℂ)
    (G : κ → ι → ℂ) (B : ℝ) (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hG : ∀ d ∈ D, Real.sqrt (∑ s ∈ S, μ s * ‖G d s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      B * ∑ d ∈ D, ‖c d‖ := by
  have hp (d : κ) (hd : d ∈ D) (e : κ) (he : e ∈ D) :
      ‖∑ s ∈ S, (μ s : ℂ) * (G d s * conj (G e s))‖ ≤ B ^ 2 := by
    apply (weighted_correlation_le_sqrt_energy S μ (G d) (G e) hμ).trans
    simpa only [pow_two] using mul_le_mul (hG d hd) (hG e he) (Real.sqrt_nonneg _) hB
  have hb : (∑ s ∈ S, μ s * ‖∑ d ∈ D, c d * G d s‖ ^ 2) ≤
      (B * ∑ d ∈ D, ‖c d‖) ^ 2 := by
    apply (weighted_sum_energy_le_correlations S D μ c G).trans
    calc
      _ ≤ ∑ d ∈ D, ∑ e ∈ D, (‖c d‖ * ‖c e‖) * B ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (hp d hd e he) (by positivity)
      _ = _ := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [← Finset.sum_mul]
        ring
  exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorWeightedCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the squarefree divisors v in the original coefficients -/

namespace Ostmann

open scoped BigOperators

theorem divisor_weight_norm_sum_le (Q : Finset ℕ) (ξ : Finset ℕ → ℂ)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) :
    (∑ V ∈ Q.powerset, ‖ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹‖) ≤
      ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply Finset.sum_le_sum
  intro V hV
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (by positivity) (hξ V hV)

theorem divisorWeightedCoefficient_norm_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ) (s : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, ‖F V s‖ ≤ B) :
    ‖divisorWeightedCoefficient Q ξ F s‖ ≤
      B * ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  unfold divisorWeightedCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ V ∈ Q.powerset, ‖ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹‖ * B := by
      apply Finset.sum_le_sum
      intro V hV
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF V hV) (norm_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (divisor_weight_norm_sum_le Q ξ hξ) hB

theorem divisorWeightedCoefficient_energy_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ)
    (S : Finset ℕ) (μ : ℕ → ℝ) (B : ℝ)
    (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, Real.sqrt (∑ s ∈ S, μ s * ‖F V s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖divisorWeightedCoefficient Q ξ F s‖ ^ 2) ≤
      B * ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply (sqrt_weighted_sum_energy_le S Q.powerset μ
    (fun V => ξ V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) F B hμ hB hF).trans
  exact mul_le_mul_of_nonneg_left (divisor_weight_norm_sum_le Q ξ hξ) hB

theorem divisorWeightedCoefficient_energy_exp_le (Q : Finset ℕ)
    (ξ : Finset ℕ → ℂ) (F : Finset ℕ → ℕ → ℂ)
    (S : Finset ℕ) (μ : ℕ → ℝ) (B : ℝ)
    (hQ : ∀ p ∈ Q, 1000000 ≤ p) (hμ : ∀ s ∈ S, 0 ≤ μ s) (hB : 0 ≤ B)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (hF : ∀ V ∈ Q.powerset, Real.sqrt (∑ s ∈ S, μ s * ‖F V s‖ ^ 2) ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖divisorWeightedCoefficient Q ξ F s‖ ^ 2) ≤
      B * Real.exp ((Q.card : ℝ) / 1000) :=
  (divisorWeightedCoefficient_energy_le Q ξ F S μ B hμ hB hξ hF).trans
    (mul_le_mul_of_nonneg_left (reciprocal_sqrt_divisor_mass_le Q hQ) hB)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SquarefreeFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique squarefree frequency decomposition -/

namespace Ostmann

theorem squarefree_square_decomposition_unique {a b c d : ℕ}
    (ha : Squarefree a) (hc : Squarefree c) (hb : 0 < b) (hd : 0 < d)
    (h : a * b ^ 2 = c * d ^ 2) : a = c ∧ b = d := by
  have hac : a = c := by
    apply Nat.eq_of_factorization_eq ha.ne_zero hc.ne_zero
    intro p
    have he := congrArg (fun n : ℕ => n.factorization p) h
    simp only [Nat.factorization_mul ha.ne_zero (pow_ne_zero _ hb.ne'),
      Nat.factorization_mul hc.ne_zero (pow_ne_zero _ hd.ne'),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he
    have hpa := ha.natFactorization_le_one p
    have hpc := hc.natFactorization_le_one p
    omega
  refine ⟨hac, ?_⟩
  rw [hac] at h
  have hbd : b ^ 2 = d ^ 2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc.ne_zero) h
  nlinarith

theorem exists_squarefreeFrequency {L u : ℕ} (hL : 0 < L) (hu : 0 < u) :
    Nonempty (SquarefreeFrequency L u) := by
  obtain ⟨a, w, ha, hw, he, hs⟩ := Nat.sq_mul_squarefree_of_pos hu
  let v := Nat.gcd a L
  let s := a / v
  have hv : 0 < v := Nat.gcd_pos_of_pos_left L ha
  have hvd : v ∣ a := Nat.gcd_dvd_left a L
  have hsa : s * v = a := Nat.div_mul_cancel hvd
  have hsp : 0 < s := by
    by_contra hh
    have hz : s = 0 := Nat.eq_zero_of_not_pos hh
    rw [hz, zero_mul] at hsa
    omega
  refine ⟨⟨s, v, w, hsp, hv, hw, hsa ▸ hs, Nat.gcd_dvd_right a L,
    Nat.coprime_div_gcd_of_squarefree hs hL.ne', ?_⟩⟩
  rw [hsa, mul_comm a]
  exact he

namespace SquarefreeFrequency

theorem v_eq_gcd {L u : ℕ} (a : SquarefreeFrequency L u) :
    a.v = Nat.gcd (a.s * a.v) L := by
  exact (Nat.gcd_mul_of_coprime_of_dvd a.s_coprime a.v_dvd).symm

theorem unique {L u : ℕ} (a b : SquarefreeFrequency L u) : a = b := by
  obtain ⟨hkernel, hw⟩ := squarefree_square_decomposition_unique
    a.kernel_squarefree b.kernel_squarefree a.w_pos b.w_pos (a.value.trans b.value.symm)
  have hv : a.v = b.v := by rw [a.v_eq_gcd, b.v_eq_gcd, hkernel]
  have hs : a.s = b.s := by
    rw [hv] at hkernel
    exact Nat.eq_of_mul_eq_mul_right b.v_pos hkernel
  cases a
  cases b
  simp_all

theorem s_le {L u : ℕ} (a : SquarefreeFrequency L u) : a.s ≤ u := by
  calc
    a.s ≤ a.s * a.v := Nat.le_mul_of_pos_right _ a.v_pos
    _ ≤ a.s * a.v * a.w ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos a.w_pos _)
    _ = u := a.value

theorem w_sq_le {L u : ℕ} (a : SquarefreeFrequency L u) : a.w ^ 2 ≤ u := by
  calc
    a.w ^ 2 ≤ a.s * a.v * a.w ^ 2 := Nat.le_mul_of_pos_left _ (Nat.mul_pos a.s_pos a.v_pos)
    _ = u := a.value

end SquarefreeFrequency

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFrequencyExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite reindexing by squarefree kernel and square part -/

namespace Ostmann

open scoped BigOperators

theorem frequencyTriple_value_injective {L U : ℕ}
    {x y : ℕ × ℕ × ℕ} (hx : x ∈ frequencyTriples L U) (hy : y ∈ frequencyTriples L U)
    (h : x.1 * x.2.1 * x.2.2 ^ 2 = y.1 * y.2.1 * y.2.2 ^ 2) : x = y := by
  let a := frequencyTripleData hx
  let b : SquarefreeFrequency L (x.1 * x.2.1 * x.2.2 ^ 2) :=
    { frequencyTripleData hy with value := h.symm }
  have he := a.unique b
  apply Prod.ext
  · exact congrArg SquarefreeFrequency.s he
  · exact Prod.ext (congrArg SquarefreeFrequency.v he) (congrArg SquarefreeFrequency.w he)

theorem frequencyTriple_value_surjective {L U u : ℕ} (hL : 0 < L)
    (hu : u ∈ Finset.Icc 1 U) :
    ∃ z ∈ frequencyTriples L U, z.1 * z.2.1 * z.2.2 ^ 2 = u := by
  obtain ⟨hu, huU⟩ := Finset.mem_Icc.mp hu
  obtain ⟨a⟩ := exists_squarefreeFrequency hL hu
  refine ⟨(a.s, a.v, a.w), mem_frequencyTriples.mpr ?_, a.value⟩
  refine ⟨a.s_pos, a.s_le.trans huU, Nat.mem_divisors.mpr ⟨a.v_dvd, hL.ne'⟩,
    a.w_pos, ?_, a.kernel_squarefree, a.s_coprime, a.value.le.trans huU⟩
  have hsq := a.w_sq_le.trans huU
  nlinarith [a.w_pos]

theorem sum_squarefree_frequencies (L U : ℕ) (hL : 0 < L) (F : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 U, F u) =
      ∑ z ∈ frequencyTriples L U, F (z.1 * z.2.1 * z.2.2 ^ 2) := by
  symm
  apply Finset.sum_bij (fun z _ => z.1 * z.2.1 * z.2.2 ^ 2)
  · intro z hz
    let a := frequencyTripleData hz
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Nat.mul_pos a.s_pos a.v_pos) (pow_pos a.w_pos _),
      (mem_frequencyTriples.mp hz).2.2.2.2.2.2.2⟩
  · intro x hx y hy hxy
    exact frequencyTriple_value_injective hx hy hxy
  · intro u hu
    obtain ⟨z, hz, he⟩ := frequencyTriple_value_surjective hL hu
    exact ⟨z, hz, he⟩
  · intro z hz
    rfl

theorem quadratic_character_square {M : ℕ} (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsQuadratic) (w : ℕ) :
    χ ((w : ZMod M) ^ 2) = if w.Coprime M then 1 else 0 := by
  classical
  by_cases hw : w.Coprime M
  · rw [ite_eq_left hw, map_pow, ← χ.pow_apply' two_ne_zero, hχ.sq_eq_one]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime w M).mpr hw)
  · rw [ite_eq_right hw, map_pow, MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime w M).not.mpr hw)]
    norm_num

theorem quadratic_character_frequency {M : ℕ} (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsQuadratic) (s v w : ℕ) :
    χ ((s * v * w ^ 2 : ℕ) : ZMod M) =
      χ (s : ZMod M) * χ (v : ZMod M) * (if w.Coprime M then 1 else 0) := by
  push_cast
  rw [map_mul χ, map_mul χ, quadratic_character_square χ hχ]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MoebiusSquareRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Möbius removal of the square-part coprimality condition -/

namespace Ostmann

open scoped BigOperators

private theorem sum_moebius_complex (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  have h' : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then (1 : ℤ) else 0 := by simpa only [ArithmeticFunction.one_apply] using h
  exact_mod_cast h'

theorem coprime_moebius_sum {M : ℕ} (hM : 0 < M) (w : ℕ) :
    (if w.Coprime M then (1 : ℂ) else 0) =
      ∑ P ∈ M.divisors, if P ∣ w then (ArithmeticFunction.moebius P : ℂ) else 0 := by
  classical
  have hg : Nat.gcd M w ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left w hM)
  have hs : M.divisors.filter (fun P => P ∣ w) = (Nat.gcd M w).divisors := by
    ext P
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, hg⟩, fun h => ⟨⟨h.1.1, hM.ne'⟩, h.1.2⟩⟩
  rw [← Finset.sum_filter, hs, sum_moebius_complex]
  congr 1
  exact propext (Nat.coprime_comm.trans Iff.rfl)

/-- This form allows the summation index to carry all the other frequency
parameters while `w` extracts only the square part. -/
theorem sum_coprime_moebius {ι : Type*} (S : Finset ι) (w : ι → ℕ) (a : ι → ℂ)
    {M : ℕ} (hM : 0 < M) :
    (∑ i ∈ S, a i * (if (w i).Coprime M then 1 else 0)) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ i ∈ S with P ∣ w i, a i := by
  classical
  simp_rw [coprime_moebius_sum hM, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

theorem squarefree_frequency_moebius_expansion (L U : ℕ) (hL : 0 < L)
    {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (hχ : χ.IsQuadratic)
    (F : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 U, χ (u : ZMod M) * F u) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ z ∈ frequencyTriples L U with P ∣ z.2.2,
          χ (z.1 : ZMod M) * χ (z.2.1 : ZMod M) * F (z.1 * z.2.1 * z.2.2 ^ 2) := by
  rw [sum_squarefree_frequencies L U hL]
  simp_rw [quadratic_character_frequency χ hχ]
  have hs := sum_coprime_moebius (frequencyTriples L U) (fun z => z.2.2)
    (fun z => χ (z.1 : ZMod M) * χ (z.2.1 : ZMod M) * F (z.1 * z.2.1 * z.2.2 ^ 2)) hM
  rw [← hs]
  apply Finset.sum_congr rfl
  intro z hz
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PositiveQuadraticUniformBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for the positive quadratic series at every kernel -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem positiveQuadraticSum_uniform_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s‖ ≤
      B * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  let Q := Real.sqrt (R * q / ((s : ℝ) * v))
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hΦ0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ := by positivity
  have hW : (W : ℝ) ≤ Real.sqrt H * Q := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans_eq
    have he : H * R * q / ((s : ℝ) * v) = H * (R * q / ((s : ℝ) * v)) := by ring
    rw [he, Real.sqrt_mul hH]
  rw [positiveQuadraticSum_eq_cutoff g a θ Φ R v H s s hR hv hs le_rfl hΦ]
  change ‖(Q : ℂ)⁻¹ * ∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
  have hsum : ‖∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w‖ ≤
      (W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W, B * SchwartzMap.seminorm ℝ 0 0 Φ := by
        apply Finset.sum_le_sum
        intro w _
        simp only [quadraticDensityTerm, norm_mul, norm_pow, norm_realAdditivePhase,
          one_pow, mul_one]
        exact mul_le_mul (hg _) (Φ.norm_le_seminorm ℝ _) (norm_nonneg _) hB
      _ = _ := by simp
  calc
    _ ≤ Q⁻¹ * ((W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hQ.le)
    _ ≤ Q⁻¹ * ((Real.sqrt H * Q) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) := by gcongr
    _ = _ := by field_simp

theorem positiveQuadraticSum_energy_uniform_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s‖ ≤
      Real.sqrt q * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  apply positiveQuadraticSum_uniform_bound g (Real.sqrt q) _ a θ Φ R v H s hR hv hH hs hΦ
  intro x
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (fun y _ => sq_nonneg ‖g y‖) (Finset.mem_univ x)).trans hg

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootNormalizedCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact coefficient energy of the normalized squarefree array -/

namespace Ostmann

open scoped BigOperators

theorem rootNormalizedCoefficient_norm_sq (F : ℕ → ℂ) (s : ℕ) :
    ‖rootNormalizedCoefficient F s‖ ^ 2 = (s : ℝ)⁻¹ * ‖F s‖ ^ 2 := by
  rw [rootNormalizedCoefficient, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg s)]

theorem rootNormalizedCoefficient_energy (S : Finset ℕ) (u : ℝ) (F : ℕ → ℂ) :
    (∑ s : S, u ^ s.val.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2) =
      ∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) * ‖F s‖ ^ 2 := by
  rw [show (∑ s : S, u ^ s.val.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2) =
    ∑ s ∈ S, u ^ s.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2 from
      Finset.sum_coe_sort S (fun s : ℕ => u ^ s.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro s _
  rw [rootNormalizedCoefficient_norm_sq]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticArrayMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform absolute-mass bound for the original coefficient arrays -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeDivisorPositive_uniform_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (U : Finset ℕ) (hU : U ∈ P.powerset) :
    ‖primeDivisorPositive P hP D a θ Φ R v U s‖ ≤
      Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  classical
  have hUP := Finset.mem_powerset.mp hU
  have hp : ∀ p ∈ U, p.Prime := fun p hp => hP p (hUP hp)
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hp)).ne'⟩
  rw [primeDivisorPositive, dite_eq_left hUP]
  apply (positiveQuadraticSum_energy_uniform_bound _ (densityCRTList_energy _ _ _ _)
    (a U) (θ U) Φ R v H s hR hv hH hs hΦ).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_sqrt
  exact_mod_cast primeSet_prod_le_of_subset P U hP hUP

theorem primeDivisorPositive_combination_uniform_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (c : Finset ℕ → ℂ)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) :
    ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ≤
      (Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ P.card := by
  let B := Real.sqrt P.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ U ∈ P.powerset, ‖c U * primeDivisorPositive P hP D a θ Φ R v U s‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ P.powerset, (1 / 16 : ℝ) ^ U.card * B := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      exact mul_le_mul (hc U hU)
        (primeDivisorPositive_uniform_bound P hP D a θ Φ R v H s hR hv hH hs hΦ U hU)
        (norm_nonneg _) (by positivity)
    _ = B * (1 + 1 / 16 : ℝ) ^ P.card := by
      rw [← Finset.sum_mul, sum_powerset_power_card, mul_comm]

theorem rootNormalizedCoefficient_norm_le (F : ℕ → ℂ) (s : ℕ) (hs : 0 < s) :
    ‖rootNormalizedCoefficient F s‖ ≤ ‖F s‖ := by
  have hsq : (1 : ℝ) ≤ Real.sqrt s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hs
  have hi : (Real.sqrt (s : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsq
  rw [rootNormalizedCoefficient, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hi

theorem rootNormalizedCoefficient_mass_le (S : Finset ℕ) (F : ℕ → ℂ) (B : ℝ)
    (hS : ∀ s ∈ S, 0 < s) (hF : ∀ s ∈ S, ‖F s‖ ≤ B) :
    (∑ s : S, ‖rootNormalizedCoefficient F s‖) ≤ (S.card : ℝ) * B := by
  calc
    _ = ∑ s ∈ S, ‖rootNormalizedCoefficient F s‖ :=
      Finset.sum_coe_sort S (fun s : ℕ => ‖rootNormalizedCoefficient F s‖)
    _ ≤ ∑ _s ∈ S, B := Finset.sum_le_sum (fun s hs =>
      (rootNormalizedCoefficient_norm_le F s (hS s hs)).trans (hF s hs))
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticMultiples
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact outer-divisor quadratic subseries -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem sum_positive_multiples (P W : ℕ) (hP : 0 < P) (f : ℕ → ℂ) :
    (∑ w ∈ (Finset.Ioc 0 W).filter (fun w => P ∣ w), f w) =
      ∑ n ∈ Finset.Ioc 0 (W / P), f (P * n) := by
  classical
  have hset : (Finset.Ioc 0 W).filter (fun w => P ∣ w) =
      (Finset.Ioc 0 (W / P)).image (fun n => P * n) := by
    ext w
    constructor
    · intro hw
      obtain ⟨hw, hPw⟩ := Finset.mem_filter.mp hw
      obtain ⟨hw0, hwW⟩ := Finset.mem_Ioc.mp hw
      have heq : P * (w / P) = w := Nat.mul_div_cancel' hPw
      apply Finset.mem_image.mpr
      refine ⟨w / P, Finset.mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hwW⟩, heq⟩
      by_contra hn
      have hz : w / P = 0 := Nat.eq_zero_of_not_pos hn
      simp only [hz, mul_zero] at heq
      omega
    · intro hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hn0, hnW⟩ := Finset.mem_Ioc.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hP hn0, ?_⟩, dvd_mul_right P n⟩
      have hh := (Nat.le_div_iff_mul_le hP).mp hnW
      simpa only [Nat.mul_comm] using hh
  rw [hset, Finset.sum_image]
  intro a _ b _ heq
  exact Nat.eq_of_mul_eq_mul_left hP heq

theorem quadraticDensityTerm_multiple {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ)
    (s P w : ℕ) :
    quadraticDensityTerm g a θ Φ R v s (P * w) =
      quadraticDensityTerm g a θ Φ R v (s * P ^ 2) w := by
  unfold quadraticDensityTerm
  have hg : a * ((P * w : ℕ) : ZMod q) ^ 2 * (s : ZMod q) =
      a * (w : ZMod q) ^ 2 * ((s * P ^ 2 : ℕ) : ZMod q) := by push_cast; ring
  have he : realAdditivePhase (θ * v * ((P * w : ℕ) : ℝ) ^ 2 / q) ^ s =
      realAdditivePhase (θ * v * (w : ℝ) ^ 2 / q) ^ (s * P ^ 2) := by
    rw [← realAdditivePhase_nat_mul, ← realAdditivePhase_nat_mul]
    congr 1
    push_cast
    ring
  have hx : (s : ℝ) * v * ((P * w : ℕ) : ℝ) ^ 2 / (R * q) =
      ((s * P ^ 2 : ℕ) : ℝ) * v * (w : ℝ) ^ 2 / (R * q) := by push_cast; ring
  rw [hg, he, hx]

theorem positiveQuadraticMultiples_eq {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ)
    (s P : ℕ) (hP : 0 < P) (hR : 0 ≤ R) (hv : 0 ≤ v) :
    positiveQuadraticMultiples g a θ Φ R v s P =
      (P : ℂ)⁻¹ * positiveQuadraticSum g a θ Φ R v (s * P ^ 2) := by
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hroot : Real.sqrt (R * q / (((s * P ^ 2 : ℕ) : ℝ) * v)) =
      Real.sqrt (R * q / ((s : ℝ) * v)) / P := by
    have he : R * q / (((s * P ^ 2 : ℕ) : ℝ) * v) =
        (R * q / ((s : ℝ) * v)) / (P : ℝ) ^ 2 := by push_cast; ring
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq (Nat.cast_nonneg P)]
  unfold positiveQuadraticMultiples positiveQuadraticSum
  simp_rw [quadraticDensityTerm_multiple]
  rw [hroot]
  push_cast
  field_simp

theorem positiveQuadraticMultiples_eq_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ)
    (s P : ℕ) (hP : 0 < P) (hR : 0 < R) (hv : 0 < v) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    positiveQuadraticMultiples g a θ Φ R v s P =
      ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
        ∑ w ∈ (quadraticCompactCutoff q R v H s).filter (fun w => P ∣ w),
          quadraticDensityTerm g a θ Φ R v s w := by
  classical
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  unfold positiveQuadraticMultiples
  congr 1
  calc
    _ = ∑ n ∈ Finset.Ioc 0 (W / P),
        if 0 < n then quadraticDensityTerm g a θ Φ R v s (P * n) else 0 := by
      apply tsum_eq_sum
      intro n hn
      by_cases hn0 : 0 < n
      · simp only [ite_eq_left hn0]
        by_contra hterm
        have hm := quadraticDensityTerm_mem_cutoff g a θ Φ R v H s s (P * n)
          hR hv hs le_rfl (Nat.mul_pos hP hn0) hΦ hterm
        have hPnW : P * n ≤ W := (Finset.mem_Ioc.mp hm).2
        have hnW : n ≤ W / P := (Nat.le_div_iff_mul_le hP).mpr (by simpa only [Nat.mul_comm] using hPnW)
        exact hn (Finset.mem_Ioc.mpr ⟨hn0, hnW⟩)
      · simp only [ite_eq_right hn0]
    _ = ∑ n ∈ Finset.Ioc 0 (W / P), quadraticDensityTerm g a θ Φ R v s (P * n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact ite_eq_left (Finset.mem_Ioc.mp hn).1
    _ = _ := (sum_positive_multiples P W hP (quadraticDensityTerm g a θ Φ R v s)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OuterDivisorNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The outer divisor gives the full reciprocal-divisor norm gain -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeDivisorMultiples_combination_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s P : ℕ)
    (hP : 0 < P) (hs : 0 < s) (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (c : Finset ℕ → ℂ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) :
    ‖∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s‖ ≤
      (Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ Q.card / P := by
  have he : (∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s) =
      (P : ℂ)⁻¹ * ∑ U ∈ Q.powerset, c U * primeDivisorPositive Q hQ D a θ Φ R v U (s * P ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    unfold primeDivisorMultiples
    ring
  rw [he, norm_mul, norm_inv, Complex.norm_natCast]
  have hp := primeDivisorPositive_combination_uniform_bound Q hQ D a θ Φ R v H (s * P ^ 2)
    hR hv hH (Nat.mul_pos hs (pow_pos hP _)) hΦ c hc
  apply (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg P))).trans_eq
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FullQuadraticCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both divisor sums in the original quadratic coefficient -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem divisorQuadraticScalar_congr_point
    (a b : ∀ U : Finset ℕ, ZMod U.toList.prod) (V U : Finset ℕ) (h : a U = b U) :
    divisorQuadraticScalar a V U = divisorQuadraticScalar b V U := by
  exact congrArg (fun x : ZMod U.toList.prod => x * (V.toList.prod : ZMod U.toList.prod)) h

theorem fullQuadraticCoefficient_one (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (c ξ : Finset ℕ → ℂ) (s : ℕ) :
    fullQuadraticCoefficient Q hQ D a θ Φ R 1 c ξ s =
      divisorWeightedCoefficient Q ξ (fun V s => ∑ U ∈ Q.powerset, c U *
        primeDivisorPositive Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod U s) s := by
  simp only [fullQuadraticCoefficient, primeDivisorMultiples, one_pow, mul_one,
    Nat.cast_one, inv_one, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_RademacherMoments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact moments of the Boolean monomials -/

namespace Ostmann

open scoped BigOperators

theorem rademacherMonomial_univ {P : Finset ℕ} (Q : Finset P) (ε : P → Bool) :
    rademacherMonomial Q ε = ∏ p : P, if p ∈ Q then (if ε p then 1 else -1 : ℝ) else 1 := by
  classical
  exact (Finset.prod_ite_mem_eq Q (fun p => if ε p then (1 : ℝ) else -1)).symm

theorem rademacherMonomial_product {ι : Type*} [Fintype ι] {P : Finset ℕ}
    (σ : ι → Finset P) (ε : P → Bool) :
    (∏ i, rademacherMonomial (σ i) ε) =
      ∏ p : P, (if ε p then (1 : ℝ) else -1) ^ monomialOccurrence σ p := by
  classical
  simp_rw [rademacherMonomial_univ]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, monomialOccurrence]

private theorem bool_sign_power_sum (n : ℕ) :
    (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ n) = if Even n then 2 else 0 := by
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, one_pow, neg_one_pow_eq_ite]
  split_ifs <;> norm_num

theorem rademacher_product_average {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, ∏ i, rademacherMonomial (σ i) ε =
        if ∀ p : P, Even (monomialOccurrence σ p) then 1 else 0 := by
  classical
  simp_rw [rademacherMonomial_product]
  rw [← Fintype.prod_sum (fun (p : P) (b : Bool) =>
    (if b then (1 : ℝ) else -1) ^ monomialOccurrence σ p)]
  simp_rw [bool_sign_power_sum]
  by_cases h : ∀ p : P, Even (monomialOccurrence σ p)
  · simp only [h, ite_true, if_true, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    have hcard : Fintype.card (P → Bool) = 2 ^ P.card := by simp
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel₀ (by positivity)]
    simp
  · obtain ⟨p, hp⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp]), mul_zero, ite_eq_right h]

theorem rademacher_even_moment {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) (a : ι → ℝ) (l : ℕ) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ i, a i * rademacherMonomial (σ i) ε| ^ (2 * l) =
      ∑ t : Fin (2 * l) → ι,
        (∏ j, a (t j)) * (if ∀ p : P, Even (monomialOccurrence (fun j => σ (t j)) p) then 1 else 0) := by
  classical
  simp only [Even.pow_abs (even_two_mul l)]
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mul_sum, mul_left_comm, rademacher_product_average]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SquareProductMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying Boolean moments with square products of the actual indices -/

namespace Ostmann

open scoped BigOperators

private theorem squarefree_factorization_indicator {s : ℕ} (hs : Squarefree s) (p : ℕ) :
    s.factorization p = if p ∈ s.primeFactors then 1 else 0 := by
  classical
  by_cases hp : p ∈ s.primeFactors
  · rw [ite_eq_left hp]
    exact Nat.factorization_eq_one_of_squarefree hs (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  · rw [ite_eq_right hp]
    by_cases hprime : p.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hp (Nat.mem_primeFactors.mpr ⟨hprime, hd, hs.ne_zero⟩)
    · exact Nat.factorization_eq_zero_of_not_prime _ hprime

theorem isSquare_iff_even_factorization_aux {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p : ℕ, p.Prime → Even (n.factorization p) := by
  constructor
  · rintro ⟨m, rfl⟩ p _
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hm hm, Finsupp.add_apply]
    exact ⟨_, rfl⟩
  · intro h
    let f : ℕ →₀ ℕ := n.factorization.mapRange (· / 2) (by simp)
    have hf : ∀ p ∈ f.support, p.Prime := by
      intro p hp
      have : p ∈ n.factorization.support := Finsupp.support_mapRange hp
      exact Nat.prime_of_mem_primeFactors (by simpa using this)
    refine ⟨f.prod (· ^ ·), ?_⟩
    have hm := Nat.prod_pow_factorization_eq_self hf
    have hm0 : f.prod (· ^ ·) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hf p hp).ne_zero)
    apply Nat.eq_of_factorization_eq hn (mul_ne_zero hm0 hm0)
    intro p
    rw [Nat.factorization_mul hm0 hm0, Finsupp.add_apply, hm]
    by_cases hp : p.Prime
    · obtain ⟨r, hr⟩ := h p hp
      simp only [f, Finsupp.mapRange_apply]
      omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp, f]

theorem squarefree_product_isSquare_iff {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (s : ι → ℕ) (hs : ∀ i, Squarefree (s i))
    (hP : ∀ i, (s i).primeFactors ⊆ P) :
    IsSquare (∏ i, s i) ↔ ∀ p : P,
      Even (monomialOccurrence (fun i => primeFactorSubset P (s i)) p) := by
  classical
  have he (p : ℕ) : (∏ i, s i).factorization p =
      ∑ i, if p ∈ (s i).primeFactors then 1 else 0 := by
    rw [Nat.factorization_prod (fun i _ => (hs i).ne_zero), Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact squarefree_factorization_indicator (hs i) p
  have hoc (p : P) : monomialOccurrence (fun i => primeFactorSubset P (s i)) p =
      (∏ i, s i).factorization p.val := by
    rw [he]
    simp only [monomialOccurrence, Finset.card_filter, mem_primeFactorSubset]
  rw [isSquare_iff_even_factorization_aux (Finset.prod_ne_zero_iff.mpr fun i _ => (hs i).ne_zero)]
  constructor
  · intro h p
    rw [hoc]
    by_cases hp : p.val.Prime
    · exact h p.val hp
    · simp only [Nat.factorization_eq_zero_of_not_prime _ hp, Even.zero]
  · intro h p hp
    by_cases hpP : p ∈ P
    · simpa only [hoc] using h ⟨p, hpP⟩
    · rw [he]
      have hnot (i : ι) : p ∉ (s i).primeFactors := fun hh => hpP (hP i hh)
      simp only [hnot, ite_false, if_false, Finset.sum_const_zero, Even.zero]

theorem squarefree_diagonal_bonami (hB : PublishedBonamiBound) (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (a : S → ℝ) (l : ℕ) (hl : 0 < l) :
    (∑ t : Fin (2 * l) → S, (∏ j, a (t j)) *
      (if IsSquare (∏ j, (t j).val) then (1 : ℝ) else 0)) ≤
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * (a s) ^ 2) ^ l := by
  have he := rademacher_even_moment P (fun s : S => primeFactorSubset P s.val) a l
  have hi (t : Fin (2 * l) → S) :
      IsSquare (∏ j, (t j).val) ↔
        ∀ p : P, Even (monomialOccurrence (fun j => primeFactorSubset P (t j).val) p) :=
    squarefree_product_isSquare_iff P (fun j => (t j).val)
      (fun j => hS _ (t j).property) (fun j => hP _ (t j).property)
  simp_rw [← hi] at he
  rw [← he]
  exact bonami_squarefree_family hB P S hS hP a l hl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_WeightedJacobiMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring square-product moments to weighted Jacobi sums

The nonsquare error is an explicit numerical bound to be supplied by the
periodic-character calculation; it is not a published or global assumption.
-/

namespace Ostmann

open scoped BigOperators

theorem realJacobi_abs_le (n m : ℕ) : |realJacobi n m| ≤ 1 := by
  rcases jacobiSym.trichotomy (n : ℤ) m with h | h | h <;> simp [realJacobi, h]

theorem realJacobi_prod {ι : Type*} (S : Finset ι) (s : ι → ℕ) (m : ℕ) :
    realJacobi (∏ i ∈ S, s i) m = ∏ i ∈ S, realJacobi (s i) m := by
  let J : ℕ →* ℝ :=
    { toFun := fun n => realJacobi n m
      map_one' := by simp [realJacobi, jacobiSym.one_left]
      map_mul' := fun a b => by simp [realJacobi, jacobiSym.mul_left] }
  exact map_prod J s S

theorem weighted_jacobi_abs_le_mass (T : Finset ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ m ∈ T, 0 ≤ μ m) (n : ℕ) :
    |∑ m ∈ T, μ m * realJacobi n m| ≤ ∑ m ∈ T, μ m := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [abs_mul, abs_of_nonneg (hμ m hm)]
  exact (mul_le_mul_of_nonneg_left (realJacobi_abs_le n m) (hμ m hm)).trans_eq (mul_one _)

theorem weighted_jacobi_moment_expansion {ι : Type*} [Fintype ι]
    (T : Finset ℕ) (μ : ℕ → ℝ) (s : ι → ℕ) (a : ι → ℝ) (q : ℕ) :
    (∑ m ∈ T, μ m * (∑ i, a i * realJacobi (s i) m) ^ q) =
      ∑ t : Fin q → ι, (∏ j, a (t j)) *
        ∑ m ∈ T, μ m * realJacobi (∏ j, s (t j)) m := by
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib, ← realJacobi_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Bonami controls the square products. Every remaining product pays only
the supplied finite nonsquare-character error `E`. -/
theorem weighted_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S T : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (μ : ℕ → ℝ)
    (hμ : ∀ m ∈ T, 0 ≤ μ m) (a : S → ℝ) (l : ℕ) (hl : 0 < l)
    (E : ℝ) (hE : 0 ≤ E)
    (hns : ∀ t : Fin (2 * l) → S, ¬IsSquare (∏ j, (t j).val) →
      |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| ≤ E) :
    (∑ m ∈ T, μ m * |∑ s : S, a s * realJacobi s.val m| ^ (2 * l)) ≤
      (∑ m ∈ T, μ m) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ^ l +
      E * (∑ s : S, |a s|) ^ (2 * l) := by
  classical
  let W := ∑ m ∈ T, μ m
  have hW : 0 ≤ W := Finset.sum_nonneg hμ
  have hJ (t : Fin (2 * l) → S) :
      |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| ≤
        W * (if IsSquare (∏ j, (t j).val) then 1 else 0) + E := by
    split_ifs with ht
    · have hh := weighted_jacobi_abs_le_mass T μ hμ (∏ j, (t j).val)
      dsimp [W]
      linarith
    · simpa only [mul_zero, zero_add] using hns t ht
  simp only [Even.pow_abs (even_two_mul l)]
  rw [weighted_jacobi_moment_expansion]
  calc
    _ ≤ ∑ t : Fin (2 * l) → S, (∏ j, |a (t j)|) *
        (W * (if IsSquare (∏ j, (t j).val) then 1 else 0) + E) := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ ≤ |(∏ j, a (t j)) * ∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| := le_abs_self _
        _ = (∏ j, |a (t j)|) * |∑ m ∈ T, μ m * realJacobi (∏ j, (t j).val) m| := by
          rw [abs_mul, Finset.abs_prod]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hJ t) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    _ = W * (∑ t : Fin (2 * l) → S, (∏ j, |a (t j)|) *
        (if IsSquare (∏ j, (t j).val) then 1 else 0)) + E * (∑ s : S, |a s|) ^ (2 * l) := by
      rw [Fintype.sum_pow, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left
      (squarefree_diagonal_bonami hB P S hS hP (fun s => |a s|) l hl) hW) _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticQuadraticCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dependence of the original coefficient on finite arithmetic residues -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticSymbolCoefficient_norm_le (M : ℕ) (U : Finset ℕ) :
    ‖quadraticSymbolCoefficient M U‖ ≤ (1 / 16 : ℝ) ^ U.card := by
  have hn : ‖((1 / 16 : ℝ) : ℂ)‖ = (1 / 16 : ℝ) := by norm_num
  rw [quadraticSymbolCoefficient, norm_mul, norm_pow, hn,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (by positivity) (realJacobi_abs_le _ _)

theorem quadraticDivisorSymbol_norm_le (M : ℕ) (V : Finset ℕ) :
    ‖quadraticDivisorSymbol M V‖ ≤ 1 := by
  simpa only [quadraticDivisorSymbol, Complex.norm_real, Real.norm_eq_abs] using
    realJacobi_abs_le V.toList.prod M

theorem realJacobi_mod_multiple (L d M : ℕ) (hd : d ∣ L) (hM : Odd M) :
    realJacobi d M = realJacobi d (M % (4 * L)) := by
  have hr : Odd (M % (4 * L)) := hM.mod_even (Even.mul_right (by decide) L)
  unfold realJacobi
  rw [jacobiSym.mod_right' d hM, jacobiSym.mod_right' d hr,
    Nat.mod_mod_of_dvd M (Nat.mul_dvd_mul_left 4 hd)]

theorem quadraticInverseResidue_mod_multiple (L M : ℕ) (U : Finset ℕ)
    (hU : U.toList.prod ∣ L) :
    quadraticInverseResidue M U = quadraticInverseResidue (M % (4 * L)) U := by
  have hd : U.toList.prod ∣ 4 * L := dvd_mul_of_dvd_right hU 4
  have he : ((M % (4 * L) : ℕ) : ZMod U.toList.prod) = (M : ZMod U.toList.prod) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact Nat.mod_mod_of_dvd M hd
  simp only [quadraticInverseResidue, he]

theorem primeDivisorPositive_congr_point (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a b : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (U : Finset ℕ) (s : ℕ)
    (ha : a U = b U) :
    primeDivisorPositive Q hQ D a θ Φ R v U s =
      primeDivisorPositive Q hQ D b θ Φ R v U s := by
  unfold primeDivisorPositive
  split_ifs
  · rw [ha]
  · rfl

theorem fullQuadraticCoefficient_congr_on (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a b : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P : ℕ) (c c' ξ ξ' : Finset ℕ → ℂ) (s : ℕ)
    (ha : ∀ U ∈ Q.powerset, a U = b U)
    (hc : ∀ U ∈ Q.powerset, c U = c' U)
    (hξ : ∀ V ∈ Q.powerset, ξ V = ξ' V) :
    fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s =
      fullQuadraticCoefficient Q hQ D b θ Φ R P c' ξ' s := by
  unfold fullQuadraticCoefficient divisorWeightedCoefficient
  apply Finset.sum_congr rfl
  intro V hV
  rw [hξ V hV]
  apply congrArg (fun z : ℂ => (ξ' V * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro U hU
  rw [hc U hU]
  apply congrArg (fun z : ℂ => c' U * z)
  unfold primeDivisorMultiples
  rw [primeDivisorPositive_congr_point Q hQ D (divisorQuadraticScalar a V)
    (divisorQuadraticScalar b V) θ Φ R V.toList.prod U
    (s * P ^ 2) (divisorQuadraticScalar_congr_point a b V U (ha U hU))]

theorem arithmeticQuadraticCoefficient_mod (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P M h₀ : ℕ) (θ : ℝ) (s : ℕ) (hM : Odd M) :
    arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s =
      arithmeticQuadraticCoefficient Q hQ D Φ R P (M % (4 * Q.toList.prod)) h₀ θ s := by
  apply fullQuadraticCoefficient_congr_on
  · intro U hU
    exact quadraticInverseResidue_mod_multiple Q.toList.prod M U
      (primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU))
  · intro U hU
    unfold quadraticSymbolCoefficient
    rw [realJacobi_mod_multiple Q.toList.prod U.toList.prod M
      (primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU)) hM]
  · intro V hV
    unfold quadraticDivisorSymbol
    rw [realJacobi_mod_multiple Q.toList.prod V.toList.prod M
      (primeSet_prod_dvd_of_subset Q V (Finset.mem_powerset.mp hV)) hM]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-level Jacobi character is primitive -/

namespace Ostmann

theorem jacobiCharacterInt_prime (p : ℕ) [Fact p.Prime] :
    jacobiCharacterInt p = quadraticChar (ZMod p) := by
  apply MulChar.ext
  intro a
  have hcast : ((((a : ZMod p).val : ℤ) : ZMod p)) = (a : ZMod p) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  calc
    jacobiCharacterInt p a = jacobiCharacterInt p ((((a : ZMod p).val : ℤ) : ZMod p)) :=
      congrArg (jacobiCharacterInt p) hcast.symm
    _ = jacobiSym ((a : ZMod p).val : ℤ) p := jacobiCharacterInt_intCast p _
    _ = legendreSym p ((a : ZMod p).val : ℤ) := (jacobiSym.legendreSym.to_jacobiSym p _).symm
    _ = quadraticChar (ZMod p) a := by rw [legendreSym, hcast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_SquarefreeJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conductor of the Jacobi character at odd squarefree level -/

namespace Ostmann

private theorem jacobi_crt_negative (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : 0 < M) (hcop : p.Coprime M) :
    ∃ n : ℕ, n.Coprime (p * M) ∧ n ≡ 1 [MOD M] ∧ jacobiSym (n : ℤ) (p * M) = -1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  let n := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have hnp : (n : ℕ) ≡ (a : ZMod p).val [MOD p] := n.property.1
  have hnM : (n : ℕ) ≡ 1 [MOD M] := n.property.2
  have hpa : ((n : ℕ) : ZMod p) = (a : ZMod p) := by
    have h := (ZMod.natCast_eq_natCast_iff (n : ℕ) (a : ZMod p).val p).mpr hnp
    simpa only [ZMod.natCast_zmod_val] using h
  have hMa : ((n : ℕ) : ZMod M) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (n : ℕ) 1 M).mpr hnM
  have hcp : (n : ℕ).Coprime p := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) p).mp
    rw [hpa]
    exact a.isUnit
  have hcM : (n : ℕ).Coprime M := by
    apply (ZMod.isUnit_iff_coprime (n : ℕ) M).mp
    rw [hMa]
    exact isUnit_one
  have hJp : jacobiSym (n : ℤ) p = -1 := by
    rw [← jacobiCharacterInt_intCast p, Int.cast_natCast, jacobiCharacterInt_prime, hpa, ha]
  have hJM : jacobiSym (n : ℤ) M = 1 := by
    have h := jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' (n : ℤ) 1 M).mp
      (by simpa only [Int.cast_natCast, Int.cast_one] using hMa))
    simpa only [jacobiSym.one_left] using h
  exact ⟨n, hcp.mul_right hcM, hnM, by rw [jacobiSym.mul_right, hJp, hJM, mul_one]⟩

/-- An odd prime factor missing from the conductor is contradicted by a
CRT unit whose Jacobi value is -1 and whose conductor residue is 1. -/
theorem jacobiCharacter_squarefree_primitive (N : ℕ) [NeZero N]
    (hN : Squarefree N) (hodd : Odd N) : (jacobiCharacter N).IsPrimitive := by
  let χ := jacobiCharacter N
  have hcN := χ.conductor_dvd_level
  have hcp (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) : p ∣ χ.conductor := by
    by_contra hpc
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hodd.not_two_dvd_nat hpN
    have hprod : p * (N / p) = N := Nat.mul_div_cancel' hpN
    have hM : 0 < N / p := by
      have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    have hcop : p.Coprime (N / p) := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hN)
    obtain ⟨n, hn, hnM, hJn⟩ := jacobi_crt_negative p (N / p) hp hp2 hM hcop
    have hnc : n.Coprime N := hprod ▸ hn
    have hcd : χ.conductor ∣ N / p := by
      apply ((hp.coprime_iff_not_dvd.mpr hpc).symm).dvd_of_dvd_mul_left
      rwa [hprod]
    have hncon : (n : ZMod χ.conductor) = 1 := by
      have h := (ZMod.natCast_eq_natCast_iff n 1 χ.conductor).mpr (hnM.of_dvd hcd)
      simpa only [Nat.cast_one] using h
    have he := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hnc)
    have hv : χ.primitiveCharacter (n : ℤ) = 1 := by
      rw [Int.cast_natCast, hncon, map_one]
    have hv' : χ (n : ℤ) = -1 := by
      change jacobiCharacter N (n : ℤ) = -1
      rw [jacobiCharacter_intCast, ← hprod, hJn]
      norm_num
    rw [hv, hv'] at he
    norm_num at he
  have hNc : (∏ p ∈ N.primeFactors, p) ∣ χ.conductor := by
    apply (Nat.prod_primeFactors_dvd_iff χ.conductor_ne_zero).mpr
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hp'.1, hcp p hp'.1 hp'.2.1, χ.conductor_ne_zero⟩
  have hNc' : N ∣ χ.conductor := by
    simpa only [Nat.prod_primeFactors_of_squarefree hN] using hNc
  exact Nat.dvd_antisymm hcN hNc'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticReciprocityCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity formulas for the sign and two-part of a kernel -/

namespace Ostmann

theorem jacobi_odd_numerator_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (N : ℤ) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) := by
  have h := jacobiSym.quadratic_reciprocity' hN ha
  rw [qrSign.symm ha hN, qrSign.neg_one_pow hN ha] at h
  rw [ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp ha), ← pow_mul]
  rw [Nat.mul_comm (a / 2) (N / 2)]
  exact h.trans (mul_comm _ _)

theorem jacobi_negative_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(N : ℤ)) a = jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) := by
  rw [jacobiSym.neg _ ha, jacobi_odd_numerator_formula N a hN ha, pow_succ]
  ring

theorem jacobi_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (2 * (N : ℤ)) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2) * ZMod.χ₈ a := by
  rw [jacobiSym.mul_left, jacobiSym.at_two ha, jacobi_odd_numerator_formula N a hN ha]
  ring

theorem jacobi_negative_twice_odd_formula (N a : ℕ) (hN : Odd N) (ha : Odd a) :
    jacobiSym (-(2 * (N : ℤ))) a =
      jacobiSym (a : ℤ) N * (ZMod.χ₄ a) ^ (N / 2 + 1) * ZMod.χ₈ a := by
  rw [jacobiSym.neg _ ha, jacobi_twice_odd_formula N a hN ha, pow_succ]
  ring

theorem signedOddKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 4)) (haodd : Odd a) :
    signedOddKernelCharacter N negative (a : ZMod (Nat.lcm N 4)) =
      (jacobiSym (if negative then -(N : ℤ) else (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 4) := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (Nat.dvd_lcm_right N 4))
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 4))]
  rw [signedOddKernelCharacter, DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    jacobiCharacter_intCast]
  have hpow (k : ℕ) : (realFourCharacter ^ k) ((a : ℤ) : ZMod 4) = (ZMod.χ₄ a : ℝ) ^ k := by
    rw [Int.cast_natCast, ← hunit.unit_spec, MulChar.pow_apply_coe]
    rfl
  rw [hpow]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, if_false, add_zero]
    exact_mod_cast (jacobi_odd_numerator_formula N a hN haodd).symm
  · simp only [ite_true, if_true]
    exact_mod_cast (jacobi_negative_odd_formula N a hN haodd).symm

theorem evenKernelTwist_value (k a : ℕ) (ha : a.Coprime 8) :
    evenKernelTwist k (a : ZMod 8) = (ZMod.χ₄ a : ℝ) ^ k * (ZMod.χ₈ a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) 8 := Nat.isCoprime_iff_coprime.mpr ha
  have hunit : IsUnit (a : ZMod 4) := (ZMod.isUnit_iff_coprime a 4).mpr
    (ha.of_dvd_right (by decide : 4 ∣ 8))
  rw [evenKernelTwist, MulChar.mul_apply, ← Int.cast_natCast (R := ZMod 8),
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, Int.cast_natCast,
    ← hunit.unit_spec, MulChar.pow_apply_coe, hunit.unit_spec]
  rfl

theorem signedEvenKernelCharacter_value (N : ℕ) [NeZero N] (negative : Bool)
    (hN : Odd N) (a : ℕ) (ha : a.Coprime (Nat.lcm N 8)) (haodd : Odd a) :
    signedEvenKernelCharacter N negative (a : ZMod (Nat.lcm N 8)) =
      (jacobiSym (if negative then -(2 * (N : ℤ)) else 2 * (N : ℤ)) a : ℝ) := by
  have hcop : IsCoprime (a : ℤ) (Nat.lcm N 8) := Nat.isCoprime_iff_coprime.mpr ha
  rw [← Int.cast_natCast (R := ZMod (Nat.lcm N 8)), signedEvenKernelCharacter,
    DirichletCharacter.mul, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, jacobiCharacter_intCast,
    Int.cast_natCast, evenKernelTwist_value _ _ (ha.of_dvd_right (Nat.dvd_lcm_right N 8))]
  rw [← mul_assoc]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, if_false, add_zero]
    exact_mod_cast (jacobi_twice_odd_formula N a hN haodd).symm
  · simp only [ite_true, if_true]
    exact_mod_cast (jacobi_negative_twice_odd_formula N a hN haodd).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticKernelConductor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conductor bounds for the signed kernel characters -/

namespace Ostmann

/-- A twist whose conductor is coprime to that of a character cannot remove
any of the latter's conductor. -/
theorem conductor_dvd_conductor_mul {n : ℕ} [NeZero n]
    (χ ψ : DirichletCharacter ℝ n) (hcop : χ.conductor.Coprime ψ.conductor) :
    χ.conductor ∣ (χ * ψ).conductor := by
  have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
  rw [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at h
  exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))

/-- Only the two-part can change when the odd squarefree Jacobi character is
multiplied by a character of level coprime to that odd part. -/
theorem odd_part_dvd_twisted_conductor (N t : ℕ) [NeZero N] [NeZero t]
    (hN : Squarefree N) (hodd : Odd N) (hcop : N.Coprime t)
    (ψ : DirichletCharacter ℝ t) :
    N ∣ (DirichletCharacter.mul (jacobiCharacter N) ψ).conductor := by
  let : NeZero (Nat.lcm N t) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne t)⟩
  let χ' := (jacobiCharacter N).changeLevel (Nat.dvd_lcm_left N t)
  let ψ' := ψ.changeLevel (Nat.dvd_lcm_right N t)
  have hχ : χ'.conductor = N := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact jacobiCharacter_squarefree_primitive N hN hodd
  have hψ : ψ'.conductor ∣ t := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact ψ.conductor_dvd_level
  have hc : χ'.conductor.Coprime ψ'.conductor := by
    rw [hχ]
    exact hcop.of_dvd_right hψ
  change N ∣ (χ' * ψ').conductor
  simpa only [hχ] using conductor_dvd_conductor_mul χ' ψ' hc

theorem signedOddKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedOddKernelCharacter N negative).conductor ∧
    (signedOddKernelCharacter N negative).conductor ≤ 4 * N := by
  let : NeZero (Nat.lcm N 4) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 4 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 2
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 4)))
      (signedOddKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 4)).trans_eq (Nat.mul_comm N 4))

theorem signedEvenKernelCharacter_conductor_bounds (N : ℕ) [NeZero N]
    (negative : Bool) (hN : Squarefree N) (hodd : Odd N) :
    N ∣ (signedEvenKernelCharacter N negative).conductor ∧
    (signedEvenKernelCharacter N negative).conductor ≤ 8 * N := by
  let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (by decide)⟩
  refine ⟨odd_part_dvd_twisted_conductor N 8 hN hodd ?_ _, ?_⟩
  · simpa using hodd.coprime_two_right.pow_right 3
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne (Nat.lcm N 8)))
      (signedEvenKernelCharacter N negative).conductor_dvd_level).trans
      ((Nat.lcm_le_mul (Nat.pos_of_ne_zero (NeZero.ne N)) (by decide : 0 < 8)).trans_eq (Nat.mul_comm N 8))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PrimitiveKernelCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive real characters representing the four signed kernel shapes -/

namespace Ostmann

theorem character_ne_one_of_conductor_dvd {n N : ℕ} [NeZero n]
    (χ : DirichletCharacter ℝ n) (hN : 1 < N) (hdiv : N ∣ χ.conductor) : χ ≠ 1 := by
  intro h
  rw [h, DirichletCharacter.conductor_one] at hdiv
  have := Nat.dvd_one.mp hdiv
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_NonsquareJacobiCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete character behind nonsquare Jacobi cancellation -/

namespace Ostmann

private theorem exists_squarefree_jacobi_level (s : ℕ) (hs : Squarefree s)
    (hs1 : 1 < s) :
    ∃ q : ℕ, 0 < q ∧ q ∣ 8 * s ∧ ∃ χ : DirichletCharacter ℝ q,
      χ ≠ 1 ∧ ∀ a : ℕ, Odd a → a.Coprime s →
        χ (a : ZMod q) = realJacobi s a := by
  rcases Nat.even_or_odd s with he | ho
  · obtain ⟨N, hN⟩ := he
    have hsN : s = 2 * N := by omega
    have hNp : 0 < N := by omega
    have hsf : Squarefree (2 * N) := hsN ▸ hs
    have hNo : Odd N := (Nat.coprime_of_squarefree_mul hsf).odd_of_left
    have hNs : Squarefree N := hsf.of_mul_right
    let : NeZero N := ⟨hNp.ne'⟩
    let : NeZero (Nat.lcm N 8) := ⟨Nat.lcm_ne_zero hNp.ne' (by decide)⟩
    let χ := signedEvenKernelCharacter N false
    have hχ : χ ≠ 1 := by
      by_cases hN1 : N = 1
      · subst N
        intro hc
        have hv := signedEvenKernelCharacter_value 1 false (by decide) 5 (by decide) (by decide)
        change χ (5 : ZMod (Nat.lcm 1 8)) = _ at hv
        have hu : IsUnit (5 : ZMod (Nat.lcm 1 8)) := (ZMod.isUnit_iff_coprime 5 _).mpr (by decide)
        rw [hc, MulChar.one_apply hu] at hv
        have hJ : jacobiSym 2 5 = -1 := by
          rw [jacobiSym.at_two (by decide)]
          norm_num [ZMod.χ₈_nat_eq_if_mod_eight]
        norm_num [hJ] at hv
      · exact character_ne_one_of_conductor_dvd χ (by omega)
          (signedEvenKernelCharacter_conductor_bounds N false hNs hNo).1
    refine ⟨Nat.lcm N 8, Nat.pos_of_ne_zero (NeZero.ne _), ?_, χ, hχ, ?_⟩
    · apply Nat.lcm_dvd
      · rw [hsN]
        exact dvd_mul_of_dvd_right (dvd_mul_left N 2) 8
      · exact dvd_mul_right 8 s
    · intro a hao hac
      have hacN := hac.of_dvd_right (hsN ▸ dvd_mul_left N 2)
      have hac8 : a.Coprime 8 := by simpa using hao.coprime_two_right.pow_right 3
      have hacq := (hacN.mul_right hac8).of_dvd_right (Nat.lcm_dvd_mul N 8)
      have hv := signedEvenKernelCharacter_value N false hNo a hacq hao
      simpa [χ, realJacobi, hsN, Nat.cast_mul] using hv
  · let : NeZero s := ⟨by omega⟩
    let : NeZero (Nat.lcm s 4) := ⟨Nat.lcm_ne_zero (NeZero.ne s) (by decide)⟩
    let χ := signedOddKernelCharacter s false
    refine ⟨Nat.lcm s 4, Nat.pos_of_ne_zero (NeZero.ne _), ?_, χ, ?_, ?_⟩
    · exact Nat.lcm_dvd (dvd_mul_left s 8) (dvd_mul_of_dvd_left (by decide : 4 ∣ 8) s)
    · exact character_ne_one_of_conductor_dvd χ hs1
        (signedOddKernelCharacter_conductor_bounds s false hs ho).1
    · intro a hao hac
      have hac4 : a.Coprime 4 := by simpa using hao.coprime_two_right.pow_right 2
      have hacq := (hac.mul_right hac4).of_dvd_right (Nat.lcm_dvd_mul s 4)
      simpa [χ, realJacobi] using signedOddKernelCharacter_value s false ho a hacq hao

/-- At level `8*n` the extra nonunit zeroes are exactly the even arguments
and the common factors with `n`. Induction from the nontrivial squarefree
kernel preserves nonprincipality. -/
theorem exists_nonsquare_jacobi_character (n : ℕ) (hn : 0 < n)
    (hns : ¬IsSquare n) :
    ∃ χ : DirichletCharacter ℝ (8 * n), χ ≠ 1 ∧
      ∀ a : ℕ, χ (a : ZMod (8 * n)) = if Odd a then realJacobi n a else 0 := by
  obtain ⟨s, w, hsp, hwp, he, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hs1 : 1 < s := by
    by_contra h
    have hs : s = 1 := by omega
    apply hns
    refine ⟨w, ?_⟩
    simpa [hs, pow_two] using he.symm
  obtain ⟨q, hqp, hqd, ψ, hψ, hvalue⟩ := exists_squarefree_jacobi_level s hsf hs1
  have hsn : s ∣ n := ⟨w ^ 2, by nlinarith [he]⟩
  have hqn : q ∣ 8 * n := hqd.trans (Nat.mul_dvd_mul_left 8 hsn)
  let : NeZero (8 * n) := ⟨by omega⟩
  let χ := ψ.changeLevel hqn
  refine ⟨χ, ?_, ?_⟩
  · exact fun hc => hψ ((DirichletCharacter.changeLevel_eq_one_iff hqn).mp hc)
  · intro a
    by_cases hao : Odd a
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hao))]
      by_cases hac : a.Coprime (8 * n)
      · have hasn : a.Coprime n := hac.of_dvd_right (dvd_mul_left n 8)
        have has : a.Coprime s := hasn.of_dvd_right hsn
        have hwan : w ∣ n := ⟨w * s, by nlinarith [he]⟩
        have hwc : w.Coprime a := (hasn.of_dvd_right hwan).symm
        have hcast : χ (a : ZMod (8 * n)) = ψ (a : ZMod q) := by
          rw [← Int.cast_natCast (R := ZMod (8 * n)),
            DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _
              (Nat.isCoprime_iff_coprime.mpr hac), Int.cast_natCast]
        rw [hcast, hvalue a hao has]
        unfold realJacobi
        congr 1
        rw [← he, Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left,
          jacobiSym.pow_left, jacobiSym.sq_one (by simpa using hwc), one_mul]
      · have hnotu : ¬IsUnit (a : ZMod (8 * n)) := by
          simpa only [ZMod.isUnit_iff_coprime] using hac
        rw [MulChar.map_nonunit χ hnotu]
        have hasn : ¬a.Coprime n := by
          intro han
          have ha8 : a.Coprime 8 := by simpa using hao.coprime_two_right.pow_right 3
          exact hac (ha8.mul_right han)
        have ha0 : a ≠ 0 := by intro h; subst a; norm_num at hao
        let : NeZero a := ⟨ha0⟩
        have hj : jacobiSym (n : ℤ) a = 0 :=
          jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Nat.coprime_comm] using hasn)
        simp [realJacobi, hj]
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (hao h))]
      apply MulChar.map_nonunit
      intro hu
      have hc := (ZMod.isUnit_iff_coprime a (8 * n)).mp hu
      have hc2 : a.Coprime 2 := hc.of_dvd_right (dvd_mul_of_dvd_left (by decide : 2 ∣ 8) n)
      exact hao hc2.odd_of_right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PeriodicCharacterSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial sums of nonprincipal periodic characters -/

namespace Ostmann

open scoped BigOperators

private theorem sum_range_periodic_blocks (f : ℕ → ℝ) (q : ℕ)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (k r : ℕ) : ∑ a ∈ Finset.range (k * q + r), f a = ∑ a ∈ Finset.range r, f a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * q + r = q + (k * q + r) by ring, Finset.sum_range_add, hz, zero_add]
    have hp' (a : ℕ) : f (q + a) = f a := by simpa only [Nat.add_comm] using hp a
    simpa only [hp'] using ih

theorem periodic_zero_sum_range_bound (f : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (hb : ∀ a, |f a| ≤ 1) (N : ℕ) : |∑ a ∈ Finset.range N, f a| ≤ q := by
  have he : N / q * q + N % q = N := by simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  rw [← he, sum_range_periodic_blocks f q hp hz]
  calc
    _ ≤ ∑ a ∈ Finset.range (N % q), |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range (N % q), (1 : ℝ) := Finset.sum_le_sum (fun a _ => hb a)
    _ = (N % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt N hq).le

theorem nonprincipal_character_sum_range_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) (N : ℕ) :
    |∑ a ∈ Finset.range N, χ (a : ZMod q)| ≤ q := by
  apply periodic_zero_sum_range_bound (fun a => χ (a : ZMod q)) q
    (Nat.pos_of_ne_zero (NeZero.ne q))
  · intro a
    simp
  · have hsum : ∑ a : Fin q, χ ((a.val : ℕ) : ZMod q) = 0 := by
      have he := (ZMod.finEquiv q).toEquiv.sum_comp (fun a => χ a)
      have heq (a : Fin q) : (ZMod.finEquiv q).toEquiv a = (a.val : ZMod q) := by
        cases q with
        | zero => exact Fin.elim0 a
        | succ q =>
          apply Fin.ext
          exact (Nat.mod_eq_of_lt a.isLt).symm
      simp_rw [heq] at he
      exact he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    exact (Fin.sum_univ_eq_sum_range (fun a => χ (a : ZMod q)) q).symm.trans hsum
  · intro a
    simpa only [Real.norm_eq_abs] using χ.norm_le_one (a : ZMod q)

/-- The nonsquare term in the original odd-modulus Jacobi moment has a
uniform initial-sum bound, with no analytic hypothesis. -/
theorem nonsquare_jacobi_sum_range_bound (n N : ℕ) (hn : 0 < n)
    (hns : ¬IsSquare n) :
    |∑ a ∈ Finset.range N, if Odd a then realJacobi n a else 0| ≤ 8 * n := by
  obtain ⟨χ, hχ, hv⟩ := exists_nonsquare_jacobi_character n hn hns
  let : NeZero (8 * n) := ⟨by omega⟩
  simpa only [hv, Nat.cast_mul, Nat.cast_ofNat] using
    nonprincipal_character_sum_range_bound (8 * n) χ hχ N

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FallingFactorialError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary collision loss for sampling distinct indices -/

namespace Ostmann

/-- A convenient collision bound with no restriction that k be smaller than J. -/
theorem pow_le_descFactorial_add (J : ℕ) (hJ : 1 ≤ J) (k : ℕ) :
    J ^ k ≤ J.descFactorial k + k ^ 2 * J ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    by_cases hkJ : k ≤ J
    · have hmul := Nat.mul_le_mul_left J ih
      have hprev : J * J ^ (k - 1) = J ^ k := by
        rw [← pow_succ', Nat.sub_add_cancel hk1]
      have hdesc : J * J.descFactorial k =
          J.descFactorial (k + 1) + k * J.descFactorial k := by
        rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel hkJ]
      have hsmall := Nat.mul_le_mul_left k (Nat.descFactorial_le_pow J k)
      have herr : J * (k ^ 2 * J ^ (k - 1)) = k ^ 2 * J ^ k := by
        calc
          _ = k ^ 2 * (J * J ^ (k - 1)) := by ring
          _ = _ := by rw [hprev]
      rw [Nat.mul_add, hdesc, herr, ← pow_succ' J k] at hmul
      have hpoly : k ^ 2 + k ≤ (k + 1) ^ 2 := by nlinarith
      have hfinal := Nat.mul_le_mul_right (J ^ k) hpoly
      simp only [Nat.add_sub_cancel]
      nlinarith
    · have hJK : J ≤ (k + 1) ^ 2 := by
        have : J ≤ k := by omega
        nlinarith
      have h := Nat.mul_le_mul_right (J ^ k) hJK
      rw [pow_succ' J k]
      simpa only [Nat.add_sub_cancel] using h.trans (Nat.le_add_left _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_OddJacobiMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit Bonami moment bound over all odd moduli -/

namespace Ostmann

open scoped BigOperators

/-- The nonsquare contribution is bounded by `8*U^(2*l)` independently of
how many moduli are summed. Only the classical Bonami input remains. -/
theorem odd_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (U M l : ℕ)
    (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l) (a : S → ℝ) :
    (∑ m ∈ Finset.range M, if Odd m then
        |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0) ≤
      (M : ℝ) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ^ l +
      (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, |a s|) ^ (2 * l) := by
  classical
  let μ : ℕ → ℝ := fun m => if Odd m then 1 else 0
  have hμ : ∀ m ∈ Finset.range M, 0 ≤ μ m := by
    intro m hm
    dsimp [μ]
    split <;> norm_num
  have hE : 0 ≤ 8 * (U : ℝ) ^ (2 * l) := by positivity
  have hns (t : Fin (2 * l) → S) (ht : ¬IsSquare (∏ j, (t j).val)) :
      |∑ m ∈ Finset.range M, μ m * realJacobi (∏ j, (t j).val) m| ≤
        8 * (U : ℝ) ^ (2 * l) := by
    have hn : 0 < ∏ j, (t j).val := Finset.prod_pos (fun j _ =>
      Nat.pos_of_ne_zero (hS _ (t j).property).ne_zero)
    have hnU : ∏ j, (t j).val ≤ U ^ (2 * l) := by
      calc
        _ ≤ ∏ _j : Fin (2 * l), U := Finset.prod_le_prod' (fun j _ => hU _ (t j).property)
        _ = _ := by simp
    have hh := nonsquare_jacobi_sum_range_bound (∏ j, (t j).val) M hn ht
    have heq : (∑ m ∈ Finset.range M, μ m * realJacobi (∏ j, (t j).val) m) =
        ∑ m ∈ Finset.range M, if Odd m then realJacobi (∏ j, (t j).val) m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [μ]
      split <;> simp_all
    rw [heq]
    exact hh.trans (by exact_mod_cast Nat.mul_le_mul_left 8 hnU)
  have h := weighted_jacobi_even_moment_bound hB P S (Finset.range M) hS hP μ hμ a l hl
    (8 * (U : ℝ) ^ (2 * l)) hE hns
  have hmass : (∑ m ∈ Finset.range M, μ m) ≤ M := by
    calc
      _ ≤ ∑ _m ∈ Finset.range M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        dsimp [μ]
        split <;> norm_num
      _ = M := by simp
  have hleft : (∑ m ∈ Finset.range M, μ m * |∑ s : S, a s * realJacobi s.val m| ^ (2 * l)) =
      ∑ m ∈ Finset.range M, if Odd m then |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [μ]
    split <;> simp_all
  rw [hleft] at h
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_right hmass (by positivity)) _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_ComplexJacobiMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The odd-modulus moment estimate for complex coefficient arrays -/

namespace Ostmann

open scoped BigOperators

theorem complex_odd_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (U M l : ℕ)
    (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l) (b : S → ℂ) :
    (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (2 : ℝ) ^ (2 * l) * ((M : ℝ) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2) ^ l +
      (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, ‖b s‖) ^ (2 * l)) := by
  classical
  let B := (M : ℝ) *
    (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2) ^ l +
    (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, ‖b s‖) ^ (2 * l)
  have hcomponent (a : S → ℝ) (ha : ∀ s, |a s| ≤ ‖b s‖) :
      (∑ m ∈ Finset.range M, if Odd m then
        |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0) ≤ B := by
    apply (odd_jacobi_even_moment_bound hB P S hS hP U M l hU hl a).trans
    have he : (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ≤
        ∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (ha s) 2) (by positivity)
    have he0 : 0 ≤ ∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2 := by
      positivity
    have hsum : (∑ s : S, |a s|) ≤ ∑ s : S, ‖b s‖ := Finset.sum_le_sum (fun s _ => ha s)
    dsimp [B]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0 he l) (by positivity))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum (2 * l)) (by positivity))
  have hre := hcomponent (fun s => (b s).re) (fun s => Complex.abs_re_le_norm (b s))
  have him := hcomponent (fun s => (b s).im) (fun s => Complex.abs_im_le_norm (b s))
  have hpoint (m : ℕ) :
      ‖∑ s : S, b s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) ≤
        (2 : ℝ) ^ (2 * l - 1) *
          (|∑ s : S, (b s).re * realJacobi s.val m| ^ (2 * l) +
            |∑ s : S, (b s).im * realJacobi s.val m| ^ (2 * l)) := by
    let z := ∑ s : S, b s * (realJacobi s.val m : ℂ)
    have hz := (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) (2 * l)).trans
      (add_pow_le (abs_nonneg z.re) (abs_nonneg z.im) (2 * l))
    simpa [z, Complex.mul_re, Complex.mul_im] using hz
  calc
    _ ≤ (2 : ℝ) ^ (2 * l - 1) *
        ((∑ m ∈ Finset.range M, if Odd m then
            |∑ s : S, (b s).re * realJacobi s.val m| ^ (2 * l) else 0) +
          ∑ m ∈ Finset.range M, if Odd m then
            |∑ s : S, (b s).im * realJacobi s.val m| ^ (2 * l) else 0) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with h
      · exact hpoint m
      · simp
    _ ≤ (2 : ℝ) ^ (2 * l - 1) * (B + B) :=
      mul_le_mul_of_nonneg_left (add_le_add hre him) (by positivity)
    _ = (2 : ℝ) ^ (2 * l) * B := by
      calc
        _ = ((2 : ℝ) ^ (2 * l - 1) * 2) * B := by ring
        _ = _ := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * l)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiFamilyMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A moment bound uniform over a finite family of coefficient arrays -/

namespace Ostmann

open scoped BigOperators

/-- The array may be chosen separately at each modulus. Thus this estimate
also bounds the pointwise maximum over the family. -/
theorem complex_odd_jacobi_chosen_moment_bound (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (U M l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l)
    (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A) :
    (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l) *
        ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) := by
  classical
  have heach (i : I) :
      (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (2 : ℝ) ^ (2 * l) * ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) := by
    apply (complex_odd_jacobi_even_moment_bound hB P S hS hP U M l hU hl (b i)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (henergy i) l
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (hmass i) (2 * l)
  calc
    _ ≤ ∑ i : I, ∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with ho
      · exact Finset.single_le_sum
          (f := fun i : I => ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l))
          (fun i _ => by positivity) (Finset.mem_univ (pick m))
      · simp
    _ ≤ ∑ _i : I, (2 : ℝ) ^ (2 * l) *
        ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) :=
      Finset.sum_le_sum (fun i _ => heach i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring the finite-family moment to products of distinct primes -/

namespace Ostmann

open scoped BigOperators

theorem inverse_choose_le (J k : ℕ) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ J) :
    ((J.choose k : ℝ))⁻¹ ≤ 2 * (k.factorial : ℝ) / (J : ℝ) ^ k := by
  have hJ : 0 < J := by nlinarith
  have hkJ : k ≤ J := by nlinarith
  have hp : J ^ k = J * J ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
  have hb := pow_le_descFactorial_add J hJ k
  have hloss := Nat.mul_le_mul_right (J ^ (k - 1)) hsize
  have hbound : J ^ k ≤ 2 * J.descFactorial k := by nlinarith
  have hchoose : (0 : ℝ) < J.choose k := by exact_mod_cast Nat.choose_pos hkJ
  have hJpow : (0 : ℝ) < (J : ℝ) ^ k := by positivity
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hchoose hJpow).mpr
  have hh : (J : ℝ) ^ k ≤ 2 * ((k.factorial : ℝ) * (J.choose k : ℝ)) := by
    exact_mod_cast (show J ^ k ≤ 2 * (k.factorial * J.choose k) by
      rwa [Nat.descFactorial_eq_factorial_mul_choose] at hbound)
  nlinarith

/-- Positivity transfers any statistic of the prime product to all odd
moduli in its range; unique factorization gives the exact uniform weight. -/
theorem prime_product_mean_le_odd_sum (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (hZ : ∀ p ∈ P, p ≤ Z) (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k, F m) ≤
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ Finset.range (Z ^ k + 1), if Odd m then F m else 0) := by
  classical
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hmem := primeSubsetProducts_mem_range P k Z hP hodd hZ
  have hs : primeSubsetProducts P k ⊆ Finset.range (Z ^ k + 1) := by
    intro m hm
    have hh := (Finset.mem_filter.mp (hmem hm)).1
    have hh' := (Finset.mem_Icc.mp hh).2
    exact Finset.mem_range.mpr (by omega)
  have heq : (∑ m ∈ primeSubsetProducts P k, F m) =
      ∑ m ∈ primeSubsetProducts P k, if Odd m then F m else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    have ho := (Finset.mem_filter.mp (hmem hm)).2.1
    simp only [ho, ite_true, if_true]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hs
  intro m hm hnot
  split <;> simp_all

/-- This is the finite, explicit version of the manuscript's uniform
Jacobi-family moment estimate, before its final numerical specialization. -/
theorem prime_product_family_moment_bound (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S R : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hR : ∀ s ∈ S, s.primeFactors ⊆ R)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (U Z k l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hZ : ∀ p ∈ P, p ≤ Z)
    (hl : 0 < l) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ P.card)
    (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A) :
    (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
      (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
        ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l) *
          (((Z ^ k + 1 : ℕ) : ℝ) * E ^ l +
            (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l))) := by
  classical
  have hdom := prime_product_mean_le_odd_sum P k Z hP hodd hZ
    (fun m => ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l))
    (fun _ => by positivity)
  have hm := complex_odd_jacobi_chosen_moment_bound hB R S hS hR U (Z ^ k + 1) l
    hU hl b pick E A henergy hmass
  have hoddnonneg : 0 ≤ ∑ m ∈ Finset.range (Z ^ k + 1),
      if Odd m then ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0 := by
    apply Finset.sum_nonneg
    intro m hm
    split <;> positivity
  exact hdom.trans ((mul_le_mul_of_nonneg_right (inverse_choose_le P.card k hk hsize)
    hoddnonneg).trans (mul_le_mul_of_nonneg_left hm (by positivity)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductNormTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Taking the even root of the finite prime-product moment bound -/

namespace Ostmann

open scoped BigOperators

/-- This finite inequality keeps the square and nonsquare contributions
separate, so their numerical estimates can be supplied independently. -/
theorem prime_product_family_norm_transfer (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S R : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hR : ∀ s ∈ S, s.primeFactors ⊆ R)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (U Z k l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hZ : ∀ p ∈ P, p ≤ Z)
    (hl : 0 < l) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ P.card)
    (b : I → S → ℂ) (pick : ℕ → I) (E A B δ : ℝ)
    (hE : 0 ≤ E) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A)
    (hsquare : (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
      ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤ B ^ (2 * l))
    (hnonsquare : (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
      ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) *
      ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤ δ ^ (2 * l)) :
    (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
      (B * Real.sqrt E + δ) ^ (2 * l) := by
  have hm := prime_product_family_moment_bound hB P S R hS hR hP hodd U Z k l hU hZ
    hl hk hsize b pick E A henergy hmass
  have hpow : (Real.sqrt E) ^ (2 * l) = E ^ l := by
    rw [pow_mul, Real.sq_sqrt hE]
  apply hm.trans
  calc
    _ = ((2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
          ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ)) * E ^ l +
        ((2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
          ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l)) *
          ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l))) := by ring
    _ ≤ B ^ (2 * l) * E ^ l + δ ^ (2 * l) :=
      add_le_add (mul_le_mul_of_nonneg_right hsquare (pow_nonneg hE _)) hnonsquare
    _ = (B * Real.sqrt E) ^ (2 * l) + δ ^ (2 * l) := by rw [mul_pow, hpow]
    _ ≤ _ := pow_add_pow_le (mul_nonneg hB0 (Real.sqrt_nonneg E)) hδ (by omega)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeProductParameterBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical overhead in the fixed-family prime-product moment estimate -/

namespace Ostmann

open Filter Asymptotics

/-- The transfer-factor logarithm is negligible after division by the
moment order. The small positive gap `mu + kappa - 1` is used explicitly. -/
theorem eventual_prime_product_parameter_budget (C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ k l : ℝ,
      0 ≤ k → k ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (1 / 1000000 : ℝ) / 2 ≤ l → l ≤ T ^ (1 / 1000000 : ℝ) →
      C * T + k * (C + 3 * Real.log T) + C * l ≤
        ε * l * T ^ (9999999 / 10000000 : ℝ) := by
  let μ : ℝ := 1 / 1000000
  let κ : ℝ := 9999999 / 10000000
  let A := 4 * C + 6
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 5 by norm_num)).bound zero_lt_one
  have hpower := (tendsto_rpow_atTop (show 0 < κ + μ - 1 by norm_num [κ, μ])).eventually_ge_atTop
    (2 * A / ε)
  filter_upwards [hlog, hpower, eventually_ge_atTop (1 : ℝ)] with T hl hp hT k l hk hkU hlL hlU
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl' : Real.log T ≤ T ^ (2 / 5 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hT0.le _), one_mul] using hl
  have hρ : T ^ (3 / 5 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hμ : T ^ μ ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show μ ≤ 1 by norm_num [μ])
  have hklog : k * Real.log T ≤ 2 * T := by
    calc
      _ ≤ (2 * T ^ (3 / 5 : ℝ)) * T ^ (2 / 5 : ℝ) :=
        mul_le_mul hkU hl' hlogT (by positivity)
      _ = 2 * T := by
        rw [mul_assoc, ← Real.rpow_add hT0]
        norm_num
  have hrough : C * T + k * (C + 3 * Real.log T) + C * l ≤ A * T := by
    have hkT : k ≤ 2 * T := hkU.trans (mul_le_mul_of_nonneg_left hρ (by norm_num))
    have hlT : l ≤ T := hlU.trans hμ
    have hkC := mul_le_mul_of_nonneg_left hkT hC
    have hlC := mul_le_mul_of_nonneg_left hlT hC
    dsimp [A]
    nlinarith
  apply hrough.trans
  have hp' : A ≤ ε / 2 * T ^ (κ + μ - 1) := by
    have hh := (div_le_iff₀ hε).mp hp
    calc
      A = (2 * A) / 2 := by ring
      _ ≤ (T ^ (κ + μ - 1) * ε) / 2 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring
  have hcombined : T ^ (κ + μ - 1) * T = T ^ μ * T ^ κ := by
    calc
      _ = T ^ (κ + μ - 1) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ ((κ + μ - 1) + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (μ + κ) := by congr 1; ring
      _ = _ := Real.rpow_add hT0 _ _
  calc
    A * T ≤ (ε / 2 * T ^ (κ + μ - 1)) * T :=
      mul_le_mul_of_nonneg_right hp' hT0.le
    _ = ε * (T ^ μ / 2) * T ^ κ := by
      calc
        _ = ε / 2 * (T ^ (κ + μ - 1) * T) := by ring
        _ = _ := by rw [hcombined]; ring
    _ ≤ ε * l * T ^ κ := by gcongr

/-- The nonsquare character-sum error is exponentially small because
the number of sampled primes grows faster than the moment order. -/
theorem eventual_prime_product_error_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ k l : ℝ,
      T ^ (3 / 5 : ℝ) / 2 ≤ k →
      1 ≤ l → l ≤ T ^ (1 / 1000000 : ℝ) →
      C * T + C * l + 2 * C * l * T + k * (C + 3 * Real.log T - T) ≤
        -20 * l * T := by
  let μ : ℝ := 1 / 1000000
  let D := 4 * C + 20
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
    (show (0 : ℝ) < 1 / 12 by norm_num)
  have hpower := (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 5 - μ by norm_num [μ])).eventually_ge_atTop
    (4 * D)
  filter_upwards [hlog, hpower, eventually_ge_atTop (4 * C),
    eventually_ge_atTop (1 : ℝ)] with T hl hp hCT hT k l hk hl1 hlU
  have hT0 : 0 < T := by linarith
  have hk0 : 0 ≤ k := le_trans (by positivity) hk
  have hl0 : 0 ≤ l := by linarith
  have hlog' : Real.log T ≤ T / 12 := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hT), abs_of_nonneg hT0.le, one_div_mul_eq_div] using hl
  have hnegative : C + 3 * Real.log T - T ≤ -T / 2 := by linarith
  have hkl : D * l ≤ k / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hT0.le μ)
    have hpowers : T ^ (3 / 5 - μ) * T ^ μ = T ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring
    rw [hpowers] at hmul
    have hDl := mul_le_mul_of_nonneg_left hlU hD
    nlinarith only [hmul, hDl, hk]
  have hCT' : C * T ≤ C * l * T :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hl1) hT0.le
  have hCl : C * l ≤ C * l * T := by
    exact le_mul_of_one_le_right (mul_nonneg hC hl0) hT
  have hkn := mul_le_mul_of_nonneg_left hnegative hk0
  have hklT := mul_le_mul_of_nonneg_right hkl hT0.le
  dsimp [D] at hklT
  nlinarith only [hCT', hCl, hkn, hklT]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimeMomentFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary transfer factors for sampling distinct prime products -/

namespace Ostmann

theorem prime_moment_factorial_bound (J k : ℕ) (a : ℝ) (hJ : 0 < J)
    (hk : (k : ℝ) ≤ Real.exp a * J) :
    2 * (k.factorial : ℝ) / (J : ℝ) ^ k ≤ 2 * Real.exp ((k : ℝ) * a) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hk k
  rw [mul_pow, ← Real.exp_nat_mul] at hp
  apply (div_le_iff₀ (pow_pos hJ0 _)).mpr
  nlinarith only [hfac, hp]

theorem prime_moment_square_factor_bound (J Z k l I : ℕ) (a t C : ℝ)
    (hJ : 0 < J) (hk : (k : ℝ) ≤ Real.exp (a - t) * J)
    (hZ : (Z : ℝ) ≤ Real.exp t) (hZ1 : 1 ≤ Z)
    (hI : (I : ℝ) ≤ Real.exp C) :
    (2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
      ((I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤
      Real.exp (2 + C + 2 * l + (k : ℝ) * a) := by
  have hfac := prime_moment_factorial_bound J k (a - t) hJ hk
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow2 : (2 : ℝ) ^ (2 * l) ≤ Real.exp (2 * l) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 (2 * l)
  have hZpow : ((Z ^ k + 1 : ℕ) : ℝ) ≤ 2 * Real.exp ((k : ℝ) * t) := by
    have h1 : (1 : ℝ) ≤ (Z : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hZ1)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Z : (0 : ℝ) ≤ Z) hZ k
    rw [← Real.exp_nat_mul] at hp
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    linarith
  calc
    _ ≤ (2 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) * (2 * Real.exp ((k : ℝ) * t)) := by
      gcongr
    _ ≤ (Real.exp 1 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) * (Real.exp 1 * Real.exp ((k : ℝ) * t)) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem prime_moment_nonsquare_factor_bound (J k l I U : ℕ) (a t C A B : ℝ)
    (hJ : 0 < J) (hk : (k : ℝ) ≤ Real.exp (a - t) * J)
    (hI : (I : ℝ) ≤ Real.exp C) (hU : (U : ℝ) ≤ Real.exp B)
    (hA : 0 ≤ A) (hmass : A ≤ Real.exp B) :
    (2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
      ((I : ℝ) * (2 : ℝ) ^ (2 * l)) *
      ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤
      Real.exp (4 + C + 2 * l + 4 * l * B + (k : ℝ) * (a - t)) := by
  have hfac := prime_moment_factorial_bound J k (a - t) hJ hk
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one,
      show (2 : ℝ) ^ 3 = 8 by norm_num] using hh
  have hfac' : 2 * (k.factorial : ℝ) / (J : ℝ) ^ k ≤
      Real.exp 1 * Real.exp ((k : ℝ) * (a - t)) :=
    hfac.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _))
  have hpow2 : (2 : ℝ) ^ (2 * l) ≤ Real.exp (2 * l) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 (2 * l)
  have hUp := pow_le_pow_left₀ (Nat.cast_nonneg U : (0 : ℝ) ≤ U) hU (2 * l)
  have hAp := pow_le_pow_left₀ hA hmass (2 * l)
  rw [← Real.exp_nat_mul] at hUp hAp
  calc
    _ ≤ (Real.exp 1 * Real.exp ((k : ℝ) * (a - t))) *
        (Real.exp C * Real.exp (2 * l)) *
        ((Real.exp 3 * Real.exp ((2 * l : ℕ) * B)) * Real.exp ((2 * l : ℕ) * B)) := by
      gcongr
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem prime_moment_sampling_ratio (C T : ℝ) (J k : ℕ)
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hJ : Real.exp T ≤ C * T * J)
    (hk : (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ)) :
    (k : ℝ) ≤ Real.exp (2 * C + 3 * Real.log T - T) * J := by
  have hT0 : 0 < T := by linarith
  have hkT : (k : ℝ) ≤ 2 * T := by
    apply hk.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hconst : 2 * C ≤ Real.exp (2 * C) := by linarith [Real.add_one_le_exp (2 * C)]
  have hpower : T ^ 2 ≤ T ^ 3 := pow_le_pow_right₀ hT (by omega)
  have hbound : 2 * C * T ^ 2 ≤ Real.exp (2 * C + 3 * Real.log T) := by
    calc
      _ ≤ Real.exp (2 * C) * T ^ 3 := mul_le_mul hconst hpower (by positivity) (Real.exp_nonneg _)
      _ = _ := by
        have hx : Real.exp (3 * Real.log T) = T ^ 3 := by
          calc
            _ = Real.exp ((3 : ℕ) * Real.log T) := by norm_num
            _ = (Real.exp (Real.log T)) ^ 3 := Real.exp_nat_mul _ _
            _ = _ := by rw [Real.exp_log hT0]
        rw [Real.exp_add, hx]
  have hscaled : (k : ℝ) * Real.exp T ≤ Real.exp (2 * C + 3 * Real.log T) * J := by
    calc
      _ ≤ (k : ℝ) * (C * T * J) := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _)
      _ ≤ (2 * T) * (C * T * J) := mul_le_mul_of_nonneg_right hkT (by positivity)
      _ = (2 * C * T ^ 2) * J := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)
  have heq : (Real.exp (2 * C + 3 * Real.log T - T) * J) * Real.exp T =
      Real.exp (2 * C + 3 * Real.log T) * J := by
    calc
      _ = (Real.exp (2 * C + 3 * Real.log T - T) * Real.exp T) * J := by ring
      _ = _ := by rw [← Real.exp_add, sub_add_cancel]
  exact (mul_le_mul_iff_left₀ (Real.exp_pos T)).mp (hscaled.trans_eq heq.symm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimeMomentAsymptotics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual square and nonsquare transfer factors at manuscript scales -/

namespace Ostmann

open Filter

theorem eventual_prime_moment_factors (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ J Z k l I U : ℕ, ∀ A : ℝ,
      0 < J → 1 ≤ Z → Real.exp T ≤ C * T * J →
      (Z : ℝ) ≤ Real.exp (T + 1) →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (I : ℝ) ≤ Real.exp (C * T) → (U : ℝ) ≤ Real.exp (C * T) →
      0 ≤ A → A ≤ Real.exp (C * T) →
      ((2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
        ((I : ℝ) * (2 : ℝ) ^ (2 * l)) * ((Z ^ k + 1 : ℕ) : ℝ) ≤
        (Real.exp (ε * T ^ (9999999 / 10000000 : ℝ))) ^ (2 * l)) ∧
      ((2 * (k.factorial : ℝ) / (J : ℝ) ^ k) *
        ((I : ℝ) * (2 : ℝ) ^ (2 * l)) *
        ((8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) ≤
        (Real.exp (-10 * T)) ^ (2 * l)) := by
  let D := 4 * C + 10
  have hC0 : 0 ≤ C := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [eventual_prime_product_parameter_budget D (2 * ε) hD (by positivity),
    eventual_prime_product_error_budget D hD, eventually_ge_atTop (1 : ℝ)] with T hs he hT
  intro J Z k l I U A hJ hZ1 hpop hZ hkL hkU hl1 hlL hlU hI hU hA hmass
  have hT0 : 0 ≤ T := by linarith
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast hl1
  have hratio := prime_moment_sampling_ratio C T J k hC0 hT hpop hkU
  have hratio' : (k : ℝ) ≤ Real.exp ((2 * C + 1 + 3 * Real.log T) - (T + 1)) * J := by
    have heq : (2 * C + 1 + 3 * Real.log T) - (T + 1) = 2 * C + 3 * Real.log T - T := by ring
    simpa only [heq] using hratio
  constructor
  · apply (prime_moment_square_factor_bound J Z k l I (2 * C + 1 + 3 * Real.log T)
      (T + 1) (C * T) hJ hratio' hZ hZ1 hI).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hb := hs k l hk0 hkU hlL hlU
    have hconst : 2 + C * T ≤ D * T := by dsimp [D]; nlinarith
    have hlconst : 2 * (l : ℝ) ≤ D * l := by dsimp [D]; nlinarith
    have hkconst : (k : ℝ) * (2 * C + 1 + 3 * Real.log T) ≤
        k * (D + 3 * Real.log T) := by dsimp [D]; nlinarith
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hb, hconst, hlconst, hkconst]
  · apply (prime_moment_nonsquare_factor_bound J k l I U (2 * C + 3 * Real.log T)
      T (C * T) A (C * T) hJ hratio hI hU hA hmass).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hb := he k l hkL hl1' hlU
    have hconst : 4 + C * T ≤ D * T := by dsimp [D]; nlinarith
    have hlconst : 2 * (l : ℝ) ≤ D * l := by dsimp [D]; nlinarith
    have hlT : 4 * (l : ℝ) * (C * T) ≤ 2 * D * l * T := by
      have hh : 4 * C ≤ 2 * D := by dsimp [D]; linarith
      have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hl0) hT0
      nlinarith only [hmul]
    have hkconst : (k : ℝ) * (2 * C + 3 * Real.log T - T) ≤
        k * (D + 3 * Real.log T - T) := by dsimp [D]; nlinarith
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hb, hconst, hlconst, hlT, hkconst]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_PrimeSetDivisorSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Divisor sums of the actual squarefree prime-set modulus -/

namespace Ostmann

open scoped BigOperators

theorem primeSet_modulus_squarefree (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Squarefree Q.toList.prod := by
  simpa using primeSubset_product_squarefree Q hQ

theorem sum_primeSet_divisors (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (f : ℕ → ℂ) :
    (∑ d ∈ Q.toList.prod.divisors, f d) = ∑ U ∈ Q.powerset, f U.toList.prod := by
  classical
  have hQpos : 0 < Q.toList.prod := prime_list_prod_pos _ (primeSet_list_prime Q hQ)
  have hQsf := primeSet_modulus_squarefree Q hQ
  symm
  apply Finset.sum_bij (fun U _ => U.toList.prod)
  · intro U hU
    exact Nat.mem_divisors.mpr ⟨primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU), hQpos.ne'⟩
  · intro U hU V hV huv
    apply primeSubset_product_injective Q hQ (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV)
    simpa using huv
  · intro d hd
    have hdQ := (Nat.mem_divisors.mp hd).1
    have hdsf : Squarefree d := hQsf.squarefree_of_dvd hdQ
    have hsub : d.primeFactors ⊆ Q := by
      intro p hp
      rw [← primeSet_modulus_primeFactors Q hQ]
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdQ, hQpos.ne'⟩
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr hsub, ?_⟩
    simpa using Nat.prod_primeFactors_of_squarefree hdsf
  · intro U _
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_JacobiComplex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete complex Jacobi character used in the Fourier expansion -/

namespace Ostmann

theorem jacobiComplex_natCast (M : ℕ) [NeZero M] (s : ℕ) :
    jacobiComplex M (s : ZMod M) = (realJacobi s M : ℂ) := by
  change ((jacobiCharacterInt M) (s : ZMod M) : ℂ) = ((jacobiSym (s : ℤ) M : ℝ) : ℂ)
  rw [← Int.cast_natCast s, jacobiCharacterInt_intCast]
  simp

theorem jacobiComplex_isQuadratic (M : ℕ) [NeZero M] : (jacobiComplex M).IsQuadratic := by
  apply MulChar.IsQuadratic.comp
  intro a
  change jacobiSym (a.val : ℤ) M = 0 ∨ jacobiSym (a.val : ℤ) M = 1 ∨ jacobiSym (a.val : ℤ) M = -1
  rcases jacobiSym.trichotomy (a.val : ℤ) M with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SquarefreeFrequencyRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite rectangular expansion underlying the original coefficients -/

namespace Ostmann

open scoped BigOperators

theorem mem_squarefreeKernelSupport (L N s : ℕ) :
    s ∈ squarefreeKernelSupport L N ↔ 1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L := by
  simp only [squarefreeKernelSupport, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem frequencyTriples_rectangle (L N : ℕ) (hL : Squarefree L) :
    frequencyTriples L N =
      ((squarefreeKernelSupport L N).product (L.divisors.product (Finset.Icc 1 N))).filter
        (fun z => z.1 * z.2.1 * z.2.2 ^ 2 ≤ N) := by
  classical
  ext z
  rcases z with ⟨s, v, w⟩
  simp only [mem_frequencyTriples, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc, mem_squarefreeKernelSupport]
  constructor
  · rintro ⟨hs, hsN, hv, hw, hwN, hsv, hcop, hval⟩
    exact ⟨⟨⟨hs, hsN, hsv.of_mul_left, hcop⟩, hv, hw, hwN⟩, hval⟩
  · rintro ⟨⟨⟨hs, hsN, hsf, hcop⟩, hv, hw, hwN⟩, hval⟩
    have hvd := (Nat.mem_divisors.mp hv).1
    have hvf : Squarefree v := hL.squarefree_of_dvd hvd
    have hsv : Squarefree (s * v) := squarefree_mul_iff.mpr
      ⟨Nat.coprime_iff_isRelPrime.mp (hcop.of_dvd_right hvd), hsf, hvf⟩
    exact ⟨hs, hsN, hv, hw, hwN, hsv, hcop, hval⟩

theorem sum_frequencyTriples_rectangle (L N : ℕ) (hL : Squarefree L)
    (F : ℕ × ℕ × ℕ → ℂ)
    (hF : ∀ z, N < z.1 * z.2.1 * z.2.2 ^ 2 → F z = 0) :
    (∑ z ∈ frequencyTriples L N, F z) =
      ∑ s ∈ squarefreeKernelSupport L N, ∑ v ∈ L.divisors, ∑ w ∈ Finset.Icc 1 N, F (s, v, w) := by
  classical
  rw [frequencyTriples_rectangle L N hL]
  calc
    _ = ∑ z ∈ (squarefreeKernelSupport L N).product (L.divisors.product (Finset.Icc 1 N)), F z := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z hz hn
      apply hF
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hz, by omega⟩)
    _ = _ := by simp only [Finset.product_eq_sprod, Finset.sum_product]

/-- Inclusion-exclusion and unique squarefree decomposition give
the three nested sums defining C_s^(P), with a common finite support. -/
theorem rectangular_frequency_moebius_expansion (L N : ℕ) (hL : Squarefree L)
    {M : ℕ} (hM : 0 < M) (χ : DirichletCharacter ℂ M) (hχ : χ.IsQuadratic)
    (F : ℕ → ℂ) (hF : ∀ u, N < u → F u = 0) :
    (∑ u ∈ Finset.Icc 1 N, χ (u : ZMod M) * F u) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ s ∈ squarefreeKernelSupport L N, χ (s : ZMod M) *
          ∑ v ∈ L.divisors, χ (v : ZMod M) *
            ∑ w ∈ (Finset.Icc 1 N).filter (fun w => P ∣ w), F (s * v * w ^ 2) := by
  classical
  rw [squarefree_frequency_moebius_expansion L N (Nat.pos_of_ne_zero hL.ne_zero) hM χ hχ F]
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  rw [Finset.sum_filter]
  rw [sum_frequencyTriples_rectangle L N hL _ (by
    intro z hz
    simp only [hF _ hz, mul_zero, ite_self])]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency summand and its exact quadratic normalization -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticFrequencyTerm_at_square {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (s v w : ℕ) :
    quadraticFrequencyTerm g a θ Φ R (s * v * w ^ 2) =
      quadraticDensityTerm g (a * (v : ZMod q)) θ Φ R v s w := by
  unfold quadraticFrequencyTerm quadraticDensityTerm
  rw [← realAdditivePhase_nat_mul]
  have hg : a * ((s * v * w ^ 2 : ℕ) : ZMod q) =
      a * (v : ZMod q) * (w : ZMod q) ^ 2 * (s : ZMod q) := by push_cast; ring
  have he : θ * ((s * v * w ^ 2 : ℕ) : ℝ) / q =
      (s : ℝ) * (θ * v * (w : ℝ) ^ 2 / q) := by push_cast; ring
  have hw : ((s * v * w ^ 2 : ℕ) : ℝ) / (R * q) =
      (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) := by push_cast; ring
  rw [hg, he, hw]

theorem quadraticFrequencyTerm_zero_above {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (N u : ℕ) (hR : 0 < R)
    (hN : H * R * q ≤ N) (hu : N < u)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    quadraticFrequencyTerm g a θ Φ R u = 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnu : (N : ℝ) < u := by exact_mod_cast hu
  have harg : H < (u : ℝ) / (R * q) := by
    apply (lt_div_iff₀ (mul_pos hR hqR)).mpr
    nlinarith
  simp only [quadraticFrequencyTerm, hΦ _ harg, mul_zero]

theorem quadratic_frequency_normalizer (q s v : ℕ) (R : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    (Real.sqrt (R * q) : ℂ)⁻¹ =
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ * (Real.sqrt (v : ℝ) : ℂ)⁻¹ *
        (Real.sqrt (R * q / ((s : ℝ) * v)) : ℂ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hsC : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hsR).ne'
  have hvC : (Real.sqrt (v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hvR).ne'
  have hRC : (Real.sqrt (R * q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hR hqR)).ne'
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul hsR.le]
  push_cast
  field_simp

theorem positiveQuadraticMultiples_eq_frequency_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R H : ℝ) (s v P N : ℕ) (hR : 0 < R) (_hH : 0 ≤ H)
    (hs : 0 < s) (hv : 0 < v) (hP : 0 < P) (hN : 1 ≤ N)
    (hcut : H * R * q ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    positiveQuadraticMultiples g (a * (v : ZMod q)) θ Φ R v s P =
      (Real.sqrt (R * q / ((s : ℝ) * v)) : ℂ)⁻¹ *
        ∑ w ∈ (Finset.Icc 1 N).filter (fun w => P ∣ w),
          quadraticFrequencyTerm g a θ Φ R (s * v * w ^ 2) := by
  classical
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [positiveQuadraticMultiples_eq_cutoff g (a * (v : ZMod q)) θ Φ R v H s P hP hR hvR hs hΦ]
  congr 1
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hvR' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hupper : Real.sqrt (H * R * q / ((s : ℝ) * v)) ≤ N := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < (s : ℝ) * v)).mpr
    have hsv : (1 : ℝ) ≤ (s : ℝ) * v := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsv (sq_nonneg (N : ℝ))]
  have hsub : quadraticCompactCutoff q R v H s ⊆ Finset.Icc 1 N := by
    intro w hw
    obtain ⟨hw0, hwW⟩ := Finset.mem_Ioc.mp hw
    refine Finset.mem_Icc.mpr ⟨hw0, ?_⟩
    have hb := (Nat.cast_le.mpr hwW).trans (Nat.floor_le (Real.sqrt_nonneg _))
    exact_mod_cast hb.trans hupper
  calc
    _ = ∑ w ∈ (Finset.Icc 1 N).filter (fun w => P ∣ w),
        quadraticDensityTerm g (a * (v : ZMod q)) θ Φ R v s w := by
      apply Finset.sum_subset (Finset.filter_subset_filter (fun w => P ∣ w) hsub)
      intro w hw hn
      obtain ⟨hw, hpw⟩ := Finset.mem_filter.mp hw
      by_contra hne
      have hm := quadraticDensityTerm_mem_cutoff g (a * (v : ZMod q)) θ Φ R v H s s w
        hR hvR hs le_rfl (Finset.mem_Icc.mp hw).1 hΦ hne
      exact hn (Finset.mem_filter.mpr ⟨hm, hpw⟩)
    _ = _ := by simp_rw [quadraticFrequencyTerm_at_square]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticFrequencyExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact coefficient expansion of the positive Fourier frequencies -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadratic_frequency_expansion {q M : ℕ} [NeZero q]
    (L N : ℕ) (hL : Squarefree L) (hM : 0 < M)
    (χ : DirichletCharacter ℂ M) (hχ : χ.IsQuadratic)
    (g : ZMod q → ℂ) (a : ZMod q) (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N) (hcut : H * R * q ≤ N)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    (Real.sqrt (R * q) : ℂ)⁻¹ *
      (∑ u ∈ Finset.Icc 1 N, χ (u : ZMod M) * quadraticFrequencyTerm g a θ Φ R u) =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ s ∈ squarefreeKernelSupport L N,
          (χ (s : ZMod M) * (Real.sqrt (s : ℝ) : ℂ)⁻¹) *
          ∑ v ∈ L.divisors, (χ (v : ZMod M) * (Real.sqrt (v : ℝ) : ℂ)⁻¹) *
            positiveQuadraticMultiples g (a * (v : ZMod q)) θ Φ R v s P := by
  classical
  rw [rectangular_frequency_moebius_expansion L N hL hM χ hχ _
    (fun u hu => quadraticFrequencyTerm_zero_above g a θ Φ R H N u hR hcut hu hΦ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hPpos : 0 < P := Nat.pos_of_mem_divisors hP
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hspos := (mem_squarefreeKernelSupport L N s).mp hs |>.1
  rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hvpos : 0 < v := Nat.pos_of_mem_divisors hv
  rw [positiveQuadraticMultiples_eq_frequency_cutoff g a θ Φ R H s v P N hR hH hspos hvpos hPpos hN hcut hΦ,
    quadratic_frequency_normalizer q s v R (NeZero.pos q) hspos hvpos hR]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorFrequencyExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original density Fourier frequencies as divisor quadratic sums -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem primeDivisorMultiples_eq_original (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U V : Finset ℕ) (hU : U ⊆ Q)
    (M h₀ s P : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hR : 0 < R)
    (hV : 0 < V.toList.prod) (hP : 0 < P) :
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
      (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s =
      positiveQuadraticMultiples (densityFourier (densityCRTList U.toList
        (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
        (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value)
        (quadraticInverseResidue M U * (V.toList.prod : ZMod U.toList.prod))
        ((h₀ : ℝ) + θ) Φ R V.toList.prod s P := by
  intro _
  rw [positiveQuadraticMultiples_eq _ _ _ _ _ _ _ _ hP hR.le (by exact_mod_cast hV.le)]
  simp only [primeDivisorMultiples, primeDivisorPositive, dite_eq_left hU, divisorQuadraticScalar]

theorem primeDivisorFrequency_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (M N h₀ : ℕ) [NeZero M] (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    primeDivisorFrequency Q hQ D U M N h₀ θ R Φ =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ s ∈ squarefreeKernelSupport Q.toList.prod N,
          ((realJacobi s M : ℂ) * (Real.sqrt (s : ℝ) : ℂ)⁻¹) *
          ∑ V ∈ Q.powerset,
            ((realJacobi V.toList.prod M : ℂ) * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) *
            primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
              (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
  have hcutU : H * R * U.toList.prod ≤ N := by
    exact (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (primeSet_prod_le_of_subset Q U hQ hU)) (mul_nonneg hH hR.le)).trans hcut
  have he := quadratic_frequency_expansion Q.toList.prod N (primeSet_modulus_squarefree Q hQ)
    (NeZero.pos M) (jacobiComplex M) (jacobiComplex_isQuadratic M)
    (densityFourier (densityCRTList U.toList (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
      (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value)
    (quadraticInverseResidue M U) ((h₀ : ℝ) + θ) R H Φ hR hH hN hcutU hΦ
  simp only [jacobiComplex_natCast] at he
  simp only [primeDivisorFrequency, dite_eq_left hU]
  rw [he]
  apply Finset.sum_congr rfl
  intro P hP
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [sum_primeSet_divisors Q hQ]
  apply Finset.sum_congr rfl
  intro V hV
  congr 1
  exact (primeDivisorMultiples_eq_original Q hQ D U V hU M h₀ s P θ R Φ hR
    (prime_list_prod_pos _ (primeSet_list_prime V (fun p hp => hQ p ((Finset.mem_powerset.mp hV) hp))))
    (Nat.pos_of_mem_divisors hP)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMomentMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from the finite even moment to expected absolute size -/

namespace Ostmann

open scoped BigOperators

theorem finite_mean_le_of_moment {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (B : ℝ) (m : ℕ) (hB : 0 ≤ B) (hm : 0 < m) (hf : ∀ i ∈ S, 0 ≤ f i)
    (h : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ m) ≤ B ^ m) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i) ≤ B := by
  by_cases hS : S.Nonempty
  · have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hw : (∑ _i ∈ S, (S.card : ℝ)⁻¹) = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ hcard.ne'
    have hj := Real.pow_arith_mean_le_arith_mean_pow S (fun _ => (S.card : ℝ)⁻¹) f
      (fun _ _ => inv_nonneg.mpr hcard.le) hw hf m
    simp only [← Finset.mul_sum] at hj
    exact (pow_le_pow_iff_left₀
      (mul_nonneg (inv_nonneg.mpr hcard.le) (Finset.sum_nonneg hf)) hB hm.ne').mp (hj.trans h)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simpa only [he, Finset.card_empty, Nat.cast_zero, inv_zero, Finset.sum_empty,
      mul_zero] using hB

theorem prime_product_mean_le_of_moment (P : Finset ℕ) (k m : ℕ)
    (f : ℕ → ℂ) (B : ℝ) (hP : ∀ p ∈ P, p.Prime) (hB : 0 ≤ B) (hm : 0 < m)
    (h : (P.card.choose k : ℝ)⁻¹ * (∑ n ∈ primeSubsetProducts P k, ‖f n‖ ^ m) ≤ B ^ m) :
    (P.card.choose k : ℝ)⁻¹ * (∑ n ∈ primeSubsetProducts P k, ‖f n‖) ≤ B := by
  rw [← primeSubsetProducts_card P k hP] at h ⊢
  exact finite_mean_le_of_moment _ _ B m hB hm (fun _ _ => norm_nonneg _) h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_DivisorCoefficientError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform errors survive both finite divisor sums -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem sixteenth_divisor_weight_bound (K : ℕ) :
    (1 + 1 / 16 : ℝ) ^ K ≤ Real.exp ((K : ℝ) / 16) := by
  have hb : (1 + 1 / 16 : ℝ) ≤ Real.exp (1 / 16) := by
    linarith [Real.add_one_le_exp (1 / 16 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 1 / 16) hb K
  simpa only [← Real.exp_nat_mul, div_eq_mul_inv, one_mul] using hp

theorem divisor_combination_difference_bound (Q : Finset ℕ)
    (c f g : Finset ℕ → ℂ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (he : ∀ U ∈ Q.powerset, ‖f U - g U‖ ≤ δ) :
    ‖(∑ U ∈ Q.powerset, c U * f U) - ∑ U ∈ Q.powerset, c U * g U‖ ≤
      δ * (1 + 1 / 16 : ℝ) ^ Q.card := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ U ∈ Q.powerset, δ * (1 / 16 : ℝ) ^ U.card := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul, mul_comm δ]
      exact mul_le_mul (hc U hU) (he U hU) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.mul_sum, sum_powerset_power_card]

theorem fullQuadraticCoefficient_difference_bound (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ θ' : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R R' : ℝ) (P : ℕ) (c ξ : Finset ℕ → ℂ) (s : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1)
    (he : ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
      ‖primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod P U s -
        primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ' Φ R' V.toList.prod P U s‖ ≤ δ) :
    ‖fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s -
      fullQuadraticCoefficient Q hQ D a θ' Φ R' P c ξ s‖ ≤
      (δ * (1 + 1 / 16 : ℝ) ^ Q.card) *
        ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  let F : Finset ℕ → ℕ → ℂ := fun V s =>
    (∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod P U s) -
      ∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ' Φ R' V.toList.prod P U s
  have hd : fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s -
      fullQuadraticCoefficient Q hQ D a θ' Φ R' P c ξ s =
        divisorWeightedCoefficient Q ξ F s := by
    simp only [fullQuadraticCoefficient, divisorWeightedCoefficient, F, mul_sub,
      Finset.sum_sub_distrib]
  rw [hd]
  exact divisorWeightedCoefficient_norm_le Q ξ F s _ (by positivity) hξ
    (fun V hV => divisor_combination_difference_bound Q c _ _ δ hδ hc (he V hV))

theorem full_coefficient_grid_error_budget (Q : Finset ℕ) (T : ℝ)
    (hT : 0 ≤ T) (hcard : (Q.card : ℝ) ≤ T) (hQ : ∀ p ∈ Q, 1000000 ≤ p) :
    (Real.exp (-128 * T) * (1 + 1 / 16 : ℝ) ^ Q.card) *
      (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤ Real.exp (-127 * T) := by
  calc
    _ ≤ (Real.exp (-128 * T) * Real.exp ((Q.card : ℝ) / 16)) *
        Real.exp ((Q.card : ℝ) / 1000) := by
      gcongr
      · exact sixteenth_divisor_weight_bound Q.card
      · exact reciprocal_sqrt_divisor_mass_le Q hQ
    _ = Real.exp (-128 * T + Q.card / 16 + Q.card / 1000) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCommonCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite support for every scale in the parameter grid -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticCompactCutoff_mono (q N : ℕ) (R Rmax v H : ℝ)
    (hR : R ≤ Rmax) (hv : 0 ≤ v) (hH : 0 ≤ H) :
    quadraticCompactCutoff q R v H N ⊆ quadraticCompactCutoff q Rmax v H N := by
  unfold quadraticCompactCutoff
  apply Finset.Ioc_subset_Ioc le_rfl
  apply Nat.floor_mono
  apply Real.sqrt_le_sqrt
  gcongr

theorem positiveQuadraticSum_eq_upper_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R Rmax v H : ℝ) (s : ℕ) (hR : 0 < R) (hRmax : R ≤ Rmax)
    (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    positiveQuadraticSum g a θ Φ R v s =
      quadraticDensitySum g (quadraticCompactCutoff q Rmax v H s) a θ Φ R v s := by
  classical
  unfold positiveQuadraticSum quadraticDensitySum
  congr 1
  calc
    _ = ∑ w ∈ quadraticCompactCutoff q Rmax v H s,
        if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0 := by
      apply tsum_eq_sum
      intro w hw
      by_cases hw0 : 0 < w
      · simp only [ite_eq_left hw0]
        by_contra hn
        exact hw (quadraticCompactCutoff_mono q s R Rmax v H hRmax hv.le hH
          (quadraticDensityTerm_mem_cutoff g a θ Φ R v H s s w hR hv hs le_rfl hw0 hΦ hn))
      · simp only [ite_eq_right hw0]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact ite_eq_left (Finset.mem_Ioc.mp hw).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticPhaseContinuity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative continuity of the original quadratic phase parameter -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem realAdditivePhase_sub_norm_le (x y : ℝ) :
    ‖realAdditivePhase x - realAdditivePhase y‖ ≤ 2 * Real.pi * |x - y| := by
  have heq : (realAdditivePhase (x - y) - 1) * realAdditivePhase y =
      realAdditivePhase x - realAdditivePhase y := by
    rw [sub_mul, one_mul, ← realAdditivePhase_add, sub_add_cancel]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - y))
  rw [mul_comm Complex.I] at hh
  calc
    _ = ‖(realAdditivePhase (x - y) - 1) * realAdditivePhase y‖ := by rw [heq]
    _ = ‖realAdditivePhase (x - y) - 1‖ := by rw [norm_mul, norm_realAdditivePhase, mul_one]
    _ ≤ |2 * Real.pi * (x - y)| := hh
    _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

theorem quadraticDensityTerm_phase_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ θ' : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s w : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ' Φ R v s w‖ ≤
      B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * R * |θ - θ'|) := by
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let z : ℝ := (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q)
  by_cases hz : H < z
  · have hzero : Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q)) = 0 := hΦ z hz
    simp only [quadraticDensityTerm, hzero, mul_zero, sub_self, norm_zero]
    positivity
  have hzH : z ≤ H := le_of_not_gt hz
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have heq (t : ℝ) : realAdditivePhase (t * v * (w : ℝ) ^ 2 / q) ^ s =
      realAdditivePhase (t * (R * z)) := by
    rw [← realAdditivePhase_nat_mul]
    congr 1
    dsimp [z]
    field_simp
  have hphase : ‖realAdditivePhase (θ * (R * z)) - realAdditivePhase (θ' * (R * z))‖ ≤
      2 * Real.pi * H * R * |θ - θ'| := by
    apply (realAdditivePhase_sub_norm_le _ _).trans
    have hdiff : θ * (R * z) - θ' * (R * z) = (θ - θ') * (R * z) := by ring
    rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg hR.le hz0)]
    have hh := mul_le_mul_of_nonneg_left hzH
      (show 0 ≤ 2 * Real.pi * R * |θ - θ'| by positivity)
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hdiff : quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ' Φ R v s w =
      g (a * (w : ZMod q) ^ 2 * (s : ZMod q)) *
        (realAdditivePhase (θ * (R * z)) - realAdditivePhase (θ' * (R * z))) * Φ z := by
    simp only [quadraticDensityTerm, heq]
    ring
  rw [hdiff, norm_mul, norm_mul]
  have hh := mul_le_mul (mul_le_mul (hg (a * (w : ZMod q) ^ 2 * (s : ZMod q))) hphase (norm_nonneg _) hB)
    (Φ.norm_le_seminorm ℝ z) (norm_nonneg _) (by positivity)
  exact hh.trans_eq (by ring)

theorem positiveQuadraticSum_phase_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ θ' : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R v s‖ ≤
      B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * R * |θ - θ'|) * Real.sqrt H := by
  let Q := Real.sqrt (R * q / ((s : ℝ) * v))
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  let C := B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * R * |θ - θ'|)
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : (W : ℝ) ≤ Real.sqrt H * Q := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans_eq
    have he : H * R * q / ((s : ℝ) * v) = H * (R * q / ((s : ℝ) * v)) := by ring
    rw [he, Real.sqrt_mul hH]
  rw [positiveQuadraticSum_eq_cutoff g a θ Φ R v H s s hR hv hs le_rfl hΦ,
    positiveQuadraticSum_eq_cutoff g a θ' Φ R v H s s hR hv hs le_rfl hΦ]
  change ‖(Q : ℂ)⁻¹ * (∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w) -
    (Q : ℂ)⁻¹ * (∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ' Φ R v s w)‖ ≤ _
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hQ]
  have hsum : ‖∑ w ∈ Finset.Ioc 0 W,
      (quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ' Φ R v s w)‖ ≤
      (W : ℝ) * C := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W, C := Finset.sum_le_sum (fun w _ =>
        quadraticDensityTerm_phase_sub_bound g B hg a θ θ' Φ R v H s w hR hv hH hΦ)
      _ = _ := by simp
  calc
    _ ≤ Q⁻¹ * ((W : ℝ) * C) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hQ.le)
    _ ≤ Q⁻¹ * ((Real.sqrt H * Q) * C) := by gcongr
    _ = _ := by dsimp [C]; field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticScaleContinuity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale continuity on a common finite quadratic cutoff -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem inv_sub_abs_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have he : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  exact div_le_self (abs_nonneg _) (one_le_mul_of_one_le_of_one_le hx hy)

theorem sqrt_sub_abs_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hsx : 1 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by simpa using hx)
  have hsy : 1 ≤ Real.sqrt y := Real.le_sqrt_of_sq_le (by simpa using hy)
  have he : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith only [Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  have hn := congrArg abs he
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x + Real.sqrt y)] at hn
  calc
    _ ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) :=
      le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = _ := hn

theorem inv_sqrt_sub_abs_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |(Real.sqrt x)⁻¹ - (Real.sqrt y)⁻¹| ≤ |x - y| := by
  have hsx : 1 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by simpa using hx)
  have hsy : 1 ≤ Real.sqrt y := Real.le_sqrt_of_sq_le (by simpa using hy)
  exact (inv_sub_abs_le_of_one_le _ _ hsx hsy).trans (sqrt_sub_abs_le_of_one_le x y hx hy)

theorem quadratic_normalizer_factor (q s : ℕ) (R v : ℝ) (hR : 0 ≤ R) :
    (Real.sqrt (R * q / ((s : ℝ) * v)))⁻¹ =
      Real.sqrt ((s : ℝ) * v / q) * (Real.sqrt R)⁻¹ := by
  have he : R * q / ((s : ℝ) * v) = R * ((q : ℝ) / ((s : ℝ) * v)) := by ring
  rw [he, Real.sqrt_mul hR, mul_inv, ← Real.sqrt_inv ((q : ℝ) / ((s : ℝ) * v)),
    inv_div, mul_comm]

theorem quadraticDensityTerm_scale_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' v : ℝ) (s w W : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hv : 0 ≤ v) (hw : w ≤ W) :
    ‖quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ Φ R' v s w‖ ≤
      B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'| := by
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have ha : 0 ≤ (s : ℝ) * v / q := by positivity
  have hd : |(s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) -
      (s : ℝ) * v * (w : ℝ) ^ 2 / (R' * q)| ≤
      ((s : ℝ) * v / q) * W ^ 2 * |R - R'| := by
    have he : (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) -
        (s : ℝ) * v * (w : ℝ) ^ 2 / (R' * q) =
        (((s : ℝ) * v / q) * w ^ 2) * (R⁻¹ - R'⁻¹) := by ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((s : ℝ) * v / q) * w ^ 2)]
    have hw' : (w : ℝ) ^ 2 ≤ (W : ℝ) ^ 2 := by gcongr
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw' ha)
      (inv_sub_abs_le_of_one_le R R' hR hR') (abs_nonneg _) (by positivity)
  have he : quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ Φ R' v s w =
      (g (a * (w : ZMod q) ^ 2 * (s : ZMod q)) * realAdditivePhase (θ * v * (w : ℝ) ^ 2 / q) ^ s) *
        (Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q)) - Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R' * q))) := by
    simp only [quadraticDensityTerm]
    ring
  rw [he, norm_mul, norm_mul, norm_pow, norm_realAdditivePhase, one_pow, mul_one]
  have hs := (schwartz_norm_sub_le Φ _ _).trans (mul_le_mul_of_nonneg_left hd (by positivity))
  have hh := mul_le_mul (hg (a * (w : ZMod q) ^ 2 * (s : ZMod q))) hs (norm_nonneg _) hB
  exact hh.trans_eq (by ring)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FiniteQuadraticScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial continuity bound for the scale parameter -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticDensitySum_scale_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' v : ℝ) (s W : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hv : 0 ≤ v) :
    ‖quadraticDensitySum g (Finset.Ioc 0 W) a θ Φ R v s -
      quadraticDensitySum g (Finset.Ioc 0 W) a θ Φ R' v s‖ ≤
      Real.sqrt ((s : ℝ) * v / q) * W * B *
        (SchwartzMap.seminorm ℝ 0 0 Φ +
          SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2) * |R - R'| := by
  let D := Real.sqrt ((s : ℝ) * v / q)
  let c := fun x : ℝ => D * (Real.sqrt x)⁻¹
  let F := fun x : ℝ => ∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ x v s w
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hS0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ := by positivity
  have hS1 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Φ := by positivity
  have hn (x : ℝ) (hx : 1 ≤ x) :
      quadraticDensitySum g (Finset.Ioc 0 W) a θ Φ x v s = (c x : ℂ) * F x := by
    unfold quadraticDensitySum
    rw [← Complex.ofReal_inv, quadratic_normalizer_factor q s x v (by linarith)]
  have hF : ‖F R‖ ≤ (W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W, B * SchwartzMap.seminorm ℝ 0 0 Φ := by
        apply Finset.sum_le_sum
        intro w _
        simp only [quadraticDensityTerm, norm_mul, norm_pow, norm_realAdditivePhase,
          one_pow, mul_one]
        exact mul_le_mul (hg _) (Φ.norm_le_seminorm ℝ _) (norm_nonneg _) hB
      _ = _ := by simp
  have hFdiff : ‖F R - F R'‖ ≤ (W : ℝ) *
      (B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'|) := by
    dsimp [F]
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W,
          B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'| := by
        apply Finset.sum_le_sum
        intro w hw
        exact quadraticDensityTerm_scale_sub_bound g B hg a θ Φ R R' v s w W hR hR' hv
          (Finset.mem_Ioc.mp hw).2
      _ = _ := by simp
  have hc' : ‖(c R' : ℂ)‖ ≤ D := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by dsimp [c]; positivity)]
    exact mul_le_of_le_one_right hD (inv_le_one_of_one_le₀
      (Real.le_sqrt_of_sq_le (by simpa using hR')))
  have hcdiff : ‖(c R : ℂ) - (c R' : ℂ)‖ ≤ D * |R - R'| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have he : c R - c R' = D * ((Real.sqrt R)⁻¹ - (Real.sqrt R')⁻¹) := by dsimp [c]; ring
    rw [he, abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_sub_abs_le_of_one_le R R' hR hR') hD
  rw [hn R hR, hn R' hR']
  have he : (c R : ℂ) * F R - (c R' : ℂ) * F R' =
      ((c R : ℂ) - (c R' : ℂ)) * F R + (c R' : ℂ) * (F R - F R') := by ring
  rw [he]
  calc
    _ ≤ ‖((c R : ℂ) - (c R' : ℂ)) * F R‖ + ‖(c R' : ℂ) * (F R - F R')‖ := norm_add_le _ _
    _ = ‖(c R : ℂ) - (c R' : ℂ)‖ * ‖F R‖ + ‖(c R' : ℂ)‖ * ‖F R - F R'‖ := by rw [norm_mul, norm_mul]
    _ ≤ (D * |R - R'|) * ((W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) +
        D * ((W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2 * |R - R'|)) := by
      gcongr
    _ = _ := by dsimp [D]; ring

/-- Both original infinite series are replaced by the same support at
`Rmax`; the finite scale estimate then applies without a cutoff error. -/
theorem positiveQuadraticSum_scale_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' Rmax v H : ℝ) (s : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hRR : R ≤ Rmax) (hR'R : R' ≤ Rmax)
    (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
    ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ Φ R' v s‖ ≤
      Real.sqrt ((s : ℝ) * v / q) * W * B *
        (SchwartzMap.seminorm ℝ 0 0 Φ +
          SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2) * |R - R'| := by
  dsimp only
  rw [positiveQuadraticSum_eq_upper_cutoff g a θ Φ R Rmax v H s (by linarith) hRR hv hH hs hΦ,
    positiveQuadraticSum_eq_upper_cutoff g a θ Φ R' Rmax v H s (by linarith) hR'R hv hH hs hΦ]
  exact quadraticDensitySum_scale_sub_bound g B hg a θ Φ R R' v s _ hR hR' hv.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticParameterGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite phase and scale grids for the quadratic coefficient arrays -/

namespace Ostmann

theorem quadraticParameterGrid_covers (Rmax δ θ R : ℝ) (hδ : 0 < δ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRmax : R ≤ Rmax) :
    ∃ j ∈ quadraticParameterGrid Rmax δ,
      0 ≤ quadraticGridPhase δ j ∧ quadraticGridPhase δ j ≤ θ ∧
      1 ≤ quadraticGridScale δ j ∧ quadraticGridScale δ j ≤ R ∧
      |θ - quadraticGridPhase δ j| < δ ∧ |R - quadraticGridScale δ j| < δ := by
  let j : ℕ × ℕ := (⌊θ / δ⌋₊, ⌊(R - 1) / δ⌋₊)
  have hR0 : 0 ≤ R - 1 := by linarith
  have hjθ : (j.1 : ℝ) ≤ θ / δ := Nat.floor_le (div_nonneg hθ0 hδ.le)
  have hjR : (j.2 : ℝ) ≤ (R - 1) / δ := Nat.floor_le (div_nonneg hR0 hδ.le)
  have hjθ' : θ / δ < (j.1 : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjR' : (R - 1) / δ < (j.2 : ℝ) + 1 := Nat.lt_floor_add_one _
  have hθlo := (le_div_iff₀ hδ).mp hjθ
  have hRlo := (le_div_iff₀ hδ).mp hjR
  have hθhi := (div_lt_iff₀ hδ).mp hjθ'
  have hRhi := (div_lt_iff₀ hδ).mp hjR'
  refine ⟨j, ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hh : j.1 ≤ ⌊1 / δ⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_right hθ1 hδ.le)
      omega
    · apply Finset.mem_range.mpr
      have hh : j.2 ≤ ⌊Rmax / δ⌋₊ := Nat.floor_mono
        (div_le_div_of_nonneg_right (by linarith : R - 1 ≤ Rmax) hδ.le)
      omega
  · dsimp [quadraticGridPhase, quadraticGridScale]
    refine ⟨by positivity, hθlo, ?_, by linarith, ?_, ?_⟩
    · have hh : 0 ≤ (j.2 : ℝ) * δ := by positivity
      linarith
    · rw [abs_of_nonneg (by linarith)]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]
      nlinarith

theorem quadraticParameterGrid_card_le (Rmax δ : ℝ) (hRmax : 0 ≤ Rmax) (hδ : 0 < δ) :
    ((quadraticParameterGrid Rmax δ).card : ℝ) ≤ (1 / δ + 1) * (Rmax / δ + 1) := by
  have ha : (⌊1 / δ⌋₊ : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hb : (⌊Rmax / δ⌋₊ : ℝ) ≤ Rmax / δ := Nat.floor_le (div_nonneg hRmax hδ.le)
  simp only [quadraticParameterGrid, Finset.card_product, Finset.card_range, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  gcongr

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGridApproximation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Approximation of the original quadratic series by the fixed grid -/

namespace Ostmann

open scoped SchwartzMap

theorem positiveQuadraticSum_parameter_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ θ' : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R R' Rmax v H δ : ℝ) (s : ℕ)
    (hR : 1 ≤ R) (hR' : 1 ≤ R') (hRR : R ≤ Rmax) (hR'R : R' ≤ Rmax)
    (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hθδ : |θ - θ'| ≤ δ) (hRδ : |R - R'| ≤ δ)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R' v s‖ ≤
      quadraticGridError q s B Rmax v H Φ * δ := by
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hR0 : 0 < R := by linarith
  have hRmax0 : 0 ≤ Rmax := by linarith
  let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
  let Cθ := B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax) * Real.sqrt H
  let CR := Real.sqrt ((s : ℝ) * v / q) * W * B *
    (SchwartzMap.seminorm ℝ 0 0 Φ +
      SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2)
  have hCθ : 0 ≤ Cθ := by dsimp [Cθ]; positivity
  have hCR : 0 ≤ CR := by dsimp [CR]; positivity
  have hphase : ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R v s‖ ≤
      Cθ * δ := by
    apply (positiveQuadraticSum_phase_sub_bound g B hg a θ θ' Φ R v H s hR0 hv hH hs hΦ).trans
    dsimp [Cθ]
    calc
      _ ≤ B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax * δ) * Real.sqrt H := by gcongr
      _ = _ := by ring
  have hscale : ‖positiveQuadraticSum g a θ' Φ R v s - positiveQuadraticSum g a θ' Φ R' v s‖ ≤
      CR * δ := by
    apply (positiveQuadraticSum_scale_sub_bound g B hg a θ' Φ R R' Rmax v H s
      hR hR' hRR hR'R hv hH hs hΦ).trans
    exact mul_le_mul_of_nonneg_left hRδ hCR
  have he : positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R' v s =
      (positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R v s) +
      (positiveQuadraticSum g a θ' Φ R v s - positiveQuadraticSum g a θ' Φ R' v s) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add hphase hscale).trans_eq
  change Cθ * δ + CR * δ = (Cθ + CR) * δ
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGridErrorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial grid-error bound on the manuscript's parameter box -/

namespace Ostmann

open scoped SchwartzMap

theorem quadraticGridError_le_power (X : ℝ) (q s : ℕ) (B Rmax v H : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hX : 2 ≤ X) (hpi : 2 * Real.pi ≤ X)
    (hq1 : 1 ≤ q) (hq : (q : ℝ) ≤ X) (hs1 : 1 ≤ s) (hs : (s : ℝ) ≤ X ^ 28)
    (hv1 : 1 ≤ v) (hv : v ≤ X) (hB0 : 0 ≤ B) (hB : B ≤ X)
    (hR0 : 0 ≤ Rmax) (hR : Rmax ≤ X ^ 14) (hH0 : 0 ≤ H) (hH : H ≤ X)
    (hΦ0 : SchwartzMap.seminorm ℝ 0 0 Φ ≤ X)
    (hΦ1 : SchwartzMap.seminorm ℝ 0 1 Φ ≤ X) :
    quadraticGridError q s B Rmax v H Φ ≤ X ^ 72 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hv0 : 0 ≤ v := by linarith
  have hsv : 1 ≤ (s : ℝ) * v := one_le_mul_of_one_le_of_one_le hs1' hv1
  have ha : (s : ℝ) * v / q ≤ X ^ 29 := by
    calc
      _ ≤ (s : ℝ) * v := div_le_self (by positivity) hq1'
      _ ≤ X ^ 28 * X := mul_le_mul hs hv hv0 (by positivity)
      _ = X ^ 29 := by ring
  have harg : H * Rmax * q / ((s : ℝ) * v) ≤ (X ^ 8) ^ 2 := by
    calc
      _ ≤ H * Rmax * q := div_le_self (by positivity) hsv
      _ ≤ X * X ^ 14 * X := by gcongr
      _ = _ := by ring
  let W := ⌊Real.sqrt (H * Rmax * q / ((s : ℝ) * v))⌋₊
  have hW : (W : ℝ) ≤ X ^ 8 := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans
    apply (Real.sqrt_le_sqrt harg).trans_eq
    exact Real.sqrt_sq (pow_nonneg hX0 _)
  have hD : Real.sqrt ((s : ℝ) * v / q) ≤ X ^ 15 := by
    have hh : X ^ 29 ≤ (X ^ 15) ^ 2 := by
      calc
        _ ≤ X ^ 30 := pow_le_pow_right₀ hX1 (by omega)
        _ = _ := by ring
    exact (Real.sqrt_le_sqrt (ha.trans hh)).trans_eq (Real.sqrt_sq (pow_nonneg hX0 _))
  have hsqrtH : Real.sqrt H ≤ X := by
    have hh : X ≤ X ^ 2 := by nlinarith
    exact (Real.sqrt_le_sqrt (hH.trans hh)).trans_eq (Real.sqrt_sq hX0)
  have htheta : B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * Rmax) * Real.sqrt H ≤ X ^ 19 := by
    calc
      _ ≤ X * X * (X * X * X ^ 14) * X := by gcongr
      _ = _ := by ring
  have hscale : Real.sqrt ((s : ℝ) * v / q) * W * B *
      (SchwartzMap.seminorm ℝ 0 0 Φ +
        SchwartzMap.seminorm ℝ 0 1 Φ * ((s : ℝ) * v / q) * W ^ 2) ≤ X ^ 25 + X ^ 70 := by
    calc
      _ ≤ X ^ 15 * X ^ 8 * X * (X + X * X ^ 29 * (X ^ 8) ^ 2) := by gcongr
      _ = _ := by ring
  unfold quadraticGridError
  change _ + (_ * (W : ℝ) * _ * _) ≤ _
  calc
    _ ≤ X ^ 19 + (X ^ 25 + X ^ 70) := add_le_add htheta hscale
    _ ≤ 3 * X ^ 70 := by
      have ha := pow_le_pow_right₀ hX1 (show 19 ≤ 70 by omega)
      have hb := pow_le_pow_right₀ hX1 (show 25 ≤ 70 by omega)
      linarith
    _ ≤ X ^ 2 * X ^ 70 := by gcongr; nlinarith
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticGridRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed polynomial-size grid with negligible approximation error -/

namespace Ostmann

open Filter
open scoped SchwartzMap

theorem quadraticParameterGrid_exponential_card (T : ℝ) (hT : 1 ≤ T) :
    ((quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T))).card : ℝ) ≤
      Real.exp (416 * T) := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : (1 : ℝ) ≤ Real.exp (200 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have h2 : (1 : ℝ) ≤ Real.exp (214 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have htwo : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfour : (4 : ℝ) ≤ Real.exp (2 * T) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 2
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  apply (quadraticParameterGrid_card_le _ _ (Real.exp_nonneg _) (Real.exp_pos _)).trans
  have hinv : 1 / Real.exp (-200 * T) = Real.exp (200 * T) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hratio : Real.exp (14 * T) / Real.exp (-200 * T) = Real.exp (214 * T) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hinv, hratio]
  calc
    _ ≤ (2 * Real.exp (200 * T)) * (2 * Real.exp (214 * T)) := by gcongr <;> linarith
    _ = 4 * Real.exp (414 * T) := by
      rw [mul_mul_mul_comm, ← Real.exp_add,
        show 200 * T + 214 * T = 414 * T by ring]
      norm_num
    _ ≤ Real.exp (2 * T) * Real.exp (414 * T) := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_UniformQuadraticGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One grid point simultaneously approximates every coefficient -/

namespace Ostmann

open Filter
open scoped SchwartzMap

/-- The quantifier order matters: the chosen grid point depends only on
the original phase and scale, and works for all moduli and kernels. -/
theorem eventual_uniform_quadratic_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ θ R : ℝ,
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ j ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)),
        0 ≤ quadraticGridPhase (Real.exp (-200 * T)) j ∧
        quadraticGridPhase (Real.exp (-200 * T)) j ≤ 1 ∧
        1 ≤ quadraticGridScale (Real.exp (-200 * T)) j ∧
        quadraticGridScale (Real.exp (-200 * T)) j ≤ Real.exp (14 * T) ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) j| ≤ Real.exp (-200 * T) ∧
        ∀ (q s : ℕ) [NeZero q] (g : ZMod q → ℂ) (B : ℝ) (a : ZMod q) (v h₀ : ℝ),
          (∀ x, ‖g x‖ ≤ B) → 1 ≤ q → (q : ℝ) ≤ Real.exp T →
          1 ≤ s → (s : ℝ) ≤ Real.exp (28 * T) →
          1 ≤ v → v ≤ Real.exp T → 0 ≤ B → B ≤ Real.exp T →
          ‖positiveQuadraticSum g a (h₀ + θ) Φ R v s -
            positiveQuadraticSum g a (h₀ + quadraticGridPhase (Real.exp (-200 * T)) j) Φ
              (quadraticGridScale (Real.exp (-200 * T)) j) v s‖ ≤ Real.exp (-128 * T) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (2 : ℝ),
    Real.tendsto_exp_atTop.eventually_ge_atTop (2 * Real.pi),
    Real.tendsto_exp_atTop.eventually_ge_atTop H,
    Real.tendsto_exp_atTop.eventually_ge_atTop (SchwartzMap.seminorm ℝ 0 0 Φ),
    Real.tendsto_exp_atTop.eventually_ge_atTop (SchwartzMap.seminorm ℝ 0 1 Φ)] with T hX hpi hHX hΦ0 hΦ1
  intro θ R hθ0 hθ1 hR hRR
  obtain ⟨j, hj, hjθ0, hjθ, hjR1, hjR, hjθδ, hjRδ⟩ :=
    quadraticParameterGrid_covers (Real.exp (14 * T)) (Real.exp (-200 * T)) θ R
      (Real.exp_pos _) hθ0 hθ1 hR hRR
  refine ⟨j, hj, hjθ0, hjθ.trans hθ1, hjR1, hjR.trans hRR, hjRδ.le, ?_⟩
  intro q s _ g B a v h₀ hg hq1 hq hs1 hs hv1 hv hB0 hB
  have hs' : (s : ℝ) ≤ (Real.exp T) ^ 28 := by simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hs
  have hR' : Real.exp (14 * T) ≤ (Real.exp T) ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  have herror := quadraticGridError_le_power (Real.exp T) q s B (Real.exp (14 * T)) v H Φ
    hX hpi hq1 hq hs1 hs' hv1 hv hB0 hB (Real.exp_nonneg _) hR' hH hHX hΦ0 hΦ1
  have hpoint := positiveQuadraticSum_parameter_sub_bound g B hg a (h₀ + θ)
    (h₀ + quadraticGridPhase (Real.exp (-200 * T)) j) Φ R
    (quadraticGridScale (Real.exp (-200 * T)) j) (Real.exp (14 * T)) v H
    (Real.exp (-200 * T)) s hR hjR1 hRR (hjR.trans hRR) (by linarith) hH (by omega)
    (by simpa only [add_sub_add_left_eq_sub] using hjθδ.le) hjRδ.le hΦ
  apply hpoint.trans
  calc
    _ ≤ (Real.exp T) ^ 72 * Real.exp (-200 * T) :=
      mul_le_mul_of_nonneg_right herror (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; norm_num; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OuterDivisorGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same fixed grid covers all sampled outer divisors -/

namespace Ostmann

open Filter
open scoped SchwartzMap

theorem eventual_uniform_outer_divisor_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ θ R : ℝ,
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ j ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)),
        0 ≤ quadraticGridPhase (Real.exp (-200 * T)) j ∧
        quadraticGridPhase (Real.exp (-200 * T)) j ≤ 1 ∧
        1 ≤ quadraticGridScale (Real.exp (-200 * T)) j ∧
        quadraticGridScale (Real.exp (-200 * T)) j ≤ Real.exp (14 * T) ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) j| ≤ Real.exp (-200 * T) ∧
        ∀ (q s P : ℕ) [NeZero q] (g : ZMod q → ℂ) (B : ℝ) (a : ZMod q) (v h₀ : ℝ),
          (∀ x, ‖g x‖ ≤ B) → 1 ≤ q → (q : ℝ) ≤ Real.exp T →
          1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
          0 < P → (P : ℝ) ≤ Real.exp (7 * T) →
          1 ≤ v → v ≤ Real.exp T → 0 ≤ B → B ≤ Real.exp T →
          ‖positiveQuadraticMultiples g a (h₀ + θ) Φ R v s P -
            positiveQuadraticMultiples g a (h₀ + quadraticGridPhase (Real.exp (-200 * T)) j) Φ
              (quadraticGridScale (Real.exp (-200 * T)) j) v s P‖ ≤ Real.exp (-128 * T) := by
  filter_upwards [eventual_uniform_quadratic_grid H Φ hH hΦ] with T hgrid
  intro θ R hθ0 hθ1 hR hRR
  obtain ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, hpoint⟩ := hgrid θ R hθ0 hθ1 hR hRR
  refine ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, ?_⟩
  intro q s P _ g B a v h₀ hg hq1 hq hs1 hs hP hPU hv1 hv hB0 hB
  have hsp1 : 1 ≤ s * P ^ 2 := Nat.mul_pos hs1 (pow_pos hP _)
  have hsp : ((s * P ^ 2 : ℕ) : ℝ) ≤ Real.exp (28 * T) := by
    push_cast
    calc
      _ ≤ Real.exp (14 * T) * (Real.exp (7 * T)) ^ 2 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; norm_num; ring
  have hp := hpoint q (s * P ^ 2) g B a v h₀ hg hq1 hq hsp1 hsp hv1 hv hB0 hB
  rw [positiveQuadraticMultiples_eq g a (h₀ + θ) Φ R v s P hP (by linarith) (by linarith),
    positiveQuadraticMultiples_eq g a _ Φ _ v s P hP (by linarith) (by linarith),
    ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg P))).trans
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (inv_le_one_of_one_le₀ (by exact_mod_cast hP))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FullCoefficientGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous discretization of the full arithmetic coefficient array -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_arithmetic_coefficient_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ θ R : ℝ,
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ j ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)),
        0 ≤ quadraticGridPhase (Real.exp (-200 * T)) j ∧
        quadraticGridPhase (Real.exp (-200 * T)) j ≤ 1 ∧
        1 ≤ quadraticGridScale (Real.exp (-200 * T)) j ∧
        quadraticGridScale (Real.exp (-200 * T)) j ≤ Real.exp (14 * T) ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) j| ≤ Real.exp (-200 * T) ∧
        ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
          (M h₀ P s : ℕ),
          (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
          (Q.toList.prod : ℝ) ≤ Real.exp T →
          0 < P → (P : ℝ) ≤ Real.exp (7 * T) →
          1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
          ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s -
            arithmeticQuadraticCoefficient Q hQ D Φ
              (quadraticGridScale (Real.exp (-200 * T)) j) P M h₀
              (quadraticGridPhase (Real.exp (-200 * T)) j) s‖ ≤ Real.exp (-127 * T) ∧
          ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
            ‖primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
                (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s -
              primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
                (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
                Φ (quadraticGridScale (Real.exp (-200 * T)) j) V.toList.prod P U s‖ ≤
              Real.exp (-128 * T) := by
  filter_upwards [eventual_uniform_outer_divisor_grid H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hg hT
  intro θ R hθ0 hθ1 hR hRR
  obtain ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, hpoint⟩ := hg θ R hθ0 hθ1 hR hRR
  refine ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, ?_⟩
  intro Q hQ D M h₀ P s hcard hlarge hL hP hPU hs hsU
  have hterm : ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
      ‖primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s -
        primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
          Φ (quadraticGridScale (Real.exp (-200 * T)) j) V.toList.prod P U s‖ ≤
        Real.exp (-128 * T) := by
    intro V hV U hU
    have hUQ := Finset.mem_powerset.mp hU
    have hVQ := Finset.mem_powerset.mp hV
    have hpU : ∀ p ∈ U, p.Prime := fun p hp => hQ p (hUQ hp)
    have hqpos : 0 < U.toList.prod := prime_list_prod_pos _ (primeSet_list_prime U hpU)
    have hvpos : 0 < V.toList.prod := prime_list_prod_pos _
      (primeSet_list_prime V (fun p hp => hQ p (hVQ hp)))
    let : NeZero U.toList.prod := ⟨hqpos.ne'⟩
    let g := densityFourier (densityCRTList U.toList (primeSet_list_prime U hpU)
      (primeSet_list_coprime U hpU) D).value
    have hqU : (U.toList.prod : ℝ) ≤ Real.exp T := by
      apply le_trans _ hL
      exact_mod_cast primeSet_prod_le_of_subset Q U hQ hUQ
    have hvU : (V.toList.prod : ℝ) ≤ Real.exp T := by
      apply le_trans _ hL
      exact_mod_cast primeSet_prod_le_of_subset Q V hQ hVQ
    have hgq : ∀ x, ‖g x‖ ≤ (U.toList.prod : ℝ) := by
      intro x
      have henergy := densityCRTList_energy U.toList (primeSet_list_prime U hpU)
        (primeSet_list_coprime U hpU) D
      have hh : ‖g x‖ ^ 2 ≤ (U.toList.prod : ℝ) :=
        (Finset.single_le_sum (fun y _ => sq_nonneg ‖g y‖) (Finset.mem_univ x)).trans henergy
      apply (Real.le_sqrt_of_sq_le hh).trans
      exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hqpos))
    have hh := hpoint U.toList.prod s P g U.toList.prod (divisorQuadraticScalar (quadraticInverseResidue M) V U)
      V.toList.prod h₀ hgq hqpos hqU hs hsU hP hPU
      (by exact_mod_cast hvpos) hvU (Nat.cast_nonneg _) hqU
    rw [positiveQuadraticMultiples_eq g _ _ Φ R V.toList.prod s P hP (by linarith)
        (by positivity),
      positiveQuadraticMultiples_eq g _ _ Φ _ V.toList.prod s P hP (by linarith)
        (by positivity)] at hh
    simpa only [primeDivisorMultiples, primeDivisorPositive, dite_eq_left hUQ] using hh
  refine ⟨?_, hterm⟩
  apply (fullQuadraticCoefficient_difference_bound Q hQ D (quadraticInverseResidue M)
    (fun _ => (h₀ : ℝ) + θ)
    (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
    Φ R (quadraticGridScale (Real.exp (-200 * T)) j) P
    (quadraticSymbolCoefficient M) (quadraticDivisorSymbol M) s
    (Real.exp (-128 * T)) (Real.exp_nonneg _)
    (fun U _ => quadraticSymbolCoefficient_norm_le M U)
    (fun V _ => quadraticDivisorSymbol_norm_le M V) hterm).trans
      (full_coefficient_grid_error_budget Q T hT hcard hlarge)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FixedQuadraticFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite family containing all discretized arithmetic arrays -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem mem_quadraticFamilyParameters (T : ℝ) (L : ℕ) (i : QuadraticFamilyIndex) :
    i ∈ quadraticFamilyParameters T L ↔
      i.1 < 4 * L ∧ i.2.1 < L ∧
      (1 ≤ i.2.2.1 ∧ i.2.2.1 ≤ ⌊Real.exp (7 * T)⌋₊) ∧
      i.2.2.2 ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)) := by
  simp only [quadraticFamilyParameters, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_range, Finset.mem_Icc]

theorem quadraticFamilyParameters_card (T : ℝ) (L : ℕ) :
    (quadraticFamilyParameters T L).card =
      (4 * L) * (L * (⌊Real.exp (7 * T)⌋₊ *
        (quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T))).card)) := by
  simp only [quadraticFamilyParameters, Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
    Nat.card_Icc, Nat.add_sub_cancel]

theorem eventual_quadraticFamilyParameters_card :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℕ, (L : ℝ) ≤ Real.exp (T / 25) →
      ((quadraticFamilyParameters T L).card : ℝ) ≤ Real.exp (425 * T) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT
  have hg := quadraticParameterGrid_exponential_card T (by linarith)
  intro L hL
  have hfour : (4 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  rw [quadraticFamilyParameters_card]
  push_cast
  calc
    _ ≤ (Real.exp T * Real.exp (T / 25)) * (Real.exp (T / 25) *
        (Real.exp (7 * T) * Real.exp (416 * T))) := by
      gcongr
      · exact Nat.floor_le (Real.exp_nonneg _)
    _ = Real.exp (T + T / 25 + T / 25 + 7 * T + 416 * T) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The index family is fixed before M and its translating residue are chosen.
The grid index works simultaneously for every kernel s in the full support. -/
theorem eventual_fixed_quadratic_family_covers (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ P : ℕ) (θ R : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      0 < P → (P : ℝ) ≤ Real.exp (7 * T) →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ i ∈ quadraticFamilyParameters T Q.toList.prod,
        i.2.2.1 = P ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) i.2.2.2| ≤ Real.exp (-200 * T) ∧
        ∀ s : ℕ, 1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
          ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s -
            fixedQuadraticCoefficient T Q hQ D Φ i s‖ ≤ Real.exp (-127 * T) := by
  filter_upwards [eventual_arithmetic_coefficient_grid H Φ hH hΦ] with T hg
  intro Q hQ D M h₀ P θ R hcard hlarge hL hM hh₀ hP hPU hθ0 hθ1 hR hRU
  obtain ⟨j, hj, _, _, _, _, hjδ, he⟩ := hg θ R hθ0 hθ1 hR hRU
  let r := M % (4 * Q.toList.prod)
  let i : QuadraticFamilyIndex := (r, h₀, P, j)
  refine ⟨i, ?_, rfl, hjδ, ?_⟩
  · have hLpos : 0 < Q.toList.prod := prime_list_prod_pos _ (primeSet_list_prime Q hQ)
    have hr : r < 4 * Q.toList.prod := Nat.mod_lt _ (Nat.mul_pos (by decide) hLpos)
    have hpU : P ≤ ⌊Real.exp (7 * T)⌋₊ := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr hPU
    simpa only [i, quadraticFamilyParameters, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc] using And.intro hr (And.intro hh₀ (And.intro (And.intro (show 1 ≤ P from hP) hpU) hj))
  · intro s hs hsU
    change ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s -
      arithmeticQuadraticCoefficient Q hQ D Φ
        (quadraticGridScale (Real.exp (-200 * T)) j) P r h₀
        (quadraticGridPhase (Real.exp (-200 * T)) j) s‖ ≤ _
    rw [← arithmeticQuadraticCoefficient_mod Q hQ D Φ _ P M h₀ _ s hM]
    exact (he Q hQ D M h₀ P s hcard hlarge hL hP hPU hs hsU).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FullCoefficientMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial absolute mass for the full coefficient family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem fullQuadraticCoefficient_norm_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R H : ℝ) (P : ℕ) (c ξ : Finset ℕ → ℂ) (s : ℕ)
    (hR : 0 < R) (hH : 0 ≤ H) (hP : 0 < P) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hξ : ∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) :
    ‖fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s‖ ≤
      ((Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ Q.card / P) *
          ∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹ := by
  apply divisorWeightedCoefficient_norm_le Q ξ _ s _ (by positivity) hξ
  intro V hV
  have hv : 0 < V.toList.prod := prime_list_prod_pos _
    (primeSet_list_prime V (fun p hp => hQ p (Finset.mem_powerset.mp hV hp)))
  exact primeDivisorMultiples_combination_bound Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod H s P
    hP hs hR (by exact_mod_cast hv) hH hΦ c hc

theorem eventual_full_coefficient_point_bound (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (R : ℝ) (P M h₀ s : ℕ) (θ : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      0 < R → 0 < P → 0 < s →
      ‖arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s‖ ≤ Real.exp (2 * T) := by
  let C := SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H
  filter_upwards [eventually_ge_atTop C, eventually_ge_atTop (0 : ℝ)] with T hTC hT
  intro Q hQ D R P M h₀ s θ hcard hlarge hL hR hP hs
  have hC : C ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hLs : Real.sqrt Q.toList.prod ≤ Real.exp (T / 50) := by
    apply (Real.sqrt_le_sqrt hL).trans_eq
    rw [← Real.exp_half]
    congr 1
    ring
  have he : (1 + 1 / 16 : ℝ) ^ Q.card ≤ Real.exp (T / 16) :=
    (sixteenth_divisor_weight_bound Q.card).trans (Real.exp_le_exp.mpr (by linarith))
  have hm : (∑ V ∈ Q.powerset, (Real.sqrt (V.toList.prod : ℝ))⁻¹) ≤ Real.exp (T / 1000) :=
    (reciprocal_sqrt_divisor_mass_le Q hlarge).trans (Real.exp_le_exp.mpr (by linarith))
  have hb := fullQuadraticCoefficient_norm_le Q hQ D (quadraticInverseResidue M)
    (fun _ => (h₀ : ℝ) + θ) Φ R H P (quadraticSymbolCoefficient M)
    (quadraticDivisorSymbol M) s hR hH hP hs hΦ
    (fun U _ => quadraticSymbolCoefficient_norm_le M U)
    (fun V _ => quadraticDivisorSymbol_norm_le M V)
  apply hb.trans
  change ((Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
    (1 + 1 / 16 : ℝ) ^ Q.card / P) * _ ≤ _
  rw [mul_assoc (Real.sqrt (Q.toList.prod : ℝ))]
  calc
    _ ≤ (Real.exp (T / 50) * Real.exp T * Real.exp (T / 16) / 1) * Real.exp (T / 1000) := by
      gcongr
      exact_mod_cast hP
    _ = Real.exp (T / 50 + T + T / 16 + T / 1000) := by
      rw [div_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventual_arithmetic_coefficient_mass (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (R : ℝ) (P M h₀ : ℕ) (θ : ℝ) (S : Finset ℕ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      0 < R → 0 < P → (∀ s ∈ S, 0 < s) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      (∑ s : S, ‖rootNormalizedCoefficient
        (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ) s‖) ≤ Real.exp (16 * T) := by
  filter_upwards [eventual_full_coefficient_point_bound H Φ hH hΦ] with T hp
  intro Q hQ D R P M h₀ θ S hcard hlarge hL hR hP hS hScard
  apply (rootNormalizedCoefficient_mass_le S _ (Real.exp (2 * T)) hS
    (fun s hs => hp Q hQ D R P M h₀ s θ hcard hlarge hL hR hP (hS s hs))).trans
  calc
    _ ≤ Real.exp (14 * T) * Real.exp (2 * T) :=
      mul_le_mul_of_nonneg_right hScard (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventual_fixed_quadratic_family_mass (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (S : Finset ℕ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, 0 < s) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      ∀ i ∈ quadraticFamilyParameters T Q.toList.prod,
      (∑ s : S, ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖) ≤
        Real.exp (16 * T) := by
  filter_upwards [eventual_arithmetic_coefficient_mass H Φ hH hΦ] with T hm
  intro Q hQ D S hcard hlarge hL hS hScard i hi
  have hmem := (mem_quadraticFamilyParameters T Q.toList.prod i).mp hi
  have hR : 0 < quadraticGridScale (Real.exp (-200 * T)) i.2.2.2 := by
    unfold quadraticGridScale
    positivity
  exact hm Q hQ D _ _ _ _ _ S hcard hlarge hL hR hmem.2.2.1.1 hS hScard

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SmallKernelFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed family with the scale needed for the small-kernel estimate -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem smallKernelParameters_subset (T : ℝ) (L : ℕ) :
    smallKernelParameters T L ⊆ quadraticFamilyParameters T L := Finset.filter_subset _ _

theorem eventual_small_kernel_family_covers (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) (θ R : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R →
      ∃ i ∈ smallKernelParameters T Q.toList.prod, ∀ s : ℕ,
        1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
        ‖arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ s -
          fixedQuadraticCoefficient T Q hQ D Φ i s‖ ≤ Real.exp (-127 * T) := by
  filter_upwards [eventual_fixed_quadratic_family_covers H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hc hT
  intro Q hQ D M h₀ θ R hcard hlarge hL hM hh₀ hθ0 hθ1 hR hRU hmargin
  obtain ⟨i, hi, hiP, hiR, he⟩ := hc Q hQ D M h₀ 1 θ R hcard hlarge hL hM hh₀
    (by decide) (by simpa using Real.one_le_exp_iff.mpr (show 0 ≤ 7 * T by positivity))
    hθ0 hθ1 hR hRU
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, hiP, ?_⟩, he⟩
  have hr := (le_abs_self (R - quadraticGridScale (Real.exp (-200 * T)) i.2.2.2)).trans hiR
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OffWitnessFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed subfamily in which all small-kernel witnesses fail -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem fixedQuadraticCoefficient_principal (T : ℝ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex) (s : ℕ) (hi : i.2.2.1 = 1) :
    fixedQuadraticCoefficient T Q hQ D Φ i s =
      divisorWeightedCoefficient Q (quadraticDivisorSymbol i.1)
        (fun V s => ∑ U ∈ Q.powerset,
          quadraticSymbolCoefficient i.1 U * fixedPrimeDivisorTerm T Q hQ D Φ i V U s) s := by
  simp only [fixedQuadraticCoefficient, arithmeticQuadraticCoefficient, hi,
    fullQuadraticCoefficient_one, fixedPrimeDivisorTerm]

theorem eventual_full_off_witness_norm (C₀ ε : ℝ) (hC₀ : 0 ≤ C₀) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (c ξ : Finset ℕ → ℂ) (G : Finset ℕ → Finset ℕ → ℕ → ℂ),
      (∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) →
      (∀ s ∈ S, ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
        ‖G V U s‖ ≤ Real.exp (-9 * Q.card / 10) * (Real.sqrt 2) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖divisorWeightedCoefficient Q ξ (fun V s => ∑ U ∈ Q.powerset, c U * G V U s) s‖ ^ 2) ≤
        Real.exp ((-799 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_off_witness_norm_card C₀ ε hC₀ hε] with T hn
  intro Q M S u hK hlarge hM hS hu huU c ξ G hc hξ hG
  refine (divisorWeightedCoefficient_energy_exp_le Q ξ _ S _
    (Real.exp ((-4 / 5 + ε) * Q.card)) hlarge (fun _ _ => by positivity)
    (Real.exp_nonneg _) hξ ?_).trans_eq ?_
  · intro V hV
    exact hn Q M S u hK hM hS hu huU c (G V) hc
      (fun s hs U hU => hG s hs V hV U hU)
  · rw [← Real.exp_add]
    congr 1
    ring

theorem eventual_off_witness_family_norm (C₀ ε : ℝ) (hC₀ : 0 ≤ C₀) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (Φ : 𝓢(ℝ, ℂ)) (i : QuadraticFamilyIndex),
      i ∈ offWitnessParameters T Q hQ D Φ S →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤
        Real.exp ((-799 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_full_off_witness_norm C₀ ε hC₀ hε] with T hn
  intro Q hQ M S u hK hlarge hM hS hu huU D Φ i hi
  have hi' := Finset.mem_filter.mp hi
  have hiP := (Finset.mem_filter.mp hi'.1).2.1
  simp_rw [fixedQuadraticCoefficient_principal T Q hQ D Φ i _ hiP]
  exact hn Q M S u hK hlarge hM hS hu huU (quadraticSymbolCoefficient i.1)
    (quadraticDivisorSymbol i.1) (fixedPrimeDivisorTerm T Q hQ D Φ i)
    (fun U _ => quadraticSymbolCoefficient_norm_le _ U)
    (fun V _ => quadraticDivisorSymbol_norm_le _ V) hi'.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_WitnessGridGap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The grid error is smaller than the small-kernel witness gap -/

namespace Ostmann

theorem witness_grid_gap (T : ℝ) (K : ℕ) (hT : 1 ≤ T) (hK : 1 ≤ K)
    (hKT : (K : ℝ) ≤ T) :
    Real.exp (-(K : ℝ)) + Real.exp (-128 * T) ≤ Real.exp (-9 * K / 10) := by
  have hten : (10 : ℝ) ≤ Real.exp (127 * T) := by
    linarith [Real.add_one_le_exp (127 * T)]
  have hinv : Real.exp (-127 * T) ≤ (1 / 10 : ℝ) := by
    rw [show -127 * T = -(127 * T) by ring, Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 10) hten
  have hsmall : Real.exp (-128 * T) ≤ (1 / 10 : ℝ) * Real.exp (-(K : ℝ)) := by
    calc
      _ ≤ Real.exp (-127 * T) * Real.exp (-(K : ℝ)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hinv (Real.exp_nonneg _)
  have hkR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have he : (1 + 1 / 10 : ℝ) ≤ Real.exp ((K : ℝ) / 10) := by
    linarith [Real.add_one_le_exp ((K : ℝ) / 10)]
  calc
    _ ≤ (1 + 1 / 10 : ℝ) * Real.exp (-(K : ℝ)) := by linarith
    _ ≤ Real.exp ((K : ℝ) / 10) * Real.exp (-(K : ℝ)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem small_witness_failure_survives_grid (T : ℝ) (K d : ℕ) (x y : ℂ)
    (hT : 1 ≤ T) (hK : 1 ≤ K) (hKT : (K : ℝ) ≤ T)
    (hx : ‖x‖ ≤ Real.exp (-(K : ℝ)) * (Real.sqrt 2) ^ d)
    (hxy : ‖x - y‖ ≤ Real.exp (-128 * T)) :
    ‖y‖ ≤ Real.exp (-9 * K / 10) * (Real.sqrt 2) ^ d := by
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hp : (1 : ℝ) ≤ (Real.sqrt 2) ^ d := one_le_pow₀ hroot
  have hh : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have he : y = x - (x - y) := by ring
    calc
      ‖y‖ = ‖x - (x - y)‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  calc
    _ ≤ Real.exp (-(K : ℝ)) * (Real.sqrt 2) ^ d + Real.exp (-128 * T) :=
      hh.trans (add_le_add hx hxy)
    _ ≤ (Real.exp (-(K : ℝ)) + Real.exp (-128 * T)) * (Real.sqrt 2) ^ d := by
      rw [add_mul]
      exact add_le_add_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hp) _
    _ ≤ _ := mul_le_mul_of_nonneg_right (witness_grid_gap T K hT hK hKT) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OffWitnessCover
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual failure of every small witness enters the fixed off-witness family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_off_witness_family_covers (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) (θ R : ℝ) (S : Finset ℕ),
      1 ≤ Q.card → (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      (∀ s ∈ S, 1 ≤ s ∧ (s : ℝ) ≤ Real.exp (14 * T)) →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R →
      (∀ s ∈ S, ∀ V ∈ Q.powerset, ∀ U ∈ Q.powerset,
        ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod U s‖ ≤
            Real.exp (-(Q.card : ℝ)) * (Real.sqrt 2) ^ U.card) →
      ∃ i ∈ offWitnessParameters T Q hQ D Φ S, ∀ s ∈ S,
        ‖arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ s -
          fixedQuadraticCoefficient T Q hQ D Φ i s‖ ≤ Real.exp (-127 * T) := by
  filter_upwards [eventual_arithmetic_coefficient_grid H Φ hH hΦ,
    eventually_ge_atTop (1 : ℝ)] with T hg hT
  intro Q hQ D M h₀ θ R S hK hcard hlarge hL hM hh₀ hS hθ0 hθ1 hR hRU hmargin hfail
  obtain ⟨j, hj, _, _, _, _, hjδ, he⟩ := hg θ R hθ0 hθ1 hR hRU
  let r := M % (4 * Q.toList.prod)
  let i : QuadraticFamilyIndex := (r, h₀, 1, j)
  have hLpos : 0 < Q.toList.prod := prime_list_prod_pos _ (primeSet_list_prime Q hQ)
  have hr : r < 4 * Q.toList.prod := Nat.mod_lt _ (Nat.mul_pos (by decide) hLpos)
  have hP : (1 : ℝ) ≤ Real.exp (7 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have hP' : ((1 : ℕ) : ℝ) ≤ Real.exp (7 * T) := by simpa only [Nat.cast_one] using hP
  have hPf : (1 : ℕ) ≤ ⌊Real.exp (7 * T)⌋₊ := (Nat.le_floor_iff (Real.exp_nonneg _)).mpr hP'
  have hi : i ∈ quadraticFamilyParameters T Q.toList.prod := by
    apply (mem_quadraticFamilyParameters T Q.toList.prod i).mpr
    exact ⟨hr, hh₀, ⟨le_rfl, hPf⟩, hj⟩
  have hiSmall : i ∈ smallKernelParameters T Q.toList.prod := by
    apply Finset.mem_filter.mpr
    refine ⟨hi, rfl, ?_⟩
    have hh := (le_abs_self (R - quadraticGridScale (Real.exp (-200 * T)) j)).trans hjδ
    change (Q.toList.prod : ℝ) ^ 6 ≤ quadraticGridScale (Real.exp (-200 * T)) j
    linarith
  have he' (s : ℕ) (hs : s ∈ S) := he Q hQ D M h₀ 1 s hcard hlarge hL (by decide) hP'
    (hS s hs).1 (hS s hs).2
  refine ⟨i, Finset.mem_filter.mpr ⟨hiSmall, ?_⟩, ?_⟩
  · intro s hs V hV U hU
    have hclose := (he' s hs).2 V hV U hU
    simp only [primeDivisorMultiples, one_pow, mul_one, Nat.cast_one, inv_one, one_mul] at hclose
    have hgrid := small_witness_failure_survives_grid T Q.card U.card _ _ hT hK hcard
      (hfail s hs V hV U hU) hclose
    change ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue r) V)
      (fun _ => (h₀ : ℝ) + quadraticGridPhase (Real.exp (-200 * T)) j)
      Φ (quadraticGridScale (Real.exp (-200 * T)) j) V.toList.prod U s‖ ≤ _
    have ha := quadraticInverseResidue_mod_multiple Q.toList.prod M U
      (primeSet_prod_dvd_of_subset Q U (Finset.mem_powerset.mp hU))
    rw [← primeDivisorPositive_congr_point Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
      (divisorQuadraticScalar (quadraticInverseResidue r) V) _ Φ _ V.toList.prod U s
      (divisorQuadraticScalar_congr_point (quadraticInverseResidue M) (quadraticInverseResidue r) V U ha)]
    exact hgrid
  · intro s hs
    change ‖arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ s -
      arithmeticQuadraticCoefficient Q hQ D Φ (quadraticGridScale (Real.exp (-200 * T)) j)
        1 r h₀ (quadraticGridPhase (Real.exp (-200 * T)) j) s‖ ≤ _
    rw [← arithmeticQuadraticCoefficient_mod Q hQ D Φ _ 1 M h₀ _ s hM]
    exact (he' s hs).1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticArrayApproximation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed array approximates the original Jacobi statistic -/

namespace Ostmann

open scoped BigOperators

theorem rootNormalizedCoefficient_sub (F G : ℕ → ℂ) (s : ℕ) :
    rootNormalizedCoefficient F s - rootNormalizedCoefficient G s =
      rootNormalizedCoefficient (fun s => F s - G s) s := by
  simp only [rootNormalizedCoefficient, mul_sub]

theorem quadraticArrayStatistic_sub_bound (S : Finset ℕ) (M : ℕ) (F G : ℕ → ℂ)
    (δ : ℝ) (hS : ∀ s ∈ S, 0 < s)
    (hFG : ∀ s ∈ S, ‖F s - G s‖ ≤ δ) :
    ‖quadraticArrayStatistic S M F - quadraticArrayStatistic S M G‖ ≤ S.card * δ := by
  unfold quadraticArrayStatistic
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _s : S, δ := by
      apply Finset.sum_le_sum
      intro s _
      rw [← sub_mul, norm_mul, rootNormalizedCoefficient_sub,
        Complex.norm_real, Real.norm_eq_abs]
      have hroot := (rootNormalizedCoefficient_norm_le (fun s => F s - G s)
        s.val (hS s.val s.property)).trans (hFG s.val s.property)
      exact (mul_le_of_le_one_right (norm_nonneg _) (realJacobi_abs_le s.val M)).trans hroot
    _ = _ := by simp

theorem quadraticArrayStatistic_grid_error (T : ℝ) (S : Finset ℕ) (M : ℕ)
    (F G : ℕ → ℂ) (hS : ∀ s ∈ S, 0 < s) (hcard : (S.card : ℝ) ≤ Real.exp (14 * T))
    (hFG : ∀ s ∈ S, ‖F s - G s‖ ≤ Real.exp (-127 * T)) :
    ‖quadraticArrayStatistic S M F - quadraticArrayStatistic S M G‖ ≤ Real.exp (-113 * T) := by
  apply (quadraticArrayStatistic_sub_bound S M F G _ hS hFG).trans
  calc
    _ ≤ Real.exp (14 * T) * Real.exp (-127 * T) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem quadraticArrayStatistic_mean_of_moment (P S : Finset ℕ) (k l : ℕ)
    {I : Type*} (F : I → ℕ → ℂ) (pick : ℕ → I) (B : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hl : 0 < l) (hB : 0 ≤ B)
    (hm : (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k,
      ‖quadraticArrayStatistic S m (F (pick m))‖ ^ (2 * l)) ≤ B ^ (2 * l)) :
    (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k,
      ‖quadraticArrayStatistic S m (F (pick m))‖) ≤ B :=
  prime_product_mean_le_of_moment P k (2 * l) _ B hP hB (by omega) hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalFourierCoefficients
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive Fourier expression is the actual arithmetic statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticArrayStatistic_finset (S : Finset ℕ) (M : ℕ) (F : ℕ → ℂ) :
    quadraticArrayStatistic S M F =
      ∑ s ∈ S, (Real.sqrt (s : ℝ) : ℂ)⁻¹ * F s * (realJacobi s M : ℂ) := by
  unfold quadraticArrayStatistic
  rw [show (∑ s : S, rootNormalizedCoefficient F s * (realJacobi s.val M : ℂ)) =
    ∑ s ∈ S, rootNormalizedCoefficient F s * (realJacobi s M : ℂ) from
      Finset.sum_coe_sort S (fun s : ℕ => rootNormalizedCoefficient F s * (realJacobi s M : ℂ))]
  simp only [rootNormalizedCoefficient]

/-- This is the exact finite form of equation (src8). Its coefficients are
the same ones whose uniform moments satisfy the stated bounds. -/
theorem originalPositiveFourier_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    originalPositiveFourier Q hQ D M N h₀ θ R Φ =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ) := by
  classical
  unfold originalPositiveFourier
  have he (U : Finset ℕ) (hU : U ∈ Q.powerset) :=
    primeDivisorFrequency_expansion Q hQ D U (Finset.mem_powerset.mp hU)
      M N h₀ θ R H Φ hR hH hN hcut hΦ
  -- First replace each original density transform by its proved expansion.
  have hexpand :
      (∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U * primeDivisorFrequency Q hQ D U M N h₀ θ R Φ) =
      ∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U *
        (∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
          ∑ s ∈ squarefreeKernelSupport Q.toList.prod N,
            ((realJacobi s M : ℂ) * (Real.sqrt (s : ℝ) : ℂ)⁻¹) *
            ∑ V ∈ Q.powerset,
              ((realJacobi V.toList.prod M : ℂ) * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) *
              primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
                (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s) := by
    apply Finset.sum_congr rfl
    intro U hU
    rw [he U hU]
  rw [hexpand]
  simp only [quadraticArrayStatistic_finset, arithmeticQuadraticCoefficient,
    fullQuadraticCoefficient, divisorWeightedCoefficient, quadraticDivisorSymbol,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro U hU
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalKernelDecomposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the principal small kernels in the original Fourier statistic -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

theorem quadraticArrayStatistic_split (S : Finset ℕ) (M A : ℕ) (F : ℕ → ℂ) :
    quadraticArrayStatistic S M F =
      quadraticArrayStatistic (S.filter (fun s => s ≤ A)) M F +
      quadraticArrayStatistic (S.filter (fun s => A < s)) M F := by
  simp only [quadraticArrayStatistic_finset]
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not S (fun s => s ≤ A)
      (fun s => (Real.sqrt (s : ℝ) : ℂ)⁻¹ * F s * (realJacobi s M : ℂ))).symm

theorem originalPositiveFourier_kernel_decomposition (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    originalPositiveFourier Q hQ D M N h₀ θ R Φ =
      principalSmallFourier Q hQ D M N h₀ θ R Φ +
      principalLargeFourier Q hQ D M N h₀ θ R Φ +
      outerFourierRemainder Q hQ D M N h₀ θ R Φ := by
  rw [originalPositiveFourier_expansion Q hQ D M N h₀ θ R H Φ hR hH hN hcut hΦ]
  have hone : 1 ∈ M.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, NeZero.ne M⟩
  rw [← Finset.add_sum_erase _ _ hone]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
  rw [quadraticArrayStatistic_split (squarefreeKernelSupport Q.toList.prod N) M
    (Q.toList.prod ^ 4)]
  rfl

theorem outerFourierRemainder_norm_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) :
    ‖outerFourierRemainder Q hQ D M N h₀ θ R Φ‖ ≤
      ∑ P ∈ M.divisors.erase 1,
        ‖quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ)‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P _
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  have hh := ArithmeticFunction.abs_moebius_le_one (n := P)
  rw [Complex.norm_intCast]
  exact_mod_cast hh

theorem originalPositiveFourier_norm_le_kernels (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖originalPositiveFourier Q hQ D M N h₀ θ R Φ‖ ≤
      ‖principalSmallFourier Q hQ D M N h₀ θ R Φ‖ +
      ‖principalLargeFourier Q hQ D M N h₀ θ R Φ‖ +
      ∑ P ∈ M.divisors.erase 1,
        ‖quadraticArrayStatistic (squarefreeKernelSupport Q.toList.prod N) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ)‖ := by
  rw [originalPositiveFourier_kernel_decomposition Q hQ D M N h₀ θ R H Φ hR hH hN hcut hΦ]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_add_le _ _) (outerFourierRemainder_norm_le Q hQ D M N h₀ θ R Φ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteWitnessProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite second-moment step in the positive witness probability -/

namespace Ostmann

open scoped BigOperators

theorem finite_event_second_moment {ι : Type*} (S E : Finset ι) (hES : E ⊆ S)
    (f : ι → ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (hfirst : A ≤ (S.card : ℝ)⁻¹ * (∑ i ∈ E, f i))
    (hsecond : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤ B ^ 2) :
    A ^ 2 ≤ ((S.card : ℝ)⁻¹ * E.card) * B ^ 2 := by
  have hμ : 0 ≤ (S.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcs : (∑ i ∈ E, f i) ^ 2 ≤ (E.card : ℝ) * (∑ i ∈ E, f i ^ 2) := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq E (fun _ => (1 : ℝ)) f)
  have hsums : (∑ i ∈ E, f i ^ 2) ≤ ∑ i ∈ S, f i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hES (fun i _ _ => sq_nonneg (f i))
  calc
    A ^ 2 ≤ ((S.card : ℝ)⁻¹ * (∑ i ∈ E, f i)) ^ 2 := pow_le_pow_left₀ hA hfirst 2
    _ = ((S.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ E, f i) ^ 2 := mul_pow _ _ _
    _ ≤ ((S.card : ℝ)⁻¹) ^ 2 * ((E.card : ℝ) * (∑ i ∈ E, f i ^ 2)) := by gcongr
    _ ≤ ((S.card : ℝ)⁻¹) ^ 2 * ((E.card : ℝ) * (∑ i ∈ S, f i ^ 2)) := by gcongr
    _ = ((S.card : ℝ)⁻¹ * E.card) * ((S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsecond (by positivity)

theorem finite_witness_probability {ι : Type*} (S E : Finset ι) (hES : E ⊆ S)
    (f : ι → ℝ) (K : ℝ) (hK : 1000 ≤ K)
    (hfirst : Real.exp ((3 / 200 : ℝ) * K) / 2 ≤
      (S.card : ℝ)⁻¹ * (∑ i ∈ E, f i))
    (hsecond : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤
      (2 * Real.exp ((103 / 1000 : ℝ) * K)) ^ 2) :
    Real.exp (-K / 5) ≤ (S.card : ℝ)⁻¹ * E.card := by
  have hh := finite_event_second_moment S E hES f
    (Real.exp ((3 / 200 : ℝ) * K) / 2) (2 * Real.exp ((103 / 1000 : ℝ) * K))
    (by positivity) hfirst hsecond
  have hr : Real.exp ((3 / 100 : ℝ) * K) / 16 ≤
      ((S.card : ℝ)⁻¹ * E.card) * Real.exp ((103 / 500 : ℝ) * K) := by
    rw [div_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at hh
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    have h₁ : 2 * ((3 / 200 : ℝ) * K) = (3 / 100 : ℝ) * K := by ring
    have h₂ : 2 * ((103 / 1000 : ℝ) * K) = (103 / 500 : ℝ) * K := by ring
    rw [h₁, h₂] at hh
    nlinarith only [hh]
  have hbound : Real.exp ((-22 / 125 : ℝ) * K) / 16 ≤ (S.card : ℝ)⁻¹ * E.card := by
    have hd := (div_le_iff₀ (Real.exp_pos ((103 / 500 : ℝ) * K))).mpr hr
    have heq : (Real.exp ((3 / 100 : ℝ) * K) / 16) / Real.exp ((103 / 500 : ℝ) * K) =
        Real.exp ((-22 / 125 : ℝ) * K) / 16 := by
      rw [div_right_comm, ← Real.exp_sub]
      congr 2
      ring
    simpa only [heq] using hd
  have h16 : (16 : ℝ) ≤ Real.exp ((3 / 125 : ℝ) * K) := by
    have ht := Real.add_one_le_exp ((3 / 125 : ℝ) * K)
    linarith
  apply le_trans _ hbound
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  calc
    Real.exp (-K / 5) * 16 ≤ Real.exp (-K / 5) * Real.exp ((3 / 125 : ℝ) * K) := by gcongr
    _ = Real.exp ((-22 / 125 : ℝ) * K) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteMomentPerturbation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring first and second moments through the checked grid error -/

namespace Ostmann

open scoped BigOperators

theorem finite_mean_pointwise_le_add {ι : Type*} (S : Finset ι)
    (f g : ι → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ)
    (hfg : ∀ i ∈ S, f i ≤ g i + δ)
    (hg : (S.card : ℝ)⁻¹ * (∑ i ∈ S, g i) ≤ B) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i) ≤ B + δ := by
  by_cases hS : S.Nonempty
  · have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
    have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg)
      (inv_nonneg.mpr (Nat.cast_nonneg S.card) : 0 ≤ (S.card : ℝ)⁻¹)
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_add] at hh
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at hh
    linarith
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hzero, Finset.sum_empty, mul_zero] at hg ⊢
    linarith

theorem finite_restricted_mean_pointwise_le_add {ι : Type*} (S E : Finset ι)
    (hES : E ⊆ S) (f g : ι → ℝ) (δ B : ℝ) (hδ : 0 ≤ δ)
    (hg : ∀ i ∈ S, 0 ≤ g i) (hfg : ∀ i ∈ E, f i ≤ g i + δ)
    (hmean : (S.card : ℝ)⁻¹ * (∑ i ∈ S, g i) ≤ B) :
    (S.card : ℝ)⁻¹ * (∑ i ∈ E, f i) ≤ B + δ := by
  have hs : (∑ i ∈ E, f i) ≤ ∑ i ∈ S, (g i + δ) :=
    (Finset.sum_le_sum hfg).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hES (fun i hi _ => add_nonneg (hg i hi) hδ))
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
    (finite_mean_pointwise_le_add S (fun i => g i + δ) g δ B hδ (fun _ _ => le_rfl) hmean)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_UniformPrimeProductMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite-family moment bound under the original prime-product law -/

namespace Ostmann

open Filter
open scoped BigOperators

/-- The manuscript's fixed-family estimate. All sampling and numerical
transfer factors are discharged; only Bonami's precisely stated published
inequality is an analytic input to this moment calculation. -/
theorem eventual_uniform_prime_product_moment (hB : PublishedBonamiBound)
    (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ {I : Type*} [Fintype I]
      (P S R : Finset ℕ) (U Z k l : ℕ),
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) →
      1 ≤ Z → Real.exp T ≤ C * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (Fintype.card I : ℝ) ≤ Real.exp (C * T) → (U : ℝ) ≤ Real.exp (C * T) →
      ∀ (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ),
      0 ≤ E → 0 ≤ A → A ≤ Real.exp (C * T) →
      (∀ i, (∑ s : S, ((2 * l : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E) →
      (∀ i, (∑ s : S, ‖b i s‖) ≤ A) →
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp (ε * T ^ (9999999 / 10000000 : ℝ)) * Real.sqrt E +
          Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_prime_moment_factors C ε hC hε] with T hfactor
  intro I _ P S R U Z k l hS hR hP hodd hU hZ hZ1 hpop hZU hk hsize hkL hkU
    hl hlL hlU hI hUU b pick E A hE hA hAA henergy hmass
  have hJ : 0 < P.card := by nlinarith
  obtain ⟨hsquare, hnonsquare⟩ := hfactor P.card Z k l (Fintype.card I) U A
    hJ hZ1 hpop hZU hkL hkU hl hlL hlU hI hUU hA hAA
  have henergy' (i : I) :
      (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E := by
    apply le_trans (Finset.sum_le_sum (fun s _ => ?_)) (henergy i)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le (2 * l) 1)) _)
      (sq_nonneg _)
  exact prime_product_family_norm_transfer hB P S R hS hR hP hodd U Z k l hU hZ
    (by omega) hk hsize b pick E A _ _ hE (Real.exp_nonneg _) (Real.exp_nonneg _)
    henergy' hmass hsquare hnonsquare

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FixedCoefficientMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the published Bonami input to the actual fixed coefficient family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_fixed_coefficient_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H η : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H) (hη : 0 < η)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (J : Finset QuadraticFamilyIndex)
      (P S R : Finset ℕ) (U Z k l : ℕ) (α : ℝ),
      J ⊆ quadraticFamilyParameters T Q.toList.prod →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (500 * T) →
      (∀ i ∈ J, Real.sqrt (∑ s ∈ S, (((2 * l : ℕ) : ℝ) ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤ Real.exp (α * Q.card)) →
      ∀ pick : ℕ → J,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp ((α + η) * Q.card) + Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_uniform_prime_product_moment hB Cpop (η / 1000)
      (by linarith) (by positivity),
    eventual_quadraticFamilyParameters_card,
    eventual_fixed_quadratic_family_mass H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hm hcard hmass hT
  intro Q hQ D J P S R U Z k l α hJ hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU hnorm pick
  have hJcard : (Fintype.card J : ℝ) ≤ Real.exp (Cpop * T) := by
    have hc : (J.card : ℝ) ≤ ((quadraticFamilyParameters T Q.toList.prod).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hJ)
    rw [Fintype.card_coe]
    exact (hc.trans (hcard Q.toList.prod hL)).trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hCpop) hT]))
  have hSpos : ∀ s ∈ S, 0 < s := fun s hs => Nat.pos_of_ne_zero (hS s hs).ne_zero
  have hmass' (i : J) : (∑ s : S,
      ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖) ≤ Real.exp (16 * T) :=
    hmass Q hQ D S hQT hlarge hL hSpos hScard i (hJ i.property)
  have he (i : J) :
      (∑ s : S, ((2 * l : ℕ) : ℝ) ^ s.val.primeFactors.card *
        ‖rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s‖ ^ 2) ≤
        Real.exp (2 * (α * Q.card)) := by
    rw [rootNormalizedCoefficient_energy]
    have hh := (Real.sqrt_le_iff.mp (hnorm i i.property)).2
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hh
  have hh := hm P S R U Z k l hS hSR hP hodd hSU hPZ hZ hpop hZU hk hsize hkL hkU hl
    hlL hlU hJcard (hU.trans (Real.exp_le_exp.mpr (by nlinarith))) (fun i s => rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ i) s)
    pick (Real.exp (2 * (α * Q.card))) (Real.exp (16 * T)) (Real.exp_nonneg _) (Real.exp_nonneg _)
    (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hCpop) hT])) he hmass'
  apply hh.trans
  apply pow_le_pow_left₀ (by positivity)
  apply add_le_add_left
  rw [← Real.exp_half, show 2 * (α * Q.card) / 2 = α * Q.card by ring, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hkη := mul_le_mul_of_nonneg_left hK hη.le
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalFourierGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Principal Fourier terms in finite frequency families -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem smallKernelParameters_principal (T : ℝ) (L : ℕ) :
    smallKernelParameters T L ⊆ principalQuadraticParameters T L := by
  intro i hi
  obtain ⟨hi, hp, _⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, hp⟩

theorem squarefreeKernelSupport_card_le (L N : ℕ) :
    (squarefreeKernelSupport L N).card ≤ N := by
  apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
  simp only [Nat.card_Icc]
  omega

theorem smallSquarefreeKernels_spec (L N s : ℕ) (hs : s ∈ smallSquarefreeKernels L N) :
    1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L ∧ s ≤ L ^ 4 := by
  obtain ⟨hs, hsmall⟩ := Finset.mem_filter.mp hs
  exact ⟨(mem_squarefreeKernelSupport L N s).mp hs |>.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.2.1,
    (mem_squarefreeKernelSupport L N s).mp hs |>.2.2.2, hsmall⟩

theorem largeSquarefreeKernels_spec (L N s : ℕ) (hL : 2 ≤ L)
    (hs : s ∈ largeSquarefreeKernels L N) :
    1 ≤ s ∧ s ≤ N ∧ Squarefree s ∧ s.Coprime L ∧ 4 * L ^ 2 ≤ s := by
  obtain ⟨hs, hlarge⟩ := Finset.mem_filter.mp hs
  obtain ⟨hs1, hsN, hsf, hcp⟩ := (mem_squarefreeKernelSupport L N s).mp hs
  refine ⟨hs1, hsN, hsf, hcp, ?_⟩
  have hpow : 4 ≤ L ^ 2 := by nlinarith
  have hh : 4 * L ^ 2 ≤ L ^ 4 := by nlinarith [Nat.zero_le ((L ^ 2 - 4) * L ^ 2)]
  exact hh.trans (Nat.le_of_lt hlarge)

theorem filteredKernel_card_le (L N : ℕ) (pred : ℕ → Prop) [DecidablePred pred] :
    ((squarefreeKernelSupport L N).filter pred).card ≤ N :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (squarefreeKernelSupport_card_le L N)

/-- One common index approximates both principal pieces. Its outer parameter
is one, and its scale remains in the small-kernel range. -/
theorem eventual_principalFourier_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) (θ R : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R →
      (N : ℝ) ≤ Real.exp (14 * T) →
      ∃ i ∈ smallKernelParameters T Q.toList.prod,
        ‖principalSmallFourier Q hQ D M N h₀ θ R Φ -
          quadraticArrayStatistic (smallSquarefreeKernels Q.toList.prod N) M
            (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤ Real.exp (-113 * T) ∧
        ‖principalLargeFourier Q hQ D M N h₀ θ R Φ -
          quadraticArrayStatistic (largeSquarefreeKernels Q.toList.prod N) M
            (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤ Real.exp (-113 * T) := by
  filter_upwards [eventual_small_kernel_family_covers H Φ hH hΦ] with T hc
  intro Q hQ D M N h₀ θ R hcard hlarge hL hM hh₀ hθ0 hθ1 hR hRU hmargin hN
  obtain ⟨i, hi, he⟩ := hc Q hQ D M h₀ θ R hcard hlarge hL hM hh₀ hθ0 hθ1 hR hRU hmargin
  have happ (pred : ℕ → Prop) [DecidablePred pred] :
      ‖quadraticArrayStatistic ((squarefreeKernelSupport Q.toList.prod N).filter pred) M
          (arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ) -
        quadraticArrayStatistic ((squarefreeKernelSupport Q.toList.prod N).filter pred) M
          (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤ Real.exp (-113 * T) := by
    apply quadraticArrayStatistic_grid_error
    · intro s hs
      exact (mem_squarefreeKernelSupport _ _ _ |>.mp (Finset.mem_filter.mp hs).1).1
    · exact (Nat.cast_le.mpr (filteredKernel_card_le _ _ pred)).trans hN
    · intro s hs
      obtain ⟨hs1, hsN, _⟩ := (mem_squarefreeKernelSupport _ _ _).mp (Finset.mem_filter.mp hs).1
      exact he s hs1 ((Nat.cast_le.mpr hsN).trans hN)
  exact ⟨i, hi, happ _, happ _⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalLargeMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first moment of the original large-kernel Fourier term -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_original_large_first_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) → 2 ≤ Q.toList.prod →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (N : ℝ) ≤ Real.exp (14 * T) →
      ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
      (∀ m ∈ primeSubsetProducts P k,
        h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
        R m ≤ Real.exp (14 * T) ∧
        (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R m) →
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) ≤
        Real.exp ((9 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) + Real.exp (-113 * T) := by
  filter_upwards [eventual_principalFourier_grid H Φ hH hΦ,
    eventual_large_kernel_prime_moment hB Cpop hCpop H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hgrid hm hT
  intro Q hQ D P N Z k l hK hQT hlarge hL hL2 hP hodd hPZ hZ hpop hZU hk hsize
    hkL hkU hl hlL hlU hN h₀ θ R hrange
  let S := largeSquarefreeKernels Q.toList.prod N
  let B := Real.exp ((9 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T)
  have hLe : (Q.toList.prod : ℝ) ≤ Real.exp T :=
    hL.trans (Real.exp_le_exp.mpr (by linarith))
  have hcard : (S.card : ℝ) ≤ Real.exp (14 * T) :=
    (Nat.cast_le.mpr (filteredKernel_card_le Q.toList.prod N _)).trans hN
  have hspec (s : ℕ) (hs : s ∈ S) := largeSquarefreeKernels_spec Q.toList.prod N s hL2 hs
  have hprodOdd (m : ℕ) (hm : m ∈ primeSubsetProducts P k) : Odd m :=
    (Finset.mem_filter.mp (primeSubsetProducts_mem_range P k Z hP hodd hPZ hm)).2.1
  have hcover (m : ℕ) (hmem : m ∈ primeSubsetProducts P k) :
      ∃ i : smallKernelParameters T Q.toList.prod,
        ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
          quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
            Real.exp (-113 * T) := by
    obtain ⟨hh, hθ0, hθ1, hR, hRU, hmargin⟩ := hrange m hmem
    obtain ⟨i, hi, _, he⟩ := hgrid Q hQ D m N (h₀ m) (θ m) (R m) hQT hlarge hLe
      (hprodOdd m hmem) hh hθ0 hθ1 hR hRU hmargin hN
    exact ⟨⟨i, hi⟩, he⟩
  have hkP : k ≤ P.card := by nlinarith
  have hne : (primeSubsetProducts P k).Nonempty := by
    apply Finset.card_pos.mp
    rw [primeSubsetProducts_card P k hP]
    exact Nat.choose_pos hkP
  obtain ⟨m₀, hm₀⟩ := hne
  obtain ⟨i₀, _⟩ := hcover m₀ hm₀
  have hex (m : ℕ) : ∃ i : smallKernelParameters T Q.toList.prod,
      m ∈ primeSubsetProducts P k →
        ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
          quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
            Real.exp (-113 * T) := by
    by_cases hh : m ∈ primeSubsetProducts P k
    · obtain ⟨i, hi⟩ := hcover m hh
      exact ⟨i, fun _ => hi⟩
    · exact ⟨i₀, fun h => (hh h).elim⟩
  choose pick hpick using hex
  let SR := S.biUnion Nat.primeFactors
  have hmoment := hm Q hQ D P S SR N Z k l hK hQT hlarge hL
    (fun s hs => (hspec s hs).2.2.1)
    (fun s hs => Finset.subset_biUnion_of_mem Nat.primeFactors hs)
    (fun s hs => ⟨(hspec s hs).2.2.2.2, (hspec s hs).2.2.2.1.symm⟩) hP hodd
    (fun s hs => (hspec s hs).2.1) hPZ hcard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hN
    (fun m => ⟨(pick m).val, smallKernelParameters_principal T Q.toList.prod (pick m).property⟩)
  have hmean := quadraticArrayStatistic_mean_of_moment P S k l
    (fun i : smallKernelParameters T Q.toList.prod => fixedQuadraticCoefficient T Q hQ D Φ i)
    pick B hP hl (by positivity) (by simpa only [quadraticArrayStatistic] using hmoment)
  rw [← primeSubsetProducts_card P k hP]
  rw [← primeSubsetProducts_card P k hP] at hmean
  apply finite_mean_pointwise_le_add _ _ _ (Real.exp (-113 * T)) B (Real.exp_nonneg _) _ hmean
  intro m hmem
  have hp := hpick m hmem
  have hh := norm_add_le
    (principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
      quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
    (quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
  simp only [sub_add_cancel] at hh
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RepeatRemovalAsymptotics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen prime population makes the relative deletion error small -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_repeat_power_budget (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      (16 * C * T * (k : ℝ) ^ 3) ^ k * C ^ 2 ≤ Real.exp (ε * K) := by
  let B := 128 * C
  let D := 2 * B + 8 + 2 * C
  have hC0 : 0 ≤ C := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound zero_lt_one
  have hp := (tendsto_rpow_atTop
    (show (0 : ℝ) < 9999999 / 10000000 - 7 / 10 by norm_num)).eventually_ge_atTop
    (1000 * D / ε)
  filter_upwards [hl, hp, eventually_ge_atTop (1 : ℝ)] with T hlog hpow hT k K hk hK
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog' : Real.log T ≤ T ^ (1 / 10 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hTpos.le _), one_mul] using hlog
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hρ : T ^ (3 / 5 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hkT : (k : ℝ) ≤ 2 * T := hk.trans (by gcongr)
  have hbase : 16 * C * T * (k : ℝ) ^ 3 ≤ Real.exp (B + 4 * Real.log T) := by
    calc
      _ ≤ 16 * C * T * (2 * T) ^ 3 := by gcongr
      _ = B * T ^ 4 := by dsimp [B]; ring
      _ ≤ Real.exp B * T ^ 4 := by gcongr; linarith [Real.add_one_le_exp B]
      _ = Real.exp (B + 4 * Real.log T) := by
        rw [Real.exp_add]
        congr 1
        simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using
          (Real.exp_nat_mul (Real.log T) 4).symm
  have hklog : (k : ℝ) * Real.log T ≤ 2 * T ^ (7 / 10 : ℝ) := by
    calc
      _ ≤ (2 * T ^ (3 / 5 : ℝ)) * T ^ (1 / 10 : ℝ) :=
        mul_le_mul hk hlog' hlogT (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hTpos]; norm_num
  have hρ' : T ^ (3 / 5 : ℝ) ≤ T ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have h1 : (1 : ℝ) ≤ T ^ (7 / 10 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hexp : (k : ℝ) * (B + 4 * Real.log T) + 2 * C ≤ D * T ^ (7 / 10 : ℝ) := by
    have hk7 : (k : ℝ) ≤ 2 * T ^ (7 / 10 : ℝ) :=
      hk.trans (mul_le_mul_of_nonneg_left hρ' (by norm_num))
    have hkb := mul_le_mul_of_nonneg_left hk7 hB
    have hc := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C by positivity)
    dsimp [D]
    nlinarith only [hkb, hc, hklog]
  have hbudget : D * T ^ (7 / 10 : ℝ) ≤ ε * K := by
    have hp' := (div_le_iff₀ hε).mp hpow
    have hh := mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hTpos.le (7 / 10 : ℝ))
    have heq : T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * T ^ (7 / 10 : ℝ) =
        T ^ (9999999 / 10000000 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      norm_num
    have heq' : (T ^ (9999999 / 10000000 - 7 / 10 : ℝ) * ε) * T ^ (7 / 10 : ℝ) =
        ε * T ^ (9999999 / 10000000 : ℝ) := by rw [mul_right_comm, heq, mul_comm]
    rw [heq'] at hh
    have hK' := mul_le_mul_of_nonneg_left hK hε.le
    nlinarith only [hh, hK']
  calc
    _ ≤ (Real.exp (B + 4 * Real.log T)) ^ k * (Real.exp C) ^ 2 := by
      apply mul_le_mul (pow_le_pow_left₀ (by positivity) hbase k) _ (sq_nonneg C) (by positivity)
      exact pow_le_pow_left₀ hC0 (by linarith [Real.add_one_le_exp C]) 2
    _ = Real.exp ((k : ℝ) * (B + 4 * Real.log T) + 2 * C) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (hexp.trans hbudget)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalMomentBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical budgets for the original Fourier moments -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventual_two_pow_moment_budget :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      1 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      (2 : ℝ) ^ k ≤ Real.exp (K / 10) := by
  filter_upwards [eventual_repeat_power_budget 1 (1 / 10) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hb hT k K hk hkU hK
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : (2 : ℝ) ≤ 16 * 1 * T * (k : ℝ) ^ 3 := by
    have hpow : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hk1
    nlinarith
  have hh := hb k K hkU hK
  norm_num only [one_pow, mul_one] at hh
  exact (pow_le_pow_left₀ (by norm_num) hbase k).trans (by simpa only [one_mul, mul_one, div_eq_mul_inv, mul_comm] using hh)

theorem original_outer_moment_budget (T K : ℝ) (k : ℕ)
    (hK : 3000 ≤ K) (hKT : K ≤ T) (hpow : (2 : ℝ) ^ k ≤ Real.exp (K / 10)) :
    (2 : ℝ) ^ k * (Real.exp ((-799 / 1000 : ℝ) * K) +
      Real.exp (-10 * T) + Real.exp (-113 * T)) ≤ 1 := by
  have hK0 : 0 ≤ K := by linarith
  have h₁ : Real.exp (K / 10) * Real.exp ((-799 / 1000 : ℝ) * K) ≤ Real.exp (-K / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h₂ : Real.exp (K / 10) * Real.exp (-10 * T) ≤ Real.exp (-K / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h₃ : Real.exp (K / 10) * Real.exp (-113 * T) ≤ Real.exp (-K / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have he : 3 * Real.exp (-K / 2) ≤ 1 := by
    have hh : (3 : ℝ) ≤ Real.exp (K / 2) := by linarith [Real.add_one_le_exp (K / 2)]
    rw [show -K / 2 = -(K / 2) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    simpa using hh
  calc
    _ ≤ Real.exp (K / 10) * (Real.exp ((-799 / 1000 : ℝ) * K) +
        Real.exp (-10 * T) + Real.exp (-113 * T)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ 3 * Real.exp (-K / 2) := by nlinarith only [h₁, h₂, h₃]
    _ ≤ 1 := he

/-- After subtracting the large, outer, and failed-witness contributions,
the second moment gives the manuscript's positive witness probability. -/
theorem original_moment_witness_probability {ι : Type*} (S : Finset ι) (E : ι → Prop)
    [DecidablePred E] (F f g o : ι → ℝ) (T K : ℝ)
    (hK : 3000 ≤ K) (hKT : K ≤ T)
    (hpoint : ∀ i ∈ S, F i ≤ f i + g i + o i)
    (hfirst : Real.exp ((3 / 200 : ℝ) * K) ≤ (S.card : ℝ)⁻¹ * (∑ i ∈ S, F i))
    (hsecond : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤
      (Real.exp ((103 / 1000 : ℝ) * K) + Real.exp (-10 * T) + Real.exp (-113 * T)) ^ 2)
    (hlarge : (S.card : ℝ)⁻¹ * (∑ i ∈ S, g i) ≤
      Real.exp ((9 / 1000 : ℝ) * K) + Real.exp (-10 * T) + Real.exp (-113 * T))
    (houter : (S.card : ℝ)⁻¹ * (∑ i ∈ S, o i) ≤ 1)
    (hfail : (S.card : ℝ)⁻¹ * (∑ i ∈ S.filter (fun i => ¬E i), f i) ≤
      Real.exp ((-797 / 1000 : ℝ) * K) + Real.exp (-10 * T) + Real.exp (-113 * T)) :
    Real.exp (-K / 5) ≤ (S.card : ℝ)⁻¹ * (S.filter E).card := by
  have hK0 : 0 ≤ K := by linarith
  have hT0 : 0 ≤ T := hK0.trans hKT
  have he10 : Real.exp (-10 * T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he113 : Real.exp (-113 * T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hef : Real.exp ((-797 / 1000 : ℝ) * K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hA : 24 ≤ Real.exp ((3 / 200 : ℝ) * K) := by
    linarith [Real.add_one_le_exp ((3 / 200 : ℝ) * K)]
  have hratio : Real.exp ((9 / 1000 : ℝ) * K) ≤ Real.exp ((3 / 200 : ℝ) * K) / 4 := by
    have he : (4 : ℝ) ≤ Real.exp ((3 / 500 : ℝ) * K) := by
      linarith [Real.add_one_le_exp ((3 / 500 : ℝ) * K)]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    calc
      _ ≤ Real.exp ((9 / 1000 : ℝ) * K) * Real.exp ((3 / 500 : ℝ) * K) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint)
    (inv_nonneg.mpr (Nat.cast_nonneg S.card) : 0 ≤ (S.card : ℝ)⁻¹)
  simp only [Finset.sum_add_distrib, mul_add] at hsum
  have hsplit := Finset.sum_filter_add_sum_filter_not S E f
  have hsplit' := congrArg (fun x : ℝ => (S.card : ℝ)⁻¹ * x) hsplit
  rw [mul_add] at hsplit'
  apply finite_witness_probability S (S.filter E) (Finset.filter_subset _ _) f K (by linarith)
  · linarith
  · have hB : 2 ≤ Real.exp ((103 / 1000 : ℝ) * K) := by
      linarith [Real.add_one_le_exp ((103 / 1000 : ℝ) * K)]
    apply hsecond.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OffWitnessMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentially small moments for the genuine off-witness family -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_off_witness_prime_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P S R : Finset ℕ) (U Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (14 * T) →
      ∀ pick : ℕ → offWitnessParameters T Q hQ D Φ S,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
        (Real.exp ((-797 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_fixed_coefficient_moment hB Cpop hCpop H (1 / 1000) Φ hH (by norm_num) hΦ,
    eventual_off_witness_family_norm 14 (1 / 1000) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with T hm hn hT
  intro Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  have hsub : offWitnessParameters T Q hQ D Φ S ⊆ quadraticFamilyParameters T Q.toList.prod :=
    fun i hi => smallKernelParameters_subset T Q.toList.prod ((Finset.mem_filter.mp hi).1)
  have hU500 : (U : ℝ) ≤ Real.exp (500 * T) :=
    hU.trans (Real.exp_le_exp.mpr (by linarith))
  have huU : ((2 * l : ℕ) : ℝ) ≤ 2 * T ^ (1 / 1000000 : ℝ) := by
    push_cast
    linarith
  have he (i : QuadraticFamilyIndex) (hi : i ∈ offWitnessParameters T Q hQ D Φ S) :
      Real.sqrt (∑ s ∈ S, (((2 * l : ℕ) : ℝ) ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤ Real.exp ((-399 / 500 : ℝ) * Q.card) := by
    have hh := hn Q hQ U S ((2 * l : ℕ) : ℝ) hK hlarge hU
      (fun s hs => ⟨hS s hs, hSU s hs⟩) (Nat.cast_nonneg _) huU D Φ i hi
    norm_num only [show (-799 / 1000 + 1 / 1000 : ℝ) = -399 / 500 by norm_num] at hh
    simpa only [neg_div] using hh
  have hh := hm Q hQ D (offWitnessParameters T Q hQ D Φ S) P S R U Z k l (-399 / 500)
    hsub hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard hZ hpop hZU hk hsize hkL hkU
    hl hlL hlU hU500 he pick
  norm_num only [show (-399 / 500 + 1 / 1000 : ℝ) = -797 / 1000 by norm_num] at hh
  simpa only [neg_div] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_OffWitnessStatistic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean absolute size of the fixed off-witness Jacobi statistic -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_off_witness_prime_mean (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P S R : Finset ℕ) (U Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (14 * T) →
      ∀ pick : ℕ → offWitnessParameters T Q hQ D Φ S,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖) ≤
        Real.exp ((-797 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) := by
  filter_upwards [eventual_off_witness_prime_moment hB Cpop hCpop H Φ hH hΦ] with T hm
  intro Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  have hh := hm Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  exact quadraticArrayStatistic_mean_of_moment P S k l
    (fun i : offWitnessParameters T Q hQ D Φ S => fixedQuadraticCoefficient T Q hQ D Φ i)
    pick _ hP hl (by positivity) hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalOffWitnessMoment
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original small-kernel statistic on the event with no witness -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

theorem eventual_original_off_witness_mean (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      1 ≤ Q.card → (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (N : ℝ) ≤ Real.exp (14 * T) →
      ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
      (∀ m ∈ primeSubsetProducts P k,
        h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
        R m ≤ Real.exp (14 * T) ∧
        (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R m) →
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ (primeSubsetProducts P k).filter
          (fun m => ¬principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ),
          ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) ≤
        Real.exp ((-797 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) + Real.exp (-113 * T) := by
  filter_upwards [eventual_off_witness_family_covers H Φ hH hΦ,
    eventual_off_witness_prime_mean hB Cpop hCpop H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hgrid hm hT
  intro Q hQ D P N Z k l hK hK1 hQT hlarge hL hP hodd hPZ hZ hpop hZU hk hsize
    hkL hkU hl hlL hlU hN h₀ θ R hrange
  let S := smallSquarefreeKernels Q.toList.prod N
  let E := (primeSubsetProducts P k).filter
    (fun m => ¬principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)
  have hES : E ⊆ primeSubsetProducts P k := Finset.filter_subset _ _
  by_cases hE : E.Nonempty
  · have hLe : (Q.toList.prod : ℝ) ≤ Real.exp T :=
      hL.trans (Real.exp_le_exp.mpr (by linarith))
    have hcard : (S.card : ℝ) ≤ Real.exp (14 * T) :=
      (Nat.cast_le.mpr (filteredKernel_card_le Q.toList.prod N _)).trans hN
    have hspec (s : ℕ) (hs : s ∈ S) := smallSquarefreeKernels_spec Q.toList.prod N s hs
    have hprodOdd (m : ℕ) (hm : m ∈ primeSubsetProducts P k) : Odd m :=
      (Finset.mem_filter.mp (primeSubsetProducts_mem_range P k Z hP hodd hPZ hm)).2.1
    have hcover (m : ℕ) (hmem : m ∈ E) :
        ∃ i : offWitnessParameters T Q hQ D Φ S,
          ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
            quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
              Real.exp (-113 * T) := by
      have hmemP := hES hmem
      obtain ⟨hh, hθ0, hθ1, hR, hRU, hmargin⟩ := hrange m hmemP
      have hfail (s : ℕ) (hs : s ∈ S) (V : Finset ℕ) (hV : V ∈ Q.powerset)
          (U : Finset ℕ) (hU : U ∈ Q.powerset) :
          ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue m) V)
            (fun _ => (h₀ m : ℝ) + θ m) Φ (R m) V.toList.prod U s‖ ≤
              Real.exp (-(Q.card : ℝ)) * (Real.sqrt 2) ^ U.card := by
        apply le_of_not_gt
        intro hbad
        exact (Finset.mem_filter.mp hmem).2 ⟨s, hs, V, hV, U, hU, hbad⟩
      obtain ⟨i, hi, he⟩ := hgrid Q hQ D m (h₀ m) (θ m) (R m) S hK1 hQT hlarge hLe
        (hprodOdd m hmemP) hh (fun s hs => ⟨(hspec s hs).1,
          (Nat.cast_le.mpr (hspec s hs).2.1).trans hN⟩)
        hθ0 hθ1 hR hRU hmargin hfail
      refine ⟨⟨i, hi⟩, ?_⟩
      exact quadraticArrayStatistic_grid_error T S m _ _
        (fun s hs => (hspec s hs).1) hcard he
    obtain ⟨m₀, hm₀⟩ := hE
    obtain ⟨i₀, _⟩ := hcover m₀ hm₀
    have hex (m : ℕ) : ∃ i : offWitnessParameters T Q hQ D Φ S, m ∈ E →
        ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
          quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ i)‖ ≤
            Real.exp (-113 * T) := by
      by_cases hh : m ∈ E
      · obtain ⟨i, hi⟩ := hcover m hh
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => (hh h).elim⟩
    choose pick hpick using hex
    let SR := S.biUnion Nat.primeFactors
    have hmean := hm Q hQ D P S SR N Z k l hK hQT hlarge hL
      (fun s hs => (hspec s hs).2.2.1)
      (fun s hs => Finset.subset_biUnion_of_mem Nat.primeFactors hs)
      hP hodd (fun s hs => (hspec s hs).2.1) hPZ hcard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hN pick
    change (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k,
      ‖quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m))‖) ≤
      Real.exp ((-797 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) at hmean
    rw [← primeSubsetProducts_card P k hP] at hmean ⊢
    apply finite_restricted_mean_pointwise_le_add _ E hES _ _ (Real.exp (-113 * T)) _
      (Real.exp_nonneg _) (fun _ _ => norm_nonneg _) _ hmean
    intro m hmem
    have hp := hpick m hmem
    have hh := norm_add_le
      (principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ -
        quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
      (quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m)))
    simp only [sub_add_cancel] at hh
    linarith
  · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    change _ * (∑ m ∈ E, _) ≤ _
    rw [he, Finset.sum_empty, mul_zero]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalWitnessProbability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive probability for the original quadratic witness -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

theorem eventual_original_witness_probability_oai (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (N Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      3000 ≤ Q.card → (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      2 ≤ Q.toList.prod →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      1 ≤ N → (N : ℝ) ≤ Real.exp (14 * T) →
      ∀ (h₀ : ℕ → ℕ) (θ R : ℕ → ℝ),
      (∀ m ∈ primeSubsetProducts P k,
        h₀ m < Q.toList.prod ∧ 0 ≤ θ m ∧ θ m ≤ 1 ∧ 1 ≤ R m ∧
        R m ≤ Real.exp (14 * T) ∧
        (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R m) →
      (∀ m ∈ primeSubsetProducts P k, H * R m * Q.toList.prod ≤ N) →
      Real.exp ((3 / 200 : ℝ) * Q.card) ≤ (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖originalPositiveFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖) →
      Real.exp (-(Q.card : ℝ) / 5) ≤ (P.card.choose k : ℝ)⁻¹ *
        ((primeSubsetProducts P k).filter (fun m =>
          principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)).card := by
  classical
  filter_upwards [eventual_original_small_second_moment hB Cpop hCpop H Φ hH hΦ,
    eventual_original_large_first_moment hB Cpop hCpop H Φ hH hΦ,
    eventual_original_off_witness_mean hB Cpop hCpop H Φ hH hΦ,
    eventual_original_outer_first_moment hB Cpop hCpop H Φ hH hΦ,
    eventual_two_pow_moment_budget, eventually_ge_atTop (1 : ℝ)] with T hs hl ho hr hp hT
  intro Q hQ D P N Z k l hK hK3 hKU hlarge hL hL2 hP hodd hPZ hmin hZ hpop hZU hk hsize
    hkL hkU hll hlL hlU hN1 hN h₀ θ R hrange hcut hfirst
  have hQT : (Q.card : ℝ) ≤ T := hKU.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num))
  have hK3' : (3000 : ℝ) ≤ Q.card := by exact_mod_cast hK3
  have hK1 : 1 ≤ Q.card := by omega
  have hsecond := hs Q hQ D P N Z k l hK hQT hlarge hL hP hodd hPZ hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R hrange
  have hlargeMean := hl Q hQ D P N Z k l hK hQT hlarge hL hL2 hP hodd hPZ hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R hrange
  have hfail := ho Q hQ D P N Z k l hK hK1 hQT hlarge hL hP hodd hPZ hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R hrange
  have houter := hr Q hQ D P N Z k l hK hKU hlarge hL hP hodd hPZ hmin hZ hpop hZU
    hk hsize hkL hkU hll hlL hlU hN h₀ θ R (fun m hm =>
      ⟨(hrange m hm).1, (hrange m hm).2.1, (hrange m hm).2.2.1,
        (hrange m hm).2.2.2.1, (hrange m hm).2.2.2.2.1, hcut m hm⟩)
  have houterOne := houter.trans (original_outer_moment_budget T Q.card k hK3' hQT
    (hp k Q.card hk hkU hK))
  rw [← primeSubsetProducts_card P k hP] at hfirst hsecond hlargeMean hfail houterOne ⊢
  apply original_moment_witness_probability (primeSubsetProducts P k)
    (fun m => principalSmallWitness Q hQ D m N (h₀ m) (θ m) (R m) Φ)
    (fun m => ‖originalPositiveFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖)
    (fun m => ‖principalSmallFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖)
    (fun m => ‖principalLargeFourier Q hQ D m N (h₀ m) (θ m) (R m) Φ‖)
    (fun m => ∑ d ∈ m.divisors.erase 1, ‖quadraticArrayStatistic
      (squarefreeKernelSupport Q.toList.prod N) m
      (arithmeticQuadraticCoefficient Q hQ D Φ (R m) d m (h₀ m) (θ m))‖)
    T Q.card hK3' hQT _ hfirst hsecond hlargeMean houterOne hfail
  intro m hm
  have hmpos : 0 < m := by
    have hh := primeSubsetProducts_mem_range P k Z hP hodd hPZ hm
    have hh' := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1
    omega
  let : NeZero m := ⟨hmpos.ne'⟩
  exact originalPositiveFourier_norm_le_kernels Q hQ D m N (h₀ m) (θ m) (R m) H Φ
    (by have hh := (hrange m hm).2.2.2.1; linarith) hH hN1 (hcut m hm) hΦ

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.eventual_original_witness_probability_oai := @OAI.Ostmann.eventual_original_witness_probability_oai
