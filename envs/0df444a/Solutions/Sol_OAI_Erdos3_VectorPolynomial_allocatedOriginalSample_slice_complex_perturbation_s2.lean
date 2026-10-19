-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_slice_complex_perturbation_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:35:15.381848+00:00
-- url     : https://prove2.me/submissions/4ddff06e-045a-42e6-9c1f-ea9db2fc6e14

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B139
import Definitions.Def_OAIE3v2B162
import Theorems.Thm_OAI_Erdos3_slicedPrincipalC2Tolerance_spec_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_entries {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O]
    (A : (I → ℝ) →L[ℝ] (O → ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i o, |A (Pi.single i 1) o| ≤ M) : ‖A‖ ≤ Fintype.card I * M := by
  apply clm_norm_le_card_mul_of_basis A hM
  intro i
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro o
  simpa only [Real.norm_eq_abs] using hA i o

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

theorem polynomialOperator_fderiv_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) (j : I) (row : O) (col : J) :
    (fderiv ℝ A x (Pi.single j 1)) (Pi.single col 1) row =
      MvPolynomial.eval x (MvPolynomial.pderiv j (p row col)) := by
  have hscalar : (fun y => A y (Pi.single col 1) row) =
      (fun y => MvPolynomial.eval y (p row col)) := funext (fun y => hentry y row col)
  have hB : DifferentiableAt ℝ (fun y => A y (Pi.single col 1)) x :=
    hA.clm_apply (differentiableAt_const _)
  have hp := mvPolynomial_fderiv_coordinate (p row col) x j
  rw [← hscalar, fderiv_apply hB row, fderiv_clm_apply hA (differentiableAt_const _)] at hp
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply] at hp
  exact hp

theorem polynomialOperator_fderiv_norm_le {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ row col j, |MvPolynomial.eval x (MvPolynomial.pderiv j (p row col))| ≤ M) :
    ‖fderiv ℝ A x‖ ≤ Fintype.card I * (Fintype.card J * M) := by
  apply clm_norm_le_card_mul_of_basis _ (mul_nonneg (Nat.cast_nonneg _) hM)
  intro j
  apply clm_norm_le_card_mul_of_entries _ hM
  intro col row
  rw [polynomialOperator_fderiv_entry A p hentry x hA j row col]
  exact hp row col j

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

omit [DecidableEq I] in
theorem polynomialVectorMap_contDiff (p : O → MvPolynomial I ℝ) :
    ContDiff ℝ ∞ (polynomialVectorMap p) := contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (p o))

theorem polynomialVectorMap_fderiv_entry (p : O → MvPolynomial I ℝ) (x : I → ℝ) (i : I) (o : O) :
    fderiv ℝ (polynomialVectorMap p) x (Pi.single i 1) o =
      MvPolynomial.eval x (MvPolynomial.pderiv i (p o)) := by
  have hd := (polynomialVectorMap_contDiff p).differentiable (by norm_num) x
  have he := mvPolynomial_fderiv_coordinate (p o) x i
  change fderiv ℝ (fun y => polynomialVectorMap p y o) x (Pi.single i 1) = _ at he
  rw [fderiv_apply hd o] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators ContDiff

theorem polynomialVectorMap_mass_c2_bounds {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial I ℝ) {d : ℕ} (hd : ∀ o i, (p o).degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hmass : ∀ o, realPolynomialMass (p o) ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖polynomialVectorMap p x‖ ≤ C ∧
      ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤ Fintype.card I * ((d : ℝ) * C) ∧
      ‖fderiv ℝ (fderiv ℝ (polynomialVectorMap p)) x‖ ≤
        Fintype.card I * (Fintype.card I * ((d : ℝ) * ((d : ℝ) * C))) := by
  have hfirst (o : O) (i : I) : realPolynomialMass (pderiv i (p o)) ≤ (d : ℝ) * C :=
    (realPolynomialMass_pderiv_degreeOf (p o) i (hd o i)).trans
      (mul_le_mul_of_nonneg_left (hmass o) (Nat.cast_nonneg _))
  have hsecond (o : O) (i j : I) :
      realPolynomialMass (pderiv j (pderiv i (p o))) ≤ (d : ℝ) * ((d : ℝ) * C) :=
    (realPolynomialMass_pderiv_degreeOf (pderiv i (p o)) j
      (mvPolynomial_pderiv_degreeOf_le (p o) i j (hd o j))).trans
      (mul_le_mul_of_nonneg_left (hfirst o i) (Nat.cast_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro o
    exact (mvPolynomial_eval_abs_le_sum_coeff (p o) x hx).trans (hmass o)
  · apply clm_norm_le_card_mul_of_entries _ (mul_nonneg (Nat.cast_nonneg _) hC)
    intro i o
    rw [polynomialVectorMap_fderiv_entry]
    exact (mvPolynomial_eval_abs_le_sum_coeff (pderiv i (p o)) x hx).trans (hfirst o i)
  · have hs : ContDiff ℝ 2 (polynomialVectorMap p) :=
      (polynomialVectorMap_contDiff p).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)
    have hs' : ContDiff ℝ 1 (fderiv ℝ (polynomialVectorMap p)) := hs.fderiv_right (by norm_num)
    exact polynomialOperator_fderiv_norm_le _ (fun o i => pderiv i (p o))
      (fun y o i => polynomialVectorMap_fderiv_entry p y i o) x (hs'.differentiable one_ne_zero x)
      (by positivity) (fun o i j =>
        (mvPolynomial_eval_abs_le_sum_coeff (pderiv j (pderiv i (p o))) x hx).trans (hsecond o i j))

theorem polynomialMassC2Budget_dominates (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    C ≤ polynomialMassC2Budget N d C ∧
      N * ((d : ℝ) * C) ≤ polynomialMassC2Budget N d C ∧
      N * (N * ((d : ℝ) * ((d : ℝ) * C))) ≤ polynomialMassC2Budget N d C := by
  have hx : 0 ≤ (N : ℝ) * d := by positivity
  have h0 : 1 ≤ (1 + (N : ℝ) * d)^2 := by nlinarith [sq_nonneg ((N : ℝ) * d)]
  have h1 : (N : ℝ) * d ≤ (1 + (N : ℝ) * d)^2 := by nlinarith [sq_nonneg ((N : ℝ) * d)]
  have h2 : ((N : ℝ) * d)^2 ≤ (1 + (N : ℝ) * d)^2 := by nlinarith
  unfold polynomialMassC2Budget
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right h0 hC
  · nlinarith [mul_le_mul_of_nonneg_right h1 hC]
  · nlinarith [mul_le_mul_of_nonneg_right h2 hC]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

theorem sigmaAxisSampler_contDiff (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, ContDiff ℝ ∞ (U d)) : ContDiff ℝ ∞ (sigmaAxisSampler U) :=
  contDiff_pi.mpr (fun s => ((contDiff_apply ℝ ℝ s.2).comp (hU s.1)).comp
    (sigmaAxisProjection I s.1).contDiff)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredC2Difference
namespace OAI

section

namespace Erdos3

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem factoredDifference_fderiv (F G R : E → Y) (t : ℝ)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (hR : Differentiable ℝ R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ F x - fderiv ℝ G x = t • fderiv ℝ R x := by
  rw [← fderiv_sub (hF x) (hG x), show F - G = t • R from funext he,
    fderiv_const_smul (hR x)]

theorem factoredDifference_second_fderiv (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) :
    fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x = t • fderiv ℝ (fderiv ℝ R) x := by
  have hF' : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hG' : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hR' : ContDiff ℝ 1 (fderiv ℝ R) := hR.fderiv_right (by norm_num)
  exact factoredDifference_fderiv _ _ _ t (hF'.differentiable one_ne_zero)
    (hG'.differentiable one_ne_zero) (hR'.differentiable one_ne_zero)
    (factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
      (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he) x

theorem factoredDifference_c2_bounds (F G R : E → Y) (t : ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hR : ContDiff ℝ 2 R)
    (he : ∀ x, F x - G x = t • R x) (x : E) {B₀ B₁ B₂ : ℝ}
    (h₀ : ‖R x‖ ≤ B₀) (h₁ : ‖fderiv ℝ R x‖ ≤ B₁) (h₂ : ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ B₂) :
    ‖F x - G x‖ ≤ |t| * B₀ ∧ ‖fderiv ℝ F x - fderiv ℝ G x‖ ≤ |t| * B₁ ∧
      ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x‖ ≤ |t| * B₂ := by
  rw [he x, factoredDifference_fderiv F G R t (hF.differentiable (by norm_num))
    (hG.differentiable (by norm_num)) (hR.differentiable (by norm_num)) he x,
    factoredDifference_second_fderiv F G R t hF hG hR he x]
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_smul_le t (R x)).trans (mul_le_mul_of_nonneg_left h₀ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ R x)).trans
      (mul_le_mul_of_nonneg_left h₁ (abs_nonneg t))
  · exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ (fderiv ℝ R) x)).trans
      (mul_le_mul_of_nonneg_left h₂ (abs_nonneg t))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawCanonicalNormalizedPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_coefficient_split {K : Type*} [DecidableEq K] (p : MvPolynomial K ℝ)
    (selected : Finset (K →₀ ℕ)) :
    p = (∑ n ∈ selected, MvPolynomial.monomial n (p.coeff n)) +
      ∑ n ∈ p.support \ selected, MvPolynomial.monomial n (p.coeff n) := by
  classical
  ext n
  by_cases hs : n ∈ selected
  · simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs]
  · by_cases hp : n ∈ p.support
    · simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs, hp]
    · have hc := MvPolynomial.notMem_support_iff.mp hp
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs, hp, hc]

theorem polynomial_coefficient_split_principal {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ)
    (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  have hnot : (0 : K →₀ ℕ) ∉ Finset.univ.image principal := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hzero
  have he := polynomial_coefficient_split p (insert 0 (Finset.univ.image principal))
  rw [Finset.sum_insert hnot, Finset.sum_image (fun i _ j _ hij => hinj hij)] at he
  exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSupportRawArray
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_support_subset {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) :
    ∀ ⦃m⦄, m ∈ (monomialArrayPolynomial e a).support → m ∈ Set.range e := by
  intro m hm
  by_contra hn
  have hz := monomialArrayPolynomial_coeff_zero_of_not_mem e a m
    (fun j hj => hn ⟨j, hj⟩)
  exact (MvPolynomial.mem_support_iff.mp hm) hz

theorem polynomial_coefficient_split_principal_on {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (S : Finset (K →₀ ℕ)) (hS : p.support ⊆ S)
    (principal : J → K →₀ ℕ) (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ fixedNonprincipalExponents S principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  unfold fixedNonprincipalExponents
  have hsub : nonprincipalSupport p principal ⊆ S \ insert 0 (Finset.univ.image principal) :=
    Finset.sdiff_subset_sdiff hS (Finset.Subset.refl _)
  have hsum : (∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n)) =
      ∑ n ∈ S \ insert 0 (Finset.univ.image principal), MvPolynomial.monomial n (p.coeff n) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hns : n ∉ p.support := by
      intro hp
      exact hnot (Finset.mem_sdiff.mpr ⟨hp, (Finset.mem_sdiff.mp hn).2⟩)
    simp only [MvPolynomial.notMem_support_iff.mp hns, map_zero]
  rw [← hsum]
  exact polynomial_coefficient_split_principal p principal hinj hzero

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

theorem integerPolynomialCoordinatePMF_active_profile_bound
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P,
      monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (hactive : L ^ h < K) (j : J) {k : ℤ}
    (hk : k ∈ (integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL j).support) :
    |(k : ℝ) / K * monomialScale T (e j) - coefficientProfileCenter P γ j| ≤
      coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  by_cases hj : j = j₀
  · subst j
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte] at hk
    have hb := constantIntegerPMF_support K ρ (by exact_mod_cast hK) hρ hk
    simp only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
      he₀, monomialScale_zero, mul_one, sub_zero]
    linarith
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisPrincipalPMF_active hh hK hL hγ hgap hactive hk
      have hscale : monomialScale T (e j) = (L : ℝ) ^ h := by
        rw [hprincipal j hp]
        simp only [integerAxisSideLength, hactive, ↓reduceIte]
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte, hscale]
      have heq : (k : ℝ) / K * (L : ℝ) ^ h = (L : ℝ) ^ h * (k : ℝ) / K := by ring
      rw [heq, abs_le]
      constructor <;> linarith [hb.1, hb.2]
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisTailPMF_support T hT hK hL hTL hε hεL (e j) (he j) hk
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte,
        sub_zero, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))]
      linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem layerContinuousPrincipalSlots_card (j : Fin m) (i : I j) :
    (layerContinuousPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inl i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceValue_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceValue c lower width) := by
  unfold principalSliceValue
  fun_prop

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceSingleton_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceSingleton c lower width) :=
  contDiff_pi.mpr (fun _ => principalSliceValue_contDiff c lower width)

section Joint

variable {D : Type*} [Fintype D]
variable {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

omit [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)] in
theorem jointSlicedPrincipal_contDiff (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :
    ContDiff ℝ ∞ (jointSlicedPrincipal c lower width) :=
  sigmaAxisSampler_contDiff _ (fun d => principalSliceSingleton_contDiff (c d) (lower d) (width d))

end Joint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPolynomialPerturbation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem jointSlicedPrincipal_polynomial_tail_comparison
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ j, Fintype (B j)] [∀ j, Fintype (F j)]
    [∀ j, DecidableEq (B j)] [∀ j, DecidableEq (F j)]
    (c : ∀ j, B j → ℝ) (lower width : ∀ j, B j × F j → ℝ)
    (b : ∀ j, B j) (i : ∀ j, F j)
    {m d : ℕ} (hdegree : ∀ j, Fintype.card (F j) ≤ m)
    {C M a δ η : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hwidth : ∀ j p, |lower j p| + |width j p| ≤ 1)
    (hc : ∀ j, (∑ b, |c j b|) ≤ C) (hprincipal : ∀ j, a ≤ |c j (b j)|)
    (hw : ∀ j l, δ ≤ width j (b j, l))
    (hlower : ∀ j l, l ≠ i j → 0 ≤ lower j (b j, l))
    (q : (Σ _j : D, Unit) → MvPolynomial (Σ j, B j × F j) ℝ)
    (hqdegree : ∀ o v, (q o).degreeOf v ≤ d) (hqmass : ∀ o, realPolynomialMass (q o) ≤ M)
    (t : ℝ)
    (ht : |t| * polynomialMassC2Budget (Fintype.card (Σ j, B j × F j)) d M ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η)
    (shift : (Σ _j : D, Unit) → ℝ)
    (φ : ((Σ _j : D, Unit) → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure (Σ j, B j × F j))
        (fun x => shift + jointSlicedPrincipal c lower width x) φ -
      mappedTest (unitBoxMeasure (Σ j, B j × F j))
        (fun x => shift + jointSlicedPrincipal c lower width x + t • polynomialVectorMap q x) φ| ≤ η := by
  classical
  let U := jointSlicedPrincipal c lower width
  let V := fun x => U x + t • polynomialVectorMap q x
  have hU : ContDiff ℝ 2 U := (jointSlicedPrincipal_contDiff c lower width).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)
  have hq : ContDiff ℝ 2 (polynomialVectorMap q) := (polynomialVectorMap_contDiff q).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)
  have hV : ContDiff ℝ 2 V := hU.add (hq.const_smul t)
  have hε := slicedPrincipalC2Tolerance_spec_s2 (B := B) (F := F) hdegree hC ha hδ hδone hη A hA
  have herr := hε.2.2 c lower width b i hwidth hc hprincipal hw hlower V hV
  have hclose : ∀ x, (∀ p, |x p| ≤ 1) →
      ‖V x - U x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η ∧
      ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ slicedPrincipalC2Tolerance (Fintype.card (Σ j, B j × F j)) (Fintype.card D) m C a δ A η := by
    intro x hx
    have hb := polynomialVectorMap_mass_c2_bounds q hqdegree hM hqmass x hx
    have hdom := polynomialMassC2Budget_dominates (Fintype.card (Σ j, B j × F j)) d hM
    have he := factoredDifference_c2_bounds V U (polynomialVectorMap q) t hV hU hq
      (fun x => add_sub_cancel_left (U x) _) x (hb.1.trans hdom.1)
      (hb.2.1.trans hdom.2.1) (hb.2.2.trans hdom.2.2)
    exact ⟨he.1.trans ht, he.2.1.trans ht, he.2.2.trans ht⟩
  have he := herr hclose (fun y => φ (shift + y)) (hφ.comp (measurable_const.add measurable_id))
    (fun y => hφone (shift + y))
  simpa only [mappedTest, V, U, add_assoc] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NonprincipalDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_nonprincipalCoefficientSlots {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) :
    j ∈ nonprincipalCoefficientSlots e principal ↔
      e j ∈ fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  simp only [nonprincipalCoefficientSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_monomialExponentSet {C K : Type*} [Fintype C]
    (e : C → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ monomialExponentSet e ↔ ∃ j, e j = m := by
  classical
  simp only [monomialExponentSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem mem_fixedNonprincipalExponents {B K : Type*} [Fintype B]
    (S : Finset (K →₀ ℕ)) (principal : B → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ fixedNonprincipalExponents S principal ↔
      m ∈ S ∧ m ≠ 0 ∧ ∀ b, principal b ≠ m := by
  classical
  simp [fixedNonprincipalExponents]

theorem nonprincipalCoefficientSlots_image {C B K : Type*} [Fintype C] [Fintype B] [DecidableEq (K →₀ ℕ)]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) :
    (nonprincipalCoefficientSlots e principal).image e =
      fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_nonprincipalCoefficientSlots e principal j).mp hj
  · intro hm
    have hs : m ∈ monomialExponentSet e :=
      ((mem_fixedNonprincipalExponents _ principal m).mp hm).1
    obtain ⟨j, rfl⟩ := (mem_monomialExponentSet e m).mp hs
    have hj := (mem_nonprincipalCoefficientSlots e principal j).mpr hm
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

theorem nonprincipalCoefficientSlots_sum {C B K R : Type*} [Fintype C] [Fintype B] [AddCommMonoid R]
    (e : C → K →₀ ℕ) (he : Function.Injective e) (principal : B → K →₀ ℕ) (f : (K →₀ ℕ) → R) :
    (∑ j ∈ nonprincipalCoefficientSlots e principal, f (e j)) =
      ∑ m ∈ fixedNonprincipalExponents (monomialExponentSet e) principal, f m := by
  classical
  rw [← nonprincipalCoefficientSlots_image e principal, Finset.sum_image (fun _ _ _ _ h => he h)]

theorem nonprincipalCoefficientSlots_not_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (b : B) (hj : e j = principal b) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.2
  exact hn b hj.symm

theorem nonprincipalCoefficientSlots_not_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (hj : e j = 0) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.1
  exact hn hj

end Erdos3

end

section

namespace Erdos3

theorem nonprincipalDilation_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C) (b : B)
    (hj : e j = principal b) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_principal e principal j b hj, ite_false]

theorem nonprincipalDilation_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : e j = 0) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_zero e principal j hj, ite_false]

theorem nonprincipalDilation_mem {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : j ∈ nonprincipalCoefficientSlots e principal) : nonprincipalDilation e principal t j = t := by
  classical
  simp only [nonprincipalDilation, hj, ite_true]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SmallAffinePolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_indexed_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (a : C → ℝ) :
    monomialArrayPolynomial e a = MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hS : (monomialArrayPolynomial e a).support ⊆ monomialExponentSet e := by
    intro m hm
    obtain ⟨j, rfl⟩ := monomialArrayPolynomial_support_subset e a hm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hs := polynomial_coefficient_split_principal_on (monomialArrayPolynomial e a)
    (monomialExponentSet e) hS principal hp hp0
  rw [← nonprincipalCoefficientSlots_sum e he principal] at hs
  have hc (b) : (monomialArrayPolynomial e a).coeff (principal b) = a (index b) := by
    rw [← hindex b]
    exact monomialArrayPolynomial_coeff e he a (index b)
  simpa only [hc, monomialArrayPolynomial_coeff e he] using hs

theorem nonprincipalDilation_constant_coeff {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (a : C → ℝ) :
    (monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j)).coeff 0 =
      (monomialArrayPolynomial e a).coeff 0 := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : e j = 0
  · simp only [hj, ite_true, nonprincipalDilation_zero e principal t j hj, one_mul]
  · simp only [hj, ite_false]

theorem monomialArrayPolynomial_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (a : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j) =
      MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*a j) := by
  have hs := monomialArrayPolynomial_indexed_split e he principal hp hp0 index hindex
    (fun j => nonprincipalDilation e principal t j*a j)
  rw [nonprincipalDilation_constant_coeff] at hs
  have hpv (b) : nonprincipalDilation e principal t (index b)*a (index b) = a (index b) := by
    rw [nonprincipalDilation_principal e principal t (index b) b (hindex b), one_mul]
  simp_rw [hpv] at hs
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [nonprincipalDilation_mem e principal t j hj]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_affine_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (c w r : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      MvPolynomial.C ((monomialArrayPolynomial e (fun j => c j+w j*r j)).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (c (index b)+w (index b)*r (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*(c j+w j*r j)) := by
  have ha : (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      (fun j => nonprincipalDilation e principal t j*(c j+w j*r j)) := by
    funext j
    ring
  rw [ha]
  exact monomialArrayPolynomial_dilated_split e he principal hp hp0 index hindex t _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

theorem coefficientProfileCenter_mul {J : Type*} (P : Finset J) (R γ : ℝ) (j : J) :
    coefficientProfileCenter P (R * γ) j = R * coefficientProfileCenter P γ j := by
  classical
  unfold coefficientProfileCenter
  split_ifs <;> ring

theorem coefficientProfileWidth_mul {J : Type*} (P : Finset J) (j₀ : J)
    (R ρ γ ε : ℝ) (j : J) :
    coefficientProfileWidth P j₀ (R * ρ) (R * γ) (R * ε) j =
      R * coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  unfold coefficientProfileWidth
  split_ifs <;> ring

theorem principalProfileSize_mul (R S : ℝ) (b : ℕ) :
    principalProfileSize (R * S) b = R * principalProfileSize S b := by
  unfold principalProfileSize
  ring

theorem tailProfileSize_mul (R S σ : ℝ) (b : ℕ) :
    tailProfileSize (R * S) σ b = R * tailProfileSize S σ b := by
  unfold tailProfileSize
  ring

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G] {B : D → Type*}
variable [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)

theorem bounded_mem_nonprincipalCoefficientSlots
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    e ∈ nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d) ↔
      e ≠ constantCoefficientSlot _ _ ∧ e ∉ principalCoefficientSlots h d := by
  classical
  rw [mem_nonprincipalCoefficientSlots, mem_fixedNonprincipalExponents]
  have hz : e.val = 0 ↔ e = constantCoefficientSlot _ _ := by
    constructor
    · intro he
      exact Subtype.ext he
    · intro he
      exact congrArg Subtype.val he
  have hp : (∃ b, canonicalPrincipalExponent h d b = e.val) ↔
      e ∈ principalCoefficientSlots h d := by
    rw [mem_principalCoefficientSlots]
    constructor <;> rintro ⟨b, hb⟩
    · exact ⟨b, Subtype.ext hb⟩
    · exact ⟨b, congrArg Subtype.val hb⟩
  have hm : e.val ∈ monomialExponentSet
      (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _) :=
    (mem_monomialExponentSet _ _).mpr ⟨e, rfl⟩
  simp only [hm, true_and, ← not_exists, hp]
  exact and_congr (not_congr hz) Iff.rfl

theorem boundedProfileCenter_dilation (γ t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileCenter (principalCoefficientSlots h d) γ e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileCenter (principalCoefficientSlots h d) γ e := by
  classical
  by_cases hp : e ∈ principalCoefficientSlots h d
  · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
    rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
      t e b (congrArg Subtype.val hb.symm), one_mul]
  · simp only [coefficientProfileCenter, hp, ite_false, mul_zero]

theorem boundedProfileWidth_dilation (ρ γ ε t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (t * ε) e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ ε e := by
  classical
  by_cases hz : e = constantCoefficientSlot _ _
  · rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d)
      t e (congrArg Subtype.val hz)]
    simp only [coefficientProfileWidth, hz, ite_true, one_mul]
  · by_cases hp : e ∈ principalCoefficientSlots h d
    · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
      rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
        t e b (congrArg Subtype.val hb.symm), one_mul]
      simp only [coefficientProfileWidth, hz, hp, ite_false, ite_true]
    · rw [nonprincipalDilation_mem Subtype.val (canonicalPrincipalExponent h d) t e
        ((bounded_mem_nonprincipalCoefficientSlots h d e).mpr ⟨hz, hp⟩)]
      simp only [coefficientProfileWidth, hz, hp, ite_false]

theorem boundedProfile_polynomial_split (hd : 0 < h d) (ρ γ ε t : ℝ)
    (r : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℝ) :
    monomialArrayPolynomial Subtype.val (fun e =>
      coefficientProfileCenter (principalCoefficientSlots h d) γ e +
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ (t * ε) e * r e) =
      MvPolynomial.C (ρ * r (constantCoefficientSlot _ _)) +
      (∑ b, MvPolynomial.monomial (canonicalPrincipalExponent h d b)
        (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot h d b))) +
      ∑ e ∈ nonprincipalCoefficientSlots
          (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _)
          (canonicalPrincipalExponent h d),
        MvPolynomial.monomial e.val (t * (ε * r e)) := by
  classical
  let c := coefficientProfileCenter (principalCoefficientSlots (G := G) (B := B) h d) γ
  let w := coefficientProfileWidth (principalCoefficientSlots (G := G) (B := B) h d)
    (constantCoefficientSlot _ _) ρ γ ε
  have heq : (fun e => c e + coefficientProfileWidth (principalCoefficientSlots h d)
      (constantCoefficientSlot _ _) ρ γ (t * ε) e * r e) =
      (fun e => nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * c e +
        (nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * w e) * r e) := by
    funext e
    rw [boundedProfileWidth_dilation]
    congr 1
    exact boundedProfileCenter_dilation h d γ t e
  rw [heq, monomialArrayPolynomial_affine_dilated_split Subtype.val Subtype.val_injective
    (canonicalPrincipalExponent h d) (canonicalPrincipalExponent_injective h d hd)
    (canonicalPrincipalExponent_ne_zero h d hd) (principalCoefficientSlot h d) (fun _ => rfl)]
  have hc : (monomialArrayPolynomial Subtype.val (fun e => c e + w e * r e)).coeff 0 =
      ρ * r (constantCoefficientSlot _ _) := by
    rw [show (0 : SamplerTupleIndex G B h →₀ ℕ) =
      (constantCoefficientSlot (SamplerTupleIndex G B h) (h d)).val from rfl,
      monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth,
      constantCoefficientSlot_not_principal h d hd, ite_false, ite_true, zero_add]
  rw [hc]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b _
    have hp : principalCoefficientSlot h d b ∈ principalCoefficientSlots (G := G) h d :=
      (mem_principalCoefficientSlots h d _).mpr ⟨b, rfl⟩
    have hz : principalCoefficientSlot (G := G) h d b ≠ constantCoefficientSlot _ _ := by
      intro hz
      exact constantCoefficientSlot_not_principal h d hd (hz ▸ hp)
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]
  · apply Finset.sum_congr rfl
    intro e he
    obtain ⟨hz, hp⟩ := (bounded_mem_nonprincipalCoefficientSlots h d e).mp he
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hz, hp, ite_false, zero_add]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

omit [Fintype D] in
theorem unitProfilePrincipalSize_pos (d : D) : 0 < unitProfilePrincipalSize (B := B) d :=
  principalProfileSize_pos zero_lt_one _

theorem unitProfileTailSize_pos (d : D) : 0 < unitProfileTailSize (G := G) (B := B) h d :=
  tailProfileSize_pos zero_lt_one zero_lt_one _

omit [DecidablePred P] in
theorem partitionedProfileTail_unit_sum (d : {d // ¬P d}) :
    (∑ _e ∈ partitionedProfileTerms (G := G) (B := B) h P d,
      |unitProfileTailSize (G := G) (B := B) h d.val|) ≤ 1 := by
  have he := unitProfileTailSize_pos (G := G) (B := B) h d.val
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl 0
    (Fintype.card (SamplerCoefficientSlot G B h d.val))
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  rw [abs_of_pos he, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (Fintype.card (SamplerCoefficientSlot G B h d.val) : ℝ) *
        unitProfileTailSize (G := G) (B := B) h d.val :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) he.le
    _ ≤ 1 := by unfold unitProfileTailSize; nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

theorem unitProfilePrincipalLowerBound_le (d : D) :
    unitProfilePrincipalLowerBound B ≤ unitProfilePrincipalSize (B := B) d := by
  classical
  have hcard : Fintype.card (B d) ≤ ∑ a, Fintype.card (B a) :=
    Finset.single_le_sum (f := fun a : D => Fintype.card (B a))
      (fun a _ => Nat.zero_le _) (Finset.mem_univ d)
  unfold unitProfilePrincipalLowerBound unitProfilePrincipalSize principalProfileSize
  apply one_div_le_one_div_of_le (by positivity)
  have hcardR : (Fintype.card (B d) : ℝ) ≤ ((∑ a, Fintype.card (B a) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedContinuousProfileScales_pos (j : Fin m) (d) :
    0 < allocatedContinuousProfileScales B U basis S j d :=
  one_div_pos.mpr (monomialScale_pos _
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v)) d.val)

include hR hσ in
theorem allocatedContinuousProfileWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num))
    (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _) d

theorem allocatedLayerCenters_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerCenters B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileCenters B R j i d := by
  unfold allocatedLayerCenters allocatedArrayCenters allocatedContinuousProfileScales
    allocatedContinuousProfileCenters
  ring

theorem allocatedLayerWidths_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerWidths B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileWidths B R σ j i d := by
  unfold allocatedLayerWidths allocatedArrayWidths allocatedContinuousProfileScales
    allocatedContinuousProfileWidths
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPartitionedProfileJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_eq (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    allocatedAxisProfilePolynomial B R σ a r =
      monomialArrayPolynomial Subtype.val (fun e =>
        coefficientProfileCenter (principalCoefficientSlots (layerSamplerDegree I n) a)
          (principalProfileSize (R a.1) (Fintype.card (B a))) e +
        coefficientProfileWidth (principalCoefficientSlots (layerSamplerDegree I n) a)
          (constantCoefficientSlot _ _) (R a.1 / 4)
          (principalProfileSize (R a.1) (Fintype.card (B a)))
          (tailProfileSize (R a.1) (σ a.1)
            (Fintype.card (SamplerCoefficientSlot G B (layerSamplerDegree I n) a))) e * r e) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    simp only [allocatedAxisProfilePolynomial, allocatedContinuousProfileCenters,
      allocatedContinuousProfileWidths, layerContinuousPrincipalSlots_card]
    rfl
  | inr i =>
    simp only [allocatedAxisProfilePolynomial, allocatedIntegerProfileCenters,
      allocatedIntegerProfileWidths, layerIntegerPrincipalSlots_card]
    rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G : Type*} [Fintype D] [Fintype G]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop)

theorem activeTailRescale_principal (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (d : {d // ¬P d}) (b : B d.val) :
    activeTailRescale h P τ r ⟨d, principalCoefficientSlot h d.val b⟩ =
      r ⟨d, principalCoefficientSlot h d.val b⟩ := by
  unfold activeTailRescale
  rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d.val)
    (τ d.val) _ b rfl, one_mul]

theorem activeTailRescale_constant (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (d : {d // ¬P d}) :
    activeTailRescale h P τ r ⟨d, constantCoefficientSlot _ _⟩ =
      r ⟨d, constantCoefficientSlot _ _⟩ := by
  unfold activeTailRescale
  rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d.val)
    (τ d.val) _ rfl, one_mul]

theorem activeTailRescale_abs_le (τ : D → ℝ) (hτ : ∀ d, |τ d| ≤ 1)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) (hr : ∀ j, |r j| ≤ 1)
    (j : ActiveProfileCoefficientIndex G B h P) : |activeTailRescale h P τ r j| ≤ 1 := by
  have hd : |nonprincipalDilation Subtype.val (canonicalPrincipalExponent h j.1.val)
      (τ j.1.val) j.2| ≤ 1 := by
    unfold nonprincipalDilation
    split_ifs
    · exact hτ _
    · norm_num
  unfold activeTailRescale
  rw [abs_mul]
  exact (mul_le_mul hd (hr j) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem boundedProfileWidth_noise_rescale (d : D) (ρ γ ε σ t v : ℝ) (ht : t ≠ 0)
    (e : SamplerCoefficientSlot G B h d) :
    coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (t * ε) e * (nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) (σ / t) e * v) =
      coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (σ * ε) e * v := by
  classical
  by_cases hz : e = constantCoefficientSlot _ _
  · rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d)
      (σ / t) e (congrArg Subtype.val hz)]
    simp only [coefficientProfileWidth, hz, ite_true, one_mul]
  · by_cases hp : e ∈ principalCoefficientSlots h d
    · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
      rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
        (σ / t) e b (congrArg Subtype.val hb.symm)]
      simp only [coefficientProfileWidth, hz, hp, ite_false, ite_true, one_mul]
    · rw [nonprincipalDilation_mem Subtype.val (canonicalPrincipalExponent h d) (σ / t) e
        ((bounded_mem_nonprincipalCoefficientSlots h d e).mpr ⟨hz, hp⟩)]
      simp only [coefficientProfileWidth, hz, hp, ite_false]
      field_simp [ht]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

omit [∀ j, Fintype (I j)] in
theorem allocatedTailRatio_abs_le {t : ℝ} (ht : 0 < t) (hσ : ∀ j, |σ j| ≤ t)
    (a : LayerSamplerAxis I n) : |σ a.1 / t| ≤ 1 := by
  rw [abs_div, abs_of_pos ht]
  exact (div_le_one ht).mpr (hσ a.1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedProfilePolynomial
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)
variable {I : Type*}

theorem slicedProfileTailPolynomial_degree
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, (ξ k).totalDegree ≤ 1) :
    (slicedProfileTailPolynomial h d ε r ξ).totalDegree ≤ h d := by
  classical
  apply (polynomial_substitution_totalDegree_le _ ξ hξ ?_).trans (Nat.mul_one _).le
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans e.property

theorem slicedProfileTailPolynomial_mass
    (ε : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, realPolynomialMass (ξ k) ≤ 1) :
    realPolynomialMass (slicedProfileTailPolynomial h d ε r ξ) ≤
      (nonprincipalCoefficientSlots
        (Subtype.val : SamplerCoefficientSlot G B h d → _)
        (canonicalPrincipalExponent h d)).card * |ε| := by
  classical
  apply (realPolynomialMass_substitution_le _ ξ (M := 1) le_rfl hξ le_rfl).trans
  simp only [one_pow, mul_one]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _e ∈ nonprincipalCoefficientSlots
        (Subtype.val : SamplerCoefficientSlot G B h d → _) (canonicalPrincipalExponent h d),
        |ε| := by
      apply Finset.sum_le_sum
      intro e _
      rw [realPolynomialMass_monomial, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hr e)
    _ = _ := by simp

theorem slicedProfileTailPolynomial_unit_mass
    (r : SamplerCoefficientSlot G B h d → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ)
    (hξ : ∀ k, realPolynomialMass (ξ k) ≤ 1) :
    realPolynomialMass (slicedProfileTailPolynomial h d
      (unitProfileTailSize (G := G) (B := B) h d) r ξ) ≤ 1 := by
  apply (slicedProfileTailPolynomial_mass h d _ r hr ξ hξ).trans
  have he := partitionedProfileTail_unit_sum (G := G) (B := B) h (fun _ => False) ⟨d, by simp⟩
  simpa only [partitionedProfileTerms, Finset.sum_const, nsmul_eq_mul] using he

theorem slicedProfile_eval_split
    (hd : 0 < h d) (ρ γ ε t : ℝ) (r : SamplerCoefficientSlot G B h d → ℝ)
    (ξ : SamplerTupleIndex G B h → MvPolynomial I ℝ) (x : I → ℝ) :
    MvPolynomial.eval (fun k => MvPolynomial.eval x (ξ k))
      (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h d =>
        coefficientProfileCenter (principalCoefficientSlots h d) γ e +
          coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
            ρ γ (t * ε) e * r e)) =
      ρ * r (constantCoefficientSlot _ _) +
        (∑ b, (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot h d b)) *
          ∏ v, MvPolynomial.eval x (ξ (.inr ⟨d, b, v⟩))) +
        t * MvPolynomial.eval x (slicedProfileTailPolynomial h d ε r ξ) := by
  classical
  rw [boundedProfile_polynomial_split h d hd]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b _
    simp only [canonicalPrincipalExponent, productBlockExponent_monomial,
      map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    ring
  · simp only [slicedProfileTailPolynomial, map_sum, MvPolynomial.eval₂Hom_monomial,
      map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_monomial,
      Finsupp.prod, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)

local notation "Input" => (Σ e, B (axis e) × Fin (h (axis e)))
local notation "Output" => (Σ _e : E, Unit)

omit [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfileValue_mul
    (R ρ γ ε : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ) (t : ℝ) (x : Input → ℝ) :
    jointSlicedProfileValue h axis (fun d => R d * ρ d) (fun d => R d * γ d)
        (fun d => R d * ε d) r ξ t x =
      fun o => R (axis o.1) * jointSlicedProfileValue h axis ρ γ ε r ξ t x o := by
  classical
  funext o
  have hs : t * (R (axis o.1) * ε (axis o.1)) = R (axis o.1) * (t * ε (axis o.1)) := by ring
  unfold jointSlicedProfileValue
  simp_rw [hs, coefficientProfileCenter_mul, coefficientProfileWidth_mul, monomialArrayPolynomial_eval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

omit [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfileValue_unit_scale
    (R : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ) (t : ℝ) (x : Input → ℝ) :
    jointSlicedProfileValue h axis (fun d => R d / 4)
        (fun d => principalProfileSize (R d) (Fintype.card (B d)))
        (fun d => tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d))) r ξ t x =
      fun o => R (axis o.1) * jointSlicedProfileValue h axis (fun _ => 1 / 4)
        (unitProfilePrincipalSize (B := B)) (unitProfileTailSize (G := G) (B := B) h) r ξ t x o := by
  have hp (d : D) : principalProfileSize (R d) (Fintype.card (B d)) =
      R d * unitProfilePrincipalSize (B := B) d := by
    simpa only [unitProfilePrincipalSize, mul_one] using principalProfileSize_mul (R d) 1 (Fintype.card (B d))
  have ht (d : D) : tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d)) =
      R d * unitProfileTailSize (G := G) (B := B) h d := by
    simpa only [unitProfileTailSize, mul_one] using tailProfileSize_mul (R d) 1 1
      (Fintype.card (SamplerCoefficientSlot G B h d))
  simp_rw [hp, ht, div_eq_mul_inv, one_mul]
  exact jointSlicedProfileValue_mul h axis R (fun _ => 4⁻¹) _ _ r ξ t x

omit [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfileValue_split
    (hh : ∀ e, 0 < h (axis e)) (ρ γ ε : D → ℝ)
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (lower width : ∀ e, B (axis e) × Fin (h (axis e)) → ℝ)
    (hξ : ∀ e b i, ξ e (.inr ⟨axis e, b, i⟩) =
      MvPolynomial.C (lower e (b, i)) + MvPolynomial.C (width e (b, i)) * MvPolynomial.X ⟨e, b, i⟩)
    (t : ℝ) :
    jointSlicedProfileValue h axis ρ γ ε r ξ t = fun x =>
      jointSlicedProfileShift h axis ρ r +
        jointSlicedPrincipal (jointSlicedProfilePrincipal h axis γ r) lower width x +
        t • polynomialVectorMap (jointSlicedProfileTail h axis ε r ξ) x := by
  funext x o
  rw [jointSlicedProfileValue, slicedProfile_eval_split h (axis o.1) (hh o.1)]
  simp only [hξ, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_bounds
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) (b : B (axis e)) :
    unitProfilePrincipalSize (B := B) (axis e) ≤
      |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ∧
    |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ≤
      2 * unitProfilePrincipalSize (B := B) (axis e) := by
  have hγ := unitProfilePrincipalSize_pos (B := B) (axis e)
  obtain ⟨hl, hu⟩ := abs_le.mp (hr e (principalCoefficientSlot h (axis e) b))
  have hlo : unitProfilePrincipalSize (B := B) (axis e) ≤
      jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b := by
    unfold jointSlicedProfilePrincipal
    nlinarith
  rw [abs_of_nonneg (hγ.le.trans hlo)]
  refine ⟨hlo, ?_⟩
  unfold jointSlicedProfilePrincipal
  nlinarith

omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_mass
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) :
    (∑ b, |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b|) ≤ 1 := by
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl
    (Fintype.card (B (axis e))) 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  calc
    _ ≤ ∑ _b : B (axis e), 2 * unitProfilePrincipalSize (B := B) (axis e) :=
      Finset.sum_le_sum (fun b _ => (jointSlicedProfilePrincipal_unit_bounds h axis r hr e b).2)
    _ = 2 * principalProfileSize 1 (Fintype.card (B (axis e))) * Fintype.card (B (axis e)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitProfilePrincipalSize]
      ring
    _ ≤ 1 := by linarith

theorem jointSlicedProfileValue_unit_comparison
    {m : ℕ} (hh : ∀ e, 0 < h (axis e)) (hm : ∀ e, h (axis e) ≤ m)
    (ρ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (hr : ∀ e j, |r e j| ≤ 1)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (hξdegree : ∀ e k, (ξ e k).totalDegree ≤ 1)
    (hξmass : ∀ e k, realPolynomialMass (ξ e k) ≤ 1)
    (lower width : ∀ e, B (axis e) × Fin (h (axis e)) → ℝ)
    (hξ : ∀ e b i, ξ e (.inr ⟨axis e, b, i⟩) =
      MvPolynomial.C (lower e (b, i)) + MvPolynomial.C (width e (b, i)) * MvPolynomial.X ⟨e, b, i⟩)
    (hwidth : ∀ e p, |lower e p| + |width e p| ≤ 1)
    (b : ∀ e, B (axis e)) (i : ∀ e, Fin (h (axis e)))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ e, a ≤ unitProfilePrincipalSize (B := B) (axis e))
    (hw : ∀ e j, δ ≤ width e (b e, j))
    (hlower : ∀ e j, j ≠ i e → 0 ≤ lower e (b e, j))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (t : ℝ)
    (ht : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card E) m 1 a δ A η)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure Input)
        (fun x => jointSlicedProfileShift h axis ρ r +
          jointSlicedPrincipal (jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r)
            lower width x) φ -
      mappedTest (unitBoxMeasure Input)
        (jointSlicedProfileValue h axis ρ (unitProfilePrincipalSize (B := B))
          (unitProfileTailSize (G := G) (B := B) h) r ξ t) φ| ≤ η := by
  classical
  rw [jointSlicedProfileValue_split h axis hh ρ _ _ r ξ lower width hξ t]
  apply jointSlicedPrincipal_polynomial_tail_comparison _ lower width b i
    (by simpa only [Fintype.card_fin] using hm) zero_le_one zero_le_one ha hδ hδone hη A hA hwidth
    (jointSlicedProfilePrincipal_unit_mass h axis r hr)
    (fun e => (hprincipal e).trans (jointSlicedProfilePrincipal_unit_bounds h axis r hr e (b e)).1)
    hw hlower _ _ _ t ht _ φ hφ hφone
  · intro o v
    exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      ((slicedProfileTailPolynomial_degree h (axis o.1) _ (r o.1) (ξ o.1) (hξdegree o.1)).trans (hm o.1))
  · intro o
    exact slicedProfileTailPolynomial_unit_mass h (axis o.1) (r o.1) (hr o.1) (ξ o.1) (hξmass o.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_principal_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) (b : B a) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff
        (canonicalPrincipalExponent (layerSamplerDegree I n) a b) =
      3 * principalProfileSize (R a.1) (Fintype.card (B a)) / 2 +
        principalProfileSize (R a.1) (Fintype.card (B a)) / 2 *
          r (principalCoefficientSlot (layerSamplerDegree I n) a b) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot (layerSamplerDegree I n) a b).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  have hp : principalCoefficientSlot (layerSamplerDegree I n) a b ∈
      principalCoefficientSlots (G := G) (layerSamplerDegree I n) a :=
    (mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩
  have hz : principalCoefficientSlot (G := G) (layerSamplerDegree I n) a b ≠
      constantCoefficientSlot _ _ := by
    intro hz
    exact constantCoefficientSlot_not_principal (layerSamplerDegree I n) a
      (Nat.zero_lt_succ _) (hz ▸ hp)
  simp only [coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]

theorem allocatedAxisProfilePolynomial_constant_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff 0 =
      R a.1 / 4 * r (constantCoefficientSlot _ _) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot (LayerSamplerVariables G I n B) (layerSamplerDegree I n a)).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  simp only [coefficientProfileCenter, coefficientProfileWidth,
    constantCoefficientSlot_not_principal (layerSamplerDegree I n) a (Nat.zero_lt_succ _),
    ite_false, ite_true, zero_add]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathPrincipal_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathPrincipal B P R σ r =
      jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
        (fun a e => r ⟨a, e⟩) := by
  funext a b
  rw [allocatedFixedPathPrincipal, allocatedAxisProfilePolynomial_principal_coeff]
  have hs : principalProfileSize (R a.val.1) (Fintype.card (B a.val)) =
      R a.val.1 * unitProfilePrincipalSize (B := B) a.val := by
    simpa only [unitProfilePrincipalSize, mul_one] using
      principalProfileSize_mul (R a.val.1) 1 (Fintype.card (B a.val))
  rw [hs]
  unfold jointSlicedProfilePrincipal
  field_simp [hR]

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathShift_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathShift B P R σ r =
      fun a => (1 / 4 : ℝ) * r ⟨a, constantCoefficientSlot _ _⟩ := by
  funext a
  rw [allocatedFixedPathShift, allocatedAxisProfilePolynomial_constant_coeff]
  field_simp [hR]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRelativeChildSliceGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleProfileNoise_polynomial (sample : Sample) (a : LayerSamplerAxis I n) :
    allocatedAxisProfilePolynomial B R σ a (allocatedSampleProfileNoise B U basis S sample a) =
      monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample a) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    unfold allocatedAxisProfilePolynomial
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [allocatedSampleProfileNoise]
    field_simp [(allocatedContinuousProfileWidths_pos B hR hσ j i e).ne']
    ring
  | inr i =>
    unfold allocatedAxisProfilePolynomial
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [allocatedSampleProfileNoise]
    field_simp [(allocatedIntegerProfileWidths_pos B hR hσ j i e).ne']
    ring

include hR hσ in
theorem allocatedSampleProfileNoise_continuous_bound (sample : Sample) (j : Fin m) (i : I j)
    (hs : affineProductProfile (allocatedLayerCenters B U basis S j i)
      (allocatedLayerWidths B U basis S j i) ((sample j).1 i) ≠ 0)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inl i⟩ e| ≤ 1 := by
  have he := (Finset.prod_ne_zero_iff.mp hs) e (Finset.mem_univ e)
  rw [allocatedLayerCenters_scale, allocatedLayerWidths_scale] at he
  have hscale := allocatedContinuousProfileScales_pos B U basis S j e
  have hwidth := allocatedContinuousProfileWidths_pos B hR hσ j i e
  have hb := affineProbabilityProfile_support _ (mul_pos hscale hwidth) he
  have hn : |(sample j).1 i e / allocatedContinuousProfileScales B U basis S j e -
      allocatedContinuousProfileCenters B R j i e| ≤
      allocatedContinuousProfileWidths B R σ j i e := by
    have heq : (sample j).1 i e / allocatedContinuousProfileScales B U basis S j e -
        allocatedContinuousProfileCenters B R j i e =
        ((sample j).1 i e - allocatedContinuousProfileScales B U basis S j e *
          allocatedContinuousProfileCenters B R j i e) / allocatedContinuousProfileScales B U basis S j e := by
      field_simp
    rw [heq, abs_div, abs_of_pos hscale]
    apply (div_le_iff₀ hscale).mpr
    nlinarith
  dsimp only [allocatedSampleProfileNoise, allocatedSampleNormalizedCoefficients]
  rw [abs_div, abs_of_pos hwidth]
  exact (div_le_one hwidth).mpr hn

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleProfileNoise_active_integer_coordinate_bound
    (sample : Sample) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (e : BoundedCoefficientExponent vars (j.val + 1))
    (he : (sample j).2 i e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inr i⟩ e| ≤ 1 := by
  have hb := integerPolynomialCoordinatePMF_active_profile_bound
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val + 1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hK := basisAxisScale_pos (basis j) i) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j / 4)
    (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent vars (j.val + 1))))
    (hρ := div_pos (hR j) (by norm_num)) (hγ := principalProfileSize_pos (hR j) _)
    (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (hj₀ := layerIntegerPrincipalSlots_not_constant B j i) (he₀ := rfl)
    (hprincipal := layerSamplerSides_integer_principal B U basis R S.value j i)
    hactive e he
  have hb' : |allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
      allocatedIntegerProfileCenters B R j i e| ≤ allocatedIntegerProfileWidths B R σ j i e := by
    simpa only [allocatedSampleNormalizedCoefficients, allocatedIntegerProfileScales,
      allocatedIntegerProfileCenters, allocatedIntegerProfileWidths,
      div_div_eq_mul_div, div_mul_eq_mul_div] using hb
  have hw := allocatedIntegerProfileWidths_pos B hR hσ j i e
  change |(allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
    allocatedIntegerProfileCenters B R j i e) / allocatedIntegerProfileWidths B R σ j i e| ≤ 1
  rw [abs_div, abs_of_pos hw]
  exact (div_le_one hw).mpr hb'

include hR hσ in
theorem allocatedSampleProfileNoise_active_integer_bound
    (sample : Sample) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hs : ∀ e, (sample j).2 i e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inr i⟩ e| ≤ 1 :=
  allocatedSampleProfileNoise_active_integer_coordinate_bound B U basis hR hσ S sample j i hactive e (hs e)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (P : LayerSamplerAxis I n → Prop)

include hR hσ in
theorem allocatedFixedPathPrincipal_of_restricted_sample (sample : Sample)
    (a : {a // ¬P a}) (b : B a.val) :
    allocatedFixedPathPrincipal B P R σ (allocatedSampleRestrictedProfileNoise B U basis S P sample) a b =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (principalCoefficientSlot degree a.val b) / R a.val.1 := by
  unfold allocatedFixedPathPrincipal
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot degree a.val b).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

include hR hσ in
theorem allocatedFixedPathShift_of_restricted_sample (sample : Sample) (a : {a // ¬P a}) :
    allocatedFixedPathShift B P R σ (allocatedSampleRestrictedProfileNoise B U basis S P sample) a =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (constantCoefficientSlot vars (degree a.val)) / R a.val.1 := by
  unfold allocatedFixedPathShift
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot vars (degree a.val)).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleLiftMap_apply (sample : Sample) (x : Input → ℝ) (o : Output) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample x o =
      allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (constantCoefficientSlot vars (degree o.1.val)) / R o.1.val.1 +
      ∑ b, (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (principalCoefficientSlot degree o.1.val b) / R o.1.val.1) *
        ∏ v, (lower o.1 (b, v) + width o.1 (b, v) * x ⟨o.1, b, v⟩) := rfl

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

include hR hσ in
theorem allocatedOriginalSamplePrincipal_eq_fixedPath (sample : Sample) :
    allocatedOriginalSamplePrincipal B U basis S sample =
      allocatedFixedPathPrincipal B short R σ
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext a b
  exact (allocatedFixedPathPrincipal_of_restricted_sample B U basis hR hσ S short sample a b).symm

include hR hσ in
theorem allocatedOriginalSampleShift_eq_fixedPath (sample : Sample) :
    allocatedOriginalSampleShift B U basis S sample =
      allocatedFixedPathShift B short R σ
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext a
  exact (allocatedFixedPathShift_of_restricted_sample B U basis hR hσ S short sample a).symm

include hR hσ in
theorem allocatedOriginalSampleLiftMap_eq_fixedPath (sample : Sample) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample =
      allocatedFixedPathLiftMap B short R σ lower width
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext x
  unfold allocatedOriginalSampleLiftMap allocatedFixedPathLiftMap
  rw [allocatedOriginalSamplePrincipal_eq_fixedPath B U basis S hR hσ sample,
    allocatedOriginalSampleShift_eq_fixedPath B U basis S hR hσ sample]

theorem allocatedOriginalSampleLiftMap_measurable :
    Measurable (fun p : Sample × (Input → ℝ) =>
      allocatedOriginalSampleLiftMap B U basis S lower width p.1 p.2) := by
  apply measurable_pi_iff.mpr
  rintro ⟨⟨⟨j, i⟩, ha⟩, u⟩
  cases i with
  | inl i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop
  | inr i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleSliceSubstitution_principal
    (a : Active) (b : B a.val) (i : Fin (degree a.val)) :
    allocatedOriginalSampleSliceSubstitution B U basis S x u lower width (.inr ⟨a.val, b, i⟩) =
      MvPolynomial.C (lower a (b, i)) +
        MvPolynomial.C (width a (b, i)) * MvPolynomial.X ⟨a, b, i⟩ := by
  simp only [allocatedOriginalSampleSliceSubstitution, a.property, ↓reduceDIte]

theorem allocatedOriginalSampleSliceSubstitution_degree (k : vars) :
    (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k).totalDegree ≤ 1 := by
  rcases k with g | ⟨a, b, i⟩
  · simp [allocatedOriginalSampleSliceSubstitution]
  · by_cases ha : short a
    · simp [allocatedOriginalSampleSliceSubstitution, ha]
    · simp only [allocatedOriginalSampleSliceSubstitution, ha, ↓reduceDIte]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem allocatedOriginalSampleSliceSubstitution_mass
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1) (k : vars) :
    realPolynomialMass (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k) ≤ 1 := by
  rcases k with g | ⟨a, b, i⟩
  · have hb := (norm_le_pi_norm (fun t => (x g t : ℝ) / (S.value : ℝ)) none).trans
      (integerScalarCubeBox_normalized_norm_le S.positive (x g))
    simpa only [allocatedOriginalSampleSliceSubstitution, realPolynomialMass_C, Real.norm_eq_abs] using hb
  · by_cases ha : short a
    · have hb := (norm_le_pi_norm
        (fun t => (u ⟨⟨a, ha⟩, b, i⟩ t : ℝ) / (sides ⟨a, b, i⟩ : ℝ)) none).trans
        (integerScalarCubeBox_normalized_norm_le (allocatedPrincipalSides_pos B U basis S ⟨a, b, i⟩)
          (u ⟨⟨a, ha⟩, b, i⟩))
      simpa only [allocatedOriginalSampleSliceSubstitution, ha, ↓reduceDIte,
        realPolynomialMass_C, Real.norm_eq_abs] using hb
    · simp only [allocatedOriginalSampleSliceSubstitution, ha, ↓reduceDIte]
      apply (realPolynomialMass_add_le _ _).trans
      apply le_trans _ (hwidth ⟨a, ha⟩ (b, i))
      rw [realPolynomialMass_C]
      apply add_le_add le_rfl
      simpa only [realPolynomialMass_X, mul_one] using
        realPolynomialMass_C_mul_le (width ⟨a, ha⟩ (b, i))
          (MvPolynomial.X (⟨⟨a, ha⟩, b, i⟩ : Input))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "grid" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleRestrictedProfileNoise_short_abs_le (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (e : ActiveProfileCoefficientIndex G B degree grid) :
    |allocatedSampleRestrictedProfileNoise B U basis S grid sample e| ≤ 1 := by
  rcases e with ⟨⟨⟨j, i⟩, ha⟩, e⟩
  have hrows := (mixedArraySupported_iff_rows _ _ _ (sample j)).mp (hs j)
  cases i with
  | inl i =>
    exact allocatedSampleProfileNoise_continuous_bound B U basis hR hσ S sample j i (hrows.1 i) e
  | inr i =>
    exact allocatedSampleProfileNoise_active_integer_bound B U basis hR hσ S sample j i
      (Nat.lt_of_not_ge ha) (hrows.2 i) e

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

include hR hσ in
theorem allocatedOriginalSampleFullSliceMap_eq_profile (sample : Sample) {t : ℝ} (ht : t ≠ 0) :
    allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample =
      jointSlicedProfileValue degree Subtype.val (fun _ => 1 / 4)
        (unitProfilePrincipalSize (B := B)) (unitProfileTailSize (G := G) (B := B) degree)
        (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩)
        (fun _ => allocatedOriginalSampleSliceSubstitution B U basis S x u lower width) t := by
  let r := noise sample
  let coeff := fun (a : Active) e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩
  let ξ := fun _ : Active => allocatedOriginalSampleSliceSubstitution B U basis S x u lower width
  have htail (j : Fin m) (N : ℕ) : tailProfileSize (R j) (σ j) N =
      σ j * tailProfileSize (R j) 1 N := by unfold tailProfileSize; ring
  have hpoly (a : Active) :
      monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B degree a.val =>
        coefficientProfileCenter (principalCoefficientSlots degree a.val)
            (principalProfileSize (R a.val.1) (Fintype.card (B a.val))) e +
          coefficientProfileWidth (principalCoefficientSlots degree a.val) (constantCoefficientSlot _ _)
            (R a.val.1 / 4) (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
            (t * tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val))) e *
              coeff a e) =
        monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample a.val) := by
    rw [← allocatedSampleProfileNoise_polynomial B U basis hR hσ S sample a.val,
      allocatedAxisProfilePolynomial_eq]
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    rw [htail]
    unfold coeff allocatedOriginalSampleTailNoise activeTailRescale
    congr 1
    exact boundedProfileWidth_noise_rescale degree a.val (R a.val.1 / 4)
      (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
      (tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val)))
      (σ a.val.1) t (allocatedSampleProfileNoise B U basis S sample a.val e) ht e
  funext y o
  change MvPolynomial.eval (fun k => MvPolynomial.eval y (ξ o.1 k)) _ / R o.1.val.1 = _
  rw [← hpoly o.1]
  change jointSlicedProfileValue degree Subtype.val (fun a => R a.1 / 4)
      (fun a => principalProfileSize (R a.1) (Fintype.card (B a)))
      (fun a => tailProfileSize (R a.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a)))
      coeff ξ t y o / R o.1.val.1 = _
  rw [jointSlicedProfileValue_unit_scale degree Subtype.val (fun a => R a.1) coeff ξ t y]
  exact mul_div_cancel_left₀ _ (hR o.1.val.1).ne'

include hR hσ in
theorem allocatedOriginalSampleLiftMap_eq_tail_ideal (sample : Sample) (t : ℝ) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample =
      fun y => jointSlicedProfileShift degree Subtype.val (fun _ => 1 / 4)
          (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩) +
        jointSlicedPrincipal
          (jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
            (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩)) lower width y := by
  rw [allocatedOriginalSampleLiftMap_eq_fixedPath B U basis S lower width hR hσ sample]
  unfold allocatedFixedPathLiftMap
  rw [allocatedFixedPathPrincipal_eq B short R σ (fun j => (hR j).ne'),
    allocatedFixedPathShift_eq B short R σ (fun j => (hR j).ne')]
  have hc : jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
      (fun a e => noise sample ⟨a, e⟩) =
      jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
        (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩) := by
    funext a b
    simp only [jointSlicedProfilePrincipal, allocatedOriginalSampleTailNoise, activeTailRescale_principal]
  have hs : (fun o : Output => (1 / 4 : ℝ) * noise sample ⟨o.1, constantCoefficientSlot _ _⟩) =
      jointSlicedProfileShift degree Subtype.val (fun _ => 1 / 4)
        (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩) := by
    funext o
    simp only [jointSlicedProfileShift, allocatedOriginalSampleTailNoise, activeTailRescale_constant]
  rw [hc, hs]

theorem allocatedOriginalSampleFullSliceMap_measurable (sample : Sample) :
    Measurable (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample) := by
  apply measurable_pi_iff.mpr
  intro o
  have hi : Continuous (fun y : Input → ℝ => fun k => MvPolynomial.eval y
      (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k)) :=
    continuous_pi (fun k => MvPolynomial.continuous_eval _)
  exact (((MvPolynomial.continuous_eval
    (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val))).comp hi).div_const
      (R o.1.val.1)).measurable

include hR hσ in
theorem allocatedOriginalSample_slice_real_perturbation
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (b : ∀ a : Active, B a.val)
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hw : ∀ a i, δ ≤ width a (b a, i))
    (hlower : ∀ a i, 0 ≤ lower a (b a, i))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hsmall : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) δ A η)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ z, ‖φ z‖ ≤ 1) :
    |(∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input| ≤ η := by
  let coeff := fun (a : Active) e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩
  have hcoeff (a : Active) (e : SamplerCoefficientSlot G B degree a.val) : |coeff a e| ≤ 1 :=
    activeTailRescale_abs_le degree short (fun a => σ a.1 / t)
      (allocatedTailRatio_abs_le ht hσbound) (noise sample)
      (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs) ⟨a, e⟩
  have he := jointSlicedProfileValue_unit_comparison degree (Subtype.val : Active → LayerSamplerAxis I n)
    (m := m) (fun a => Nat.zero_lt_succ _) (fun a => Nat.succ_le_of_lt a.val.1.isLt)
    (fun _ => 1 / 4) coeff hcoeff
    (fun _ => allocatedOriginalSampleSliceSubstitution B U basis S x u lower width)
    (fun _ k => allocatedOriginalSampleSliceSubstitution_degree B U basis S x u lower width k)
    (fun _ k => allocatedOriginalSampleSliceSubstitution_mass B U basis S x u lower width hwidth k)
    lower width
    (fun a b i => allocatedOriginalSampleSliceSubstitution_principal B U basis S x u lower width a b i)
    hwidth b (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (unitProfilePrincipalLowerBound_pos B) hδ hδone hη
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw (fun a i _ => hlower a i)
    A hA t hsmall φ hφ hbound
  rw [allocatedOriginalSampleLiftMap_eq_tail_ideal B U basis hR hσ S lower width sample t,
    allocatedOriginalSampleFullSliceMap_eq_profile B U basis hR hσ S x u lower width sample ht.ne']
  exact he

include hR hσ in
theorem allocatedOriginalSample_slice_complex_perturbation_s2_oai
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (b : ∀ a : Active, B a.val)
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hw : ∀ a i, δ ≤ width a (b a, i))
    (hlower : ∀ a i, 0 ≤ lower a (b a, i))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hsmall : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) δ A η)
    (φ : (Output → ℝ) → ℂ) (hφ : Measurable φ) (hbound : ∀ z, ‖φ z‖ ≤ 1) :
    ‖(∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input‖ ≤ 2 * η := by
  let f := fun y => φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
  let g := fun y => φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
  have hif : Integrable f (unitBoxMeasure Input) :=
    ⟨(hφ.comp ((allocatedOriginalSampleLiftMap_measurable B U basis S lower width).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hbound _))⟩
  have hig : Integrable g (unitBoxMeasure Input) :=
    ⟨(hφ.comp (allocatedOriginalSampleFullSliceMap_measurable B U basis S x u lower width sample)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hbound _))⟩
  have hre := allocatedOriginalSample_slice_real_perturbation B U basis hR hσ S x u lower width
    sample hs hwidth b hδ hδone hη hw hlower A hA ht hσbound hsmall
    (fun y => (φ y).re) (Complex.measurable_re.comp hφ)
    (fun y => (Complex.abs_re_le_norm _).trans (hbound y))
  have him := allocatedOriginalSample_slice_real_perturbation B U basis hR hσ S x u lower width
    sample hs hwidth b hδ hδone hη hw hlower A hA ht hσbound hsmall
    (fun y => (φ y).im) (Complex.measurable_im.comp hφ)
    (fun y => (Complex.abs_im_le_norm _).trans (hbound y))
  have hfre : (∫ y, f y ∂unitBoxMeasure Input).re = ∫ y, (f y).re ∂unitBoxMeasure Input := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hif).symm
  have hgre : (∫ y, g y ∂unitBoxMeasure Input).re = ∫ y, (g y).re ∂unitBoxMeasure Input := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hig).symm
  have hfim : (∫ y, f y ∂unitBoxMeasure Input).im = ∫ y, (f y).im ∂unitBoxMeasure Input := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hif).symm
  have hgim : (∫ y, g y ∂unitBoxMeasure Input).im = ∫ y, (g y).im ∂unitBoxMeasure Input := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hig).symm
  change ‖(∫ y, f y ∂unitBoxMeasure Input) - ∫ y, g y ∂unitBoxMeasure Input‖ ≤ _
  calc
    _ ≤ |((∫ y, f y ∂unitBoxMeasure Input) - ∫ y, g y ∂unitBoxMeasure Input).re| +
        |((∫ y, f y ∂unitBoxMeasure Input) - ∫ y, g y ∂unitBoxMeasure Input).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ η + η := by
      apply add_le_add
      · rw [Complex.sub_re, hfre, hgre]
        exact hre
      · rw [Complex.sub_im, hfim, hgim]
        exact him
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_slice_complex_perturbation_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_slice_complex_perturbation_s2_oai.{u_1, u_2, u_3, u_4}
