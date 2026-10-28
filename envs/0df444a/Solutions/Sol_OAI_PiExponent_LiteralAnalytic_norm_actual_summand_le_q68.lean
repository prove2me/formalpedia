-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:11:11.96399+00:00
-- url     : https://prove2.me/submissions/4523c1bd-385a-43a6-bc7e-b2e53c81a710

import Mathlib
import Definitions.Def_OAIQ068A009
import Definitions.Def_OAIQ068A025
import Theorems.Thm_OAI_PiExponent_AnalyticCollision_translated_row_determinant_exp_bound_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_AnalyticCollision
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Complex Finset

namespace PiExponent.AnalyticCollision

theorem differentiable_exponentialMonomial (b h : ℂ) (d : ℕ) :
    Differentiable ℂ (exponentialMonomial b h d) := by
  exact ((Complex.differentiable_exp.comp (differentiable_id.const_mul h)).const_mul b).mul
    (differentiable_id.pow d)

theorem norm_exponentialMonomial_le (b h : ℂ) (d : ℕ) {z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖exponentialMonomial b h d z‖ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ d := by
  unfold exponentialMonomial
  simp only [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg b)
    exact (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (by simpa only [norm_mul] using mul_le_mul_of_nonneg_left hz (norm_nonneg h)))
  · exact pow_le_pow_left₀ (norm_nonneg z) hz d
  · positivity
  · exact pow_nonneg hR d

theorem norm_rowTest_le {f : ℂ → ℂ} {D : ℝ}
    (hD : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖f t‖ ≤ D) (ell : ℕ) :
    ‖rowTest ell f‖ ≤ (2 : ℝ) ^ ell * D := by
  unfold rowTest
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 / 2 : ℝ) * (2 ^ ell * (2 * D)) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR]
      norm_num only [one_div, inv_div, div_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD z hz) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem period_center_radius_bound {K j : ℕ} (hK : 0 < K) (hj : j < K) :
    ‖(j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ + 3 / 4 ≤ (100 * (K : ℝ)) / 2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj.le
  have hnorm : ‖(j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ =
      (j : ℝ) * (2 * Real.pi) := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
  have hprod : (j : ℝ) * (2 * Real.pi) ≤ (K : ℝ) * 8 :=
    mul_le_mul hjK hpi (by positivity) (by positivity)
  linarith

theorem norm_exponentialMonomial_le_exp_budget (b h : ℂ) (d A : ℕ)
    {z : ℂ} {R H w0 wstar : ℝ} (hR : 1 ≤ R) (hH : 0 ≤ H)
    (hw0 : 0 < w0) (hws : 0 < wstar) (hz : ‖z‖ ≤ R)
    (hb : ‖b‖ ≤ (2 : ℝ) ^ A) (hh : ‖h‖ ≤ H / w0)
    (hd : d ≤ A) (hA : (A : ℝ) ≤ H / wstar) :
    ‖exponentialMonomial b h d z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have h2R : 0 < 2 * R := by positivity
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ d := norm_exponentialMonomial_le b h d hR0 hz
    _ ≤ (2 : ℝ) ^ A * Real.exp ((H / w0) * R) * R ^ A := by
      apply mul_le_mul
      · exact mul_le_mul hb (Real.exp_le_exp.mpr
          (mul_le_mul hh le_rfl hR0 (div_nonneg hH hw0.le)))
          (Real.exp_pos _).le (by positivity)
      · exact pow_le_pow_right₀ hR hd
      · positivity
      · positivity
    _ = Real.exp ((H / w0) * R + (A : ℝ) * Real.log (2 * R)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log h2R, mul_pow]
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul hA (le_refl _) hlog (div_nonneg hH hws.le)
      calc
        _ ≤ (H / w0) * R + (H / wstar) * Real.log (2 * R) := add_le_add le_rfl ha
        _ = _ := by ring

end PiExponent.AnalyticCollision

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_CollisionCombinatorics
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

theorem sum_multiplicity_eq_card_filter {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) :
    ∑ a ∈ groups, multiplicity rows group a =
      (rows.filter fun i => group i ∈ groups).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter rows groups group

theorem cutoff_mul_high_count_le_sum {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) (cutoff : ℝ)
    (hnonneg : ∀ i ∈ rows, 0 ≤ weight i) :
    cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) ≤
      ∑ i ∈ rows, weight i := by
  classical
  calc
    _ = ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), cutoff := by
      simp [mul_comm]
    _ ≤ ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ rows, weight i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ rows)
      intro i hi _
      exact hnonneg i hi

theorem sum_weight_ge_of_low_count_le {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) {cutoff η : ℝ}
    (hcutoff : 0 ≤ cutoff) (hnonneg : ∀ i ∈ rows, 0 ≤ weight i)
    (hlow : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) ≤
      η * rows.card) :
    cutoff * (1 - η) * rows.card ≤ ∑ i ∈ rows, weight i := by
  classical
  have hcard : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) +
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) = rows.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := rows)
      (fun i => weight i ≤ cutoff))
  have hhigh : (1 - η) * rows.card ≤
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) := by nlinarith
  calc
    _ = cutoff * ((1 - η) * rows.card) := by ring
    _ ≤ cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) :=
      mul_le_mul_of_nonneg_left hhigh hcutoff
    _ ≤ ∑ i ∈ rows, weight i := cutoff_mul_high_count_le_sum rows weight cutoff hnonneg

end PiExponent.Collision

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RowTranslation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial

section FiniteExpansion
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

omit [Fintype σ] [DecidableEq σ] in
theorem shifted_X_pow (c : σ → R) (i : σ) (n : ℕ) :
    (X i + C (c i)) ^ n =
      ∑ b : Fin (n + 1), C ((n.choose b : R) * c i ^ (n - b)) * X i ^ (b : ℕ) := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem shifted_product_expansion (c : σ → R) (a : σ → ℕ) :
    (∏ i, (X i + C (c i)) ^ a i) =
      ∑ b : (∀ i, Fin (a i + 1)),
        C (∏ i, ((a i).choose (b i) : R) * c i ^ (a i - b i)) *
          monomial (multiIndex (fun i => (b i : ℕ))) 1 := by
  simp_rw [shifted_X_pow]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, ← map_prod, prod_X_pow]
  have hidx : Finsupp.indicator Finset.univ (fun i _ => (b i : ℕ)) =
      multiIndex (fun i => (b i : ℕ)) := by
    ext i
    simp [Finsupp.indicator]
  rw [hidx]

omit [DecidableEq σ] in
theorem shift_monomial_one (c : σ → R) (a : σ →₀ ℕ) :
    shift c (monomial a 1) = ∏ i, (X i + C (c i)) ^ a i := by
  simp only [shift, eval₂Hom_monomial, map_one, one_mul]
  exact a.prod_fintype _ (fun i => pow_zero _)

theorem shiftCoefficient_eq (c : σ → R) (β a : σ →₀ ℕ) :
    shiftCoefficient c β a = ∏ i, ((a i).choose (β i) : R) * c i ^ (a i - β i) := by
  classical
  rw [shiftCoefficient, shift_monomial_one, shifted_product_expansion, coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  by_cases h : ∀ i, β i ≤ a i
  · let b₀ : ∀ i, Fin (a i + 1) := fun i => ⟨β i, Nat.lt_succ_of_le (h i)⟩
    have hidx : multiIndex (fun i => (b₀ i : ℕ)) = β := by ext i; simp [b₀]
    rw [Finset.sum_eq_single b₀]
    · simp [hidx, b₀]
    · intro b hb hne
      have hidx' : multiIndex (fun i => (b i : ℕ)) ≠ β := by
        intro he
        apply hne
        funext i
        apply Fin.ext
        have hi := congrArg (fun d : σ →₀ ℕ => d i) he
        simpa [b₀] using hi
      simp [hidx']
    · simp
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hright : (∏ j, ((a j).choose (β j) : R) * c j ^ (a j - β j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hright]
    apply Finset.sum_eq_zero
    intro b hb
    have hidx : multiIndex (fun j => (b j : ℕ)) ≠ β := by
      intro he
      have hi' := congrArg (fun d : σ →₀ ℕ => d i) he
      have hbi : (b i : ℕ) = β i := by simpa using hi'
      have hlt := (b i).isLt
      omega
    simp [hidx]

end FiniteExpansion

section FormalSeriesRow
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

omit [DecidableEq σ] in
theorem rowScalar_ne_zero_le (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ)
    (h : rowScalar ε τ β a d k ≠ 0) : β ≤ a := by
  intro i
  by_contra hn
  have hi : a i < β i := by omega
  have hp : (∏ j, (a j).choose (β j) * (a j - β j).choose (d j) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]
  exact h (by simp [rowScalar, hp])

end FormalSeriesRow

section FiniteExpansion
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem choose_product_le_four_pow (a β d : ℕ) :
    a.choose β * (a - β).choose d ≤ 4 ^ a := by
  calc
    a.choose β * (a - β).choose d ≤ 2 ^ a * 2 ^ (a - β) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ ≤ 2 ^ a * 2 ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    _ = 4 ^ a := by rw [← mul_pow]; norm_num

omit [DecidableEq σ] in
theorem multi_choose_product_le_four_pow (a β d : σ → ℕ) :
    (∏ i, (a i).choose (β i) * (a i - β i).choose (d i)) ≤
      4 ^ (∑ i, a i) := by
  calc
    _ ≤ ∏ i, 4 ^ a i := Finset.prod_le_prod' (fun i hi => choose_product_le_four_pow _ _ _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _


omit [DecidableEq σ] in
theorem norm_rowScalar_le (ε : σ → ℂ) (τ : σ → PowerSeries ℂ)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (B : ℝ)
    (hτ : ‖PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ))‖ ≤ B) :
    ‖rowScalar ε τ β a d k‖ ≤
      (4 : ℝ) ^ (∑ i, a i) * (∏ i, ‖ε i‖ ^ (a i - β i - d i)) * B := by
  have hbin : ((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℝ) ≤
      (4 : ℝ) ^ (∑ i, a i) := by
    exact_mod_cast multi_choose_product_le_four_pow (fun i => a i) (fun i => β i) (fun i => (d i : ℕ))
  simp only [rowScalar, norm_mul, norm_prod, norm_pow, Complex.norm_natCast]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hbin (by positivity)) hτ
    (norm_nonneg _) (by positivity)

end FiniteExpansion

variable {R : Type*} [CommRing R]

theorem order_tail (T : ℕ) (f : PowerSeries R) :
    (T : ℕ∞) ≤ (tail T f).order := by
  apply PowerSeries.nat_le_order
  exact fun k hk => coeff_tail_of_lt T k f hk

theorem order_tail_prod {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) :
    ((∑ i ∈ s, d i * T i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, tail (T i) (f i) ^ d i).order := by
  calc
    ((∑ i ∈ s, d i * T i : ℕ) : ℕ∞) = ∑ i ∈ s, d i • (T i : ℕ∞) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, d i • (tail (T i) (f i)).order := by
      exact Finset.sum_le_sum (fun i hi => nsmul_le_nsmul_right (order_tail _ _) _)
    _ ≤ ∑ i ∈ s, (tail (T i) (f i) ^ d i).order := by
      exact Finset.sum_le_sum (fun i hi => PowerSeries.le_order_pow _ _)
    _ ≤ (∏ i ∈ s, tail (T i) (f i) ^ d i).order := PowerSeries.le_order_prod _ _

theorem tail_budget_nat {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) (k : ℕ)
    (hk : PowerSeries.coeff k (∏ i ∈ s, tail (T i) (f i) ^ d i) ≠ 0) :
    ∑ i ∈ s, d i * T i ≤ k := by
  exact_mod_cast (order_tail_prod s T d f).trans (PowerSeries.order_le k hk)

theorem tail_weight_budget {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) (k : ℕ) (w : ι → ℝ) (v F : ℝ)
    (hv : 0 ≤ v) (hF : 0 < F)
    (hT : ∀ i ∈ s, F * w i ≤ v * T i)
    (hk : PowerSeries.coeff k (∏ i ∈ s, tail (T i) (f i) ^ d i) ≠ 0) :
    ∑ i ∈ s, (d i : ℝ) * w i ≤ v * k / F := by
  apply (le_div_iff₀ hF).2
  calc
    (∑ i ∈ s, (d i : ℝ) * w i) * F =
        ∑ i ∈ s, (d i : ℝ) * (F * w i) := by rw [Finset.sum_mul]; congr 1; ext i; ring
    _ ≤ ∑ i ∈ s, (d i : ℝ) * (v * T i) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hT i hi) (Nat.cast_nonneg _))
    _ = v * (∑ i ∈ s, (d i * T i : ℕ) : ℕ) := by
      simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ v * k := mul_le_mul_of_nonneg_left (by exact_mod_cast tail_budget_nat s T d f k hk) hv

end PiExponent.RowTranslation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LogTailAnalytic
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.LogTailAnalytic

theorem eval_trunc_log (T : ℕ) (z : ℂ) :
    (PowerSeries.trunc T (PowerSeries.log ℂ)).eval z = Complex.logTaylor T z := by
  change (PowerSeries.trunc T (PowerSeries.log ℂ)).eval₂ (RingHom.id ℂ) z = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  unfold Complex.logTaylor
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply, PowerSeries.coeff_log]
  by_cases h : n = 0
  · simp [h]
  · simp [h, map_div₀, map_pow]
    ring

theorem analyticAt_logTail (T : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (logTail T) z := by
  unfold logTail Complex.logTaylor
  apply AnalyticAt.sub
  · apply Finset.analyticAt_fun_sum
    intro n hn
    fun_prop
  · exact (analyticAt_const.add analyticAt_id).clog (Complex.mem_slitPlane_of_norm_lt_one hz)

 theorem norm_logTail_le (T : ℕ) (hT : 1 ≤ T) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logTail T z‖ ≤ ‖z‖ ^ T * (1 - ‖z‖)⁻¹ / T := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  unfold logTail
  rw [norm_sub_rev]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    Complex.norm_log_sub_logTaylor_le n hz

theorem norm_logTail_le_one (T : ℕ) (hT : 1 ≤ T) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖logTail T z‖ ≤ 1 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hpow : ‖z‖ ^ T ≤ 1 / 2 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
    rw [pow_succ]
    have hh : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg z) hz1.le
    nlinarith [norm_nonneg z]
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖z‖) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  calc
    ‖logTail T z‖ ≤ ‖z‖ ^ T * (1 - ‖z‖)⁻¹ / T := norm_logTail_le T hT hz1
    _ ≤ (1 / 2 : ℝ) * 2 / T := by gcongr
    _ ≤ 1 := by rw [div_le_iff₀ (by positivity : (0 : ℝ) < T)]; nlinarith

theorem norm_prod_logTail_le_one {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖∏ i ∈ s, logTail (T i) z ^ d i‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro i hi
    positivity
  · intro i hi
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_logTail_le_one (T i) (hT i hi) hz)

theorem analyticAt_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (fun t => ∏ i ∈ s, logTail (T i) t ^ d i) z := by
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact (analyticAt_logTail (T i) hz).pow (d i)

theorem norm_rowTest_prod_logTail_le {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) (k : ℕ) :
    ‖AnalyticCollision.rowTest k (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)‖ ≤
      (2 : ℝ) ^ k := by
  have h := AnalyticCollision.norm_rowTest_le
    (f := fun z => ∏ i ∈ s, logTail (T i) z ^ d i) (D := 1) ?_ k
  · simpa only [mul_one] using h
  intro z hz
  apply norm_prod_logTail_le_one s T d hT
  exact (by simpa only [Metric.mem_sphere, dist_zero_right] using hz : ‖z‖ = 1 / 2).le

theorem hasSum_formal_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * z ^ n)
      (Complex.log (1 + z)) := by
  convert Complex.hasSum_taylorSeries_log hz using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [PowerSeries.coeff_log, hn, map_div₀, map_pow]
    ring

theorem hasSum_trunc_log (T : ℕ) (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) * z ^ n)
      (Complex.logTaylor T z) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range T)
    (f := fun n => PowerSeries.coeff n
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) * z ^ n) ?_
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← eval_trunc_log]
    change (PowerSeries.trunc T (PowerSeries.log ℂ)).eval₂ (RingHom.id ℂ) z = _
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp [PowerSeries.coeff_trunc, Finset.mem_range.mp hn]
  · intro n hn
    have hn' : ¬ n < T := by simpa only [Finset.mem_range] using hn
    simp [PowerSeries.coeff_trunc, hn']

theorem hasSum_formal_logTail (T : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
      (RowTranslation.tail T (PowerSeries.log ℂ)) * z ^ n) (logTail T z) := by
  have hfun : (fun n => PowerSeries.coeff n (RowTranslation.tail T (PowerSeries.log ℂ)) * z ^ n) =
      fun b => PowerSeries.coeff b ((PowerSeries.trunc T (PowerSeries.log ℂ) : Polynomial ℂ) : PowerSeries ℂ) * z ^ b -
        PowerSeries.coeff b (PowerSeries.log ℂ) * z ^ b :=
    funext fun n => by simp only [RowTranslation.tail, map_sub, sub_mul]
  rw [hfun]
  exact (hasSum_trunc_log T z).sub (hasSum_formal_log hz)

theorem hasSum_coeff_mul {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * z ^ n) (x * y) := by
  have hfn := hf.summable.norm
  have hgn := hg.summable.norm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at heq
  rw [← heq] at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have he : a.1 + a.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
  rw [← he, pow_add]
  ring

theorem hasSum_coeff_one (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

 theorem hasSum_coeff_pow {f : PowerSeries ℂ} {x z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x) (d : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (f ^ d) * z ^ n) (x ^ d) := by
  induction d with
  | zero => simpa only [pow_zero] using hasSum_coeff_one z
  | succ d hd => simpa only [pow_succ] using hasSum_coeff_mul hd hf

theorem hasSum_formal_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
      (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i) * z ^ n)
      (∏ i ∈ s, logTail (T i) z ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using hasSum_coeff_one z
  | @insert i s hi hs =>
    simpa only [Finset.prod_insert hi] using
      hasSum_coeff_mul (hasSum_coeff_pow (hasSum_formal_logTail (T i) hz) (d i)) hs

theorem hasFPowerSeriesAt_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ) :
    HasFPowerSeriesAt (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n
          (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_formal_prod_logTail s T d hn

theorem rowTest_prod_logTail_eq_coeff {ι : Type*} (s : Finset ι) (T d : ι → ℕ) (k : ℕ) :
    AnalyticCollision.rowTest k (fun z => ∏ i ∈ s, logTail (T i) z ^ d i) =
      PowerSeries.coeff k (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i) := by
  have hd : DifferentiableOn ℂ (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    apply (analyticAt_prod_logTail s T d ?_).differentiableAt.differentiableWithinAt
    have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_prod_logTail s T d)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p k (fun _ => 1)) he
  simpa only [AnalyticCollision.rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem norm_coeff_prod_formal_logTail_le {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i)‖ ≤
      (2 : ℝ) ^ k := by
  rw [← rowTest_prod_logTail_eq_coeff]
  exact norm_rowTest_prod_logTail_le s T d hT k

end PiExponent.LogTailAnalytic

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InterpolationMatrix
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

theorem column_mem_iff {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (a : Fin (m + 1) → ℕ) :
    a ∈ PiExponent.realWeightedSimplex (columnWeights w0 w) H ↔
      w0 * (a 0 : ℝ) + ∑ i, w i * (a i.succ : ℝ) ≤ H := by
  have hp : ∀ i, 0 < columnWeights w0 w i := by
    intro i
    refine Fin.cases hw0 (fun j => hw j) i
  rw [PiExponent.mem_realWeightedSimplex hp, Fin.sum_univ_succ]
  rfl

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

theorem column_weight_le {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (c : Column w0 w H) :
    w0 * (c.1 0 : ℝ) + ∑ i, w i * (c.1 i.succ : ℝ) ≤ H :=
  (column_mem_iff hw0 hw c.1).mp c.2

theorem row_weight_lt {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (ρ : Row K v0 θ w H) :
    v0 * (ρ.2.1 0 : ℝ) + (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ < H :=
  (row_mem_iff hv0 hθ hw ρ.2.1).mp ρ.2.2

end PiExponent.InterpolationMatrix

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MatrixTranslation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

theorem periodMonomial_as_shift {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) :
    periodMonomial j ω h a = C ((1 + PowerSeries.X) ^ h) *
      shift (fun _ => periodCoordinate j ω) (monomial (InterpolationMatrix.exponentVector a) 1) := by
  rw [periodMonomial, shift_monomial_one]
  simp [add_comm]

theorem periodMonomial_coeff {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (periodMonomial j ω h a).coeff A =
      ((∏ i, (a i).choose (A i) : ℕ) : PowerSeries ℂ) *
        (1 + PowerSeries.X) ^ h * periodCoordinate j ω ^ (∑ i : Fin m, (a i - A i)) := by
  rw [periodMonomial_as_shift, coeff_C_mul]
  change _ * shiftCoefficient _ _ _ = _
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [InterpolationMatrix.exponentVector_apply, Nat.cast_prod]
  ring

end PiExponent.MatrixTranslation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_PeriodAnalytic
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open PiExponent.AnalyticCollision PiExponent.LogTailAnalytic

namespace PiExponent.PeriodAnalytic

theorem hasSum_coeff_C (b z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C b) * z ^ n) b := by
  convert hasSum_ite_eq 0 b using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem hasSum_coeff_X (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * z ^ n) z := by
  convert hasSum_ite_eq 1 z using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem hasSum_coeff_add {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f + g) * z ^ n) (x + y) := by
  simpa only [map_add, add_mul] using hf.add hg

theorem hasSum_periodSeries (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (periodSeries b center h d) * z ^ n)
      (periodFunction b center h d z) := by
  exact hasSum_coeff_mul
    (hasSum_coeff_mul (hasSum_coeff_C b z)
      (hasSum_coeff_pow (hasSum_coeff_add (hasSum_coeff_one z) (hasSum_coeff_X z)) h))
    (hasSum_coeff_pow (hasSum_coeff_add (hasSum_coeff_C center z) (hasSum_formal_log hz)) d)

theorem analyticAt_periodFunction (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (periodFunction b center h d) z := by
  unfold periodFunction
  apply AnalyticAt.mul
  · fun_prop
  · exact (analyticAt_const.add ((analyticAt_const.add analyticAt_id).clog
      (Complex.mem_slitPlane_of_norm_lt_one hz))).pow d

theorem hasFPowerSeriesAt_periodFunction (b center : ℂ) (h d : ℕ) :
    HasFPowerSeriesAt (periodFunction b center h d)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
        (periodSeries b center h d))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_periodSeries b center h d hn

theorem rowTest_periodFunction_eq_coeff (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (periodFunction b center h d) =
      PowerSeries.coeff ell (periodSeries b center h d) := by
  have hd : DifferentiableOn ℂ (periodFunction b center h d)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    apply (analyticAt_periodFunction b center h d ?_).differentiableAt.differentiableWithinAt
    have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_periodFunction b center h d)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p ell (fun _ => 1)) he
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem rowTest_congr_sphere {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), f z = g z) (ell : ℕ) :
    rowTest ell f = rowTest ell g := by
  simp only [rowTest, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  change (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • f z =
    (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • g z
  rw [hfg z hz]

theorem periodFunction_eq_exponentialMonomial (b center : ℂ) (h d : ℕ)
    (hcenter : Complex.exp center = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    periodFunction b center h d z =
      exponentialMonomial b (h : ℂ) d (center + Complex.log (1 + z)) := by
  have hz0 : 1 + z ≠ 0 := by
    intro heq
    have heq' : z = -1 := by linear_combination heq
    simp [heq'] at hz
  unfold periodFunction exponentialMonomial
  rw [Complex.exp_nat_mul, Complex.exp_add, hcenter, Complex.exp_log hz0, one_mul]

theorem exp_period_center (j : ℕ) :
    Complex.exp ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

theorem rowTest_exponentialMonomial_eq_coeff (b : ℂ) (j h d ell : ℕ) :
    rowTest ell (fun t => exponentialMonomial b (h : ℂ) d
      ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) =
    PowerSeries.coeff ell (periodSeries b ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) h d) := by
  rw [← rowTest_periodFunction_eq_coeff]
  apply rowTest_congr_sphere
  intro t ht
  symm
  apply periodFunction_eq_exponentialMonomial _ _ _ _ (exp_period_center j)
  have hn : ‖t‖ = (1 / 2 : ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right] using ht
  rw [hn]
  norm_num

theorem periodMonomial_coeff_eq_rowTest {m : ℕ} (j h ell : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell ((MatrixTranslation.periodMonomial j
      (2 * (Real.pi : ℂ) * Complex.I) h a).coeff A) =
    rowTest ell (fun t => exponentialMonomial
      ((∏ i, (a i).choose (A i) : ℕ) : ℂ) (h : ℂ) (∑ i : Fin m, (a i - A i))
      ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) := by
  rw [rowTest_exponentialMonomial_eq_coeff, MatrixTranslation.periodMonomial_coeff]
  simp only [periodSeries, MatrixTranslation.periodCoordinate, map_natCast]

theorem norm_binomial_product_le {m : ℕ} (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤ (2 : ℝ) ^ (∑ i, a i) := by
  rw [Complex.norm_natCast]
  have h : (∏ i, (a i).choose (A i) : ℕ) ≤ 2 ^ (∑ i, a i) := by
    calc
      _ ≤ ∏ i, 2 ^ a i := Finset.prod_le_prod' (fun i _ => Nat.choose_le_two_pow _ _)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  exact_mod_cast h

theorem differentiable_columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) : Differentiable ℂ (columnFunction h a A) :=
  differentiable_exponentialMonomial _ _ _

theorem norm_columnFunction_le {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hcol : w0 * h + ∑ i, w i * a i ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hwpos (i) : 0 ≤ w i := hws.le.trans (hw i)
  have hsum0 : 0 ≤ ∑ i, w i * a i := Finset.sum_nonneg fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _)
  have hh : ‖(h : ℂ)‖ ≤ H / w0 := by
    rw [Complex.norm_natCast, le_div_iff₀ hw0]
    nlinarith
  have htot : (((∑ i, a i : ℕ) : ℝ)) ≤ H / wstar := by
    rw [le_div_iff₀ hws]
    have hs : wstar * ∑ i, (a i : ℝ) ≤ ∑ i, w i * a i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
    have hcast : ((∑ i, a i : ℕ) : ℝ) = ∑ i, (a i : ℝ) := by push_cast; rfl
    rw [hcast]
    nlinarith
  exact norm_exponentialMonomial_le_exp_budget _ _ _ _ hR hH hw0 hws hz
    (norm_binomial_product_le a A) hh
    (Finset.sum_le_sum fun i _ => Nat.sub_le _ _) htot

end PiExponent.PeriodAnalytic

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_Collision
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent

theorem formal_period_collision_bound
    {m : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (transverse : κ → Fin m →₀ ℕ)
    (j ell h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 v0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (ell r)
      ((MatrixTranslation.periodMonomial (j r) (2 * (Real.pi : ℂ) * Complex.I)
        (h c) (a c)).coeff (transverse (group r))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A, (Collision.multiplicity Finset.univ group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (holomorphicError K w0 v0 wstar + Collision.collisionRemainder (Fintype.card ι) H)) := by
  let R : NNReal := ⟨100 * (K : ℝ), by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < 100 * K; positivity
  have hR1 : (1 : ℝ) ≤ R := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    change (1 : ℝ) ≤ 100 * K
    linarith
  have hb := AnalyticCollision.translated_row_determinant_exp_bound_q68
    group (fun A c => PeriodAnalytic.columnFunction (h c) (a c) (transverse A))
    (fun r => (j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ell R hR hH
    (fun A c => PeriodAnalytic.differentiable_columnFunction _ _ _)
    (A := (R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar) (v := v0)
    (fun A c z hz => PeriodAnalytic.norm_columnFunction_le (h c) (a c) (transverse A) w
      hR1 hH.le hw0 hws hw (hcol c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    (fun r => AnalyticCollision.period_center_radius_bound hK (hj r)) hell
  have hRv : (R : ℝ) = 100 * K := rfl
  rw [hRv] at hb
  have he : (2 : ℝ) * (100 * K) = 200 * K := by ring
  rw [he] at hb
  simp_rw [PeriodAnalytic.periodMonomial_coeff_eq_rowTest]
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold holomorphicError
  ring

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_CollisionOccupancy
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.Collision

open scoped BigOperators

variable {G : Type*}

theorem sum_sq_le_card_mul_sum_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, n a ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : G => (1 : ℝ)) n

theorem sum_sq_le_card_mul_total_sq (S U : Finset G) (hSU : S ⊆ U)
    (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ U, n a ^ 2 := by
  apply (sum_sq_le_card_mul_sum_sq S n).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg hSU (fun a _ _ => sq_nonneg (n a))

variable [Fintype G]

theorem sum_sq_le_card_mul_univ_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a, n a ^ 2 := by
  exact sum_sq_le_card_mul_total_sq S Finset.univ (Finset.subset_univ S) n

end PiExponent.Collision

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_DeterminantAnalyticBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.DeterminantAnalyticBound

theorem two_alternative_exponent
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta nu c N bbar E : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N) :
    -nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) -
      c * (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
      (Fintype.card ι : ℝ) * H * E ≤
    (Fintype.card ι : ℝ) * H *
      (E + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar))) := by
  classical
  let S := (Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)
  let M : ℝ := Fintype.card ι
  let Z : ℝ := ∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass : (∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)) =
      (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) := by
    have hn := Collision.sum_multiplicity_eq_card_filter (Finset.univ : Finset ι) S group
    have hn' : (∑ a ∈ S, Collision.multiplicity Finset.univ group a) =
        ((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hn
    exact_mod_cast hn'
  by_cases hlow : eta * M ≤ ∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)
  · have hsq : eta ^ 2 * M ^ 2 ≤ N * Z := by
      calc
        _ = (eta * M) ^ 2 := by ring
        _ ≤ (∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg heta hM) hlow 2
        _ ≤ (S.card : ℝ) * Z := Collision.sum_sq_le_card_mul_univ_sq S _
        _ ≤ N * Z := mul_le_mul_of_nonneg_right hcap hZ
    have hcollision : -c * Z ≤ M * H * (-c * eta ^ 2 * M / (H * N)) := by
      have hz : eta ^ 2 * M ^ 2 / N ≤ Z := (div_le_iff₀ hN).mpr (by nlinarith [hsq])
      have hh := mul_le_mul_of_nonneg_left hz hc
      have he : M * H * (-c * eta ^ 2 * M / (H * N)) = -c * (eta ^ 2 * M ^ 2 / N) := by
        field_simp
      rw [he]
      nlinarith [hh]
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤ 0 := by
      have hp := mul_nonneg hnu (sub_nonneg.mpr hbeta)
      nlinarith [hp]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_left (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith
  · have hl : (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) ≤
        eta * (Finset.univ : Finset ι).card := by
      rw [← hmass]
      exact (le_of_not_ge hlow)
    have hwgt := Collision.sum_weight_ge_of_low_count_le (Finset.univ : Finset ι)
      (fun i => weight (group i)) (mul_nonneg hA hH.le) (fun i _ => hw _) hl
    have hwgt' : A * H * (1 - eta) * M ≤ ∑ i, weight (group i) := by
      simpa only [Finset.card_univ, M] using hwgt
    have hmul := mul_le_mul_of_nonneg_left hwgt' hnu
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤
        M * H * (-nu * (A * (1 - eta) - bbar)) := by nlinarith [hmul]
    have hcollision : -c * Z ≤ 0 := by nlinarith [mul_nonneg hc hZ]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_right (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith

theorem translated_summand_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N)
    (hscalar : ‖scalar‖ ≤ Real.exp
      (-nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
        (Fintype.card ι : ℝ) * H * Etr))
    (hdet : ‖determinant‖ ≤ Real.exp
      (-c * (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (Ehol + rho))) :
    ‖scalar * determinant‖ ≤ Real.exp ((Fintype.card ι : ℝ) * H *
      (Etr + Ehol + rho + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar)))) := by
  rw [norm_mul]
  apply (mul_le_mul hscalar hdet (norm_nonneg _) (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := two_alternative_exponent group weight hH hA heta hnu hc hN hw hbeta hcap
    (E := Etr + Ehol + rho)
  nlinarith [h]

end PiExponent.DeterminantAnalyticBound

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_Parameters
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

namespace Parameters

variable {ν : ℝ} (p : Parameters ν)

theorem A_pos : 0 < (p.A : ℝ) := lt_trans p.theta_pos p.theta_lt_A

end Parameters

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MatrixArithmetic
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

open scoped BigOperators

namespace MatrixArithmetic

theorem actual_row_card_pos {m K : ℕ} {v0 θ H : ℝ} {q : Fin m → ℕ}
    (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    0 < Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0, hK⟩, ⟨fun _ => 0, ?_⟩⟩⟩
  apply (InterpolationMatrix.row_mem_iff hv0 hθ hw _).mpr
  simpa using hH

end MatrixArithmetic

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_DeterminantContradiction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace PiExponent.DeterminantContradiction

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem finiteDenominators_two_le {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

end PiExponent.DeterminantContradiction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ApproximationCenters
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

theorem norm_period_error (p : ℤ) (q : ℕ) :
    ‖approximatePeriod p q - logarithmicPeriod‖ =
      2 * |Real.pi - (p : ℝ) / q| := by
  have heq : approximatePeriod p q - logarithmicPeriod =
      (2 * Complex.I) * (((p : ℝ) / q - Real.pi : ℝ) : ℂ) := by
    unfold approximatePeriod logarithmicPeriod
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num [norm_mul, abs_sub_comm]

theorem norm_center_error_le (nu : ℝ) {p : ℤ} {q j K : ℕ}
    (hj : j ≤ K)
    (happrox : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) * (approximatePeriod p q - logarithmicPeriod)‖ ≤
      2 * K * (q : ℝ) ^ (-nu) := by
  rw [norm_mul, norm_period_error]
  have hjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
  have hqpow : 0 ≤ (q : ℝ) ^ (-nu) := Real.rpow_nonneg (by positivity) _
  simp only [Complex.norm_natCast]
  nlinarith [abs_nonneg (Real.pi - (p : ℝ) / q)]

theorem ceil_log_bounds {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ (⌈Real.log q⌉₊ : ℝ) - Real.log q ∧
      (⌈Real.log q⌉₊ : ℝ) - Real.log q < 1 := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  constructor
  · exact sub_nonneg.mpr (Nat.le_ceil _)
  · have := Nat.ceil_lt_add_one hlog
    linarith

theorem rpow_neg_le_exp_ceil_log (nu : ℝ) {q : ℕ} (hnu : 0 ≤ nu) (hq : 1 ≤ q) :
    (q : ℝ) ^ (-nu) ≤
      Real.exp nu * Real.exp (-nu * (⌈Real.log q⌉₊ : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [Real.rpow_def_of_pos hqpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hw := (ceil_log_bounds hq).2
  nlinarith

theorem norm_center_error_exp (nu : ℝ) {p : ℤ} {q j K : ℕ}
    (hnu : 0 ≤ nu) (hq : 1 ≤ q) (hj : j ≤ K)
    (happrox : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ‖(j : ℂ) * (approximatePeriod p q - logarithmicPeriod)‖ ≤
      (2 * K * Real.exp nu) * Real.exp (-nu * (⌈Real.log q⌉₊ : ℝ)) := by
  calc
    _ ≤ 2 * K * (q : ℝ) ^ (-nu) := norm_center_error_le nu hj happrox
    _ ≤ 2 * K * (Real.exp nu * Real.exp (-nu * (⌈Real.log q⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log nu hnu hq) (by positivity)
    _ = _ := by ring

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MatrixTranslationBounds
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.MatrixTranslationBounds

open scoped BigOperators
open RowTranslation

theorem error_power_product_le {σ : Type*} [Fintype σ]
    (ε : σ → ℂ) (e : σ → ℕ) (w : σ → ℝ) (C ν : ℝ)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    (∏ i, ‖ε i‖ ^ e i) ≤ Real.exp (∑ i, (e i : ℝ) * (C - ν * w i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod (fun i hi => by positivity)
  intro i hi
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (hε i) _

theorem norm_rowScalar_exp_basic {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ) (C ν : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp ((∑ i, a i : ℕ) * Real.log 4 +
        (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) +
          (k : ℝ) * Real.log 2) := by
  have hτ := LogTailAnalytic.norm_coeff_prod_formal_logTail_le Finset.univ T
    (fun i => (d i : ℕ)) (fun i hi => hT i) k
  apply (norm_rowScalar_le ε _ β a d k ((2 : ℝ) ^ k) hτ).trans
  calc
    _ ≤ (4 : ℝ) ^ (∑ i, a i) *
        Real.exp (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (error_power_product_le ε _ w C ν hε) (by positivity))
        (by positivity)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem sum_exponents_le {σ : Type*} [Fintype σ] (w : σ → ℝ) (a : σ → ℕ)
    (H ws : ℝ) (hws : 0 < ws) (hw : ∀ i, ws ≤ w i) (ha : weight w a ≤ H) :
    ((∑ i, a i : ℕ) : ℝ) ≤ H / ws := by
  apply (le_div_iff₀ hws).2
  calc
    ((∑ i, a i : ℕ) : ℝ) * ws = ∑ i, ws * (a i : ℝ) := by
      simp only [Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring_nf
    _ ≤ weight w a := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _))
    _ ≤ H := ha

theorem residual_exponent_identity {σ : Type*} [Fintype σ]
    (a β : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ) (C ν : ℝ) :
    (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) =
      C * ((∑ i, (a i - β i - d i) : ℕ) : ℝ) -
        ν * weight w (fun i => a i - β i) + ν * weight w (fun i => (d i : ℕ)) := by
  simp only [weight, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_sub (Nat.le_of_lt_succ (d i).isLt)]
  ring_nf

theorem norm_rowScalar_exp_weighted {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp (-ν * weight w (fun i => a i - β i) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  by_cases hz : PowerSeries.coeff k (∏ i, tail (T i) (PowerSeries.log ℂ) ^ (d i : ℕ)) = 0
  · simp [rowScalar, hz, Real.exp_nonneg]
  have hbudget : weight w (fun i => (d i : ℕ)) ≤ H / F := by
    have hb := tail_weight_budget Finset.univ T (fun i => (d i : ℕ))
      (fun _ => PowerSeries.log ℂ) k w v F hv.le hF (fun i hi => hTw i) hz
    have hkv : v * (k : ℝ) ≤ H := by nlinarith [(le_div_iff₀ hv).mp hk]
    have hb' : weight w (fun i => (d i : ℕ)) ≤ v * k / F := by
      simpa [weight, mul_comm] using hb
    exact hb'.trans (div_le_div_of_nonneg_right hkv hF.le)
  have hsize := sum_exponents_le w (fun i => a i) H ws hws hw ha
  have hcount : ((∑ i, (a i - β i - d i) : ℕ) : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum (fun i hi => (Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  apply (norm_rowScalar_exp_basic ε T β a d k w C ν hT hε).trans
  apply Real.exp_le_exp.mpr
  rw [residual_exponent_identity]
  calc
    _ ≤ (Real.log 4 + C) * ((∑ i, a i : ℕ) : ℝ) -
        ν * weight w (fun i => a i - β i) + ν * (H / F) + (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcount hC,
        mul_le_mul_of_nonneg_left hbudget hν,
        mul_le_mul_of_nonneg_right hk hlog2]
    _ ≤ (Real.log 4 + C) * (H / ws) -
        ν * weight w (fun i => a i - β i) + ν * (H / F) + (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsize (add_nonneg hlog4 hC)]
    _ = _ := by ring_nf

theorem weight_sub_le_weight_tsub {σ : Type*} [Fintype σ]
    (w : σ → ℝ) (a β : σ → ℕ) (hw : ∀ i, 0 ≤ w i) :
    weight w a - weight w β ≤ weight w (fun i => a i - β i) := by
  simp only [weight, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub]
  apply mul_le_mul_of_nonneg_left _ (hw i)
  by_cases h : β i ≤ a i
  · rw [Nat.cast_sub h]
  · have hle : a i ≤ β i := by omega
    rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast hle)

theorem norm_rowScalar_exp_weight_difference {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  apply (norm_rowScalar_exp_weighted ε T β a d k w C ν H ws v F
    hC hν hws hv hF hw ha hk hT hTw hε).trans
  apply Real.exp_le_exp.mpr
  have h := weight_sub_le_weight_tsub w (fun i => a i) (fun i => β i)
    (fun i => hws.le.trans (hw i))
  nlinarith [mul_le_mul_of_nonneg_left h hν]

theorem actual_error_exp {σ : Type*} (p : σ → ℤ) (q : σ → ℕ)
    (j K : ℕ) (ν : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hν : 0 ≤ ν)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |Real.pi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν)) :
    ∀ i, ‖(j : ℂ) * (approximatePeriod (p i) (q i) - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + ν) - ν * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have h := norm_center_error_exp ν hν (hq i) hj (happrox i)
  have hKpos : (0 : ℝ) < 2 * K := by exact_mod_cast (by omega : 0 < 2 * K)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
  congr 1
  ring_nf

theorem truncationOrder_pos {F v w : ℝ} (hF : 0 < F) (hv : 0 < v) (hw : 0 < w) :
    1 ≤ truncationOrder F v w := by
  exact Nat.ceil_pos.mpr (div_pos (mul_pos hF hw) hv)

theorem truncationOrder_budget {F v w : ℝ} (hv : 0 < v) :
    F * w ≤ v * truncationOrder F v w := by
  have h := Nat.le_ceil (F * w / v)
  have h' := (div_le_iff₀ hv).mp h
  simpa [truncationOrder, mul_comm] using h'

end PiExponent.MatrixTranslationBounds

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LiteralAnalyticSummand
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.LiteralAnalytic
open DeterminantContradiction

theorem fixedWeights_pos {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < fixedWeights d i := by
  change 0 < MatrixArithmetic.logWeights (finiteDenominators d) i
  rw [logWeights_eq]
  exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)

theorem fixedWeights_lower {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    d.wstar ≤ fixedWeights d i := by
  change d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i
  rw [logWeights_eq]
  exact d.wstar_lower i

theorem rowOrder_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) :
    (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
  have hr := InterpolationMatrix.row_weight_lt d.v0_pos d.base.theta_pos (fixedWeights_pos d) r
  have hs : 0 ≤ (∑ i, fixedWeights d i * (r.2.1 i.succ : ℝ)) / (d.base.theta : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _))
      d.base.theta_pos.le
  apply (le_div_iff₀ d.v0_pos).mpr
  nlinarith

theorem indexWeight_nonneg {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) :
    0 ≤ indexWeight d a := by
  unfold indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _)

theorem indexWeight_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Transverse d H) :
    indexWeight d a ≤ H :=
  (MatrixTranslation.mem_transverseIndices (fixedWeights d) H (fixedWeights_pos d) a.1).mp a.2

theorem norm_choiceScalar_le {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) + H * d.translationError) := by
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hC : 0 ≤ Real.log (2 * (d.K : ℝ)) + nu :=
    add_nonneg (Real.log_nonneg (by linarith)) hnu
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply le_trans _ (rowOrder_le d r)
    exact_mod_cast Nat.le_of_lt_succ t.2.2.isLt
  have hT : ∀ i, 1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i :=
    fun i => MatrixTranslationBounds.truncationOrder_pos d.F0_pos d.v0_pos (fixedWeights_pos d i)
  have hTw : ∀ i, d.F0 * fixedWeights d i ≤
      (d.v0 : ℝ) * MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i :=
    fun _ => MatrixTranslationBounds.truncationOrder_budget d.v0_pos
  have heps := MatrixTranslationBounds.actual_error_exp (finiteNumerators d) (finiteDenominators d)
    r.1.val d.K nu d.K_pos r.1.isLt.le hnu
    (fun i => le_trans (by decide : 1 ≤ 2) (finiteDenominators_two_le d i))
    (fun i => (d.approximations i.val).2.2)
  have hb := MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - logarithmicPeriod))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (beta d r) t.1.1 t.2.1 t.2.2 (fixedWeights d)
    (Real.log (2 * (d.K : ℝ)) + nu) nu H d.wstar d.v0 d.F0
    hC hnu d.wstar_pos d.v0_pos d.F0_pos (fixedWeights_lower d) (indexWeight_le d t.1)
    hk hT hTw heps
  simpa only [choiceScalar, indexWeight, rowWeight, AdmissibleParameters.translationError, add_assoc]
    using hb

theorem rowWeight_le_indexWeight_of_ne_zero {nu : ℝ} (d : FixedData nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) (ht : choiceScalar d r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  have h := RowTranslation.rowScalar_ne_zero_le _ _ _ _ _ _ ht
  unfold rowWeight indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h i)
    (fixedWeights_pos d i).le

theorem actualRowCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H :=
  MatrixArithmetic.actual_row_card_pos (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.v0_pos d.base.theta_pos hH
    (fixedWeights_pos d)

theorem sum_rowWeight_eq {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H * actualMean d H := by
  have hM : (actualRowCount d H : ℝ) ≠ 0 := by exact_mod_cast (actualRowCount_pos d hH).ne'
  unfold actualMean MatrixArithmetic.meanRowWeight
  change (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H *
    (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H /
      ((actualRowCount d H : ℝ) * H))
  rw [mul_div_cancel₀ _ (mul_ne_zero hM hH.ne')]
  unfold MatrixArithmetic.rowWeightedSum rowWeight MatrixTranslationBounds.weight beta fixedWeights
  simp only [InterpolationMatrix.exponentVector_apply, mul_comm]

theorem low_transverse_capacity {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun A => indexWeight d A ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤ lowIndexCount d H := by
  classical
  let f : {A : Transverse d H // indexWeight d A ≤ (d.base.A : ℝ) * H} →
      ↥(MatrixTranslation.transverseIndices (fixedWeights d) ((d.base.A : ℝ) * H)) :=
    fun A => ⟨A.1.1, (MatrixTranslation.mem_transverseIndices _ _ (fixedWeights_pos d) _).mpr A.2⟩
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    simpa only [f] using hh
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_subtype] at hh
  have hc : Fintype.card ↥(MatrixTranslation.transverseIndices (fixedWeights d)
      ((d.base.A : ℝ) * H)) = lowIndexCount d H := by
    simp only [Fintype.card_coe, MatrixTranslation.card_transverseIndices]
    rfl
  rw [hc] at hh
  exact_mod_cast hh

theorem lowIndexCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < lowIndexCount d H := by
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, ?_⟩
  apply (mem_realWeightedSimplex (fixedWeights_pos d)).mpr
  simp only [Nat.cast_zero, mul_zero, Finset.sum_const_zero]
  exact mul_nonneg d.base.A_pos.le hH.le

theorem norm_scalar_product_le {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) - (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod (fun r _ => norm_nonneg _) (fun r _ => norm_choiceScalar_le d hnu r (f r))).trans
  rw [← Real.exp_sum]
  apply le_of_eq
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_rowWeight_eq d hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
  ring_nf

theorem norm_choiceMatrix_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  have horders : ((∑ r : Row d H, (r.2.1 0 - ((f r).2.2 : ℕ)) : ℕ) : ℝ) ≤
      (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        exact le_trans (by exact_mod_cast Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ)) (rowOrder_le d r)
      _ = _ := by simp; ring_nf
  have hb := formal_period_collision_bound (fun r => (f r).1) (fun A : Transverse d H => A.1)
    (fun r => r.1.val) (fun r => r.2.1 0 - ((f r).2.2 : ℕ))
    (fun c => (selection c).1 0) (fun c i => (selection c).1 i.succ) (fixedWeights d)
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) hH d.w0_pos d.wstar_pos (fixedWeights_lower d)
    (fun r => r.1.isLt)
    (fun c => InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)) horders
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl

theorem norm_actual_summand_le_q68_oai {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det‖ ≤
    Real.exp ((actualRowCount d H : ℝ) * H *
      (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r, choiceScalar d r (f r)) = 0
  · simp [hs, Real.exp_nonneg]
  have hmono : (actualRowCount d H : ℝ) * H * actualMean d H ≤ ∑ r, indexWeight d (f r).1 := by
    rw [← sum_rowWeight_eq d hH]
    apply Finset.sum_le_sum
    intro r _
    apply rowWeight_le_indexWeight_of_ne_zero d r (f r)
    exact Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r)
  have hb := DeterminantAnalyticBound.translated_summand_bound
    (fun r => (f r).1) (fun A : Transverse d H => indexWeight d A)
    (∏ r, choiceScalar d r (f r)) (choiceMatrix d selection f).det
    hH d.base.A_pos.le d.base.eta_pos.le hnu collisionConstant_pos.le
    (by exact_mod_cast lowIndexCount_pos d hH)
    (indexWeight_nonneg d) hmono (low_transverse_capacity d H)
    (norm_scalar_product_le d hnu hH f) (norm_choiceMatrix_le d hH selection f)
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold AdmissibleParameters.analyticError collisionRate collisionConstant actualRowCount
  ring_nf

end PiExponent.LiteralAnalytic

end OAI
end

theorem solution : type_of% @OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le_q68_oai := @OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le_q68_oai
