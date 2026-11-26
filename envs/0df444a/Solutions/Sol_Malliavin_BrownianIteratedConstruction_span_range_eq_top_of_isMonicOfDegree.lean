-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.span_range_eq_top_of_isMonicOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:34.174833+00:00
-- url     : https://prove2.me/submissions/77d596ff-a00f-4d32-b47a-c07cba58ae50

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (p : ℕ → Polynomial ℝ)
    (hp : ∀ n, Polynomial.IsMonicOfDegree (p n) n) :
    Submodule.span ℝ (Set.range p) = ⊤ := by
  let H := Submodule.span ℝ (Set.range p)
  apply top_unique
  intro f _hf
  change f ∈ H
  have hpow : ∀ n : ℕ, (Polynomial.X : Polynomial ℝ) ^ n ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n = 0
        · subst n
          have hp0 : p 0 = 1 := Polynomial.isMonicOfDegree_zero_iff.mp (hp 0)
          have hgen : p 0 ∈ H := Submodule.subset_span ⟨0, rfl⟩
          simpa [hp0] using hgen
        · let q : Polynomial ℝ := p n - Polynomial.X ^ n
          have hqdeg : q.natDegree < n := (hp n).natDegree_sub_X_pow hn
          have hq : q ∈ H := by
            rw [q.as_sum_support_C_mul_X_pow]
            apply Submodule.sum_mem
            intro i hi
            rw [← Polynomial.smul_eq_C_mul]
            exact H.smul_mem (q.coeff i) <|
              ih i ((Polynomial.le_natDegree_of_mem_supp i hi).trans_lt hqdeg)
          have hgen : p n ∈ H := Submodule.subset_span ⟨n, rfl⟩
          have hrecover : p n - q = Polynomial.X ^ n := by
            simp [q]
          rw [← hrecover]
          exact H.sub_mem hgen hq
  rw [f.as_sum_support_C_mul_X_pow]
  apply Submodule.sum_mem
  intro i _hi
  rw [← Polynomial.smul_eq_C_mul]
  exact H.smul_mem (f.coeff i) (hpow i)
end Malliavin.BrownianIteratedConstruction
