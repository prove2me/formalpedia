-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:08.762122+00:00
-- url     : https://prove2.me/submissions/bef3bf94-f4af-41ab-af81-25ccd290d809

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_eq_top_of_isMonicOfDegree
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
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


attribute [local simp] Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
variable {M : Type*} [AddCommMonoid M] [Module ℝ M]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (p : ℕ → Polynomial ℝ) (hp : Submodule.span ℝ (Set.range p) = ⊤)
    (xpow : ℕ → M) :
    Submodule.span ℝ (Set.range fun n ↦ polynomialFamilyLinearMap xpow (p n)) =
      Submodule.span ℝ (Set.range xpow) := by
  let T : Polynomial ℝ →ₗ[ℝ] M := polynomialFamilyLinearMap xpow
  change Submodule.span ℝ (Set.range fun n ↦ T (p n)) =
    Submodule.span ℝ (Set.range xpow)
  have hfamilyImage : T '' Set.range p = Set.range (fun n ↦ T (p n)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨p n, ⟨n, rfl⟩, rfl⟩
  have hTpow (n : ℕ) : T (Polynomial.X ^ n) = xpow n := by
    exact polynomialFamilyLinearMap_X_pow xpow n
  have hpowerImage : T '' Set.range (fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n) =
      Set.range xpow := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hTpow n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Polynomial.X ^ n, ⟨n, rfl⟩, hTpow n⟩
  have hpowerSpan : Submodule.span ℝ
      (Set.range fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n) = ⊤ :=
    span_range_eq_top_of_isMonicOfDegree _
      (Polynomial.isMonicOfDegree_X_pow ℝ)
  calc
    Submodule.span ℝ (Set.range fun n ↦ T (p n)) =
        Submodule.span ℝ (T '' Set.range p) := by rw [hfamilyImage]
    _ = (Submodule.span ℝ (Set.range p)).map T := Submodule.span_image T
    _ = (⊤ : Submodule ℝ (Polynomial ℝ)).map T := by rw [hp]
    _ = (Submodule.span ℝ
        (Set.range fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n)).map T := by
      rw [hpowerSpan]
    _ = Submodule.span ℝ
        (T '' Set.range fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n) := by
      rw [Submodule.map_span]
    _ = Submodule.span ℝ (Set.range xpow) := by rw [hpowerImage]
end Malliavin.BrownianIteratedConstruction
