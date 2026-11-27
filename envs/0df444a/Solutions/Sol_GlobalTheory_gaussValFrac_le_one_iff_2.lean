-- Prove2me | solution 2 for GlobalTheory.gaussValFrac_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:13.758802+00:00
-- url     : https://prove2.me/submissions/d7f3b820-ac09-4781-ba1c-bceda56b841e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_exists_eq_C_mul_gaussVal_eq_one
import Theorems.Thm_GlobalTheory_gaussValFrac_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
namespace GlobalTheory
theorem _root_.solution {x : F} :
    gaussValFrac v σ F x ≤ 1 ↔ ∃ f g : MvPolynomial σ K, gaussVal v f ≤ 1 ∧ gaussVal v g = 1 ∧
      x = algebraMap _ F f / algebraMap _ F g := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) x
    obtain ⟨c, g', hc, -, hg', rfl⟩ :=
      exists_eq_C_mul_gaussVal_eq_one v (nonZeroDivisors.ne_zero hg)
    have e : algebraMap _ F f / algebraMap _ F (C c * g') =
        algebraMap _ F (C c⁻¹ * f) / algebraMap _ F g' := by
      have : algebraMap (MvPolynomial σ K) F (C c⁻¹) = (algebraMap _ F (C c : MvPolynomial σ K))⁻¹ :=
        map_inv₀ ((algebraMap (MvPolynomial σ K) F).comp C) c
      rw [map_mul, map_mul, this]
      ring
    refine ⟨C c⁻¹ * f, g', ?_, hg', e⟩
    rwa [e, gaussValFrac_div, hg', div_one] at h
  · rintro ⟨f, g, hf, hg, rfl⟩
    rwa [gaussValFrac_div, hg, div_one]
end GlobalTheory
