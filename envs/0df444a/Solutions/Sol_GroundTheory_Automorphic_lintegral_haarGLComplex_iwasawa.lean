-- Prove2me | solution 1 for GroundTheory.Automorphic.lintegral_haarGLComplex_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:35.305975+00:00
-- url     : https://prove2.me/submissions/15914941-b6f0-4ca1-9395-536ca6ecb246

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroups
import Theorems.Thm_GroundTheory_Automorphic_haarGLComplex_eq_smul_map_kbHomeomorph
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix Set
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
namespace GroundTheory.Automorphic
theorem _root_.solution (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure]
    (μK : Measure (unitaryGroup n ℂ)) [μK.IsHaarMeasure]
    (μB : Measure (upperPosSubgroup n ℂ)) [μB.IsHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL n ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(haarGLComplex μ₀) =
        c * ∫⁻ k, ∫⁻ b, f (Unitary.toUnits k * b) ∂μB.inv ∂μK := by
  obtain ⟨c, hc, h⟩ := haarGLComplex_eq_smul_map_kbHomeomorph μ₀ μK μB
  refine ⟨c, hc, fun f hf => ?_⟩
  rw [h, lintegral_smul_measure, lintegral_map hf kbHomeomorph.measurable]
  have := lintegral_prod (μ := μK) (ν := μB.inv) _ (hf.comp kbHomeomorph.measurable).aemeasurable
  simp only [Function.comp_def] at this
  rw [this, ENNReal.smul_def, smul_eq_mul]
  rfl
end GroundTheory.Automorphic
