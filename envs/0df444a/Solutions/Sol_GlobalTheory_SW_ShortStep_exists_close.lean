-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.exists_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:20.254191+00:00
-- url     : https://prove2.me/submissions/05a367ff-4f26-4139-8cf5-80b157fb5219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_basis_one
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution (h : IsType Ψ) : ∃ C : ℝ, ∀ x : Ψ → ℂ, ∃ a : E, IsIntegral ℤ a ∧
    ∀ τ : Ψ, ‖τ.1 a + x τ‖ ≤ C := by
  obtain ⟨b, hb⟩ := basis_one h
  refine ⟨∑ i, ‖b i‖, fun x => ?_⟩
  obtain ⟨a, ha, e⟩ := (hb _).1 (ZSpan.floor b x).2
  refine ⟨-a, ha.neg, fun τ => le_trans ?_ (ZSpan.norm_fract_le b x)⟩
  refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ τ)
  rw [ZSpan.fract_apply, e]
  simp [neg_add_eq_sub]
end GlobalTheory.SW.ShortStep
