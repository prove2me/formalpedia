-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.one_le_norm_embAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:11:37.432737+00:00
-- url     : https://prove2.me/submissions/49586d49-fdc6-4bde-8871-0f82a6446ef1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {E m : Type} [Field E] [NumberField E] [Fintype m] {w : m → 𝓞 E}
    (hw : w ≠ 0) : 1 ≤ ‖embAll E m w‖ := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  have h1 : (w j : E) ≠ 0 := by simpa using hj
  have h2 := one_le_house_of_isIntegral (w j).isIntegral_coe h1
  exact h2.trans (norm_le_pi_norm (embAll E m w) j)
end GlobalTheory.SW.EisConv
