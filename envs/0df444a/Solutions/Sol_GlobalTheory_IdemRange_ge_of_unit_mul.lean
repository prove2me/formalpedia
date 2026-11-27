-- Prove2me | solution 1 for GlobalTheory.IdemRange.ge_of_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:10:31.440812+00:00
-- url     : https://prove2.me/submissions/4e32fcb1-be4a-4f37-bf51-cd10a38030f5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEmbeddingCongrIntegralCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RingHomEqOfCongruentIntegralUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCharacterGeneralizedEigenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LimitIdempotentRangeLeSumEigenspaces
import Theorems.Thm_GlobalTheory_IdemRange_mm_add
import Theorems.Thm_GlobalTheory_IdemRange_not_mm_one
import Theorems.Thm_GlobalTheory_CongruentCharacters_mm_add
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.IdemRange
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.IdemRange
theorem _root_.solution {c a : C} {w : ℝ} (hc : V.MM c) (h : V.Ge w ((1 - c) * a)) : V.Ge w a := by
  have h1 : V.v (1 - c) ≤ 0 := by
    by_contra hh
    have : V.MM (1 - c + c) := mm_add (not_le.mp hh) hc
    rw [sub_add_cancel] at this
    exact not_mm_one this
  unfold VF.Ge at *
  rw [V.v.map_mul] at h
  exact h.trans (add_le_of_nonpos_left h1)
end GlobalTheory.IdemRange
