-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.not_isSiegel_indefinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:55.255342+00:00
-- url     : https://prove2.me/submissions/85171964-c410-4aad-9d72-d326ac198508

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_IsSiegel_dotProduct_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution : ¬ IsSiegel !![I, 2 * I; 2 * I, I] := by
  intro h
  have := h.dotProduct_pos (x := ![1, -1]) (by
    intro e
    simpa using congrFun e 0)
  simp [dotProduct, mulVec, Fin.sum_univ_two] at this
end GlobalTheory.RiemannThetaModel
