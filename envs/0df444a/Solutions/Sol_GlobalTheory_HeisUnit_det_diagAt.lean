-- Prove2me | solution 1 for GlobalTheory.HeisUnit.det_diagAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:50.317299+00:00
-- url     : https://prove2.me/submissions/03169a9c-22ab-4789-996e-b3dde8469d4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Theorems.Thm_GlobalTheory_SplitFlip_det_diagGL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.HeisUnit
theorem _root_.solution {n : ℕ} (x : kˣ) (i0 : Fin n) : Matrix.GeneralLinearGroup.det (diagAt x i0) = x := by
  rw [diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]
end GlobalTheory.HeisUnit
