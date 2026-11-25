-- Prove2me | solution 1 for GlobalTheory.FrameGram.lead_mul_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:51:49.412146+00:00
-- url     : https://prove2.me/submissions/f0e96beb-9542-4ed0-afe6-24912657242b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
import Theorems.Thm_GlobalTheory_FrameGram_submatrix_mul_upper
import Theorems.Thm_GlobalTheory_FrameGram_det_sub_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram
namespace GlobalTheory.FrameGram
theorem _root_.solution {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (M * B) l = lead M l := by
  unfold lead
  rw [submatrix_mul_upper _ _ _ _ hB, Matrix.det_mul, det_sub_upper _ _ hB h1, mul_one]
end GlobalTheory.FrameGram
