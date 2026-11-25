-- Prove2me | solution 1 for GlobalTheory.FrameGram.lead_lower_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:01.065808+00:00
-- url     : https://prove2.me/submissions/ea4eaccf-2402-422d-9371-96cb5289182f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
import Theorems.Thm_GlobalTheory_FrameGram_lead_mul_upper
import Theorems.Thm_GlobalTheory_FrameGram_lead_transpose

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
    lead (B.transpose * M) l = lead M l := by
  rw [← lead_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, lead_mul_upper _ _ hB h1,
    lead_transpose]
end GlobalTheory.FrameGram
