-- Prove2me | solution 1 for GlobalTheory.witt_free_tuples_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:37.304506+00:00
-- url     : https://prove2.me/submissions/c6fed54d-2483-4f10-9c61-a1d556bb399c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesFin
import Theorems.Thm_GlobalTheory_T_isField_or_exists_swapped_idempotent_of_quadraticEtale
import Theorems.Thm_GlobalTheory_T_witt_extension_hermitian_frames
import Theorems.Thm_GlobalTheory_T_witt_free_tuples_split_quadratic_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J) (Y Y' : Matrix (Fin n) (Fin k) E)
    (hY : Free Y) (hY' : Free Y') (hP : pairM σ J Y Y = pairM σ J Y' Y') :
    ∃ g, IsUn σ J g ∧ g * Y = Y' := by
  rcases GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale σ hσ with hF | hS
  · letI := hF.toField
    exact GlobalTheory.T.witt_extension_hermitian_frames σ hσ J hJ Y Y' hY hY' hP
  · exact GlobalTheory.T.witt_free_tuples_split_quadratic_etale σ hσ hS J hJ Y Y' hY hY' hP
end GlobalTheory
