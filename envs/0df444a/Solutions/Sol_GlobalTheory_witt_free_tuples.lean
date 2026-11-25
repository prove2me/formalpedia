-- Prove2me | solution 1 for GlobalTheory.witt_free_tuples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:55.431399+00:00
-- url     : https://prove2.me/submissions/4737c473-205c-455f-8e78-c9cd87e24ac5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtaleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesFin
import Theorems.Thm_GlobalTheory_witt_free_tuples_fin
import Theorems.Thm_GlobalTheory_free_reindex
import Theorems.Thm_GlobalTheory_pairM_reindex

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
theorem _root_.solution {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n : ℕ} {a : Type}
    [Fintype a] [DecidableEq a] (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J)
    (X X' : Matrix (Fin n) a E) (hX : Free X) (hX' : Free X')
    (hP : pairM σ J X X = pairM σ J X' X') : ∃ g, IsUn σ J g ∧ g * X = X' := by
  let e : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
  obtain ⟨g, hg, hgX⟩ := witt_free_tuples_fin σ hσ J hJ (X.submatrix id e) (X'.submatrix id e)
    (free_reindex e hX) (free_reindex e hX')
    (by rw [pairM_reindex, pairM_reindex, hP])
  refine ⟨g, hg, ?_⟩
  ext i j
  have h := congrFun (congrFun hgX i) (e.symm j)
  simpa [Matrix.mul_apply] using h
end GlobalTheory
