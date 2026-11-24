-- Prove2me | solution 1 for GlobalTheory.SgAlg.witt_free_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:39.912769+00:00
-- url     : https://prove2.me/submissions/43196a84-17b2-4c99-a1b7-14c3b222a62a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_witt_vec
import Theorems.Thm_GlobalTheory_SgAlg_WittField_pairM_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory.SgAlg Matrix
namespace GlobalTheory.SgAlg
theorem _root_.solution : ∀ {E : Type} [Field E] (σ : E →+* E), IsQA σ → ∀ {n a : ℕ}
    (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X →
    Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  intro E _ σ hQ n a J hJ X X' ⟨L, hL⟩ ⟨L', hL'⟩ hG
  obtain ⟨hσ, ⟨e, he⟩, -, h2, -⟩ := hQ
  have hδ : e - σ e ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
  have hσδ : σ (e - σ e) = -(e - σ e) := by rw [map_sub, hσ]; ring
  obtain ⟨g, hg, hgx⟩ := WittField.witt_vec hσ hJ.1 hJ.2 hδ hσδ h2.ne_zero a
    (fun j k => X k j) (fun j k => X' k j) (fun i => L i) (fun i => L' i)
    (fun i j => by rw [← Matrix.mul_apply', hL, Matrix.one_apply])
    (fun i j => by rw [← Matrix.mul_apply', hL', Matrix.one_apply])
    (fun i j => by rw [← WittField.pairM_entry X j i, ← WittField.pairM_entry X' j i, hG])
  refine ⟨g, hg, ?_⟩
  ext k j
  have := congrFun (hgx j) k
  simpa [Matrix.mul_apply, mulVec, dotProduct] using this
end GlobalTheory.SgAlg
