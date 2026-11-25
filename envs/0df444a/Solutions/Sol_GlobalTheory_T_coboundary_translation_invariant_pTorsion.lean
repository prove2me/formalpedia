-- Prove2me | solution 1 for GlobalTheory.T.coboundary_translation_invariant_pTorsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:12.618422+00:00
-- url     : https://prove2.me/submissions/20dcc35f-4b3e-4723-a645-d67e21607f2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoboundaryTranslationInvariantPTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoboundaryTranslationInvariantPTorsionStatement
import Theorems.Thm_GlobalTheory_PDivGroup_cobOne_transl_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (x : G.A (n + 1)) (b : G.A 1), G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b → ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 ∧ ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  first | exact @GlobalTheory.PDivGroup.cobOne_transl_invariant | exact GlobalTheory.PDivGroup.cobOne_transl_invariant | (intros; apply GlobalTheory.PDivGroup.cobOne_transl_invariant <;> assumption)
end _root_.GlobalTheory.T
