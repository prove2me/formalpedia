-- Prove2me | solution 1 for GlobalTheory.T.exists_mulP_eq_of_transl_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:27:38.898522+00:00
-- url     : https://prove2.me/submissions/eb9290ed-4896-4875-b86e-8630619a3594

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariantStatement
import Theorems.Thm_GlobalTheory_PDivGroup_exists_mulP_eq_of_transl_eq


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
theorem _root_.solution : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (a : G.A (n + 1)), G.transl n a = a ⊗ₜ[R] 1 → ∃ e : G.A n, G.mulP n e = a := by
  first | exact @GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | exact GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | (intros; apply GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq <;> assumption)
end _root_.GlobalTheory.T
