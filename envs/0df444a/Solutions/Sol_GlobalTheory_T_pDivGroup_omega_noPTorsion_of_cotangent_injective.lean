-- Prove2me | solution 1 for GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:51.197483+00:00
-- url     : https://prove2.me/submissions/aea0f772-6010-475e-aab2-50912632c504

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupOmegaNoPTorsionOfCotangentInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement
import Theorems.Thm_GlobalTheory_omega_eq_zero_of_p_smul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R), (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) → ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  first | exact @GlobalTheory.omega_eq_zero_of_p_smul_eq_zero | exact GlobalTheory.omega_eq_zero_of_p_smul_eq_zero | (intros; apply GlobalTheory.omega_eq_zero_of_p_smul_eq_zero <;> assumption)
end _root_.GlobalTheory.T
