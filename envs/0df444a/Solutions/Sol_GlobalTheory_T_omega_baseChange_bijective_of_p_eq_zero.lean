-- Prove2me | solution 1 for GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:36.569501+00:00
-- url     : https://prove2.me/submissions/b1ce139d-89c6-4a8d-b939-87c410c0be6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaBaseChangeBijectiveOfPEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaBaseChangeBijectiveOfPEqZeroStatement
import Theorems.Thm_GlobalTheory_PDivGroup_omega_baseChange_bijective


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
theorem _root_.solution : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type) [CommRing R'] [Algebra R R'], (p : R) = 0 → Function.Bijective (liftSemi (G.toBase R').omega) := by
  first | exact @GlobalTheory.PDivGroup.omega_baseChange_bijective | exact GlobalTheory.PDivGroup.omega_baseChange_bijective | (intros; apply GlobalTheory.PDivGroup.omega_baseChange_bijective <;> assumption)
end _root_.GlobalTheory.T
