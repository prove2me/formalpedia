-- Prove2me | solution 1 for GlobalTheory.PDivGroup.kerIdeal_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:52.411293+00:00
-- url     : https://prove2.me/submissions/7bf1426e-cdb0-465f-a446-65a8647bf421

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_comp_of_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv
open GlobalTheory
open GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
open scoped TensorProduct
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
namespace GlobalTheory.PDivGroup
namespace _root_.GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) :
    _root_.GlobalTheory.PDiv.kerIdeal (G.mulP n) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by
  unfold _root_.GlobalTheory.PDiv.torsionIdeal
  rw [← G.mulP_comp_res n,
    _root_.GlobalTheory.PDiv.kerIdeal_comp_of_surjective _ (G.res_surjective n)]
end _root_.GlobalTheory.PDivGroup
end GlobalTheory.PDivGroup
