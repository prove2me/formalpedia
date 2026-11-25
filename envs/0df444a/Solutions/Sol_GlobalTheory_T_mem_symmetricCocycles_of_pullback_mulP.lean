-- Prove2me | solution 1 for GlobalTheory.T.mem_symmetricCocycles_of_pullback_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:34.75921+00:00
-- url     : https://prove2.me/submissions/e5c55092-8447-45d0-9390-594cc79022fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSymmetricCocyclesOfPullbackMulP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSymmetricCocyclesOfPullbackMulPStatement
import Theorems.Thm_GlobalTheory_PDivGroup_mem_symCocycles_of_pullTwo_mulP


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
theorem _root_.solution : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (c : G.A n ⊗[R] G.A n), pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1)) → c ∈ symCocycles R (G.A n) := by
  first | exact @GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | exact GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | (intros; apply GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP <;> assumption)
end _root_.GlobalTheory.T
