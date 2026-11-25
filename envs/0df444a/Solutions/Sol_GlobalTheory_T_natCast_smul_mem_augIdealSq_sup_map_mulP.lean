-- Prove2me | solution 1 for GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:44.81479+00:00
-- url     : https://prove2.me/submissions/583e5334-0ee0-4a97-85f2-d79a15cc2f4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastSmulMemAugIdealSqSupMapMulP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastSmulMemAugIdealSqSupMapMulPStatement
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_natCast_smul_mem_augSq_sup_map


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
theorem _root_.solution : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))), (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  first | exact @GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map | exact GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map | (intros; apply GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map <;> assumption)
end _root_.GlobalTheory.T
