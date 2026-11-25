-- Prove2me | solution 1 for GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:59:22.9133+00:00
-- url     : https://prove2.me/submissions/8f7ce5c4-ad37-40d3-8afd-095405295892

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSymmetricCocyclesOfPullbackMulP
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_Test_mulP_injective
import Theorems.Thm_GlobalTheory_PDivGroup_pullbackTwo_mulP_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory
open GlobalTheory.PDivGroup
namespace GlobalTheory.PDivGroup
theorem _root_.solution {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) (h : pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1))) :
    c ∈ symCocycles R (G.A n) := by
  rw [mem_symCocycles] at h ⊢
  have h3 : Function.Injective
      (TensorProduct.map (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) (pullbackTwo (G.mulP n))) :=
    TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n)
      (G.pullbackTwo_mulP_injective n)
  refine ⟨h3 ?_, G.pullbackTwo_mulP_injective n ?_⟩
  · rw [← cobTwo_pullTwo, h.1, map_zero]
  · rw [← h.2]
    exact TensorProduct.map_comm _ _ c
end GlobalTheory.PDivGroup
