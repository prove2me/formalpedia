-- Prove2me | solution 1 for GlobalTheory.PDivGroup.cobOne_transl_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:19:40.861969+00:00
-- url     : https://prove2.me/submissions/d5a289cf-a558-4d65-83a7-7394a473fc02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoboundaryTranslationInvariantPTorsion
import Theorems.Thm_GlobalTheory_PDivGroup_lTensor_transl_sub_cobOne

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
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
namespace GlobalTheory.PDivGroup
theorem _root_.solution {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (x : G.A (n + 1)) (b : G.A 1) (h : G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) :
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 ∧
    ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor
      (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  have h2 := G.lTensor_transl_sub_cobOne n x b h
  refine ⟨?_, h2⟩
  rw [← (mem_symCocycles.1 (cobOne_mem x)).2, LinearMap.rTensor_comm, h2, map_zero]
end GlobalTheory.PDivGroup
