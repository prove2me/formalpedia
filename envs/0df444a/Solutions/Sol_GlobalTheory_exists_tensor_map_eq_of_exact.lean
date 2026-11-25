-- Prove2me | solution 1 for GlobalTheory.exists_tensor_map_eq_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:05.063842+00:00
-- url     : https://prove2.me/submissions/9c22dcfc-b95f-44e0-9727-a80fc74b7dc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPullbackMulPOfPTorsionInvariant
import Theorems.Thm_GlobalTheory_IsBicharacter_map


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
namespace GlobalTheory
theorem _root_.solution {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R M]
    [Module.Flat R N] [Module.Flat R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (h : Function.Exact f g) (F : N ⊗[R] N)
    (h₁ : g.rTensor N F = 0) (h₂ : g.lTensor N F = 0) :
    ∃ c : M ⊗[R] M, TensorProduct.map f f c = F := by
  obtain ⟨F', rfl⟩ := (Module.Flat.lTensor_exact N h F).1 h₂
  have h₃ : g.rTensor M F' = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := P) f hf
    rw [map_zero, ← h₁, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  obtain ⟨c, rfl⟩ := (Module.Flat.rTensor_exact M h F').1 h₃
  exact ⟨c, by rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]⟩
end GlobalTheory
