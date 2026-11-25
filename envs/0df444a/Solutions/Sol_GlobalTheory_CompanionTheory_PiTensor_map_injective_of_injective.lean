-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:52.573887+00:00
-- url     : https://prove2.me/submissions/e2848553-d3a1-461f-9401-9bdbc9be4108

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapInjectiveOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PiTensor
namespace GlobalTheory.CompanionTheory.PiTensor
theorem _root_.solution
    (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    (f : ∀ i, M i →ₗ[K] N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  have hg : ∀ i, ∃ g : N i →ₗ[K] M i, g ∘ₗ f i = LinearMap.id := fun i =>
    LinearMap.exists_leftInverse_of_injective (f i) (LinearMap.ker_eq_bot.2 (hf i))
  choose g hg using hg
  have hcomp : PiTensorProduct.map g ∘ₗ PiTensorProduct.map f = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  refine Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_
  exact LinearMap.congr_fun hcomp x
end GlobalTheory.CompanionTheory.PiTensor
