-- Prove2me | solution 1 for GlobalTheory.exists_surjective_lift_of_ker_le_maximalIdeal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:56.31507+00:00
-- url     : https://prove2.me/submissions/604ed447-ddf9-46b0-a8f3-b95defd25b04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleGeneratorsTowerLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
    {A B : Type} [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] [AddCommGroup B] [Module Λ B]
    (t : A →ₗ[Λ] B) (ht : Function.Surjective t)
    (hk : LinearMap.ker t ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ A))
    {a : ℕ} (p : (Fin a → Λ) →ₗ[Λ] B) (hp : Function.Surjective p) :
    ∃ q : (Fin a → Λ) →ₗ[Λ] A, Function.Surjective q ∧ t ∘ₗ q = p := by
  obtain ⟨q, hq⟩ := Module.projective_lifting_property t p ht
  refine ⟨q, ?_, hq⟩
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal Λ)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) fun y _ => ?_
  obtain ⟨x, hx⟩ := hp (t y)
  have h1 : y - q x ∈ LinearMap.ker t := by
    rw [LinearMap.mem_ker, map_sub, ← hx, ← hq, LinearMap.comp_apply, sub_self]
  have h2 : y = q x + (y - q x) := by abel
  rw [h2]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self q x) (hk h1)
end GlobalTheory
