-- Prove2me | solution 1 for GlobalTheory.existsUnique_algHom_of_compatible_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:47.763853+00:00
-- url     : https://prove2.me/submissions/68289144-cd3a-433d-a8fc-301821eb9064

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_existsUnique_of_compatible_tower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
namespace GlobalTheory
theorem _root_.solution {A B : Type*} [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [IsAdicComplete I B] {C : ℕ → Type*} [∀ n, Ring (C n)] [∀ n, Algebra R (C n)]
    (π : ∀ n, B →ₐ[R] C n) (hπ : ∀ n, Function.Surjective (π n))
    (hker : ∀ n x, π n x = 0 ↔ x ∈ (I ^ n • ⊤ : Submodule R B))
    (t : ∀ n, C (n + 1) → C n) (ht : ∀ n x, t n (π (n + 1) x) = π n x)
    (f : ∀ n, A →ₐ[R] C n) (hf : ∀ n a, t n (f (n + 1) a) = f n a) :
    ∃! g : A →ₐ[R] B, ∀ n a, π n (g a) = f n a := by
  have H := fun a ↦ existsUnique_of_compatible_tower I (fun n ↦ π n) hπ
    (fun n x y ↦ by rw [← hker, map_sub, sub_eq_zero]) t ht (fun n ↦ f n a) (fun n ↦ hf n a)
  choose g hg hu using H
  refine ⟨{ toFun := g
            map_one' := (hu _ _ fun n ↦ by simp).symm
            map_mul' a b := (hu _ _ fun n ↦ by simp [hg]).symm
            map_zero' := (hu _ _ fun n ↦ by simp).symm
            map_add' a b := (hu _ _ fun n ↦ by simp [hg]).symm
            commutes' r := (hu _ _ fun n ↦ by simp).symm }, fun n a ↦ hg a n,
    fun g' hg' ↦ AlgHom.ext fun a ↦ hu a _ fun n ↦ hg' n a⟩
end GlobalTheory
