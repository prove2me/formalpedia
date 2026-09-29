-- Prove2me | solution 1 for HopfOrder.exists_greatest_of_sup_closed_of_le_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/479fad20-89d2-5325-afc5-7b89d947c192

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (P : Subalgebra R A → Prop) (hsup : ∀ S S', P S → P S' → P (S ⊔ S'))
    (M : Subalgebra R A) [IsNoetherian R M] (hle : ∀ S, P S → S ≤ M) (h0 : ∃ S, P S) :
    ∃ S, P S ∧ ∀ S', P S' → S' ≤ S := by
  classical

  let F : {S : Subalgebra R A // P S} → Submodule R M := fun S =>
    Submodule.comap M.val.toLinearMap (Subalgebra.toSubmodule S.1)
  obtain ⟨S₀, hS₀⟩ := h0
  have hne : (Set.range F).Nonempty := ⟨F ⟨S₀, hS₀⟩, ⟨⟨S₀, hS₀⟩, rfl⟩⟩
  obtain ⟨N, ⟨⟨S, hS⟩, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R M) (Set.range F) hne
  refine ⟨S, hS, fun S' hS' => ?_⟩

  have hsup : P (S ⊔ S') := hsup S S' hS hS'
  have hFle : F ⟨S, hS⟩ ≤ F ⟨S ⊔ S', hsup⟩ := by
    intro m hm
    exact (le_sup_left : S ≤ S ⊔ S') hm
  have hEq : F ⟨S ⊔ S', hsup⟩ = F ⟨S, hS⟩ :=
    (hFle.eq_or_lt.resolve_right (hmax (F ⟨S ⊔ S', hsup⟩) ⟨⟨S ⊔ S', hsup⟩, rfl⟩)).symm
  intro x hx
  have hxM : x ∈ M := hle (S ⊔ S') hsup ((le_sup_right : S' ≤ S ⊔ S') hx)
  have hx' : (⟨x, hxM⟩ : M) ∈ F ⟨S ⊔ S', hsup⟩ := (le_sup_right : S' ≤ S ⊔ S') hx
  rw [hEq] at hx'
  exact hx'

end S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian
end P2MW
export P2MW.S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian (solution)
