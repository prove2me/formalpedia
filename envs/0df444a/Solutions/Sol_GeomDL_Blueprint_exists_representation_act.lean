-- Prove2me | solution 1 for GeomDL.Blueprint.exists_representation_act
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:37:57.816123+00:00
-- url     : https://prove2.me/submissions/4cd62b09-fed2-442d-bafe-6024e4a9a6fd

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

theorem solution {G Ω : Type*} [Group G] [MulAction G Ω] :
    ∃ ρ : Representation ℝ G (Ω → ℝ),
      (∀ (g : G) (x : Ω → ℝ) (u : Ω), ρ g x u = x (g⁻¹ • u)) ∧
      (∀ (g h : G) (x : Ω → ℝ), ρ g (ρ h x) = ρ (g * h) x) := by
  let ρ : Representation ℝ G (Ω → ℝ) :=
    { toFun := fun g =>
        { toFun := fun x u => x (g⁻¹ • u)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := by ext x u; simp
      map_mul' := by intro g h; ext x u; simp [mul_smul] }
  refine ⟨ρ, fun g x u => rfl, fun g h x => ?_⟩
  rw [map_mul]; rfl
