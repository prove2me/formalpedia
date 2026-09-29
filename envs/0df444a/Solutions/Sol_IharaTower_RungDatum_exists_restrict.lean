-- Prove2me | solution 1 for IharaTower.RungDatum.exists_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/57025e49-3703-5a1d-af5d-b47fe1f251b8

import Mathlib
import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_RungDatum_exists_restrict

set_option autoImplicit false

open IharaTower

theorem solution {𝒪 : Type} [CommRing 𝒪]
    {T₀ Tₐ T₁ : Type} [CommRing T₀] [CommRing Tₐ] [CommRing T₁] [Algebra 𝒪 T₀] [Algebra 𝒪 Tₐ] [Algebra 𝒪 T₁]
    {M₀ Mₐ M₁ : Type} [AddCommGroup M₀] [AddCommGroup Mₐ] [AddCommGroup M₁]
    [Module T₀ M₀] [Module Tₐ Mₐ] [Module T₁ M₁] [Module 𝒪 M₀] [Module 𝒪 Mₐ] [Module 𝒪 M₁]
    [IsScalarTower 𝒪 T₀ M₀] [IsScalarTower 𝒪 Tₐ Mₐ] [IsScalarTower 𝒪 T₁ M₁]
    {P₀ : LevelPairing (𝒪 := 𝒪) T₀ M₀} {Pₐ : LevelPairing (𝒪 := 𝒪) Tₐ Mₐ} (P₁ : LevelPairing (𝒪 := 𝒪) T₁ M₁)
    (R : RungDatum (𝒪 := 𝒪) T₀ Tₐ M₀ Mₐ P₀ Pₐ)
    (ι : M₁ →ₗ[𝒪] Mₐ) (hι : Function.Injective ι)
    (hB : ∀ x y : M₁, P₁.B x y = Pₐ.B (ι x) (ι y))
    (hcomb : ∀ m : M₀, R.i m ∈ LinearMap.range ι) :
    ∃ (iα : M₀ →ₗ[𝒪] M₁) (jα : M₁ →ₗ[𝒪] M₀),
      (∀ m, ι (iα m) = R.i m) ∧ (∀ m', jα m' = R.j (ι m')) ∧
      (∀ m' m, P₀.B (jα m') m = P₁.B m' (iα m)) ∧ (∀ m, jα (iα m) = R.Δ • m) := by

  let e : M₁ ≃ₗ[𝒪] LinearMap.range ι := LinearEquiv.ofInjective ι hι
  let iα : M₀ →ₗ[𝒪] M₁ := e.symm.toLinearMap.comp (LinearMap.codRestrict (LinearMap.range ι) R.i hcomb)
  have hiα : ∀ m, ι (iα m) = R.i m := fun m => by
    have : (e (iα m) : Mₐ) = R.i m := by
      simp only [iα, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
        LinearMap.codRestrict_apply]
    simpa [e, LinearEquiv.ofInjective_apply] using this
  let jα : M₁ →ₗ[𝒪] M₀ := R.j.comp ι
  refine ⟨iα, jα, hiα, fun m' => rfl, fun m' m => ?_, fun m => ?_⟩
  · show P₀.B (R.j (ι m')) m = P₁.B m' (iα m)
    rw [R.adjoint, hB, hiα]
  · show R.j (ι (iα m)) = R.Δ • m
    rw [hiα, R.comp_eq_smul]

end S_IharaTower_RungDatum_exists_restrict
end P2MW
export P2MW.S_IharaTower_RungDatum_exists_restrict (solution)
