-- Prove2me | solution 1 for LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c6c25f4e-7c85-598e-9d9f-1f946e12ce50

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul

set_option autoImplicit false

universe u v w

namespace HomARSol

open Submodule

theorem pi_mem_smul_top {B : Type u} [CommRing B] (J : Ideal B) {N : Type w} [AddCommGroup N] [Module B N]
    {r : ℕ} (x : Fin r → N) (hx : ∀ i, x i ∈ J • (⊤ : Submodule B N)) :
    x ∈ J • (⊤ : Submodule B (Fin r → N)) := by
  classical
  have : x = ∑ i, Pi.single i (x i) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  refine Submodule.sum_mem _ fun i _ => ?_

  have hlin : ∀ y : N, y ∈ J • (⊤ : Submodule B N) → (Pi.single i y : Fin r → N) ∈ J • (⊤ : Submodule B (Fin r → N)) := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha z _
      have : (Pi.single i (a • z) : Fin r → N) = a • Pi.single i z := by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [Pi.single_apply, h]
      rw [this]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · intro z z' hz hz'
      rw [Pi.single_add]
      exact Submodule.add_mem _ hz hz'
  exact hlin _ (hx i)

end HomARSol

open HomARSol in
theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (g : M →ₗ[B] N),
      LinearMap.range g ≤ I ^ (n + c) • (⊤ : Submodule B N) →
      g ∈ I ^ n • (⊤ : Submodule B (M →ₗ[B] N)) := by
  classical
  obtain ⟨r, gen, hgen⟩ := Module.Finite.exists_fin (R := B) (M := M)

  let ev : (M →ₗ[B] N) →ₗ[B] (Fin r → N) :=
    { toFun := fun g i => g (gen i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro g h hgh
    refine LinearMap.ext_on_range hgen fun i => ?_
    exact congrFun hgh i
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range ev)
  refine ⟨k, fun n g hg => ?_⟩
  have h1 : ev g ∈ I ^ (n + k) • (⊤ : Submodule B (Fin r → N)) ⊓ LinearMap.range ev := by
    refine ⟨pi_mem_smul_top _ _ fun i => hg ⟨gen i, rfl⟩, ⟨g, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : ev g ∈ I ^ n • LinearMap.range ev :=
    Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨h, hh, hhg⟩ := h2
  rw [← hev hhg]
  exact hh

end S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul
end P2MW
export P2MW.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul (solution)
