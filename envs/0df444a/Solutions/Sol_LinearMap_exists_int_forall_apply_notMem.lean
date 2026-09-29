-- Prove2me | solution 1 for LinearMap.exists_int_forall_apply_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/742ecdcf-0379-549f-8d74-f9039e5ceaff

import Mathlib
import Theorems.Thm_LinearMap_exists_int_forall_apply_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_int_forall_apply_notMem

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

theorem solution
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] V) (W : ι → Submodule K V)
    (h : ∀ t ∈ S, ∃ c : Fin r → K, f t c ∉ W t) :
    ∃ c : Fin r → ℤ, ∀ t ∈ S, f t (fun i => (c i : K)) ∉ W t := by
  classical

  have hφ : ∀ t ∈ S, ∃ φ : Module.Dual K V, φ ∘ₗ f t ≠ 0 ∧ (W t).map φ = ⊥ := by
    intro t ht
    obtain ⟨c₀, hc₀⟩ := h t ht
    obtain ⟨φ, hφ0, hφW⟩ := (W t).exists_dual_map_eq_bot_of_notMem hc₀ inferInstance
    exact ⟨φ, fun h0 => hφ0 (by simpa using LinearMap.congr_fun h0 c₀), hφW⟩
  choose! φ hφne hφW using hφ

  obtain ⟨c, hc⟩ := LinearMap.exists_int_forall_apply_ne S (fun t => φ t ∘ₗ f t) (fun _ => 0) hφne
  refine ⟨c, fun t ht hmem => hc t ht ?_⟩
  have hz : φ t (f t (fun i => (c i : K))) ∈ (W t).map (φ t) := Submodule.mem_map_of_mem hmem
  rw [hφW t ht, Submodule.mem_bot] at hz
  simpa using hz

#print axioms solution

end S_LinearMap_exists_int_forall_apply_notMem
end P2MW
export P2MW.S_LinearMap_exists_int_forall_apply_notMem (solution)
