-- Prove2me | solution 1 for LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/815305b6-1d0f-52f7-ae41-9cb015f38001

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional

set_option autoImplicit false

theorem solution
    {X : Type*} (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥Y]
    (T : ℕ → (↥Y →ₗ[ℂ] (X → ℂ)))
    (hT : ∀ (y : ↥Y) (x : X), Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : X → ℂ) x))) :
    ∃ n, ∀ y : ↥Y, T n y = 0 → y = 0 := by
  classical
  let ev : X → (↥Y →ₗ[ℂ] ℂ) := fun x =>
    { toFun := fun y => (y : X → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Finset X → Submodule ℂ ↥Y := fun s => ⨅ x ∈ s, LinearMap.ker (ev x)
  have hW_anti : ∀ s t : Finset X, s ⊆ t → W t ≤ W s := fun s t hst =>
    biInf_mono hst
  have hsep : ∃ s : Finset X, W s = ⊥ := by
    suffices h : ∀ (d : ℕ) (s : Finset X), Module.finrank ℂ ↥(W s) ≤ d → ∃ t : Finset X, W t = ⊥ from
      h _ ∅ le_rfl
    intro d
    induction d with
    | zero =>
      intro s hs
      exact ⟨s, Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hs)⟩
    | succ d ih =>
      intro s hs
      by_cases hbot : W s = ⊥
      · exact ⟨s, hbot⟩
      · obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff (W s)).mp hbot
        have hyfun : (y : X → ℂ) ≠ 0 := fun h => hy0 (Subtype.ext h)
        obtain ⟨x, hx⟩ : ∃ x, (y : X → ℂ) x ≠ 0 := Function.ne_iff.mp hyfun
        refine ih (insert x s) (Nat.le_of_lt_succ (lt_of_lt_of_le ?_ hs))
        apply Submodule.finrank_lt_finrank_of_lt
        refine lt_of_le_of_ne (hW_anti s _ (Finset.subset_insert x s)) fun heq => hx ?_
        have hy' : y ∈ W (insert x s) := heq ▸ hyW
        have h1 := (Submodule.mem_iInf _).mp hy' x
        have h2 := (Submodule.mem_iInf _).mp h1 (Finset.mem_insert_self x s)
        simpa [ev] using h2
  obtain ⟨s, hs⟩ := hsep
  let Φ : (X → ℂ) →ₗ[ℂ] (↥s → ℂ) :=
    { toFun := fun f i => f i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦinj : ∀ y : ↥Y, Φ (y : X → ℂ) = 0 → y = 0 := by
    intro y hy
    have hyW : y ∈ W s := by
      refine (Submodule.mem_iInf _).mpr fun x => (Submodule.mem_iInf _).mpr fun hx => ?_
      show (y : X → ℂ) x = 0
      exact congr_fun hy ⟨x, hx⟩
    rw [hs] at hyW
    exact (Submodule.mem_bot ℂ).mp hyW
  let b := Module.finBasis ℂ ↥Y
  let v : Fin (Module.finrank ℂ ↥Y) → (↥s → ℂ) := fun j => Φ (b j : X → ℂ)
  have hv : LinearIndependent ℂ v := by
    refine LinearIndependent.map' b.linearIndependent (Φ ∘ₗ Y.subtype) ?_
    rw [LinearMap.ker_eq_bot']
    intro y hy
    exact hΦinj y hy
  have htend : Filter.Tendsto (fun n => fun j => Φ (T n (b j))) Filter.atTop (nhds v) := by
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_pi_nhds]
    intro i
    exact hT (b j) i
  obtain ⟨n, hn⟩ := (htend.eventually hv.eventually).exists
  refine ⟨n, fun y hy => ?_⟩
  have h0 : ∑ j, (b.repr y j) • Φ (T n (b j)) = 0 := by
    have hΦ0 : Φ (T n y) = 0 := by rw [hy, map_zero]
    have hy' : y = ∑ j, (b.repr y j) • b j := (b.sum_repr y).symm
    rw [hy', map_sum, map_sum] at hΦ0
    simpa only [map_smul] using hΦ0
  have hc := Fintype.linearIndependent_iff.mp hn (fun j => b.repr y j) h0
  rw [← b.sum_repr y]
  exact Finset.sum_eq_zero fun j _ => by rw [show b.repr y j = 0 from hc j, zero_smul]

end S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
end P2MW
export P2MW.S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional (solution)
