-- Prove2me | solution 1 for MasulloGRH.nuclear_repr_of_quasinuclear_chain
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:37:49.211842+00:00
-- url     : https://prove2.me/submissions/2eef08c2-ff9a-4b9e-a688-5df1ea3bd2d0

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_quasinuclear_comp_nuclear_expansion

set_option autoImplicit false

open MasulloGRH Filter Topology

universe u

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E]
    (q p r : Seminorm ℂ E)
    (g : ℕ → E →ₗ[ℂ] ℂ) (μ : ℕ → ℝ) (hμ0 : ∀ n, 0 ≤ μ n) (hμ : Summable μ)
    (hg : ∀ n x, ‖g n x‖ ≤ p x) (hq : ∀ x, q x ≤ ∑' n, μ n * ‖g n x‖)
    (h : ℕ → E →ₗ[ℂ] ℂ) (ν : ℕ → ℝ) (hν0 : ∀ n, 0 ≤ ν n) (hν : Summable ν)
    (hh : ∀ n x, ‖h n x‖ ≤ r x) (hp : ∀ x, p x ≤ ∑' n, ν n * ‖h n x‖) :
    ∃ (k : ℕ → E →ₗ[ℂ] ℂ) (y : ℕ → E) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖k n x‖ ≤ r x) ∧ (∀ n, q (y n) ≤ 1) ∧
      ∀ x, Tendsto (fun N => q (x - ∑ n ∈ Finset.range N, (c n * k n x) • y n)) atTop (𝓝 0) := by
  letI : TopologicalSpace E := ⊥
  haveI : DiscreteTopology E := ⟨rfl⟩
  let toCLM : (E →ₗ[ℂ] ℂ) → StrongDual ℂ E := fun l => ⟨l, continuous_of_discreteTopology⟩
  obtain ⟨k, y, c, hc0, hc, hk, hy, hexp⟩ :=
    quasinuclear_comp_nuclear_expansion E q p r (fun n => toCLM (g n)) μ hμ0 hμ hg hq
      (fun n => toCLM (h n)) ν hν0 hν hh hp
  exact ⟨fun n => (k n : E →ₗ[ℂ] ℂ), y, c, hc0, hc, hk, hy, hexp⟩
