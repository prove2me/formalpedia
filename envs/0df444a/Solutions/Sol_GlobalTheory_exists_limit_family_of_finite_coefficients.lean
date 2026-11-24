-- Prove2me | solution 1 for GlobalTheory.exists_limit_family_of_finite_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:48.247836+00:00
-- url     : https://prove2.me/submissions/69a0e0a1-7b24-4864-9e69-4349545a0b43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLimitFamilyOfFiniteCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (σ I R : Type) [Finite σ] [Finite I] [Finite R]
    (F : ℕ → I → (σ →₀ ℕ) → R) :
    ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧
      ∀ x m, m.degree ≤ N → F M x m = G x m := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩

  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → R, MapClusterPt G Filter.atTop F :=
    exists_clusterPt_of_compactSpace _
  refine ⟨G, fun N M₀ => ?_⟩

  have hnhds : ∀ᶠ H in nhds G, ∀ x, ∀ m ∈ {m : σ →₀ ℕ | m.degree ≤ N}, H x m = G x m := by
    refine Filter.eventually_all.2 fun x => ?_
    refine ((Finsupp.finite_of_degree_le N).eventually_all).2 fun m _ => ?_
    have hc : Continuous fun H : I → (σ →₀ ℕ) → R => H x m :=
      (continuous_apply m).comp (continuous_apply x)
    exact hc.continuousAt.eventually (isOpen_discrete {G x m} |>.mem_nhds rfl)
  obtain ⟨M, hM, hFM⟩ := Filter.frequently_atTop.1 (hG.frequently hnhds) M₀
  exact ⟨M, hM, fun x m hm => hFM x m hm⟩
end GlobalTheory
