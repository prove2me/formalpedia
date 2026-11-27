-- Prove2me | solution 1 for GlobalTheory.ZLattice_finite_and_ncard_le_of_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:47.939576+00:00
-- url     : https://prove2.me/submissions/7146312d-cd83-4f0a-9441-7966e52ff87d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_ZLattice_finite_and_ncard_le_of_norm_map_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {n : ℕ} (hn : finrank ℝ E = n) {v : Fin n → E}
    (hvL : ∀ i, v i ∈ L) (hv : LinearIndependent ℝ v) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖v i‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → E →ₗ[ℝ] E) (hφ : Set.InjOn φ G) (hφL : ∀ g ∈ G, ∀ x ∈ L, φ g x ∈ L)
    (hG : ∀ g ∈ G, ∀ x ∈ L, ‖φ g x‖ ≤ c * ‖x‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) := by
  let ψ : G → L →ₗ[ℤ] L := fun g => ((φ g).restrictScalars ℤ).restrict (hφL g g.2)
  have hψ : Set.InjOn ψ Set.univ := by
    intro g _ g' _ h
    refine Subtype.ext (hφ g.2 g'.2 ?_)
    refine LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := L)) fun x hx => ?_
    exact congrArg Subtype.val (LinearMap.congr_fun h ⟨x, hx⟩)
  obtain ⟨hf, hc⟩ := ZLattice_finite_and_ncard_le_of_norm_map_le L hn
    (v := fun i => ⟨v i, hvL i⟩) hv h1 hc hL hvN Set.univ ψ hψ
    fun g _ x => hG g g.2 x x.2
  rw [Set.ncard_univ, Nat.card_coe_set_eq] at hc
  exact ⟨Set.finite_coe_iff.1 (Set.finite_univ_iff.1 hf), hc⟩
end GlobalTheory
