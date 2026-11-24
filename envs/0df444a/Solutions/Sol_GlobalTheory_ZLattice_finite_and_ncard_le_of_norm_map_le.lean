-- Prove2me | solution 1 for GlobalTheory.ZLattice_finite_and_ncard_le_of_norm_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:14.953804+00:00
-- url     : https://prove2.me/submissions/4c1c46c5-ccff-448f-8327-13ebd1f72a23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_norm_map_le
import Theorems.Thm_GlobalTheory_linearIndependent_int_of_real

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
    [DiscreteTopology L] [IsZLattice ℝ L] {n : ℕ} (hn : finrank ℝ E = n) {v : Fin n → L}
    (hv : LinearIndependent ℝ fun i => (v i : E)) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖(v i : E)‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G)
    (hG : ∀ g ∈ G, ∀ x : L, ‖(φ g x : E)‖ ≤ c * ‖(x : E)‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) :=
  finite_and_ncard_le_of_norm_map_le L ((ZLattice.rank ℝ L).trans hn)
    (linearIndependent_int_of_real L hv) h1 hc hL hvN G φ hφ hG
end GlobalTheory
