-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:41.681834+00:00
-- url     : https://prove2.me/submissions/1a5ef6fe-458d-4224-b919-ff7245d9c872

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_lin_ne_zero
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_ev_lin
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_lin_dvd
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_eq_zero_of_forall_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
namespace GlobalTheory.SummableSeriesBounds
theorem _root_.solution (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    (π : C) (hπ : ‖π‖ < 1) :
    ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B),
      (∀ Φ : PowerSeries C, Φ ∈ B ↔ ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b) ∧
      (∀ Φ : B, ev Φ = ∑' n : ℕ, coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧
      (∀ Φ : B, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  refine ⟨bdd C, ev hπ, lin π, fun _ => Iff.rfl, fun _ => rfl, lin_ne_zero π,
    fun Φ => ⟨lin_dvd hπ Φ, ?_⟩, fun Φ hΦ => ?_⟩
  · rintro ⟨G, rfl⟩
    rw [map_mul, ev_lin, zero_mul]
  · by_contra hc
    push_neg at hc
    exact hΦ (eq_zero_of_forall_dvd hπ Φ hc)
end GlobalTheory.SummableSeriesBounds
