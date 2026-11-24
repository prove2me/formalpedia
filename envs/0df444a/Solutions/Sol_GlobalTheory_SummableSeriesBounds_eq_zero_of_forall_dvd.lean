-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.eq_zero_of_forall_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:52.160777+00:00
-- url     : https://prove2.me/submissions/5d708262-f752-4b94-831d-652174cb68a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_bound_of_lin_pow_mul
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_decay

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
theorem _root_.solution {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ∀ n, lin π ^ n ∣ Φ) :
    Φ = 0 := by
  obtain ⟨b, hb⟩ := Φ.2
  apply Subtype.ext
  ext m
  have key : ∀ n, ‖coeff m (Φ : PowerSeries C)‖ ≤ ‖π‖ ^ n * b := by
    intro n
    obtain ⟨G, hG⟩ := h (n + m)
    have h1 := bound_of_lin_pow_mul hπ (n + m) G (by rw [← hG]; exact hb)
    have h2 := decay hπ h1 (n + m) m
    rw [Nat.add_sub_cancel] at h2
    rw [hG]
    exact h2
  have ht : Tendsto (fun k : ℕ => ‖π‖ ^ k * b) atTop (𝓝 (0 * b)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const b
  rw [zero_mul] at ht
  have := ge_of_tendsto' ht key
  simpa using this
end GlobalTheory.SummableSeriesBounds
