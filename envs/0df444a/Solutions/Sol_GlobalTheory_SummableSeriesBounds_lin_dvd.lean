-- Prove2me | solution 1 for GlobalTheory.SummableSeriesBounds.lin_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:49.354514+00:00
-- url     : https://prove2.me/submissions/3e07a54f-04d3-40db-84e0-8091881101c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_coeff_zero_lin
import Theorems.Thm_GlobalTheory_SummableSeriesBounds_coeff_succ_lin

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
theorem _root_.solution [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ev hπ Φ = 0) :
    lin π ∣ Φ := by
  obtain ⟨b, hb⟩ := Φ.2
  have hs : ∀ m, Summable fun k => ‖coeff (k + m) (Φ : PowerSeries C) * π ^ k‖ :=
    fun m => summable_norm_mul_pow_of_bounded hπ (a := fun k => coeff (k + m) (Φ : PowerSeries C))
      (fun k => hb _)
  let g : ℕ → C := fun m => ∑' k, coeff (k + m) (Φ : PowerSeries C) * π ^ k
  have hg : ∀ m, g m = coeff m (Φ : PowerSeries C) + π * g (m + 1) := by
    intro m
    simp only [g]
    rw [(hs m).of_norm.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp
    · refine tsum_congr fun k => ?_
      rw [show k + 1 + m = k + (m + 1) by ring]
      ring
  have hg0 : g 0 = 0 := h
  have hgb : ∀ m, ‖g m‖ ≤ ∑' k, b * ‖π‖ ^ k := by
    intro m
    refine tsum_of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b).hasSum fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hb _) (by positivity)
  refine ⟨⟨PowerSeries.mk fun n => g (n + 1), ⟨_, fun n => by rw [coeff_mk]; exact hgb _⟩⟩, ?_⟩
  apply Subtype.ext
  change (Φ : PowerSeries C) = (X - PowerSeries.C π) * PowerSeries.mk fun n => g (n + 1)
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_lin, coeff_mk]
    have := hg 0
    rw [hg0] at this
    linear_combination -this
  | succ n =>
    rw [coeff_succ_lin, coeff_mk, coeff_mk]
    linear_combination -hg (n + 1)
end GlobalTheory.SummableSeriesBounds
