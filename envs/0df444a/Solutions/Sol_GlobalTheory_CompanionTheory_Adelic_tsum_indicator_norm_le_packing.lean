-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:38.998964+00:00
-- url     : https://prove2.me/submissions/8795e66e-1e78-4899-879a-d5e20f1b4474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_Packing_Sep_card_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_Packing_exists_max_sep
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_Packing_Sep_exists_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.Adelic.Packing
namespace GlobalTheory.CompanionTheory.Adelic
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  intro V _ _ _ Λ _ e r R hr hrR
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_sep e hr hrR
  set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf
  have hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
      ∑ t ∈ s, f (l - t) := by
    intro l
    by_cases hl : ‖e l‖ ≤ R
    · obtain ⟨t, ht, hlt⟩ := hs.exists_near hr hmax hl
      have h1 : f (l - t) = 1 := Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _
      calc Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le) l
        _ = f (l - t) := h1.symm
        _ ≤ ∑ t ∈ s, f (l - t) :=
            Finset.single_le_sum (f := fun t => f (l - t)) (fun _ _ => zero_le) ht
    · rw [Set.indicator_of_notMem (by simpa using hl)]
      exact zero_le
  have hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l := fun t =>
    (Equiv.subRight t).tsum_eq f
  have hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) := by
    have h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V := by
      refine (Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)
      have := hr.le.trans hrR
      gcongr
      norm_num
    calc (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  calc ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l
      ≤ ∑' l : Λ, ∑ t ∈ s, f (l - t) := ENNReal.tsum_le_tsum hpt
    _ = ∑ t ∈ s, ∑' l : Λ, f (l - t) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by
        simp only [hshift, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr
end GlobalTheory.CompanionTheory.Adelic
