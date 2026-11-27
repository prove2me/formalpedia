-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Hgt.integrable_of_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:09.464071+00:00
-- url     : https://prove2.me/submissions/7e42043b-fdb4-4fd0-8486-d870325714f8

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HgtCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Hgt
open scoped NNReal ENNReal
open MeasureTheory Topology
namespace GlobalTheory.ThK.Dbl.Hgt
theorem _root_.solution {G : Type} [MeasurableSpace G] (μ : Measure G) {f : G → ℝ} (hf : Measurable f) (h0 : ∀ g, 0 < f g)
    {R : ℝ} (h1 : 1 ≤ R) (hR : ∀ g, f g ≤ R) {C : ℝ≥0∞} (hC : C ≠ ⊤) (b : ℝ≥0)
    (h : ∀ j : ℕ, μ {g | (1 / 2) ^ j ≤ f g} ≤ C * b ^ j) : ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => f g ^ t) μ := by
  classical
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (b + 1) by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, fun t ht => ⟨(hf.pow_const t).aestronglyMeasurable, ?_⟩⟩
  have t0 : 0 ≤ t := (Nat.cast_nonneg k).trans ht
  let P : ℕ → Set G := fun j => {g | (1 / 2) ^ j ≤ f g ∧ f g ≤ 2 * R * (1 / 2) ^ j}
  have hP : ⋃ j, P j = Set.univ := Set.eq_univ_of_forall fun g => by
    have ex : ∃ j : ℕ, (1 / 2 : ℝ) ^ j ≤ f g := (exists_pow_lt_of_lt_one (h0 g) (by norm_num)).imp fun _ => le_of_lt
    refine Set.mem_iUnion.2 ⟨Nat.find ex, Nat.find_spec ex, ?_⟩
    rcases e : Nat.find ex with _ | j
    · have := hR g; simp; linarith
    · have := Nat.find_min ex (m := j) (by omega)
      have p : (0 : ℝ) < (1 / 2) ^ j := by positivity
      rw [pow_succ]; nlinarith
  set ρ : ℝ≥0∞ := ENNReal.ofReal ((1 / 2) ^ t) * b
  have hρ : ρ < 1 := by
    have : ((1 / 2 : ℝ)) ^ t ≤ (1 / 2) ^ k := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht
    rw [lt_div_iff₀ (by positivity)] at hk
    have p : (0 : ℝ) < (1 / 2) ^ t := by positivity
    rw [show ρ = ENNReal.ofReal ((1 / 2) ^ t * b) by rw [ENNReal.ofReal_mul p.le, ENNReal.ofReal_coe_nnreal], ENNReal.ofReal_lt_one]
    nlinarith [b.2, show (0 : ℝ) ≤ b from b.2]
  calc ∫⁻ g, ‖f g ^ t‖ₑ ∂μ = ∫⁻ g in ⋃ j, P j, ‖f g ^ t‖ₑ ∂μ := by rw [hP, Measure.restrict_univ]
    _ ≤ ∑' j, ∫⁻ g in P j, ‖f g ^ t‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal ((2 * R) ^ t) * C * ρ ^ j := ENNReal.tsum_le_tsum fun j => by
      refine (setLIntegral_mono (g := fun _ => ENNReal.ofReal ((2 * R) ^ t) * ENNReal.ofReal ((1 / 2) ^ t) ^ j)
        measurable_const fun g hg => ?_).trans ?_
      · rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (h0 g).le _), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul_natCast (by norm_num), mul_comm t, Real.rpow_natCast_mul (by norm_num),
          ← Real.mul_rpow (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (h0 g).le hg.2 t0)
      · rw [setLIntegral_const]
        refine (mul_le_mul_right ((measure_mono fun g hg => hg.1).trans (h j)) _).trans_eq ?_
        simp only [ρ, mul_pow]; ring
    _ < ⊤ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.lt_top)
        (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ))
end GlobalTheory.ThK.Dbl.Hgt
