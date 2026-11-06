-- Prove2me | solution 1 for LinParamBandits.UEFinite.radius_deviation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:32:18.396198+00:00
-- url     : https://prove2.me/submissions/1963a72a-8682-487f-91ef-3fed03e5d6f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy
import Theorems.Thm_LinParamBandits_UEFinite_chernoff_finite_arms
import Theorems.Thm_LinParamBandits_UEFinite_chernoff_infinite_arms

open MeasureTheory ProbabilityTheory

namespace UEFinRadDevAux

open LinParamBandits.UEFinite

lemma kappa0_ge_two (ū lam₀ : ℝ) (hū : 0 < ū) (hlam₀ : 0 < lam₀) : 2 ≤ kappa0 ū lam₀ := by
  unfold kappa0
  have h1 : 0 ≤ Real.log (1 + 36 * ū ^ 2 / lam₀) := Real.log_nonneg (by
    have : 0 ≤ 36 * ū ^ 2 / lam₀ := by positivity
    linarith)
  have h2 : 1 ≤ Real.sqrt (1 + Real.log (1 + 36 * ū ^ 2 / lam₀)) := by
    rw [Real.one_le_sqrt]; linarith
  linarith

/-- Case `min = |𝒰|` (Theorem B.1): `t^{5n} e^{-ζ²/2} ≤ 1/t²` for `ζ = 4κ₀² √(log t) √n`. -/
lemma bound_B1 (κ : ℝ) (hκ : 2 ≤ κ) (t n : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n) :
    (t : ℝ) ^ (5 * n) * Real.exp (-(4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt n) ^ 2 / 2) ≤
      1 / (t : ℝ) ^ 2 := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hsq : (4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt n) ^ 2 =
      16 * κ ^ 4 * Real.log t * n := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hlog, Real.sq_sqrt (by positivity)]; ring
  rw [hsq]
  have hpow : (t : ℝ) ^ (5 * n) = Real.exp ((5 * n : ℝ) * Real.log t) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos htpos]; push_cast; ring_nf
  have hinv : 1 / (t : ℝ) ^ 2 = Real.exp (-2 * Real.log t) := by
    rw [show (-2 : ℝ) * Real.log t = -(2 * Real.log t) by ring, Real.exp_neg,
      show (2 : ℝ) * Real.log t = Real.log ((t : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), one_div]
  rw [hpow, hinv, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hκ4 : 16 ≤ κ ^ 4 := by nlinarith [sq_nonneg κ, sq_nonneg (κ ^ 2 - 4)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (5 * n : ℝ) * Real.log t + -(16 * κ ^ 4 * Real.log t * n) / 2 =
      (n : ℝ) * Real.log t * (5 - 8 * κ ^ 4) := by ring
  rw [this]
  have h1 : (n : ℝ) * Real.log t * (5 - 8 * κ ^ 4) ≤ (n : ℝ) * Real.log t * (-2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  nlinarith

/-- Case `min = r log t` (Theorem B.2): `t^{rκ₀²} e^{-ζ²/4} ≤ 1/t²` for `ζ = 4κ₀ √(r log t)`. -/
lemma bound_B2 (κ : ℝ) (hκ : 2 ≤ κ) (t r : ℕ) (ht : 2 ≤ t) (hr : 2 ≤ r) :
    (t : ℝ) ^ ((r : ℝ) * κ ^ 2) * Real.exp (-(4 * κ * Real.sqrt ((r : ℝ) * Real.log t)) ^ 2 / 4) ≤
      1 / (t : ℝ) ^ 2 := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hsq : (4 * κ * Real.sqrt ((r : ℝ) * Real.log t)) ^ 2 = 16 * κ ^ 2 * (r * Real.log t) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hsq, Real.rpow_def_of_pos htpos]
  have hinv : 1 / (t : ℝ) ^ 2 = Real.exp (-2 * Real.log t) := by
    rw [show (-2 : ℝ) * Real.log t = -(2 * Real.log t) by ring, Real.exp_neg,
      show (2 : ℝ) * Real.log t = Real.log ((t : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), one_div]
  rw [hinv, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have : Real.log t * (r * κ ^ 2) + -(16 * κ ^ 2 * (r * Real.log t)) / 4 =
      -(3 * r * κ ^ 2) * Real.log t := by ring
  rw [this]
  have h3 : 2 ≤ 3 * r * κ ^ 2 := by nlinarith
  nlinarith

lemma two_le_zeta2 (κ : ℝ) (hκ : 2 ≤ κ) (t r : ℕ) (ht : 2 ≤ t) (hr : 2 ≤ r) :
    2 ≤ 4 * κ * Real.sqrt ((r : ℝ) * Real.log t) := by
  have hlog2 : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : 1 ≤ (r : ℝ) * Real.log t := by nlinarith
  have h2 : 1 ≤ Real.sqrt ((r : ℝ) * Real.log t) := by rw [Real.one_le_sqrt]; exact h1
  nlinarith

end UEFinRadDevAux

open UEFinRadDevAux in
theorem solution
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰cpt : IsCompact 𝒰) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : LinParamBandits.UEFinite.NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : LinParamBandits.UEFinite.ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : LinParamBandits.UEFinite.IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) :
    (∀ u ∈ 𝒰, LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ u (LinParamBandits.UEGeneral.Zhat h - z) > LinParamBandits.UEFinite.radius σ₀ ū lam₀ 𝒰 h u} ≤
        ENNReal.ofReal (1 / (t : ℝ) ^ 2)) ∧
    (∀ x : LinParamBandits.LowerBound.Vec r, LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (ψ.act t h - x) (LinParamBandits.UEGeneral.Zhat h - z) >
        LinParamBandits.UEFinite.alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) * Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) *
          LinParamBandits.UEFinite.normC h (ψ.act t h - x)} ≤
        ENNReal.ofReal (1 / (t : ℝ) ^ 2)) := by
  set κ := LinParamBandits.UEFinite.kappa0 ū lam₀ with hκdef
  have hκ : 2 ≤ κ := kappa0_ge_two ū lam₀ hū hlam₀
  have ht2 : 2 ≤ t := le_trans hr ht
  have hlog : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hα : LinParamBandits.UEFinite.alpha σ₀ ū lam₀ = 4 * σ₀ * κ ^ 2 := rfl
  -- The key: both inequalities hold for an arbitrary direction-valued map.
  -- Case analysis on the width.
  have key : ∀ (F : LinParamBandits.LowerBound.History r t → LinParamBandits.LowerBound.Vec r),
      (∀ ζ : ℝ, 0 < ζ → 𝒰.Finite →
        LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (F h) (LinParamBandits.UEGeneral.Zhat h - z) >
          ζ * σ₀ * LinParamBandits.UEFinite.normC h (F h)} ≤
          ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2))) →
      (∀ ζ : ℝ, 2 ≤ ζ →
        LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (F h) (LinParamBandits.UEGeneral.Zhat h - z) >
          ζ * κ * σ₀ * Real.sqrt (Real.log t) * LinParamBandits.UEFinite.normC h (F h)} ≤
          ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * κ ^ 2) * Real.exp (-ζ ^ 2 / 4))) →
      LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (F h) (LinParamBandits.UEGeneral.Zhat h - z) >
        LinParamBandits.UEFinite.alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
          Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) * LinParamBandits.UEFinite.normC h (F h)} ≤
        ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
    intro F hB1 hB2
    -- the Theorem B.2 case, with width = r log t
    have caseB2 : LinParamBandits.UEGeneral.width 𝒰 t = (r : ℝ) * Real.log t →
        LinParamBandits.UEGeneral.histMeasure ν z ψ t {h | inner ℝ (F h) (LinParamBandits.UEGeneral.Zhat h - z) >
          LinParamBandits.UEFinite.alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
            Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) * LinParamBandits.UEFinite.normC h (F h)} ≤
          ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
      intro hw
      set ζ := 4 * κ * Real.sqrt ((r : ℝ) * Real.log t) with hζ
      have hcoef : LinParamBandits.UEFinite.alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
          Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) = ζ * κ * σ₀ * Real.sqrt (Real.log t) := by
        rw [hw, hα, hζ]; ring
      simp_rw [hcoef]
      refine (hB2 ζ (two_le_zeta2 κ hκ t r ht2 hr)).trans (ENNReal.ofReal_le_ofReal ?_)
      exact bound_B2 κ hκ t r ht2 hr
    by_cases hfin : 𝒰.Finite
    · have hwdef : LinParamBandits.UEGeneral.width 𝒰 t = min ((r : ℝ) * Real.log t) (𝒰.ncard : ℝ) := by
        unfold LinParamBandits.UEGeneral.width; rw [if_pos hfin]
      rcases le_total ((r : ℝ) * Real.log t) (𝒰.ncard : ℝ) with hle | hle
      · exact caseB2 (by rw [hwdef, min_eq_left hle])
      · have hw : LinParamBandits.UEGeneral.width 𝒰 t = (𝒰.ncard : ℝ) := by rw [hwdef, min_eq_right hle]
        have hn : 1 ≤ 𝒰.ncard := (Set.ncard_pos hfin).mpr h𝒰ne
        set ζ := 4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt (𝒰.ncard : ℝ) with hζ
        have hlogpos : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
        have hζpos : 0 < ζ := by
          have : (0 : ℝ) < 𝒰.ncard := by exact_mod_cast hn
          positivity
        have hcoef : LinParamBandits.UEFinite.alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
            Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) = ζ * σ₀ := by
          rw [hw, hα, hζ]; ring
        simp_rw [hcoef]
        refine (hB1 ζ hζpos hfin).trans (ENNReal.ofReal_le_ofReal ?_)
        exact bound_B1 κ hκ t _ ht2 hn
    · exact caseB2 (by unfold LinParamBandits.UEGeneral.width; rw [if_neg hfin])
  refine ⟨fun u hu => ?_, fun x => ?_⟩
  · have := key (fun _ => u)
      (fun ζ hζ hfin => (LinParamBandits.UEFinite.chernoff_finite_arms σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 hfin h𝒰ne
        ν hν hnoise b harms ψ hψ t ht u z ζ hζ).1)
      (fun ζ hζ => (LinParamBandits.UEFinite.chernoff_infinite_arms σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰cpt h𝒰ne
        ν hν hnoise b harms ψ hψ t ht u z ζ hζ).1)
    simpa [LinParamBandits.UEFinite.radius] using this
  · exact key (fun h => ψ.act t h - x)
      (fun ζ hζ hfin => (LinParamBandits.UEFinite.chernoff_finite_arms σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 hfin h𝒰ne
        ν hν hnoise b harms ψ hψ t ht x z ζ hζ).2)
      (fun ζ hζ => (LinParamBandits.UEFinite.chernoff_infinite_arms σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰cpt h𝒰ne
        ν hν hnoise b harms ψ hψ t ht x z ζ hζ).2)
