-- Prove2me | solution 1 for MasulloRH.arbitrary_precision_gaussian_approximation_at_each_single_slope
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:05:51.429466+00:00
-- url     : https://prove2.me/submissions/47785381-ccfd-4a8c-8860-50b044616a58

import Definitions.Def_MasulloRH_VerticalThetaApproximation
import Theorems.Thm_MasulloRH_rational_frequency_modulations_span_a_nonvanishing_L2_weight
import Theorems.Thm_MasulloRH_window_energy_sandwiched_by_endpoint_mellin_errors
import Theorems.Thm_MasulloRH_entire_theta_mellin_multiplier
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

open MeasureTheory Filter Topology Set MasulloRH MasulloRH.GaussianApproximation
open MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation

private theorem nonzeroLine (c : ℝ) : ∀ᵐ t : ℝ, thetaMultiplier (pointAt c t) ≠ 0 := by
  let S := {z : ℂ | thetaMultiplier z = 0}
  obtain ⟨hd,_,h1⟩ := entire_theta_mellin_multiplier
  have hNon : thetaMultiplier 1 ≠ 0 := by
    rw [h1]
    apply div_ne_zero _ (by norm_num)
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  have ha : AnalyticOnNhd ℂ thetaMultiplier univ := fun x _ => hd.analyticAt x
  have hco := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
    (fun h => hNon (h (mem_univ 1)))
  have hdisc : Sᶜ ∈ codiscrete ℂ := hco
  have count : S.Countable := (HereditarilyLindelofSpace.isLindelof S).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp hdisc).2
  have hinj : Function.Injective (pointAt c) := by
    intro x y h
    simpa [pointAt] using congrArg Complex.im h
  exact (count.preimage hinj).ae_notMem volume

private theorem lineApprox (c ε : ℝ) (hc : 0 < c) (hc' : c < 1) (hε : 0 < ε) :
    MemLp (fun t : ℝ => thetaMultiplier (pointAt c t)) 2 ∧
    ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ),
      energy c 0 (approximation a y) < ε := by
  let G := fun t => gaussian (pointAt c t)
  let H := fun t => thetaMultiplier (pointAt c t)
  have hcG : Continuous G := by dsimp [G,gaussian,pointAt]; fun_prop
  have hcH : Continuous H := entire_theta_mellin_multiplier.1.continuous.comp
    (show Continuous (pointAt c) by unfold pointAt; fun_prop)
  have h0 := ((window_energy_sandwiched_by_endpoint_mellin_errors
    (m:=0) (fun _ => (0,0)) (fun _ => 0)).1 c hc hc').1
  have hG : MemLp G 2 := (memLp_two_iff_integrable_sq_norm hcG.aestronglyMeasurable).mpr
    (by simpa [VerticalThetaApproximation.spectrum,G] using h0)
  have h1 := ((window_energy_sandwiched_by_endpoint_mellin_errors
    (m:=1) (fun _ => (1,0)) (fun _ => 0)).1 c hc hc').1
  have hdiff : MemLp (fun t => G t-H t) 2 :=
    (memLp_two_iff_integrable_sq_norm (hcG.sub hcH).aestronglyMeasurable).mpr
      (by simpa [VerticalThetaApproximation.spectrum,asComplex,G,H] using h1)
  have hid : G - (fun t => G t-H t) = H := by funext t; change G t - (G t-H t) = H t; abel
  have hH : MemLp H 2 := hid ▸ hG.sub hdiff
  obtain ⟨m,a,y,h⟩ := rational_frequency_modulations_span_a_nonvanishing_L2_weight c G H hG hH
    (nonzeroLine c) (2*Real.pi*ε) (by positivity)
  change mass c a y < _ at h
  rw [((window_energy_sandwiched_by_endpoint_mellin_errors a y).1 c hc hc').2] at h
  exact ⟨hH,m,a,y,(mul_lt_mul_iff_right₀ (by positivity : (0:ℝ) < 2*Real.pi)).mp h⟩

theorem solution (c ε : ℝ) (hc : 0 < c) (hc' : c < 1) (hε : 0 < ε) :
    MemLp (fun t : ℝ => thetaMultiplier (pointAt c t)) 2 ∧
    ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) (δ : ℝ),
      0 < δ ∧ 0 < c-δ ∧ c+δ < 1 ∧
      ∀ p b : ℝ, 0 ≤ b → |p-c|+b ≤ δ → energy p b (approximation a y) < ε := by
  obtain ⟨hH,m,a,y,hgood⟩ := lineApprox c ε hc hc' hε
  let r := min c (1-c)/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hL : 0 < c-r := by dsimp [r]; linarith [min_le_left c (1-c)]
  have hU : c+r < 1 := by dsimp [r]; linarith [min_le_right c (1-c)]
  let f := approximation a y
  let w := fun p b x : ℝ => Real.exp (2*p*x+2*b*|x|) * ‖f x‖^2
  have hi (p b : ℝ) (hb : 0 ≤ b) (h₁ : 0 < p-b) (h₂ : p+b < 1) : Integrable (w p b) :=
    ((window_energy_sandwiched_by_endpoint_mellin_errors a y).2 p b hb h₁ h₂).1
  let widths := fun n : ℕ => r/((n:ℝ)+1)
  have hpos (n : ℕ) : 0 < widths n := div_pos hr (by positivity)
  have hle (n : ℕ) : widths n ≤ r := (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr (by nlinarith [mul_nonneg hr.le (Nat.cast_nonneg n : (0:ℝ)≤n)])
  have hlim : Tendsto widths atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul r
  have hdom : Tendsto (fun n => energy c (widths n) f) atTop (𝓝 (energy c 0 f)) := by
    apply tendsto_integral_of_dominated_convergence (w c r)
    · intro n
      exact (hi c (widths n) (hpos n).le (by linarith [hle n]) (by linarith [hle n])).aestronglyMeasurable
    · exact hi c r hr.le hL hU
    · intro n
      exact Eventually.of_forall fun x => by
        change ‖Real.exp _ * ‖f x‖^2‖ ≤ Real.exp _ * ‖f x‖^2
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right (hle n) (abs_nonneg x)])
    · exact Eventually.of_forall fun x =>
        (show Continuous (fun b : ℝ => w c b x) by dsimp [w]; fun_prop).continuousAt.tendsto.comp hlim
  obtain ⟨n,hn⟩ := (hdom.eventually_lt_const hgood).exists
  refine ⟨hH,m,a,y,widths n,hpos n,by linarith [hle n],by linarith [hle n],?_⟩
  intro p b hb hwin
  have habs := abs_le.mp (show |p-c| ≤ widths n-b by linarith)
  have ii := hi p b hb (by linarith [hle n]) (by linarith [hle n])
  have jj := hi c (widths n) (hpos n).le (by linarith [hle n]) (by linarith [hle n])
  apply lt_of_le_of_lt (integral_mono ii jj ?_) hn
  intro x
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have ha : (p-c)*x ≤ |p-c| * |x| := (le_abs_self _).trans_eq (abs_mul _ _)
  nlinarith only [ha,mul_le_mul_of_nonneg_right hwin (abs_nonneg x)]
