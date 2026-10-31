-- Prove2me | solution 1 for OAI.SLEExactGauge.sourceLowerMain_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:48:12.746223+00:00
-- url     : https://prove2.me/submissions/619749f6-7145-4079-9064-a715ccbd5c76

import Mathlib
import Definitions.Def_SLELowerPositivity
import Definitions.Def_OAIQ27Sle000
import Theorems.Thm_OAI_SLEExactGauge_RegularSLEPresentation_source_actual_retained_experiment_allKappa

section
-- module Solutions.OAIQ27_SLE.SLE_OptionalStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Optional Stopping for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma stopGridIndex_le (n k : ℕ) (t : ℝ≥0) :
    stopGridIndex n t ≤ k ↔ t ≤ stopGridTime n k := by
  have hd : 0 < (n : ℝ≥0) + 1 := by positivity
  simp only [stopGridIndex, Nat.ceil_le, stopGridTime, le_div_iff₀ hd, mul_comm]

lemma stopGrid_bounds (n : ℕ) (t : ℝ≥0) :
    t ≤ stopGrid n t ∧ stopGrid n t ≤ t + 1 / ((n : ℝ≥0) + 1) := by
  have hd : 0 < (n : ℝ≥0) + 1 := by positivity
  constructor
  · exact (stopGridIndex_le n _ t).mp le_rfl
  · dsimp [stopGrid, stopGridTime, stopGridIndex]
    rw [div_le_iff₀ hd]
    calc
      _ ≤ ((n : ℝ≥0) + 1) * t + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      _ = (t + 1 / ((n : ℝ≥0) + 1)) * ((n : ℝ≥0) + 1) := by
        conv_rhs => rw [add_mul, div_mul_cancel₀ _ hd.ne']
        ac_rfl

lemma stopGrid_tendsto (t : ℝ≥0) : Tendsto (fun n => stopGrid n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))))
  · exact fun n => (stopGrid_bounds n t).1
  · intro n
    simpa only [one_div] using (stopGrid_bounds n t).2

lemma measurable_discrete_eval {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k))
    {j : Ω → ℕ} (hj : Measurable j) : Measurable (fun ω => f (j ω) ω) := by
  exact (measurable_from_prod_countable_right (f := fun p : ℕ × Ω => f p.1 p.2) hf).comp (hj.prodMk measurable_id)

lemma stopping_time_measurable_nnreal {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) : Measurable τ := by
  simpa only [WithTop.untopD_coe] using hτ.measurable'.untopD 0

lemma stopGridIndex_measurable {Ω : Type*} [MeasurableSpace Ω]
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) (n : ℕ) :
    Measurable (fun ω => stopGridIndex n (τ ω)) := by
  exact (measurable_const.mul hτ).nat_ceil

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ClippedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipped Coordinates for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma greenLogDensity_contDiff (κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => greenLogNormSq κ p.1 p.2) := by
    exact ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add
      ((contDiff_const.mul him).exp)
  have hlog := hN.log (fun p => (greenLogNormSq_pos κ p.1 p.2).ne')
  unfold greenLogDensity
  apply ContDiff.exp
  exact (((contDiff_const.add (contDiff_const.mul contDiff_fst.snd)).add
    (contDiff_const.mul him)).sub (contDiff_const.mul hlog))

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_LoewnerCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Loewner Charts for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge


lemma IsCapacityTwoWitness.fullRadius_positive
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    0 < fullRadius G T z := by
  exact div_pos (mul_pos (by norm_num) (h.imag_positive T z hz))
    (h.derivative_norm_positive hU T z hz)

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BoundaryDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Density for chordal SLE. -/

section


section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma codimension_pos (κ : ℝ) (hκ8 : κ < 8) : 0 < codimension κ := by
  dsimp [codimension, dimension]
  linarith

lemma greenExponent_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < greenExponent κ := by
  unfold greenExponent
  have : 1 < 8 / κ := (lt_div_iff₀ hκ).mpr (by simpa using hκ8)
  linarith

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SwallowExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swallow Exit for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma logCoordinates_snd (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0) :
    (logLoewnerCoordinates G z t).2 = Real.log ‖deriv (G t) z‖ := by
  simp only [logLoewnerCoordinates, Real.toNNReal_coe]

lemma greenLogNormSq_logCoordinates (κ b : ℝ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0)
    (hy : 0 < (G t z).im) :
    greenLogNormSq κ (logLoewnerCoordinates G z t) b =
      Complex.normSq (G t z - ((Real.sqrt κ * b : ℝ) : ℂ)) := by
  have he : Real.exp (2 * Real.log (G t z).im) = (G t z).im ^ 2 := by
    rw [show 2 * Real.log (G t z).im = Real.log (G t z).im + Real.log (G t z).im by ring,
      Real.exp_add, Real.exp_log hy, pow_two]
  rw [greenLogNormSq, logCoordinates_re, logCoordinates_im, he]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, pow_two]

lemma greenLogDensity_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (κ b : ℝ) (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t)
    (hUb : U t = Real.sqrt κ * b) :
    greenLogDensity κ (logLoewnerCoordinates G z t) b = greenDensity κ U γ G t z := by
  have hy := h.imag_positive t z hz
  have hj := h.derivative_norm_positive hU t z hz
  have hn : 0 < ‖G t z - ((Real.sqrt κ * b : ℝ) : ℂ)‖ := by
    apply norm_pos_iff.mpr
    simpa only [hUb] using h.centered_ne_zero t z hz
  have hs : 0 < Real.sin (Complex.arg (G t z - (U t : ℂ))) := by
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero, hUb]
    exact div_pos hy hn
  have hR := h.fullRadius_positive hU t z hz
  have hlogR : Real.log (fullRadius G t z) =
      Real.log 2 + Real.log (G t z).im - Real.log ‖deriv (G t) z‖ := by
    rw [fullRadius, Real.log_div (mul_ne_zero (by norm_num) hy.ne') hj.ne',
      Real.log_mul (by norm_num) hy.ne']
  have hlogS : Real.log (Real.sin (Complex.arg (G t z - (U t : ℂ)))) =
      Real.log (G t z).im - Real.log ‖G t z - ((Real.sqrt κ * b : ℝ) : ℂ)‖ := by
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero, hUb,
      Real.log_div hy.ne' hn.ne']
  rw [greenDensity, ite_eq_left hz, Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hs,
    ← Real.exp_add, hlogR, hlogS, greenLogDensity, logCoordinates_im, logCoordinates_snd,
    greenLogNormSq_logCoordinates κ b G z t hy, Complex.normSq_eq_norm_sq, Real.log_pow]
  congr 1
  push_cast
  ring

end SLEExactGauge
end


section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
 
theorem exists_measurable_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (C t)) ∧ IsBrownianReal C P ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  let b (n k : ℕ) : Ω → ℝ :=
    (hB.aemeasurable (stopGridTime n k)).mk (B (stopGridTime n k))
  have hb (n k : ℕ) : Measurable (b n k) := (hB.aemeasurable _).measurable_mk
  have heq : ∀ᵐ ω ∂P, ∀ n k, b n k ω = B (stopGridTime n k) ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (hB.aemeasurable _).ae_eq_mk.symm
  let C (t : ℝ≥0) (ω : Ω) : ℝ :=
    limUnder atTop (fun n => b n (stopGridIndex n t) ω)
  have hm (t : ℝ≥0) : Measurable (C t) :=
    (StronglyMeasurable.limUnder (fun n => (hb n _).stronglyMeasurable)).measurable
  have hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := by
    filter_upwards [hB.cont, heq] with ω hω heqω
    intro t
    change limUnder atTop (fun n => b n (stopGridIndex n t) ω) = B t ω
    simp_rw [heqω]
    exact (hω.continuousAt.tendsto.comp (stopGrid_tendsto t)).limUnder_eq
  refine ⟨C, hm, ⟨?_, ?_⟩, hCB⟩
  · exact hB.toIsPreBrownianReal.congr (fun t => hCB.mono fun ω hω => (hω t).symm)
  · filter_upwards [hB.cont, hCB] with ω hω heqω
    simpa only [heqω] using hω

 

theorem exists_continuous_measurable_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) ∧
      (∀ ω, Continuous (fun t => C t ω)) ∧ IsBrownianReal C P ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  classical
  obtain ⟨V, hVm, hV, hVB⟩ := exists_measurable_brownian_version hB
  let N := toMeasurable P {ω | ¬ Continuous (fun t => V t ω)}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN : P N = 0 := by
    rw [show N = toMeasurable P {ω | ¬ Continuous (fun t => V t ω)} from rfl,
      measure_toMeasurable]
    exact ae_iff.mp hV.cont
  let C (t : ℝ≥0) (ω : Ω) := if ω ∈ N then (0 : ℝ) else V t ω
  have hCm (t) : Measurable (C t) := measurable_const.piecewise hNm (hVm t)
  have hCc (ω) : Continuous (fun t => C t ω) := by
    by_cases hω : ω ∈ N
    · simpa only [C, ite_eq_left hω] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
    · have hv : Continuous (fun t => V t ω) := by
        by_contra hh
        exact hω (subset_toMeasurable P _ hh)
      simpa only [C, ite_eq_right hω] using hv
  have hCV : ∀ᵐ ω ∂P, ∀ t, C t ω = V t ω := by
    filter_upwards [show ∀ᵐ ω ∂P, ω ∉ N from (ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hN))] with ω hω
    intro t
    simp only [C, ite_eq_right hω]
  have hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := by
    filter_upwards [hCV, hVB] with ω hω hω'
    exact fun t => (hω t).trans (hω' t)
  refine ⟨C, measurable_uncurry_of_continuous_of_measurable hCc hCm, hCc, ?_, hCB⟩
  exact ⟨hV.toIsPreBrownianReal.congr (fun t => hCV.mono fun ω hω => (hω t).symm),
    Eventually.of_forall hCc⟩

 

theorem exists_regular_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) ∧
      (∀ ω, Continuous (fun t => C t ω)) ∧ (∀ ω, C 0 ω = 0) ∧
      IsBrownianReal C P ∧ (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  obtain ⟨V, hVm, hVc, hV, hVB⟩ := exists_continuous_measurable_brownian_version hB
  let C (t : ℝ≥0) (ω : Ω) := V t ω - V 0 ω
  have hV0m : Measurable (V 0) := hVm.comp (measurable_const.prodMk measurable_id)
  have hCm : Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) :=
    hVm.sub (hV0m.comp measurable_snd)
  have hCc (ω : Ω) : Continuous (fun t => C t ω) := (hVc ω).sub continuous_const
  have hCV : ∀ᵐ ω ∂P, ∀ t, C t ω = V t ω := by
    filter_upwards [hV.eval_zero_ae_eq_zero] with ω h0
    intro t
    simp only [C, h0, sub_zero]
  refine ⟨C, hCm, hCc, fun ω => sub_self _, ?_, ?_⟩
  · exact ⟨hV.toIsPreBrownianReal.congr (fun t => hCV.mono fun ω hω => (hω t).symm),
      Eventually.of_forall hCc⟩
  · filter_upwards [hCV, hVB] with ω hω hω'
    exact fun t => (hω t).trans (hω' t)
end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_NearRealContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near Real Contraction for chordal SLE. -/

section


section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma upper_mobius_norm_lt_one {v w : ℂ} (hv : 0 < v.im) (hw : 0 < w.im) :
    ‖(v - w) / (v - star w)‖ < 1 := by
  have hd : v - star w ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hh
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have he : ‖v - w‖ ^ 2 < ‖v - star w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_pos hv hw]
  nlinarith [norm_nonneg (v - w), norm_nonneg (v - star w)]

 

lemma radius_of_halfplane_map {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball z r))
    (hm : MapsTo f (ball z r) upperHalfPlane) (hf : deriv f z ≠ 0) :
    r ≤ 2 * (f z).im / ‖deriv f z‖ := by
  have hz : z ∈ ball z r := mem_ball_self hr
  have hy : 0 < (f z).im := hm hz
  have hden (w : ℂ) (hw : w ∈ ball z r) : f w - star (f z) ≠ 0 := by
    intro he
    have hx := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hx
    have hwyo : 0 < (f w).im := hm hw
    linarith
  let g := fun w => (f w - f z) / (f w - star (f z))
  have hg0 : g z = 0 := by dsimp [g]; rw [sub_self, zero_div]
  have hgd : DifferentiableOn ℂ g (ball z r) :=
    (hd.sub_const _).div (hd.sub_const _) hden
  have hgm : MapsTo g (ball z r) (closedBall (g z) 1) := by
    intro w hw
    rw [hg0, mem_closedBall_zero_iff]
    exact (upper_mobius_norm_lt_one (hm hw) hy).le
  have hdz : HasDerivAt f (deriv f z) z := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hgg : deriv g z = deriv f z / (f z - star (f z)) := by
    calc
      deriv g z = (deriv f z * (f z - star (f z)) - (f z - f z) * deriv f z) /
          (f z - star (f z)) ^ 2 :=
        ((hdz.sub_const (f z)).div (hdz.sub_const (star (f z))) (hden z hz)).deriv
      _ = _ := by
        rw [sub_self, zero_mul, sub_zero, pow_two, mul_div_mul_right _ _ (hden z hz)]
  have hn : ‖f z - star (f z)‖ = 2 * (f z).im := by
    rw [Complex.star_def, Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hy), Complex.norm_I, mul_one]
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hr
  rw [hgg, norm_div, hn] at hh
  have hn' := norm_pos_iff.mpr hf
  apply (le_div_iff₀ hn').mpr
  have hq := (div_le_div_iff₀ (mul_pos (by norm_num) hy) hr).mp hh
  nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma ball_subset_survivingDomain {γ : ℝ≥0 → ℂ} {t : ℝ≥0} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : z ∈ survivingDomain γ t)
    (hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 t)) :
    ball z r ⊆ survivingDomain γ t := by
  have hcc := (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hfree
  intro w hw
  refine ⟨hfree hw, ?_⟩
  rw [← connectedComponentIn_eq (hcc hw)]
  exact hz.2

lemma ball_subset_upperHalfPlane {z : ℂ} {r : ℝ} (hr : r ≤ z.im) :
    ball z r ⊆ upperHalfPlane := by
  intro w hw
  have hh : ‖w - z‖ < r := mem_ball_iff_norm.mp hw
  have hi := Complex.abs_im_le_norm (w - z)
  simp only [Complex.sub_im] at hi
  change 0 < w.im
  have hx := neg_le_abs (w.im - z.im)
  linarith

 

lemma IsCapacityTwoWitness.trace_approach_of_radius_lt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) (r : ℝ)
    (hr : 0 < r) (hy : r ≤ z.im) (hR : fullRadius G t z < r) :
    ∃ s ∈ Icc 0 t, dist (γ s) z < r := by
  by_contra hn
  have hn' (s : ℝ≥0) (hs : s ∈ Icc 0 t) : r ≤ dist (γ s) z :=
    le_of_not_gt (fun he => hn ⟨s, hs, he⟩)
  have hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 t) := by
    intro w hw
    refine ⟨ball_subset_upperHalfPlane hy hw, ?_⟩
    rintro ⟨s, hs, rfl⟩
    exact not_lt_of_ge (hn' s hs) (mem_ball.mp hw)
  have hb := ball_subset_survivingDomain hr hz hfree
  have hd : DifferentiableOn ℂ (G t) (ball z r) := (h.2.2.2.1 t).mono hb
  have hm : MapsTo (G t) (ball z r) upperHalfPlane := fun w hw => h.2.2.2.2.2.1 t (hb hw)
  have hf : deriv (G t) z ≠ 0 := norm_pos_iff.mp (h.derivative_norm_positive hU t z hz)
  exact not_lt_of_ge (radius_of_halfplane_map hr hd hm hf) hR

end SLEExactGauge
end


section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m} {τ : Ω → ℝ≥0}

 

lemma stopping_grid_piece_measurable
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (n k : ℕ) :
    MeasurableSet[ℱ (stopGridTime n k)] (A ∩ {ω | stopGridIndex n (τ ω) = k}) := by
  have hle (j : ℕ) : MeasurableSet[ℱ (stopGridTime n j)]
      (A ∩ {ω | stopGridIndex n (τ ω) ≤ j}) := by
    simpa only [stopGridIndex_le, WithTop.coe_le_coe] using hA.2 (stopGridTime n j)
  cases k with
  | zero => simpa only [Nat.le_zero] using hle 0
  | succ k =>
    have he : A ∩ {ω | stopGridIndex n (τ ω) = k + 1} =
        (A ∩ {ω | stopGridIndex n (τ ω) ≤ k + 1}) \ (A ∩ {ω | stopGridIndex n (τ ω) ≤ k}) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
      constructor
      · rintro ⟨hω, heq⟩
        exact ⟨⟨hω, heq.le⟩, fun hb => by omega⟩
      · rintro ⟨⟨hω, hle⟩, hn⟩
        exact ⟨hω, by have hh : ¬ stopGridIndex n (τ ω) ≤ k := fun hk => hn ⟨hω, hk⟩; omega⟩
    rw [he]
    exact (hle (k + 1)).diff (ℱ.mono (monotone_stopGridTime n (Nat.le_succ k)) _ (hle k))

omit m in
lemma grid_partition_union (A : Set Ω) (n : ℕ) :
    (⋃ k : ℕ, A ∩ {ω | stopGridIndex n (τ ω) = k}) = A := by
  ext ω
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

omit m in
lemma grid_partition_disjoint (A : Set Ω) (n : ℕ) :
    Pairwise (fun i j : ℕ => Disjoint (A ∩ {ω | stopGridIndex n (τ ω) = i}) (A ∩ {ω | stopGridIndex n (τ ω) = j})) := by
  intro i j hij
  apply disjoint_left.mpr
  intro ω hi hj
  exact hij (hi.2.symm.trans hj.2)

 

lemma integral_stopping_grid_glue [IsFiniteMeasure P]
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (n : ℕ)
    (f : Ω → ℝ) (hf : Integrable f P) (c : ℝ)
    (hpiece : ∀ k : ℕ, (∫ ω in A ∩ {ω | stopGridIndex n (τ ω) = k}, f ω ∂P) =
      P.real (A ∩ {ω | stopGridIndex n (τ ω) = k}) * c) :
    (∫ ω in A, f ω ∂P) = P.real A * c := by
  have hm (k : ℕ) : MeasurableSet (A ∩ {ω | stopGridIndex n (τ ω) = k}) :=
    ℱ.le _ _ (stopping_grid_piece_measurable hτ hA n k)
  have hfSum := hasSum_integral_iUnion hm (grid_partition_disjoint (τ := τ) A n) hf.integrableOn
  have hconstSum := hasSum_integral_iUnion hm (grid_partition_disjoint (τ := τ) A n)
    (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P).integrableOn
  simp only [grid_partition_union, hpiece] at hfSum
  simp only [grid_partition_union, integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at hconstSum
  exact HasSum.unique hfSum (hconstSum.mul_right c)

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BrownianStrongMarkov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Brownian Strong Markov for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))

include hm in
lemma shiftedFDD_measurable (I : Finset ℝ≥0) (s : ℝ≥0) :
    Measurable (shiftedFDD B I s) :=
  Measurable.of_eval (fun i => (hm (s + i)).sub (hm s))

include hB hm in
omit [IsProbabilityMeasure P] in
lemma shiftedFDD_indep (I : Finset ℝ≥0) (s : ℝ≥0) :
    Indep (Filtration.natural B (fun t => (hm t).stronglyMeasurable) s)
      (MeasurableSpace.comap (shiftedFDD B I s) inferInstance) P := by
  have hi := ((hB.indepFun_shift s).comp
    (Measurable.of_eval (fun i : I => measurable_pi_apply (i : ℝ≥0))) measurable_id).symm
  rw [Filtration.natural_eq_comap B _ s]
  exact (IndepFun_iff_Indep _ _ _).mp hi

include hB hm in
omit [IsProbabilityMeasure P] in
lemma shiftedFDD_setIntegral (I : Finset ℝ≥0) (s : ℝ≥0)
    (φ : BoundedContinuousFunction (I → ℝ) ℝ) {A : Set Ω}
    (hA : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] A) :
    (∫ ω in A, φ (shiftedFDD B I s ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  rw [(shiftedFDD_indep hB hm I s).setIntegral_eq_mul
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s)
    (shiftedFDD_measurable hm I s).aemeasurable hA φ.continuous.aestronglyMeasurable]
  congr 1
  exact ((hB.shift s).hasLaw I).integral_comp φ.continuous.aestronglyMeasurable

include hm in
lemma shiftedFDD_grid_measurable {τ : Ω → ℝ≥0} (hτm : Measurable τ)
    (I : Finset ℝ≥0) (n : ℕ) :
    Measurable (fun ω => shiftedFDD B I (stopGrid n (τ ω)) ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_discrete_eval
    (fun k ω => B (stopGridTime n k + i) ω - B (stopGridTime n k) ω)
    (fun k => (hm _).sub (hm _)) (stopGridIndex_measurable hτm n)

include hB hm in
lemma shiftedFDD_grid_setIntegral {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (I : Finset ℝ≥0) (φ : BoundedContinuousFunction (I → ℝ) ℝ) (n : ℕ) :
    (∫ ω in A, φ (shiftedFDD B I (stopGrid n (τ ω)) ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  apply integral_stopping_grid_glue hτ hA n _
    (Integrable.of_bound (φ.continuous.measurable.comp
      (shiftedFDD_grid_measurable hm (stopping_time_measurable_nnreal hτ) I n)).aestronglyMeasurable
      ‖φ‖ (Eventually.of_forall (fun ω => φ.norm_coe_le_norm _)))
  intro k
  have hk := stopping_grid_piece_measurable hτ hA n k
  have hk' := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le _ _ hk
  rw [setIntegral_congr_fun hk' (g := fun ω => φ (shiftedFDD B I (stopGridTime n k) ω))
    (fun ω hω => by
      have he : stopGridIndex n (τ ω) = k := hω.2
      simp only [Function.comp_def, stopGrid, he])]
  exact shiftedFDD_setIntegral hB hm I _ φ hk

omit mΩ in
lemma shiftedFDD_grid_tendsto
    (hc : ∀ ω, Continuous (fun t => B t ω)) (I : Finset ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n => shiftedFDD B I (stopGrid n (τ ω)) ω) atTop
      (𝓝 (shiftedFDD B I (τ ω) ω)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact ((hc ω).continuousAt.tendsto.comp ((stopGrid_tendsto (τ ω)).add_const (i : ℝ≥0))).sub
    ((hc ω).continuousAt.tendsto.comp (stopGrid_tendsto (τ ω)))

include hB hm in
 

theorem brownian_strongMarkov_integral
    (hc : ∀ ω, Continuous (fun t => B t ω)) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (I : Finset ℝ≥0) (φ : BoundedContinuousFunction (I → ℝ) ℝ) :
    (∫ ω in A, φ (shiftedFDD B I (τ ω) ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (F := fun n ω => φ (shiftedFDD B I (stopGrid n (τ ω)) ω))
    (f := fun ω => φ (shiftedFDD B I (τ ω) ω)) (fun _ => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp
      (shiftedFDD_grid_measurable hm (stopping_time_measurable_nnreal hτ) I n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall (fun ω => φ.norm_coe_le_norm _))
    (Eventually.of_forall (fun ω => φ.continuous.continuousAt.tendsto.comp
      (shiftedFDD_grid_tendsto hc I τ ω)))
  simp only [shiftedFDD_grid_setIntegral hB hm hτ hA I φ] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
  (hc : ∀ ω, Continuous (fun t => B t ω))

include hm hc in
lemma brownianRestart_measurable {τ : Ω → ℝ≥0} (hτm : Measurable τ) :
    Measurable (fun ω t => brownianRestart B τ t ω) := by
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  apply Measurable.of_eval
  intro t
  exact (hBm.comp ((hτm.add_const t).prodMk measurable_id)).sub
    (hBm.comp (hτm.prodMk measurable_id))

include hB hm hc in
lemma brownian_restart_fdd_restrict {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (I : Finset ℝ≥0) :
    (P.restrict A).map (fun ω => shiftedFDD B I (τ ω) ω) =
      P A • BrownianReal.projectiveFamily I := by
  have hXm : Measurable (fun ω => shiftedFDD B I (τ ω) ω) :=
    (Finset.measurable_restrict I).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ))
  let : IsFiniteMeasure (P A • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P A)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hXm.aemeasurable φ.continuous.aestronglyMeasurable,
    integral_smul_measure]
  exact brownian_strongMarkov_integral hB hm hc hτ hA I φ

include hB hm hc in
 

theorem brownian_restart_path_law {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (fun ω t => brownianRestart B τ t ω) =
      P A • P.map (fun ω t => B t ω) := by
  have hXm := brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)
  have hBm : Measurable (fun ω t => B t ω) := Measurable.of_eval hm
  let (I : Finset ℝ≥0) : IsFiniteMeasure (P A • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P A)
  have hL : IsProjectiveLimit ((P.restrict A).map (fun ω t => brownianRestart B τ t ω))
      (fun I => P A • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hXm]
    exact brownian_restart_fdd_restrict hB hm hc hτ hA I
  have hR : IsProjectiveLimit (P A • P.map (fun ω t => B t ω))
      (fun I => P A • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_smul,
      Measure.map_map (Finset.measurable_restrict I) hBm]
    exact congrArg (fun ν => P A • ν) (hB.hasLaw I).map_eq
  exact hL.unique hR

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge


namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

lemma measurePreserving_val (a : RegularSLEPresentation P κ γ) :
    MeasurePreserving (Subtype.val : a.samples → Ω) (P.comap Subtype.val) P := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe a.measurable_samples,
    Measure.restrict_eq_self_of_ae_mem a.full_samples]

end RegularSLEPresentation

 

theorem exists_regular_sle_presentation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P) :
    Nonempty (RegularSLEPresentation P κ γ) := by
  classical
  obtain ⟨B, hB, htrace⟩ := hSLE.2
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have htraceC : ∀ᵐ ω ∂P, IsCapacityTwoTrace (fun t => Real.sqrt κ * C t ω) (γ ω) := by
    filter_upwards [htrace, hCB] with ω hω heq
    simpa only [heq] using hω
  let N := toMeasurable P {ω | ¬ IsCapacityTwoTrace (fun t => Real.sqrt κ * C t ω) (γ ω)}
  let S := Nᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hNa : P N = 0 := by
    rw [show N = toMeasurable P {ω | ¬ IsCapacityTwoTrace
      (fun t => Real.sqrt κ * C t ω) (γ ω)} from rfl, measure_toMeasurable]
    exact ae_iff.mp htraceC
  have hSa : ∀ᵐ ω ∂P, ω ∈ S := by
    apply ae_iff.mpr
    simpa only [S, mem_compl_iff, not_not, ofPred_mem_eq] using hNa
  have hw (ω : S) : IsCapacityTwoTrace (fun t => Real.sqrt κ * C t ω) (γ ω) := by
    by_contra hh
    exact ω.property (subset_toMeasurable P _ hh)
  choose G F hGF using hw
  have hval : MeasurePreserving (Subtype.val : S → Ω) (P.comap Subtype.val) P := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe hSm, Measure.restrict_eq_self_of_ae_mem hSa]
  refine ⟨{
    samples := S
    measurable_samples := hSm
    full_samples := hSa
    B := fun t ω => C t ω
    measurable_B := fun t => (hCm.comp (measurable_prodMk_left (x := t))).comp measurable_subtype_coe
    continuous_B := fun ω => hCc ω
    zero_B := fun ω => hC0 ω
    brownian := ?_
    G := G
    F := F
    witness := hGF }⟩
  exact ⟨⟨fun I => (hC.hasLaw I).comp hval.hasLaw⟩, Eventually.of_forall (fun ω => hCc ω)⟩

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_FiniteStoppedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Stopped Law for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma greenDensity_nonneg
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (κ : ℝ) (t : ℝ≥0) (z : ℂ) :
    0 ≤ greenDensity κ U γ G t z := by
  classical
  by_cases hz : z ∈ survivingDomain γ t
  · rw [greenDensity, ite_eq_left hz]
    have hy := h.imag_positive t z hz
    apply mul_nonneg
    · exact Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) hy.le) (norm_nonneg _)) _
    · apply Real.rpow_nonneg
      rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_nonneg hy.le (norm_nonneg _)
  · simp only [greenDensity, ite_eq_right hz, le_refl]

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RadiusClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radius Clocks for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge



theorem continuous_zero_hit_stopping
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → ℝ) (hXa : Adapted ℱ X)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (n : ℝ≥0) :
    IsStoppingTime ℱ (hittingAfter X {0} n) := by
  intro T
  have he : {ω | hittingAfter X {0} n ω ≤ (T : WithTop ℝ≥0)} =
      {ω | ∃ t : Icc n T, X t ω = 0} := by
    ext ω
    simp only [mem_ofPred_eq, hittingAfter_zero_le_iff X hXc, Subtype.exists, exists_prop]
  rw [he]
  by_cases hnT : n ≤ T
  · let : Nonempty (Icc n T) := ⟨⟨n, le_rfl, hnT⟩⟩
    have hm (t : Icc n T) : @Measurable Ω ℝ (ℱ T) (borel ℝ) (X t) :=
      (hXa t).mono (ℱ.mono t.property.2) le_rfl
    let : MeasurableSpace Ω := ℱ T
    exact measurableSet_exists_zero_compact (fun t : Icc n T => X t) hm
      (fun ω => (hXc ω).comp continuous_subtype_val)
  · have hnil : IsEmpty (Icc n T) := ⟨fun t => hnT (t.property.1.trans t.property.2)⟩
    have : {ω | ∃ t : Icc n T, X t ω = 0} = ∅ := by ext ω; simp
    rw [this]
    exact @MeasurableSet.empty Ω (ℱ T)

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_KernelConsistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Consistency for chordal SLE. -/

section
section


section

open Set Filter Metric MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}



lemma IsCapacityTwoWitness.radius_ge_of_no_trace_approach
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    {r : ℝ} (hr : 0 < r) (hy : r ≤ z.im)
    (havoid : ∀ a ∈ Icc 0 t, r ≤ dist (γ a) z) : r ≤ fullRadius G t z := by
  by_contra hlt
  obtain ⟨a, ha, hd⟩ := h.trace_approach_of_radius_lt hU t z hz r hr hy (lt_of_not_ge hlt)
  exact (not_lt_of_ge (havoid a ha)) hd

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse Moments for chordal SLE. -/

section
section


section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma spatialHitTime_lt_of_dist_lt {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hstart : r ≤ dist (γ 0) z)
    (t : ℝ≥0) (ht : dist (γ t) z < r) : spatialHitTime γ z r < t := by
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t from bot_le)
    (hc.dist continuous_const).continuousOn ⟨ht.le, hstart⟩
  have hst : s < t := lt_of_le_of_ne hs.2 (by intro h; subst s; exact ht.ne he)
  exact ((spatialHitTime_le_iff hc z r s).mpr ⟨s, ⟨bot_le, le_rfl⟩, he⟩).trans_lt
    (WithTop.coe_lt_coe.mpr hst)

end SLEExactGauge

end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

lemma valid_measurable (n : ℕ) :
    MeasurableSet {p : ℝ≥0 × (ℂ × Ω) | c.valid n p.1 p.2.1 p.2.2} := by
  have hz : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => p.2.1.im) :=
    Complex.measurable_im.comp (measurable_fst.comp measurable_snd)
  have hQ : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => (c.Q n p.1 p.2).1.im) :=
    Complex.measurable_im.comp ((c.measurable n).comp
      ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)).fst
  exact (measurableSet_lt measurable_const hz).inter
    ((measurableSet_le (Real.measurable_log.comp hz) measurable_const).inter
      (measurableSet_le measurable_const hQ))

lemma derivative_compact (n : ℕ) (z : ℂ) (ω : Ω) (T : ℝ≥0) (t : ℝ)
    (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt (fun s => c.Q n s (z, ω))
      (clippedLogLoewnerField (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
        (U t.toNNReal ω) (c.Q n t (z, ω))) (Icc 0 (T : ℝ)) t :=
  (c.derivative n z ω t ht.1).mono Icc_subset_Ici_self

lemma live_of_valid {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (n : ℕ) (t : ℝ≥0) (z : ℂ) (hv : c.valid n t z ω) :
    z ∈ survivingDomain γ t := by
  exact (clipped_log_identification_of_endpoint hUc h t z hv.1 _ _ _
    (fun s => c.Q n s (z, ω)) (c.initial n z ω)
    (c.derivative_compact n z ω t) hv.2.2 hv.2.1).1

lemma agrees_of_live {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (n : ℕ) (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (hlo : -(n : ℝ) ≤ Real.log (G t z).im) (hhi : Real.log z.im ≤ (n : ℝ)) :
    c.Q n t (z, ω) = logLoewnerCoordinates G z t := by
  exact clipped_log_loewner_agrees hUc h t z hz _ _ _ hlo hhi
    (fun s => c.Q n s (z, ω)) (c.initial n z ω)
    (c.derivative_compact n z ω t) ⟨t.coe_nonneg, le_rfl⟩

lemma eventually_valid_agrees {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    ∀ᶠ n : ℕ in atTop, c.valid n t z ω ∧
      c.Q n t (z, ω) = logLoewnerCoordinates G z t := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (-Real.log (G t z).im) (Real.log z.im))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlo : -(n : ℝ) ≤ Real.log (G t z).im := by
    have ha := (le_max_left (-Real.log (G t z).im) (Real.log z.im)).trans (hN.trans hNn)
    linarith
  have hhi : Real.log z.im ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
  have he := c.agrees_of_live ω hUc h n t z hz hlo hhi
  refine ⟨⟨hz.1.1, hhi, ?_⟩, he⟩
  rw [he, logCoordinates_im]
  exact hlo

end SpatialClippedFamily
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

lemma greenApprox_measurable (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (n : ℕ) :
    Measurable (c.greenApprox κ B n) := by
  have hQ := (c.measurable n).comp
    ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hB : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => B p.1 p.2.2) :=
    hBm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply Measurable.ite (c.valid_measurable n) _ measurable_const
  exact (greenLogDensity_contDiff κ).continuous.measurable.comp (hQ.prodMk hB)

lemma jointGreen_measurable (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    Measurable (c.jointGreen κ B) :=
  (StronglyMeasurable.limUnder (fun n => (c.greenApprox_measurable κ B hBm n).stronglyMeasurable)).measurable

lemma jointGreen_eq (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hUc : Continuous (fun t => U t ω))
    (hU : ∀ t, U t ω = Real.sqrt κ * B t ω)
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) :
    c.jointGreen κ B (t, z, ω) = greenDensity κ (fun s => U s ω) γ G t z := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  by_cases hz : z ∈ survivingDomain γ t
  · filter_upwards [c.eventually_valid_agrees ω hUc hw t z hz] with n hn
    rw [greenApprox, ite_eq_left hn.1, hn.2]
    exact greenLogDensity_logCoordinates hUc hw κ (B t ω) z t hz (hU t)
  · filter_upwards [] with n
    have hn : ¬ c.valid n t z ω := fun hv => hz (c.live_of_valid ω hUc hw n t z hv)
    simp only [greenApprox, ite_eq_right hn, greenDensity, ite_eq_right hz]

end SpatialClippedFamily



end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SpatialMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial Means for chordal SLE. -/

section
section


section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma spatialHitTime_measurable {Ω : Type*} [MeasurableSpace Ω]
    (γ : Ω → ℝ≥0 → ℂ) (hc : ∀ ω, Continuous (γ ω))
    (hm : ∀ t, Measurable (fun ω => γ ω t)) (r : ℝ) :
    Measurable (fun p : ℂ × Ω => spatialHitTime (γ p.2) p.1 r) := by
  let X (t : ℝ≥0) (p : ℂ × Ω) : ℝ := dist (γ p.2 t) p.1 - r
  have hXa : Adapted (⊤ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℂ × Ω))) X := by
    intro t
    exact (((hm t).comp measurable_snd).dist measurable_fst).sub_const r
  have hXc (p : ℂ × Ω) : Continuous (fun t => X t p) :=
    ((hc p.2).dist continuous_const).sub continuous_const
  have h := continuous_zero_hit_stopping ⊤ X hXa hXc 0
  exact h.measurable.mono h.measurableSpace_le le_rfl

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma jointGreen_measurable :
    Measurable (fun p : ℝ≥0 × (ℂ × a.samples) => greenDensity κ
      (fun t => Real.sqrt κ * a.B t p.2.2) (γ p.2.2) (a.G p.2.2) p.1 p.2.1) := by
  have hm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  let c := spatialClippedFamily (fun t ω => Real.sqrt κ * a.B t ω)
    (hm.const_mul _) (fun ω => (a.continuous_B ω).const_mul _)
  convert c.jointGreen_measurable κ a.B hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (c.jointGreen_eq κ a.B p.2.2 ((a.continuous_B _).const_mul _)
    (fun _ => rfl) (a.witness _) p.1 p.2.1).symm

lemma spatialGreenWeight_measurable (r : ℝ) :
    Measurable (fun p : ℂ × a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2) p.1 r) := by
  classical
  have hm (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have hc (ω : a.samples) : Continuous (γ ω) := a.trace_continuous ω
  have ht : Measurable (fun p : ℂ × a.samples => spatialHitTime (γ p.2) p.1 r) :=
    spatialHitTime_measurable (fun ω : a.samples => γ ω) hc hm r
  have he : MeasurableSet {p : ℂ × a.samples | spatialHitTime (γ p.2) p.1 r = ⊤} :=
    measurableSet_eq_fun ht measurable_const
  have hg := a.jointGreen_measurable.comp ((ht.untopD 0).prodMk measurable_id)
  have hh := @Measurable.ite _ _ _ _ _ _ _ (fun _ => Classical.propDecidable _) he
    (measurable_const (a := (0 : ℝ))) hg
  simpa only [spatialGreenWeight, Function.comp_def, id_eq] using hh

end RegularSLEPresentation
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.radius_before_spatial_hit
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im) (t : ℝ≥0)
    (hz : z ∈ survivingDomain γ t) (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    r ≤ fullRadius G t z := by
  apply h.radius_ge_of_no_trace_approach hU t z hz hr hy
  intro s hs
  by_contra hn
  have hstart : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hhit := spatialHitTime_lt_of_dist_lt h.1 z r hstart s (lt_of_not_ge hn)
  exact (not_lt_of_ge ht) (hhit.trans_le (WithTop.coe_le_coe.mpr hs.2))

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.green_before_spatial_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hr : 0 < r)
    (z : ℂ) (hy : r ≤ z.im) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    greenDensity κ U γ G t z ≤ r ^ (-codimension κ) := by
  by_cases hz : z ∈ survivingDomain γ t
  · have hR := h.radius_before_spatial_hit hU z r hr hy t hz ht
    have hs : 0 ≤ Real.sin (Complex.arg (G t z - (U t : ℂ))) := by
      rw [Complex.sin_arg]
      have hi := (h.imag_positive t z hz).le
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_nonneg hi (norm_nonneg _)
    rw [greenDensity, ite_eq_left hz]
    calc
      _ ≤ r ^ (-codimension κ) * 1 := mul_le_mul
        (Real.rpow_le_rpow_of_nonpos hr hR (neg_nonpos.mpr (codimension_pos κ hκ8).le))
        (Real.rpow_le_one hs (Real.sin_le_one _) (greenExponent_pos κ hκ hκ8).le)
        (Real.rpow_nonneg hs _) (Real.rpow_nonneg hr.le _)
      _ = _ := mul_one _
  · rw [greenDensity, ite_eq_right hz]
    exact Real.rpow_nonneg hr.le _

lemma IsCapacityTwoWitness.spatialGreenWeight_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hr : 0 < r)
    (z : ℂ) (hy : r ≤ z.im) :
    0 ≤ spatialGreenWeight κ U γ G z r ∧
      spatialGreenWeight κ U γ G z r ≤ r ^ (-codimension κ) := by
  by_cases ht : spatialHitTime γ z r = ⊤
  · simp only [spatialGreenWeight, ite_eq_left ht]
    exact ⟨le_rfl, Real.rpow_nonneg hr.le _⟩
  · rw [spatialGreenWeight, ite_eq_right ht]
    refine ⟨greenDensity_nonneg h κ _ z, h.green_before_spatial_bound hU hκ hκ8 hr z hy _ ?_⟩
    exact WithTop.coe_untopD_le _ _

end SLEExactGauge

end

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal

open Set Filter Metric Complex
open scoped Topology NNReal

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal

end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Measures for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

attribute [local instance] OAI.SLEExactGauge.stoppedTraceFactorRealPathMeasurable
attribute [local instance] OAI.SLEExactGauge.stoppedTraceFactorComplexPathMeasurable
local instance stoppedTraceFactorRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedTraceFactorComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma source_trace_factor {Ω : Type*} [m : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → C(ℝ≥0, ℂ))
    (ha : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => γ ω t)) :
    ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
      γ = Φ ∘ (fun ω => (⟨fun t => B t ω, hc ω⟩ : C(ℝ≥0, ℝ))) := by
  let bp : Ω → C(ℝ≥0, ℝ) := fun ω => ⟨fun t => B t ω, hc ω⟩
  have hb (t : ℝ≥0) : @Measurable Ω ℝ (MeasurableSpace.comap bp (borel _)) (borel ℝ)
      (B t) := by
    exact (continuous_eval_const t).measurable.comp (Measurable.of_comap_le le_rfl)
  have hle (t : ℝ≥0) :
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t ≤
        MeasurableSpace.comap bp (borel _) := by
    change (⨆ s ≤ t, MeasurableSpace.comap (B s) (borel ℝ)) ≤ _
    exact iSup_le fun s => iSup_le fun _ => measurable_iff_comap_le.mp (hb s)
  have hγ : @Measurable Ω C(ℝ≥0,ℂ)
      (MeasurableSpace.comap bp (borel _)) (borel _) γ := by
    let : MeasurableSpace Ω := MeasurableSpace.comap bp (borel _)
    exact source_path_measurable γ (fun t => (ha t).mono (hle t) le_rfl)
  exact hγ.exists_eq_measurable_comp
end
end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_reverseField_sub_real (a u v : ℝ) (z : ℂ) :
    reverseField a (u - v) (z - (v : ℂ)) = reverseField a u z := by
  unfold reverseField
  congr 2
  apply Complex.ext <;> simp [reverseCenter]

 

lemma IsCapacityTwoWitness.source_shifted_reverse_identifies
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (Q : ℝ → ℂ) (hQ0 : Q 0 = w)
    (hQd : ∀ s ∈ Icc 0 (t : ℝ), HasDerivWithinAt Q
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (Q s))
        (Icc 0 (t : ℝ)) s) :
    F (T + t) (w + (U T : ℂ)) = F T (Q t + (U T : ℂ)) := by
  have hzH : w + (U T : ℂ) ∈ upperHalfPlane := by
    change 0 < (w + (U T : ℂ)).im
    simpa using ha.trans_le haw
  let z := F (T + t) (w + (U T : ℂ))
  have hz : z ∈ survivingDomain γ (T + t) := h.2.2.2.2.2.2.1 _ hzH
  have hzt : z ∈ survivingDomain γ T :=
    survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le)) hz
  have ht (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      (((T + t : ℝ≥0) : ℝ) - s).toNNReal = T + ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2])]
    simp only [NNReal.coe_add]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    ring
  let R (s : ℝ) := G (((T + t : ℝ≥0) : ℝ) - s).toNNReal z - (U T : ℂ)
  have hRd (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : HasDerivWithinAt R
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (R s))
      (Icc 0 (t : ℝ)) s := by
    have hs' : s ∈ Icc 0 ((T + t : ℝ≥0) : ℝ) :=
      ⟨hs.1, by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2]⟩
    have hd := ((h.reverse_path_derivative (T+t) (w + (U T : ℂ)) ha
      (by simpa using haw) s hs').sub_const (U T : ℂ)).mono
      (show Icc (0 : ℝ) t ⊆ Icc 0 ((T+t : ℝ≥0) : ℝ) from
        Icc_subset_Icc le_rfl (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg]))
    change HasDerivWithinAt R _ _ _ at hd
    simpa only [R, ht s hs, source_reverseField_sub_real] using hd
  have he : EqOn Q R (Icc 0 (t : ℝ)) := by
    apply ODE_solution_unique
      (fun s => reverseField_lipschitz ha (U (T + ((t : ℝ) - s).toNNReal) - U T))
      (fun s hs => (hQd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQd s ⟨hs.1, hs.2.le⟩))
      (fun s hs => (hRd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hRd s ⟨hs.1, hs.2.le⟩))
    simpa only [R, sub_zero, Real.toNNReal_coe, z,
      h.2.2.2.2.2.2.2.2.1 (T+t) _ hzH, add_sub_cancel_right] using hQ0
  have heT := he ⟨t.coe_nonneg, le_rfl⟩
  have htime : (((T + t : ℝ≥0) : ℝ) - (t : ℝ)).toNNReal = T := by
    simp only [NNReal.coe_add, add_sub_cancel_right, Real.toNNReal_coe]
  have hQ : Q t + (U T : ℂ) = G T z := by
    simpa only [R, htime, sub_add_cancel] using congrArg (fun v : ℂ => v + (U T : ℂ)) heT
  rw [hQ, h.2.2.2.2.2.2.2.1 T z hzt]

end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.stoppedReverseFlowRealPathMeasurable
local instance stoppedReverseFlowRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma source_canonical_reverse_flow (κ : ℝ) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    ∃ Q : ℝ → C(ℝ≥0, ℝ) → ℂ,
      (∀ s, Measurable (Q s)) ∧
      (∀ p, Q 0 p = (Real.sqrt κ * p T : ℝ) + (a : ℂ) * I) ∧
      ∀ p s, 0 ≤ s → HasDerivWithinAt (fun r => Q r p)
        (reverseField a (Real.sqrt κ * p ((T : ℝ) - s).toNNReal) (Q s p)) (Ici 0) s := by
  let V (s : ℝ) (p : C(ℝ≥0, ℝ)) := Real.sqrt κ * p ((T : ℝ) - s).toNNReal
  have hV : Continuous (fun q : ℝ × C(ℝ≥0, ℝ) => V q.1 q.2) := by
    apply continuous_const.mul
    exact continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_fst)))
  have hw : Measurable (fun p : C(ℝ≥0, ℝ) =>
      (Real.sqrt κ * p T : ℝ) + (a : ℂ) * I) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_eval_const T))).measurable.add_const _
  obtain ⟨Q, hQm, hQ0, hQd⟩ := exists_measurable_reverse_flow V hV.measurable
    (fun p => hV.comp (continuous_id.prodMk continuous_const)) _ hw ha
  exact ⟨Q, fun s => hQm.comp (measurable_prodMk_left (x := s)), hQ0, hQd⟩

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.stoppedRestartLawRealPathMeasurable
local instance stoppedRestartLawComplexPathMeasurable_r896653_1 : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stoppedRestartLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

local instance stoppedRestartLawComplexPathBorel_r896653_1 : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_restart_continuous_driver_law
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (sourceRestartDriverPath B hc τ) =
      P A • P.map (sourceDriverPath B hc) := by
  have hbm : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  have hrm : Measurable (sourceRestartDriverPath B hc τ) :=
    source_path_measurable _ (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  apply source_path_evaluation_embedding.map_injective
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)))
    (brownian_restart_path_law hB hm hc hτ hA)
  have hem : Measurable (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [Measure.map_map source_path_evaluation_embedding.measurable hrm,
    Measure.map_smul,
    Measure.map_map source_path_evaluation_embedding.measurable hbm]
  rw [Measure.map_map hem (brownianRestart_measurable hm hc
    (stopping_time_measurable_nnreal hτ)), Measure.map_smul,
    Measure.map_map hem (Measurable.of_eval hm)] at he
  exact he

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.stoppedTraceLawRealPathMeasurable
attribute [local instance] OAI.SLEExactGauge.stoppedTraceLawComplexPathMeasurable
local instance stoppedTraceLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedTraceLawComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem sourceStoppedTraceLaw : SourceStoppedTraceLawTarget := by
  intro Ω m P κ hκ hκ8 B hB hm hc γ G F hw
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let bp := sourceDriverPath B hc
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hbm : Measurable bp := source_path_measurable bp hm
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => gp ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω)
      ?_ (fun ω => continuous_const.mul (hc ω)) γ G F hw
    intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
  obtain ⟨Φ, hΦm, hΦ⟩ := source_trace_factor B hm hc gp hγa
  have hΦe (ω : Ω) : Φ (bp ω) = gp ω := (congrFun hΦ ω).symm
  have hgm : Measurable gp := hΦ ▸ hΦm.comp hbm
  refine ⟨Φ, hΦm, hΦe, ?_⟩
  intro τ hτ
  let rp := sourceRestartDriverPath B hc τ
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map rp = P A • P.map bp :=
    source_restart_continuous_driver_law hB hm hc τ hτ hA
  have hlaw0 : P.map rp = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hlaw univ MeasurableSet.univ
  constructor
  · intro A hA
    have he := congrArg (Measure.map Φ) (hlaw A hA)
    rw [Measure.map_map hΦm hrm, Measure.map_smul,
      Measure.map_map hΦm hbm] at he
    have hcomp : Φ ∘ bp = gp := hΦ.symm
    simpa only [hcomp, rp, gp, Function.comp_def] using he
  · choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
      source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
    let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
    have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall ha⟩
    have hQorig (ω : Ω) (t : ℝ≥0) (n : ℕ) :
        Q t n t (bp ω) = F ω t ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) := by
      apply (hw ω).reverse_flow_identifies t
        ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (bp ω)) (hQ0 t n (bp ω))
      intro s hs
      exact (hQd t n (bp ω) s hs.1).mono Icc_subset_Ici_self
    have hQlimit (ω : Ω) (t : ℝ≥0) :
        Tendsto (fun n => Q t n t (bp ω)) atTop (𝓝 (Φ (bp ω) t)) := by
      have ht := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
      simpa only [hQorig, hΦe, gp, sourceTracePath, ContinuousMap.coe_mk, Function.comp_def] using ht
    have hset (t : ℝ≥0) : MeasurableSet
        {p : C(ℝ≥0,ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
      measurableSet_tendsto (𝓝 (0 : ℂ)) (fun n => (hQm t n t).sub
        ((continuous_eval_const t).measurable.comp hΦm))
    have hQR (t : ℝ≥0) : ∀ᵐ ω ∂P,
        Tendsto (fun n => Q t n t (rp ω)) atTop (𝓝 (Φ (rp ω) t)) := by
      have ho : ∀ᵐ p ∂P.map bp,
          Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
        apply (ae_map_iff hbm.aemeasurable (hset t)).2
        exact Eventually.of_forall (fun ω => tendsto_sub_nhds_zero_iff.mpr (hQlimit ω t))
      rw [← hlaw0] at ho
      filter_upwards [(ae_map_iff hrm.aemeasurable (hset t)).1 ho] with ω hω
      exact tendsto_sub_nhds_zero_iff.mp hω
    have hQRall : ∀ᵐ ω ∂P, ∀ j : ℕ,
        Tendsto (fun n => Q (denseSeq ℝ≥0 j) n (denseSeq ℝ≥0 j) (rp ω)) atTop
          (𝓝 (Φ (rp ω) (denseSeq ℝ≥0 j))) := ae_all_iff.mpr (fun j => hQR _)
    filter_upwards [hQRall] with ω hω
    have hcoc (t : ℝ≥0) (n : ℕ) :
        F ω (τ ω + t) ((Real.sqrt κ * B (τ ω + t) ω : ℝ) + (a n : ℂ) * I) =
        F ω (τ ω) (Q t n t (rp ω) + (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
      have he := (hw ω).source_shifted_reverse_identifies (τ ω) t
        ((Real.sqrt κ * (rp ω) t : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (rp ω)) (hQ0 t n (rp ω))
        (fun s hs => by
          have hh := (hQd t n (rp ω) s hs.1).mono
            (show Icc (0 : ℝ) t ⊆ Ici 0 from Icc_subset_Ici_self)
          simpa only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk,
            mul_sub] using hh)
      convert he using 2
      all_goals try with_reducible_and_instances rfl
      simp only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk]
      push_cast
      ring
    have hdense (j : ℕ) (hj : Φ (rp ω) (denseSeq ℝ≥0 j) ∈ upperHalfPlane) :
        γ ω (τ ω + denseSeq ℝ≥0 j) = F ω (τ ω)
          (Φ (rp ω) (denseSeq ℝ≥0 j) + (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
      let t := denseSeq ℝ≥0 j
      have hz : Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ) ∈ upperHalfPlane := by
        simpa only [upperHalfPlane, mem_ofPred_eq, add_im, ofReal_im, add_zero] using hj
      have hFt : ContinuousAt (F ω (τ ω))
          (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)) :=
        ((hw ω).2.2.2.2.1 (τ ω)).continuousOn.continuousAt
          (isOpen_upperHalfPlane.mem_nhds hz)
      have hlimF := hFt.tendsto.comp ((hω j).add_const ((Real.sqrt κ * B (τ ω) ω : ℝ) : ℂ))
      have hlimγ := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 (τ ω + t)).comp hy
      simp only [Function.comp_def, hcoc] at hlimγ
      exact tendsto_nhds_unique hlimγ hlimF
    let S : Set ℝ≥0 := {t | Φ (rp ω) t ∈ upperHalfPlane}
    have hSo : IsOpen S := isOpen_upperHalfPlane.preimage (Φ (rp ω)).continuous
    have hleft : ContinuousOn (fun t => γ ω (τ ω + t)) S :=
      ((hw ω).1.comp (continuous_const.add continuous_id)).continuousOn
    have hright : ContinuousOn (fun t => F ω (τ ω)
        (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ))) S := by
      apply ((hw ω).2.2.2.2.1 (τ ω)).continuousOn.comp
        ((Φ (rp ω)).continuous.add_const _).continuousOn
      intro t ht
      simpa only [S, upperHalfPlane, mem_ofPred_eq, add_im, ofReal_im, add_zero] using ht
    have hEq : EqOn (fun t => γ ω (τ ω + t))
        (fun t => F ω (τ ω) (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)))
        (S ∩ range (denseSeq ℝ≥0)) := by
      rintro t ⟨ht, j, rfl⟩
      exact hdense j ht
    exact hEq.of_subset_closure hleft hright inter_subset_left
      ((denseRange_denseSeq ℝ≥0).open_subset_closure_inter hSo)
end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal

end

end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RetainedSeedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Seed Moments for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_unit_ball_height {z₀ z : ℂ} (hz₀ : 2 < z₀.im) (hz : z ∈ closedBall z₀ 1) :
    1 < z.im := by
  have hdist : abs (z.im-z₀.im) ≤ dist z z₀ := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
  have hh : dist z z₀ ≤ 1 := hz
  have ha := neg_abs_le (z.im-z₀.im)
  linarith

end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RetainedDyadicGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Dyadic Geometry for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma retainedSquare_iff_address (k : ℕ) (ij : ℤ × ℤ) (z : ℂ) :
    z ∈ retainedDyadicSquare k ij ↔ retainedDyadicAddress k z = ij := by
  simp only [retainedDyadicSquare, mem_ofPred_eq, retainedDyadicAddress,
    Prod.ext_iff, Int.floor_eq_iff]
  tauto

lemma retainedSquare_address (k : ℕ) (z : ℂ) :
    z ∈ retainedDyadicSquare k (retainedDyadicAddress k z) :=
  (retainedSquare_iff_address _ _ _).mpr rfl

end SLEExactGauge
end

 
section
open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge
noncomputable section
lemma source_dyadic_side_eq (k : ℕ) : (2:ℝ)^(-(k:ℝ)) = (1/2:ℝ)^k := by
  rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,←inv_pow]
  norm_num
lemma source_dyadic_side_pos (k : ℕ) : 0 < (2:ℝ)^(-(k:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_HausdorffLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hausdorff Limits for chordal SLE. -/

section

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma excessiveSquares_measurable {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) :
    MeasurableSet (excessiveSquares κ D ν k₀ N ω) := by
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro hk
  apply MeasurableSet.iUnion
  intro ij
  have hQ : MeasurableSet (retainedDyadicSquare k ij) := by
    have hre : Measurable (fun z : ℂ => (2:ℝ)^k*z.re) := by fun_prop
    have him : Measurable (fun z : ℂ => (2:ℝ)^k*z.im) := by fun_prop
    exact (measurableSet_le measurable_const hre).inter
      ((measurableSet_lt hre measurable_const).inter
      ((measurableSet_le measurable_const him).inter (measurableSet_lt him measurable_const)))
  exact hQ.inter (MeasurableSet.const _)

lemma excessiveSquares_prod_measurable {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) :
    MeasurableSet {p : Ω × ℂ | p.2 ∈ excessiveSquares κ D ν k₀ N p.1} := by
  have hQ (k : ℕ) (ij : ℤ × ℤ) : MeasurableSet (retainedDyadicSquare k ij) := by
    have hre : Measurable (fun z : ℂ => (2:ℝ)^k*z.re) := by fun_prop
    have him : Measurable (fun z : ℂ => (2:ℝ)^k*z.im) := by fun_prop
    exact (measurableSet_le measurable_const hre).inter
      ((measurableSet_lt hre measurable_const).inter
      ((measurableSet_le measurable_const him).inter (measurableSet_lt him measurable_const)))
  have hh : MeasurableSet (⋃ k ∈ Set.Icc k₀ N, ⋃ ij : ℤ × ℤ,
      {p : Ω × ℂ | p.2 ∈ retainedDyadicSquare k ij ∧
        ENNReal.ofReal (retainedThreshold κ D k) < ν N p.1 (retainedDyadicSquare k ij)}) := by
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro hk
    apply MeasurableSet.iUnion
    intro ij
    exact (measurable_snd (hQ k ij)).inter (measurableSet_lt measurable_const
      ((Kernel.measurable_coe _ (hQ k ij)).comp measurable_fst))
  simpa only [excessiveSquares, mem_iUnion, mem_ofPred_eq, Set.ofPred_exists] using hh

lemma retainedMeasure_measurable {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) [IsFiniteKernel (ν N)] {K : Set ℂ}
    (hK : MeasurableSet K) :
    Measurable (fun ω => retainedMeasure κ D ν k₀ N ω K) := by
  have hm := Kernel.measurable_kernel_prodMk_left (κ := ν N)
    ((measurable_snd hK).inter (excessiveSquares_prod_measurable κ D ν k₀ N).compl)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  rw [retainedMeasure, Measure.restrict_apply hK]
  rfl

lemma retainedMeasure_square_bound {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) (k : ℕ)
    (hk₀ : k₀ ≤ k) (hkN : k ≤ N) (ij : ℤ × ℤ) :
    retainedMeasure κ D ν k₀ N ω (retainedDyadicSquare k ij) ≤
      ENNReal.ofReal (retainedThreshold κ D k) := by
  by_cases hbad : ENNReal.ofReal (retainedThreshold κ D k) <
      ν N ω (retainedDyadicSquare k ij)
  · have hsub : retainedDyadicSquare k ij ⊆ excessiveSquares κ D ν k₀ N ω := by
      intro z hz
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨hk₀,hkN⟩, mem_iUnion.mpr ⟨ij,hz,hbad⟩⟩⟩
    have hz : (ν N ω).restrict (excessiveSquares κ D ν k₀ N ω)ᶜ
        (retainedDyadicSquare k ij) = 0 := by
      apply MeasureTheory.measure_mono_null hsub
      simp [Measure.restrict_apply' (excessiveSquares_measurable κ D ν k₀ N ω).compl]
    exact hz.le.trans bot_le
  · exact (Measure.restrict_apply_le _ _).trans (le_of_not_gt hbad)



end SLEExactGauge
end

 
section

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge



lemma normalized_supported_probability_compact {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {ν : ProbabilityMeasure ℂ | ν Kᶜ = 0} := by
  have he : Topology.IsClosedEmbedding
      (ProbabilityMeasure.toFiniteMeasure (Ω := ℂ)) :=
    ⟨ProbabilityMeasure.toFiniteMeasure_isEmbedding ℂ, by
      rw [ProbabilityMeasure.range_toFiniteMeasure]
      exact isClosed_eq FiniteMeasure.continuous_mass continuous_const⟩
  have hc := he.isCompact_preimage
    (isCompact_setOfPred_finiteMeasure_le_of_isCompact (1 : ℝ≥0) hK)
  simpa only [Set.preimage_ofPred_eq, ProbabilityMeasure.mass_toFiniteMeasure,
    le_refl, true_and, ProbabilityMeasure.coeFn_toFiniteMeasure] using hc

lemma probability_limit_ball_bound
    {νs : ℕ → ProbabilityMeasure ℂ} {ν : ProbabilityMeasure ℂ}
    (hlim : Tendsto νs atTop (𝓝 ν)) (x : ℂ) (r : ℝ) (c : ℝ≥0∞)
    (hb : ∀ᶠ n in atTop, (νs n : Measure ℂ) (Metric.ball x r) ≤ c) :
    (ν : Measure ℂ) (Metric.ball x r) ≤ c := by
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim Metric.isOpen_ball).trans
    (liminf_le_of_frequently_le hb.frequently)

lemma probability_limit_shrinking_carriers
    {νs : ℕ → ProbabilityMeasure ℂ} {ν : ProbabilityMeasure ℂ}
    (hlim : Tendsto νs atTop (𝓝 ν)) {E : Set ℂ} (hE : IsClosed E)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (νs n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0) :
    (ν : Measure ℂ) Eᶜ = 0 := by
  have hnull (δ : ℝ) (hδ : 0 < δ) :
      (ν : Measure ℂ) (Metric.cthickening δ E)ᶜ = 0 := by
    apply le_antisymm _ bot_le
    apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      Metric.isClosed_cthickening.isOpen_compl).trans
    have hzero : ∀ᶠ n in atTop, (νs n : Measure ℂ) (Metric.cthickening δ E)ᶜ ≤ 0 := by
      filter_upwards [he.eventually_le_const hδ] with n hn
      exact (measure_mono (Set.compl_subset_compl.mpr (Metric.cthickening_mono hn E))).trans
        (hcarrier n).le
    exact liminf_le_of_frequently_le hzero.frequently
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  apply measure_mono_null (t := ⋃ n, (Metric.cthickening (δ n) E)ᶜ)
  · intro x hx
    have hnot : x ∉ closure E := by simpa only [hE.closure_eq, Set.mem_compl_iff] using hx
    obtain ⟨n, hn⟩ := (hδlim.eventually
      (Metric.eventually_notMem_cthickening_of_infEDist_pos hnot)).exists
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · exact measure_iUnion_null (fun n => hnull (δ n) (hδpos n))

 

lemma gauge_mass_distribution {h : ℝ → ℝ} (hh : IsGauge h)
    (ν : Measure ℂ) (C : ℝ≥0) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ x r, 0 < r → r < ρ →
      ν (Metric.ball x r) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    ν ≤ (C : ℝ≥0∞) • hausdorffGauge h := by
  let m : ℝ≥0∞ → ℝ≥0∞ := fun r => (C : ℝ≥0∞) * extendedGauge h r
  have hs : ν ≤ Measure.mkMetric m := by
    refine Measure.le_mkMetric m ν (ENNReal.ofReal (ρ / 2))
      (ENNReal.ofReal_pos.mpr (by positivity)) ?_
    intro s hs
    by_cases he : s.Nonempty
    · obtain ⟨x, hx⟩ := he
      have htop : Metric.ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
      let d : ℝ := (Metric.ediam s).toReal
      have hd : 0 ≤ d := ENNReal.toReal_nonneg
      have hdρ : d ≤ ρ / 2 := by
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hs).trans_eq
          (ENNReal.toReal_ofReal (by positivity))
      have hdρ' : d < ρ := by linarith
      have hcont : Tendsto h (𝓝[>] d) (𝓝 (h d)) :=
        (hh.continuousOn d hd).mono (fun y hy => hd.trans (le_of_lt hy))
      have ht : Tendsto (fun r => ENNReal.ofReal ((C : ℝ) * h r))
          (𝓝[>] d) (𝓝 (ENNReal.ofReal ((C : ℝ) * h d))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_const_nhds.mul hcont)
      have hle : ν s ≤ ENNReal.ofReal ((C : ℝ) * h d) := by
        apply ge_of_tendsto ht
        filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hdρ').filter_mono inf_le_left]
          with r hr hrρ
        have hsub : s ⊆ Metric.ball x r := by
          intro y hy
          have hdist : dist y x ≤ d := by
            simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
              ENNReal.toReal_mono htop (Metric.edist_le_ediam_of_mem hy hx)
          exact hdist.trans_lt hr
        have := (measure_mono hsub).trans (hball x r (hd.trans_lt hr) hrρ)
        simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using this
      simpa only [m, extendedGauge, d, ENNReal.ofReal_mul C.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using hle
    · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]
      exact bot_le
  exact hs.trans (Measure.mkMetric_mono_smul ENNReal.coe_ne_top
    (ENNReal.coe_ne_zero.mpr hC.ne') (Filter.Eventually.of_forall fun _ => le_rfl))



lemma source_gauge_bounded_scaling (κ : ℝ) (_hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℝ, 0 ≤ r → r ≤ a →
      h (L * r) ≤ L ^ dimension κ * h r := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨δ, hδ, hδf⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hf
  change 0 < δ at hδ
  let a := min δ (Real.exp (-1)) / (2 * L)
  have ha : 0 < a := div_pos (lt_min hδ (Real.exp_pos _)) (by positivity)
  refine ⟨a, ha, fun r hr hra => ?_⟩
  rcases hr.eq_or_lt with rfl | hr
  · simp [hh.zero]
  have hR : L * r ≤ min δ (Real.exp (-1)) / 2 := by
    have := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp hra
    nlinarith
  have hRδ : L * r < δ := by
    have := min_le_left δ (Real.exp (-1))
    linarith
  have hRe : L * r ≤ Real.exp (-1) := by
    have := min_le_right δ (Real.exp (-1))
    have := Real.exp_pos (-1)
    linarith
  have hrR : r ≤ L * r := by nlinarith
  have hRpos : 0 < L * r := mul_pos hLp hr
  have hlog : 1 ≤ Real.log (1 / (L * r)) := by
    have := Real.log_le_log hRpos hRe
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hlogle : Real.log (1 / (L * r)) ≤ Real.log (1 / r) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hr hrR)
  have hll0 : 0 ≤ Real.log (Real.log (1 / (L * r))) :=
    Real.log_nonneg hlog
  have hllle := Real.log_le_log (by linarith : 0 < Real.log (1 / (L * r))) hlogle
  have hp : 0 ≤ codimension κ / 2 := by dsimp [codimension, dimension]; linarith
  rw [hδf ⟨hRpos, hRδ⟩, hδf ⟨hr, hrR.trans_lt hRδ⟩]
  dsimp [hFormula]
  rw [Real.mul_rpow hLp.le hr.le, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hll0 hllle hp)
      (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hLp.le _)

lemma retainedBallSquares_card (k : ℕ) (x : ℂ) :
    (retainedBallSquares k x).card = 9 := by
  have hc (a : ℤ) : (Finset.Icc (a-1) (a+1)).card = 3 := by
    rw [Int.card_Icc]
    have he : a+1+1-(a-1) = 3 := by ring
    rw [he]
    rfl
  simp [retainedBallSquares, Finset.card_product, hc]

lemma retainedBallSquares_cover (k : ℕ) (x : ℂ) (r : ℝ)
    (hr : r ≤ (1/2:ℝ)^k) :
    Metric.ball x r ⊆ ⋃ ij ∈ (retainedBallSquares k x : Set (ℤ × ℤ)),
      retainedDyadicSquare k ij := by
  intro z hz
  have hdist : ‖z-x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hs : (2:ℝ)^k * r ≤ 1 := by
    calc
      (2:ℝ)^k*r ≤ (2:ℝ)^k*(1/2:ℝ)^k := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have bound (a b : ℝ) (hb : |b-a| < r) :
      ⌊(2:ℝ)^k*a⌋ - 1 ≤ ⌊(2:ℝ)^k*b⌋ ∧
      ⌊(2:ℝ)^k*b⌋ ≤ ⌊(2:ℝ)^k*a⌋ + 1 := by
    have hb1 := mul_lt_mul_of_pos_left (abs_lt.mp hb).1 (by positivity : 0 < (2:ℝ)^k)
    have hb2 := mul_lt_mul_of_pos_left (abs_lt.mp hb).2 (by positivity : 0 < (2:ℝ)^k)
    have hf1 := Int.floor_le ((2:ℝ)^k*a)
    have hf2 := Int.lt_floor_add_one ((2:ℝ)^k*a)
    constructor
    · apply Int.le_floor.mpr
      push_cast
      nlinarith
    · apply Int.floor_le_iff.mpr
      push_cast
      nlinarith
  have hre : |z.re-x.re| < r := by
    exact (Complex.abs_re_le_norm (z-x)).trans_lt hdist
  have him : |z.im-x.im| < r := by
    exact (Complex.abs_im_le_norm (z-x)).trans_lt hdist
  refine mem_iUnion.mpr ⟨retainedDyadicAddress k z, mem_iUnion.mpr ⟨?_, retainedSquare_address k z⟩⟩
  change (⌊(2:ℝ)^k*z.re⌋, ⌊(2:ℝ)^k*z.im⌋) ∈
    (Finset.Icc (⌊(2:ℝ)^k*x.re⌋ - 1) (⌊(2:ℝ)^k*x.re⌋ + 1)) ×ˢ
    (Finset.Icc (⌊(2:ℝ)^k*x.im⌋ - 1) (⌊(2:ℝ)^k*x.im⌋ + 1))
  simpa only [Finset.mem_product, Finset.mem_Icc] using And.intro (bound _ _ hre) (bound _ _ him)

lemma retained_dyadic_ball_bound (μ : Measure ℂ) (k : ℕ) (b : ℝ≥0∞)
    (hb : ∀ ij, μ (retainedDyadicSquare k ij) ≤ b) (x : ℂ) (r : ℝ)
    (hr : r ≤ (1/2:ℝ)^k) : μ (Metric.ball x r) ≤ 9*b := by
  calc
    μ (Metric.ball x r) ≤ μ (⋃ ij ∈ (retainedBallSquares k x : Set (ℤ×ℤ)),
        retainedDyadicSquare k ij) := measure_mono (retainedBallSquares_cover k x r hr)
    _ ≤ ∑ ij ∈ retainedBallSquares k x, μ (retainedDyadicSquare k ij) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ ij ∈ retainedBallSquares k x, b := Finset.sum_le_sum (fun _ _ => hb _)
    _ = 9*b := by simp [retainedBallSquares_card, nsmul_eq_mul]

lemma dyadic_side_rpow (k : ℕ) : (2:ℝ)^(-(k:ℝ)) = (1/2:ℝ)^k := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
  norm_num

lemma dyadic_side_loglog (k : ℕ) (hk : 0 < k) :
    Real.log (Real.log (1 / ((1/2:ℝ)^k))) =
      Real.log (k:ℝ) + Real.log (Real.log 2) := by
  have he : 1 / ((1/2:ℝ)^k) = (2:ℝ)^k := by
    rw [one_div, ← inv_pow]
    norm_num
  rw [he, Real.log_pow, Real.log_mul (by exact_mod_cast hk.ne')
    (Real.log_pos (by norm_num : (1:ℝ)<2)).ne']

lemma retained_threshold_gauge_eventually (κ : ℝ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hf : HasSmallRadiusFormula h (hFormula κ))
    (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ k : ℕ in atTop, retainedThreshold κ D k ≤
      D * (2:ℝ)^(codimension κ/2) * h ((1/2:ℝ)^k) := by
  have ht : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall (fun k => by change 0 < (1/2:ℝ)^k; positivity)⟩
  have hform : ∀ᶠ k : ℕ in atTop, h ((1/2:ℝ)^k) = hFormula κ ((1/2:ℝ)^k) :=
    ht.eventually hf
  have hlog : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hform, hlog.eventually_ge_atTop (max 0 (-2*Real.log (Real.log 2))),
    eventually_ge_atTop 1] with k hkf hkl hk1
  have hla : 0 ≤ Real.log (k:ℝ) := (le_max_left _ _).trans hkl
  have hlb : -2*Real.log (Real.log 2) ≤ Real.log (k:ℝ) := (le_max_right _ _).trans hkl
  have hll := dyadic_side_loglog k (by omega)
  have hll0 : 0 ≤ Real.log (Real.log (1 / ((1/2:ℝ)^k))) := by rw [hll]; linarith
  have hle : Real.log (k:ℝ) ≤ 2 * Real.log (Real.log (1 / ((1/2:ℝ)^k))) := by
    rw [hll]; linarith
  have hp : 0 ≤ codimension κ / 2 := by dsimp [codimension, dimension]; linarith
  unfold retainedThreshold
  rw [dyadic_side_rpow]
  calc
    D * ((1/2:ℝ)^k)^dimension κ * (Real.log (k:ℝ))^(codimension κ/2)
      ≤ D * ((1/2:ℝ)^k)^dimension κ *
          (2 * Real.log (Real.log (1 / ((1/2:ℝ)^k))))^(codimension κ/2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hla hle hp)
          (mul_nonneg hD (Real.rpow_nonneg (by positivity) _))
    _ = D * (2:ℝ)^(codimension κ/2) * h ((1/2:ℝ)^k) := by
      rw [Real.mul_rpow (by norm_num) hll0, hkf]
      dsimp [hFormula]
      ring

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ActualRetainedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Retained Kernel for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma sourceFiniteGreenDensity_measurable (r : ℝ) (T : ℝ≥0) :
    Measurable (fun p : a.samples × ℂ => ENNReal.ofReal (if spatialHitTime (γ p.1) p.2 r ≤ T then
      spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t p.1) (γ p.1) (a.G p.1) p.2 r else 0)) := by
  have hm (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have ht := (spatialHitTime_measurable (fun ω : a.samples => γ ω) a.trace_continuous hm r).comp measurable_swap
  have hW := (a.spatialGreenWeight_measurable r).comp measurable_swap
  exact (Measurable.ite (measurableSet_le ht measurable_const) hW measurable_const).ennreal_ofReal
lemma sourceFiniteGreenKernel_apply (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples)
    (S : Set ℂ) (hS : MeasurableSet S) :
    a.sourceFiniteGreenKernel z₀ T N ω S = finiteSpatialGreenMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1 ∩ S) := by
  rw [sourceFiniteGreenKernel,Kernel.withDensity_apply' _ (a.sourceFiniteGreenDensity_measurable _ T)]
  simp only [Kernel.const_apply,finiteSpatialGreenMass,Measure.restrict_restrict hS,inter_comm]
  rfl
lemma sourceFiniteGreenKernel_univ (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples) :
    a.sourceFiniteGreenKernel z₀ T N ω univ = finiteSpatialGreenMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1) := by
  rw [a.sourceFiniteGreenKernel_apply z₀ T N ω univ MeasurableSet.univ,inter_univ]
lemma sourceFiniteGreenKernel_supported (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples) :
    a.sourceFiniteGreenKernel z₀ T N ω (closedBall z₀ 1)ᶜ = 0 := by
  rw [a.sourceFiniteGreenKernel_apply z₀ T N ω _ measurableSet_closedBall.compl,inter_compl_self]
  simp [finiteSpatialGreenMass]
lemma sourceFiniteGreenKernel_finite (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 2 < z₀.im) (T : ℝ≥0) (N : ℕ) :
    IsFiniteKernel (a.sourceFiniteGreenKernel z₀ T N) := by
  let r := (2:ℝ)^(-(N:ℝ))
  have hr : 0 < r := source_dyadic_side_pos N
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [source_dyadic_side_eq]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨⟨ENNReal.ofReal (r^(-codimension κ))*volume (closedBall z₀ 1),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_closedBall_lt_top),?_⟩⟩
  intro ω
  rw [a.sourceFiniteGreenKernel_univ]
  change (∫⁻ z in closedBall z₀ 1, ENNReal.ofReal (if spatialHitTime (γ ω) z r ≤ T then
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0)) ≤ _
  calc
    _ ≤ ∫⁻ z in closedBall z₀ 1, ENNReal.ofReal (r^(-codimension κ)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz'
      apply ENNReal.ofReal_le_ofReal
      split_ifs
      · exact (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hκ hκ8 hr z
          (hr1.trans (source_unit_ball_height hz hz').le) |>.2
      · exact Real.rpow_nonneg hr.le _
    _ = _ := by simp
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma sourceFiniteGreenKernel_carrier (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples) :
    a.sourceFiniteGreenKernel z₀ T N ω (cthickening ((2:ℝ)^(-(N:ℝ))) (γ ω '' Icc 0 T))ᶜ = 0 := by
  have hm := (isClosed_cthickening : IsClosed (cthickening ((2:ℝ)^(-(N:ℝ))) (γ ω '' Icc 0 T))).measurableSet
  rw [a.sourceFiniteGreenKernel_apply z₀ T N ω _ hm.compl,finiteSpatialGreenMass]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_closedBall.inter hm.compl)] with z hz
  have hn : ¬ spatialHitTime (γ ω) z ((2:ℝ)^(-(N:ℝ))) ≤ T := by
    intro ht
    obtain ⟨t,ht,hd⟩ := (spatialHitTime_le_iff (a.trace_continuous ω) z _ T).mp ht
    exact hz.2 (mem_cthickening_of_dist_le z (γ ω t) _ _ ⟨t,ht,rfl⟩ (by simpa [dist_comm] using hd.le))
  simp only [ite_eq_right hn, ENNReal.ofReal_zero,Pi.zero_apply]
end RegularSLEPresentation
lemma source_dyadic_tendsto : Tendsto (fun N : ℕ => (2:ℝ)^(-(N:ℝ))) atTop (𝓝 0) := by
  simp_rw [source_dyadic_side_eq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma retainedMeasure_zero_of_zero {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) {S : Set ℂ} (hS : ν N ω S = 0) :
    retainedMeasure κ D ν k₀ N ω S = 0 := by
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans hS.le) bot_le
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_gauge_lipschitz_image_le (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {K : ℝ≥0} {f : ℂ → ℂ} {S : Set ℂ} (hLip : LipschitzOnWith K f S) :
    hausdorffGauge h (f '' S) ≤
      ENNReal.ofReal ((max (K : ℝ) 1)^dimension κ)*hausdorffGauge h S := by
  let L : ℝ≥0 := max K 1
  have hL : 1 ≤ (L : ℝ) := le_max_right _ _
  have hLp : 0 < (L : ℝ) := zero_lt_one.trans_le hL
  have hLC : LipschitzOnWith L f S := hLip.weaken (le_max_left _ _)
  have himg (t : Set ℂ) : ediam (f '' (t ∩ S)) ≤ (L:ℝ≥0∞)*ediam t := by
    simpa only [NNReal.coe_one,ENNReal.rpow_one] using hLC.holderOnWith.ediam_image_inter_le t
  obtain ⟨a,ha,hscale⟩ := source_gauge_bounded_scaling κ hκ hκ8 h hh hf (L:ℝ) hL
  let C : ℝ≥0∞ := ENNReal.ofReal ((L:ℝ)^dimension κ)
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hLp _)).ne'
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  change hausdorffGauge h (f '' S) ≤ C*hausdorffGauge h S
  simp only [hausdorffGauge,Measure.mkMetric_apply,ENNReal.mul_iSup,
    ENNReal.mul_iInf_of_ne hC0 hCt,←ENNReal.tsum_mul_left]
  refine iSup_le fun R => iSup_le fun hR => ?_
  have ht : Tendsto (fun d : ℝ≥0∞ => (L:ℝ≥0∞)*d) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_const_mul (a := (L:ℝ≥0∞)) ENNReal.coe_ne_top).tendsto 0
  obtain ⟨δ,hδ,Hδ⟩ := ENNReal.nhds_zero_basis_Iic.eventually_iff.mp
    (ht.eventually (gt_mem_nhds hR))
  let ε := min δ (ENNReal.ofReal a)
  have hε : 0 < ε := lt_min hδ (ENNReal.ofReal_pos.mpr ha)
  have hεa : ε ≤ ENNReal.ofReal a := min_le_right _ _
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hεa
  refine le_iSup₂_of_le ε hε <| iInf₂_mono' fun t hSt =>
    ⟨fun n => f '' (t n ∩ S), ?_, iInf_mono' fun htε => ⟨?_,?_⟩⟩
  · grw [←image_iUnion,←iUnion_inter,←hSt,inter_self]
  · intro n
    exact (himg (t n)).trans (Hδ ((htε n).trans (min_le_left _ _))).le
  · apply ENNReal.tsum_le_tsum
    intro n
    simp only [iSup_le_iff,image_nonempty]
    intro hn
    simp only [Nonempty.mono ((t n).inter_subset_left) hn,ciSup_pos]
    have hd : ediam (t n) ≠ ⊤ := ne_top_of_le_ne_top hεt (htε n)
    have hda : (ediam (t n)).toReal ≤ a := by
      simpa only [ENNReal.toReal_ofReal ha.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top ((htε n).trans hεa)
    have hprod : (L:ℝ≥0∞)*ediam (t n) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hd
    have him := ENNReal.toReal_mono hprod (himg (t n))
    rw [ENNReal.toReal_mul,ENNReal.coe_toReal] at him
    change ENNReal.ofReal (h (ediam (f '' (t n ∩ S))).toReal) ≤
      ENNReal.ofReal ((L:ℝ)^dimension κ)*ENNReal.ofReal (h (ediam (t n)).toReal)
    rw [←ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hLp) _)]
    apply ENNReal.ofReal_le_ofReal
    exact (hh.monotoneOn ENNReal.toReal_nonneg (mul_nonneg hLp.le ENNReal.toReal_nonneg) him).trans
      (hscale _ ENNReal.toReal_nonneg hda)

lemma source_gauge_lipschitz_null (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {K : ℝ≥0} {f : ℂ → ℂ} {S : Set ℂ} (hLip : LipschitzOnWith K f S)
    (hS : hausdorffGauge h S = 0) : hausdorffGauge h (f '' S) = 0 := by
  have hb : hausdorffGauge h (f '' S) ≤ 0 := by
    simpa only [hS,mul_zero] using source_gauge_lipschitz_image_le κ hκ hκ8 h hh hf hLip
  exact le_antisymm hb zero_le
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_gauge_holomorphic_compact_null (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {f : ℂ → ℂ} {D K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) (hd : DifferentiableOn ℂ f D) (hz : hausdorffGauge h K = 0) :
    hausdorffGauge h (f '' K) = 0 := by
  classical
  have hlocal (x : K) : ∃ L : ℝ≥0, ∃ V : Set ℂ, V ∈ 𝓝 (x:ℂ) ∧ LipschitzOnWith L f V :=
    (hd.analyticAt (hD.mem_nhds (hKD x.property))).contDiffAt.exists_lipschitzOnWith
  choose L V hV hLip using hlocal
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun x : K => interior (V x))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr
      ⟨⟨x,hx⟩,mem_interior_iff_mem_nhds.mpr (hV ⟨x,hx⟩)⟩)
  apply measure_mono_null (t := ⋃ i : I, f '' (K ∩ V i.val))
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hI hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,⟨x,⟨hx,interior_subset hxi⟩,rfl⟩⟩
  · apply measure_iUnion_null
    intro i
    exact source_gauge_lipschitz_null κ hκ hκ8 h hh hf
      ((hLip i.val).mono inter_subset_right) (measure_mono_null inter_subset_left hz)

lemma source_inverse_chart_gauge_positive (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (U : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U η G F) (s : ℝ≥0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (hpos : 0 < hausdorffGauge h K) :
    0 < hausdorffGauge h (F s '' K) := by
  have hGc : DifferentiableOn ℂ (G s) (survivingDomain η s) := hw.2.2.2.1 s
  have hFc : ContinuousOn (F s) upperHalfPlane := (hw.2.2.2.2.1 s).continuousOn
  have hFK : IsCompact (F s '' K) := hK.image_of_continuousOn (hFc.mono hKH)
  have hFD : F s '' K ⊆ survivingDomain η s := by
    rintro _ ⟨z,hz,rfl⟩
    exact hw.2.2.2.2.2.2.1 s (hKH hz)
  have hId : G s '' (F s '' K) = K := by
    ext z
    constructor
    · rintro ⟨_,⟨w,hwK,rfl⟩,rfl⟩
      simpa only [hw.2.2.2.2.2.2.2.2.1 s w (hKH hwK)] using hwK
    · intro hz
      exact ⟨F s z,⟨z,hz,rfl⟩,hw.2.2.2.2.2.2.2.2.1 s z (hKH hz)⟩
  by_contra hn
  have hnull : hausdorffGauge h (F s '' K) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hhnull := source_gauge_holomorphic_compact_null κ hκ hκ8 h hh hf
    (isOpen_survivingDomain hw.1 s) hFK hFD hGc hnull
  rw [hId] at hhnull
  exact (ne_of_gt hpos) hhnull
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

theorem source_retained_compact_interior_lower_bound
    {h : ℝ → ℝ} (hh : IsGauge h) {K E : Set ℂ}
    (hK : IsCompact K) (hE : IsClosed E)
    (μ : ℕ → FiniteMeasure ℂ) (a C : ℝ≥0) (ha : 0 < a) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmass : ∀ n, a ≤ (μ n).mass)
    (hKsupport : ∀ n, μ n Kᶜ = 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (μ n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0)
    (hball : ∀ x r, 0 < r → r < ρ →
      ∀ᶠ n in atTop, (μ n : Measure ℂ) (Metric.ball x r) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    0 < hausdorffGauge h (K ∩ E) := by
  have hmpos (n : ℕ) : 0 < (μ n).mass := ha.trans_le (hmass n)
  have hmne (n : ℕ) : μ n ≠ 0 := (μ n).mass_nonzero_iff.mp (hmpos n).ne'
  let νs : ℕ → ProbabilityMeasure ℂ := fun n => (μ n).normalize
  have hνK (n : ℕ) : νs n ∈ {ν : ProbabilityMeasure ℂ | ν Kᶜ = 0} := by
    change (μ n).normalize Kᶜ = 0
    rw [(μ n).normalize_eq_of_nonzero (hmne n), hKsupport n, mul_zero]
  obtain ⟨ν, hνK, φ, hφ, hlim⟩ :=
    (normalized_supported_probability_compact hK).tendsto_subseq hνK
  have hνcarrier (n : ℕ) :
      ((νs ∘ φ) n : Measure ℂ) (Metric.cthickening ((e ∘ φ) n) E)ᶜ = 0 := by
    change ((μ (φ n)).normalize : Measure ℂ) (Metric.cthickening (e (φ n)) E)ᶜ = 0
    rw [(μ (φ n)).toMeasure_normalize_eq_of_nonzero (hmne (φ n)),
      Measure.coe_nnreal_smul_apply, hcarrier (φ n), mul_zero]
  have hνE : (ν : Measure ℂ) E = 1 :=
    (prob_compl_eq_zero_iff hE.measurableSet).mp
      (probability_limit_shrinking_carriers hlim hE (e ∘ φ)
        (he.comp hφ.tendsto_atTop) hνcarrier)
  have hνKE : (ν : Measure ℂ) (K ∩ E) = 1 := by
    apply (prob_compl_eq_zero_iff (hK.isClosed.inter hE).measurableSet).mp
    rw [compl_inter]
    apply measure_union_null
    · exact (ProbabilityMeasure.null_iff_toMeasure_null _ _).mp hνK
    · exact (prob_compl_eq_zero_iff hE.measurableSet).mpr hνE
  have hνball (x : ℂ) (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) :
      (ν : Measure ℂ) (Metric.ball x r) ≤ (↑(C / a) : ℝ≥0∞) * ENNReal.ofReal (h r) := by
    apply probability_limit_ball_bound hlim
    filter_upwards [hφ.tendsto_atTop.eventually (hball x r hr hrρ)] with n hn
    change ((μ (φ n)).normalize : Measure ℂ) (Metric.ball x r) ≤ _
    rw [(μ (φ n)).toMeasure_normalize_eq_of_nonzero (hmne (φ n)),
      Measure.coe_nnreal_smul_apply]
    have hfactor : (↑((μ (φ n)).mass⁻¹) : ℝ≥0∞) ≤ (↑(a⁻¹) : ℝ≥0∞) := by
      rw [ENNReal.coe_inv (hmpos (φ n)).ne', ENNReal.coe_inv ha.ne']
      exact ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr (hmass (φ n)))
    calc
      (↑((μ (φ n)).mass⁻¹) : ℝ≥0∞) * (μ (φ n) : Measure ℂ) (Metric.ball x r)
          ≤ (↑(a⁻¹) : ℝ≥0∞) * ((C : ℝ≥0∞) * ENNReal.ofReal (h r)) :=
        mul_le_mul' hfactor hn
      _ = (↑(C / a) : ℝ≥0∞) * ENNReal.ofReal (h r) := by
        rw [div_eq_mul_inv, ENNReal.coe_mul]
        ac_rfl
  have hdom := gauge_mass_distribution hh (ν : Measure ℂ) (C / a)
    (div_pos hC ha) ρ hρ hνball
  by_contra hn
  have hz : hausdorffGauge h (K ∩ E) = 0 := le_antisymm (le_of_not_gt hn) bot_le
  have hbound := Measure.le_iff'.mp hdom (K ∩ E)
  simp only [hνKE, Measure.smul_apply, hz, smul_eq_mul, mul_zero, not_le_of_gt zero_lt_one]
    at hbound

 
theorem source_retained_compact_interior_lower_bound_of_frequently
    {h : ℝ → ℝ} (hh : IsGauge h) {K E : Set ℂ}
    (hK : IsCompact K) (hE : IsClosed E)
    (μ : ℕ → FiniteMeasure ℂ) (a C : ℝ≥0) (ha : 0 < a) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmass : ∃ᶠ n in atTop, a ≤ (μ n).mass)
    (hKsupport : ∀ n, μ n Kᶜ = 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (μ n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0)
    (hball : ∀ x r, 0 < r → r < ρ →
      ∀ᶠ n in atTop, (μ n : Measure ℂ) (Metric.ball x r) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    0 < hausdorffGauge h (K ∩ E) := by

  obtain ⟨φ, hφ, hm⟩ := Filter.subseq_forall_of_frequently (p := fun n : ℕ => a ≤ (μ n).mass)
    (x := id) tendsto_id hmass
  apply source_retained_compact_interior_lower_bound hh hK hE (μ ∘ φ) a C ha hC ρ hρ hm
    (fun n => hKsupport (φ n)) (e ∘ φ) (he.comp hφ) (fun n => hcarrier (φ n))
  intro x r hr hrρ
  exact hφ.eventually (hball x r hr hrρ)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
theorem sourceRetainedDyadicInterior_proved : SourceRetainedDyadicInteriorTarget := by
  intro κ hκ hκ8 h hh hf K E hK hE μ a ha hmass hKsupport e he hcarrier D hD k₀ htest
  obtain ⟨b, hb, hscale⟩ := source_gauge_bounded_scaling κ hκ hκ8 h hh hf 2 (by norm_num)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp
    (retained_threshold_gauge_eventually κ hκ8 h hf D hD.le)
  let J := max k₀ k₁
  let ρ : ℝ := min 1 (min b ((1/2:ℝ)^J/2))
  have hρ : 0 < ρ := lt_min (by norm_num) (lt_min hb (by positivity))
  let C : ℝ≥0 := ⟨9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ, by positivity⟩
  have hC : 0 < C := by change 0 < 9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ; positivity
  apply source_retained_compact_interior_lower_bound_of_frequently hh hK hE μ a C ha hC ρ hρ
    hmass hKsupport e he hcarrier
  intro x r hr hrρ
  have hr1 : r ≤ 1 := hrρ.le.trans (min_le_left _ _)
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hside : (1/2:ℝ)^k < 2*r := by rw [pow_succ] at hklo; linarith
  have hrJ : 2*r < (1/2:ℝ)^J := by
    have hv : r < (1/2:ℝ)^J/2 := hrρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hJk : J ≤ k := (pow_lt_pow_iff_right_of_lt_one₀
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp (hside.trans hrJ) |>.le
  have hbound : retainedThreshold κ D k ≤
      D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ * h r := by
    have hmono : h ((1/2:ℝ)^k) ≤ h (2*r) :=
      hh.monotoneOn (show 0 ≤ (1/2:ℝ)^k by positivity)
        (show 0 ≤ 2*r by positivity) hside.le
    have hrb : r ≤ b := hrρ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc
      retainedThreshold κ D k ≤ D * (2:ℝ)^(codimension κ/2) * h ((1/2:ℝ)^k) :=
        hk₁ k ((le_max_right _ _).trans hJk)
      _ ≤ D * (2:ℝ)^(codimension κ/2) * ((2:ℝ)^dimension κ * h r) :=
        mul_le_mul_of_nonneg_left (hmono.trans (hscale r hr.le hrb)) (by positivity)
      _ = _ := by ring
  filter_upwards [eventually_ge_atTop k] with N hN
  calc
    (μ N : Measure ℂ) (Metric.ball x r) ≤ 9 * ENNReal.ofReal (retainedThreshold κ D k) :=
      retained_dyadic_ball_bound (μ N) k _ (by
        simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
          htest N k ((le_max_left _ _).trans hJk) hN) x r hkhi
    _ = ENNReal.ofReal (9 * retainedThreshold κ D k) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤9)]
      norm_num
    _ ≤ ENNReal.ofReal ((C:ℝ)*h r) := by
      apply ENNReal.ofReal_le_ofReal
      change 9 * retainedThreshold κ D k ≤
        (9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ) * h r
      calc
        9 * retainedThreshold κ D k ≤ 9 * (D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ * h r) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = _ := by ring
    _ = (C:ℝ≥0∞) * ENNReal.ofReal (h r) := by
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma source_actual_retained_interior_pathwise (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz₀ : 2 < z₀.im) (T : ℝ≥0) (D b : ℝ) (hD : 0 < D) (hb : 0 < b) (k₀ : ℕ)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (ω : a.samples) (hω : ∃ᶠ N in atTop, ENNReal.ofReal b ≤
      retainedMeasure κ D (a.sourceFiniteGreenKernel z₀ T) k₀ N ω (closedBall z₀ 1)) :
    0 < hausdorffGauge h (closedBall z₀ 1 ∩ (γ ω '' Icc 0 T)) := by
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hκ hκ8 z₀ hz₀ T N
  let μ (N : ℕ) : FiniteMeasure ℂ := ⟨retainedMeasure κ D ν k₀ N ω, by
    dsimp [retainedMeasure]; infer_instance⟩
  have hmass : ∃ᶠ N in atTop, (⟨b,hb.le⟩ : ℝ≥0) ≤ (μ N).mass := by
    apply hω.mono
    intro N hN
    have hm : ENNReal.ofReal b ≤ (μ N : Measure ℂ) univ :=
      hN.trans (measure_mono (subset_univ _))
    change b ≤ ((μ N).mass : ℝ)
    have ht := ENNReal.toReal_mono (measure_ne_top (μ N : Measure ℂ) univ) hm
    simpa only [ENNReal.toReal_ofReal hb.le, ← FiniteMeasure.ennreal_mass,
      ENNReal.coe_toReal] using ht
  have hK (N : ℕ) : μ N (closedBall z₀ 1)ᶜ = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact retainedMeasure_zero_of_zero κ D ν k₀ N ω (a.sourceFiniteGreenKernel_supported z₀ T N ω)
  have hcarrier (N : ℕ) : (μ N : Measure ℂ) (cthickening ((2:ℝ)^(-(N:ℝ))) (γ ω '' Icc 0 T))ᶜ = 0 :=
    retainedMeasure_zero_of_zero κ D ν k₀ N ω (a.sourceFiniteGreenKernel_carrier z₀ T N ω)
  have htest (N k : ℕ) (hk₀ : k₀ ≤ k) (hkN : k ≤ N) (ij : ℤ × ℤ) :
      (μ N (retainedDyadicSquare k ij) : ℝ≥0∞) ≤ ENNReal.ofReal (retainedThreshold κ D k) := by
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact retainedMeasure_square_bound κ D ν k₀ N ω k hk₀ hkN ij
  exact sourceRetainedDyadicInterior_proved κ hκ hκ8 h hh hf (closedBall z₀ 1) (γ ω '' Icc 0 T)
    (isCompact_closedBall _ _) (isCompact_Icc.image (a.trace_continuous ω)).isClosed
    μ ⟨b,hb.le⟩ hb hmass hK (fun N => (2:ℝ)^(-(N:ℝ))) source_dyadic_tendsto hcarrier D hD k₀ htest
end RegularSLEPresentation
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.actualRetainedKernelDriverMeasurableSpace
attribute [local instance] OAI.SLEExactGauge.actualRetainedKernelTraceMeasurableSpace
local instance actualRetainedKernelDriverBorelSpace : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance actualRetainedKernelTraceBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_brownian_continuous_law_unique
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B B' : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hc' : ∀ ω, Continuous (fun t => B' t ω)) :
    P.map (sourceDriverPath B hc) = P.map (sourceDriverPath B' hc') := by
  have hL : IsProjectiveLimit (P.map (fun ω t => B t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (Measurable.of_eval hm)]
    exact (hB.hasLaw I).map_eq
  have hR : IsProjectiveLimit (P.map (fun ω t => B' t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (Measurable.of_eval hm')]
    exact (hB'.hasLaw I).map_eq
  apply source_path_evaluation_embedding.map_injective
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n))) (hL.unique hR)
  have hem : Measurable (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [Measure.map_map source_path_evaluation_embedding.measurable (source_path_measurable _ hm),
    Measure.map_map source_path_evaluation_embedding.measurable (source_path_measurable _ hm')]
  rw [Measure.map_map hem (Measurable.of_eval hm),
    Measure.map_map hem (Measurable.of_eval hm')] at he
  exact he


theorem sourceTraceLawUnique_proved : SourceTraceLawUniqueTarget := by
  intro Ω m P κ hκ hκ8 B B' hB hB' hm hm' hc hc' γ η G F G' F' hw hw'
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let bp := sourceDriverPath B hc
  let rp := sourceDriverPath B' hc'
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  let ep := sourceTracePath η (fun ω => (hw' ω).1)
  have hbm : Measurable bp := source_path_measurable bp hm
  have hrm : Measurable rp := source_path_measurable rp hm'
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => gp ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω)
      ?_ (fun ω => continuous_const.mul (hc ω)) γ G F hw
    intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
  obtain ⟨Φ,hΦm,hΦ⟩ := source_trace_factor B hm hc gp hγa
  have hΦe (ω : Ω) : Φ (bp ω) = gp ω := (congrFun hΦ ω).symm
  have hlaw : P.map bp = P.map rp := source_brownian_continuous_law_unique B B' hB hB' hm hm' hc hc'
  choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
    source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
  let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ha⟩
  have hQorig (ω : Ω) (t : ℝ≥0) (n : ℕ) :
      Q t n t (bp ω) = F ω t ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) := by
    apply (hw ω).reverse_flow_identifies t
      ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
      (fun s => Q t n s (bp ω)) (hQ0 t n (bp ω))
    intro s hs
    exact (hQd t n (bp ω) s hs.1).mono Icc_subset_Ici_self
  have hQnew (ω : Ω) (t : ℝ≥0) (n : ℕ) :
      Q t n t (rp ω) = F' ω t ((Real.sqrt κ * B' t ω : ℝ) + (a n : ℂ) * I) := by
    apply (hw' ω).reverse_flow_identifies t
      ((Real.sqrt κ * B' t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
      (fun s => Q t n s (rp ω)) (hQ0 t n (rp ω))
    intro s hs
    exact (hQd t n (rp ω) s hs.1).mono Icc_subset_Ici_self
  have hQlimit (ω : Ω) (t : ℝ≥0) :
      Tendsto (fun n => Q t n t (bp ω)) atTop (𝓝 (Φ (bp ω) t)) := by
    have ht := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
    simpa only [hQorig,hΦe,gp,sourceTracePath,ContinuousMap.coe_mk,Function.comp_def] using ht
  have hset (t : ℝ≥0) : MeasurableSet
      {p : C(ℝ≥0,ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 (0:ℂ)) (fun n => (hQm t n t).sub
      ((continuous_eval_const t).measurable.comp hΦm))
  have hQR (t : ℝ≥0) : ∀ᵐ ω ∂P, Tendsto (fun n => Q t n t (rp ω)) atTop (𝓝 (Φ (rp ω) t)) := by
    have ho : ∀ᵐ p ∂P.map bp, Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
      apply (ae_map_iff hbm.aemeasurable (hset t)).2
      exact Eventually.of_forall (fun ω => tendsto_sub_nhds_zero_iff.mpr (hQlimit ω t))
    rw [hlaw] at ho
    filter_upwards [(ae_map_iff hrm.aemeasurable (hset t)).1 ho] with ω hω
    exact tendsto_sub_nhds_zero_iff.mp hω
  have hEQ : ∀ᵐ ω ∂P, Φ (rp ω) = ep ω := by
    filter_upwards [ae_all_iff.mpr (fun j : ℕ => hQR (denseSeq ℝ≥0 j))] with ω hω
    apply DFunLike.coe_injective
    apply (denseRange_denseSeq ℝ≥0).equalizer (Φ (rp ω)).continuous (ep ω).continuous
    funext j
    have ht := ((hw' ω).2.2.2.2.2.2.2.2.2.2.2.2 (denseSeq ℝ≥0 j)).comp hy
    have hn := hω j
    simp only [hQnew] at hn
    exact tendsto_nhds_unique hn ht
  have he := congrArg (Measure.map Φ) hlaw
  rw [Measure.map_map hΦm hbm,Measure.map_map hΦm hrm] at he
  have hcomp : Φ ∘ bp = gp := hΦ.symm
  rw [hcomp] at he
  exact he.trans (Measure.map_congr hEQ)
end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_TracePosCombined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Pos Combined for chordal SLE. -/

section

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_gauge_cost_nonempty (h : ℝ → ℝ) (hh : IsGauge h) (A : Set ℂ) :
    (⨆ _ : A.Nonempty, extendedGauge h (ediam A)) = extendedGauge h (ediam A) := by
  by_cases hA : A.Nonempty
  · simp [hA]
  · rw [Set.not_nonempty_iff_eq_empty.mp hA]
    simp [extendedGauge,hh.zero]

lemma source_gauge_cover_formula (h : ℝ → ℝ) (hh : IsGauge h) (K : Set ℂ) :
    hausdorffGauge h K = ⨆ (r : ℝ≥0∞) (_ : 0 < r),
      ⨅ (U : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, U n) (_ : ∀ n, ediam (U n) ≤ r),
        ∑' n, extendedGauge h (ediam (U n)) := by
  simp only [hausdorffGauge,Measure.mkMetric_apply,source_gauge_cost_nonempty h hh]

lemma source_gauge_open_enlargement (h : ℝ → ℝ) (hh : IsGauge h)
    (A : Set ℂ) (r : ℝ) (hr : (ediam A).toReal < r) (hA : ediam A ≠ ∞)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ U : Set ℂ, IsOpen U ∧ A ⊆ U ∧ ediam U < ENNReal.ofReal r ∧
      extendedGauge h (ediam U) ≤ extendedGauge h (ediam A) + ε := by
  let b (n : ℕ) : ℝ := 1 / ((n:ℝ)+1)
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  have hb0 : Tendsto b atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let d := (ediam A).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hlim : Tendsto (fun n => d + 2*b n) atTop (𝓝 d) := by
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add (hb0.const_mul 2)
  have hhlim : Tendsto (fun n => ENNReal.ofReal (h (d+2*b n))) atTop
      (𝓝 (extendedGauge h (ediam A))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hh.continuousOn d hd).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hlim,Eventually.of_forall (fun n => show 0 ≤ d+2*b n by positivity)⟩))
  have hcost : extendedGauge h (ediam A) < extendedGauge h (ediam A) + ε := by
    exact ENNReal.lt_add_right (by simp [extendedGauge]) (ENNReal.coe_pos.mpr hε).ne'
  obtain ⟨n,hn,hc⟩ := ( (hlim.eventually (gt_mem_nhds hr)).and
    (hhlim.eventually (gt_mem_nhds hcost)) ).exists
  let U := thickening (b n) A
  have hUb : Bornology.IsBounded U := (isBounded_iff_ediam_ne_top.mpr hA).thickening
  have hdiam : (ediam U).toReal ≤ d+2*b n := diam_thickening_le A (hb n).le
  refine ⟨U,isOpen_thickening, self_subset_thickening (hb n) A,?_,?_⟩
  · rw [←ENNReal.ofReal_toReal hUb.ediam_ne_top]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hdiam.trans_lt hn,by linarith⟩
  · exact (ENNReal.ofReal_le_ofReal (hh.monotoneOn ENNReal.toReal_nonneg
      (show 0 ≤ d+2*b n by positivity) hdiam)).trans hc.le


lemma source_null_compact_finite_open_cover (h : ℝ → ℝ) (hh : IsGauge h)
    (K : Set ℂ) (hK : IsCompact K) (hzero : hausdorffGauge h K = 0)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    sourceFiniteOpenCover h (ENNReal.ofReal r) (ENNReal.ofReal ε) K := by
  have hsmall :
      (⨅ (U : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, U n)
        (_ : ∀ n, ediam (U n) ≤ ENNReal.ofReal (r/2)),
          ∑' n, extendedGauge h (ediam (U n))) < ENNReal.ofReal (ε/2) := by
    apply lt_of_le_of_lt (b := hausdorffGauge h K)
    · rw [source_gauge_cover_formula h hh]
      exact le_iSup_of_le (ENNReal.ofReal (r/2))
        (le_iSup_of_le (ENNReal.ofReal_pos.mpr (by positivity)) le_rfl)
    · simpa only [hzero] using ENNReal.ofReal_pos.mpr (show 0 < ε/2 by positivity)
  obtain ⟨U,hU,hdiam,hcost⟩ := (by simpa only [iInf_lt_iff] using hsmall)
  obtain ⟨e,he,hes⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr (show 0 < ε/2 by positivity)).ne' ℕ
  have hfin (n : ℕ) : ediam (U n) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam n)
  have hrd (n : ℕ) : (ediam (U n)).toReal < r := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam n)
    rw [ENNReal.toReal_ofReal (by positivity)] at hb
    linarith
  choose V hopen hUV hVdiam hVcost using fun n =>
    source_gauge_open_enlargement h hh (U n) r (hrd n) (hfin n) (e n) (he n)
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover V hopen (hU.trans (iUnion_mono hUV))
  refine ⟨V,I,fun n _ => hopen n,fun n _ => (hVdiam n).le,hI,?_⟩
  calc
    (∑ n ∈ I, extendedGauge h (ediam (V n))) ≤ ∑' n, extendedGauge h (ediam (V n)) :=
      ENNReal.sum_le_tsum I
    _ ≤ ∑' n, (extendedGauge h (ediam (U n)) + e n) := ENNReal.tsum_le_tsum hVcost
    _ = (∑' n, extendedGauge h (ediam (U n))) + ∑' n, (e n : ℝ≥0∞) := ENNReal.tsum_add
    _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add hcost hes
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
end
end SLEExactGauge
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_fine_content_finite_cover (h : ℝ → ℝ) (hh : IsGauge h)
    {K : Set ℂ} {R r ε : ℝ≥0∞} (hr : r ≤ R) (hc : sourceFiniteOpenCover h r ε K) :
    sourceFineGaugeContent h R K < ε := by
  classical
  obtain ⟨U,I,hopen,hdiam,hcover,hcost⟩ := hc
  let V (n : ℕ) : Set ℂ := if n ∈ I then U n else ∅
  have hKV : K ⊆ ⋃ n, V n := by
    intro z hz
    obtain ⟨n,hn,hzn⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion.mpr ⟨n,by simpa only [V,ite_eq_left hn] using hzn⟩
  have hVdiam (n : ℕ) : ediam (V n) ≤ R := by
    by_cases hn : n ∈ I
    · simpa only [V,ite_eq_left hn] using (hdiam n hn).trans hr
    · simp [V,hn]
  unfold sourceFineGaugeContent
  apply lt_of_le_of_lt (b := ∑' n, extendedGauge h (ediam (V n)))
  · exact iInf_le_of_le V (iInf_le_of_le hKV (iInf_le_of_le hVdiam le_rfl))
  have hsum : (∑' n, extendedGauge h (ediam (V n))) = ∑ n ∈ I, extendedGauge h (ediam (U n)) := by
    rw [tsum_eq_sum (s := I) (fun n hn => by simp [V,hn,extendedGauge,hh.zero])]
    exact Finset.sum_congr rfl (fun n hn => by simp only [V,ite_eq_left hn])
  simpa only [hsum] using hcost

lemma source_coverScale_tendsto : Tendsto sourceCoverScale atTop (𝓝 0) := by
  unfold sourceCoverScale
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma source_compact_gauge_null_criterion (h : ℝ → ℝ) (hh : IsGauge h)
    (K : Set ℂ) (hK : IsCompact K) :
    hausdorffGauge h K = 0 ↔ ∀ n : ℕ,
      sourceFiniteOpenCover h (sourceCoverScale n) (sourceCoverScale n) K := by
  constructor
  · intro hz n
    exact source_null_compact_finite_open_cover h hh K hK hz _ _ (by positivity) (by positivity)
  · intro hcov
    apply le_antisymm _ zero_le
    rw [source_gauge_cover_formula h hh]
    refine iSup_le fun R => iSup_le fun hR => ?_
    change sourceFineGaugeContent h R K ≤ 0
    apply le_of_tendsto_of_tendsto tendsto_const_nhds source_coverScale_tendsto
    filter_upwards [source_coverScale_tendsto.eventually (gt_mem_nhds hR)] with n hn
    exact (source_fine_content_finite_cover h hh hn.le (hcov n)).le
end
end SLEExactGauge
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.tracePosCoverComplexPathMeasurable
local instance tracePosCoverComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_finite_open_cover_trace_isOpen (h : ℝ → ℝ) (C : Set ℂ) (hC : IsClosed C)
    (s t : ℝ≥0) (r ε : ℝ≥0∞) :
    IsOpen {γ : C(ℝ≥0,ℂ) | sourceFiniteOpenCover h r ε (C ∩ (γ '' Icc s t))} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro γ hγ
  obtain ⟨U,I,ho,hd,hcov,hcost⟩ := hγ
  let O := ⋃ n ∈ I, U n
  have hO : IsOpen O := isOpen_iUnion (fun n => isOpen_iUnion (fun hn => ho n hn))
  have hmap : MapsTo γ (Icc s t) (Cᶜ ∪ O) := by
    intro u hu
    by_cases hc : γ u ∈ C
    · exact Or.inr (hcov ⟨hc,⟨u,hu,rfl⟩⟩)
    · exact Or.inl hc
  have hev := (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc (hC.isOpen_compl.union hO)).mem_nhds hmap
  filter_upwards [hev] with g hg
  refine ⟨U,I,ho,hd,?_,hcost⟩
  rintro z ⟨hz,u,hu,rfl⟩
  exact (hg hu).resolve_left (fun hn => hn hz)


theorem sourceTracePositiveMeasurable_proved : SourceTracePositiveMeasurableTarget := by
  intro h hh C hC s t
  have hnull : MeasurableSet {γ : C(ℝ≥0,ℂ) | hausdorffGauge h (C ∩ (γ '' Icc s t)) = 0} := by
    have heq : {γ : C(ℝ≥0,ℂ) | hausdorffGauge h (C ∩ (γ '' Icc s t)) = 0} =
        ⋂ n : ℕ, {γ : C(ℝ≥0,ℂ) | sourceFiniteOpenCover h (sourceCoverScale n) (sourceCoverScale n)
          (C ∩ (γ '' Icc s t))} := by
      ext γ
      simp only [mem_ofPred_eq,mem_iInter]
      exact source_compact_gauge_null_criterion h hh _
        ((isCompact_Icc.image γ.continuous).inter_left hC)
    rw [heq]
    exact MeasurableSet.iInter (fun n =>
      (source_finite_open_cover_trace_isOpen h C hC s t _ _).measurableSet)
  simpa only [compl_ofPred,←ne_eq,←pos_iff_ne_zero] using hnull.compl
end
end SLEExactGauge
end
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SimplePastMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simple Past Mesh for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology


section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable


theorem sourceInteriorRetainedTransfer_proved_allKappa : SourceInteriorRetainedTransferTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  obtain ⟨T,D,b,p,k₀,hT,hD,hb,hp,hlim⟩ := a.source_actual_retained_experiment_allKappa hκ hκ8 z₀ hz₀
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hk hκ8 z₀ hz₀ T N
  let E : Set a.samples := {ω | ∃ᶠ N in atTop, ENNReal.ofReal b ≤
    retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)}
  have hE : MeasurableSet E := by
    have heq : E = ⋂ n : ℕ, ⋃ N ≥ n,
        {ω | ENNReal.ofReal b ≤ retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)} := by
      ext ω
      simp [E,frequently_atTop]
    rw [heq]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun N => MeasurableSet.iUnion
      (fun _ => measurableSet_le measurable_const (retainedMeasure_measurable κ D ν k₀ N measurableSet_closedBall))))
  refine ⟨T,E,hT,hE,(ENNReal.ofReal_pos.mpr hp).trans_le hlim,?_⟩
  intro ω hω
  have hpos := a.source_actual_retained_interior_pathwise hk hκ8 z₀ hz₀ T D b (zero_lt_one.trans_le hD) hb
    k₀ h hh hf ω hω
  refine ⟨hpos,?_⟩
  intro U η G F hw s
  exact source_inverse_chart_gauge_positive κ hk hκ8 h hh hf U η G F hw s
    ((isCompact_closedBall z₀ 1).inter_right (isCompact_Icc.image (a.trace_continuous ω)).isClosed)
    (fun z hz => zero_lt_one.trans (source_unit_ball_height hz₀ hz.1)) hpos
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance simplePastMeshDriverMeasurableSpace_r896653_1 : MeasurableSpace C(ℝ≥0, ℝ) := borel _
attribute [local instance] OAI.SLEExactGauge.simplePastMeshTraceMeasurableSpace
local instance simplePastMeshDriverBorelSpace_r896653_1 : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance simplePastMeshTraceBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_dilation_gauge_positive_allKappa (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {c : ℂ} (hc : c ≠ 0) {S : Set ℂ} (hS : IsCompact S)
    (hp : 0 < hausdorffGauge h S) : 0 < hausdorffGauge h ((fun z => c*z) '' S) := by
  by_contra hn
  have hz : hausdorffGauge h ((fun z => c*z) '' S) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have he := source_gauge_holomorphic_compact_null κ hκ hκ8 h hh hf
    (D := univ) (f := fun z => c⁻¹*z) isOpen_univ (hS.image (continuous_const.mul continuous_id))
    (subset_univ _) (by fun_prop) hz
  have hi : (fun z => c⁻¹*z) '' ((fun z => c*z) '' S) = S := by
    rw [←image_comp]
    simp only [Function.comp_def,←mul_assoc,inv_mul_cancel₀ hc,one_mul,image_id']
  change hausdorffGauge h ((fun z => c⁻¹*z) '' ((fun z => c*z) '' S)) = 0 at he
  rw [hi] at he
  exact hp.ne' he

lemma RegularSLEPresentation.source_trace_path_measurable_allKappa
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) :
    Measurable (sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous) := by
  apply source_path_measurable
  intro t
  exact (a.trace_adapted t).mono (a.filtration.le t) le_rfl

lemma RegularSLEPresentation.source_scale_trace_law_allKappa
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ℝ≥0) (hc : 0 < c) :
    (P.comap (Subtype.val : a.samples → Ω)).map
      (sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous) =
    (P.comap (Subtype.val : a.samples → Ω)).map
      (sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω))
        (a.sourceScaled c hc).trace_continuous) := by
  exact sourceTraceLawUnique_proved κ hκ hκ8 a.B (a.sourceScaled c hc).B
    a.brownian (a.sourceScaled c hc).brownian a.measurable_B (a.sourceScaled c hc).measurable_B
    a.continuous_B (a.sourceScaled c hc).continuous_B _ _ a.G a.F
    (a.sourceScaled c hc).G (a.sourceScaled c hc).F a.witness (a.sourceScaled c hc).witness


theorem sourceUniformInteriorSeed_proved_allKappa : SourceUniformInteriorSeedTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ a h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  let z₀ : ℂ := 3*I
  have hz₀ : 2 < z₀.im := by norm_num [z₀]
  obtain ⟨T,E,hT,hE,hp,hseed⟩ :=
    sourceInteriorRetainedTransfer_proved_allKappa κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let Q := P.comap (Subtype.val : a.samples → Ω)
  refine ⟨Q E,hp,?_⟩
  intro δ hδ
  let c := NNReal.sqrt (δ/T)
  have hc : 0 < c := by dsimp [c]; exact NNReal.sqrt_pos.mpr (div_pos hδ hT)
  have hc2 : c^2 = δ/T := NNReal.sq_sqrt _
  have ht : sourceScaleTime c δ = T := by
    unfold sourceScaleTime
    rw [hc2]
    field_simp
  let K := (fun z : ℂ => (c:ℂ)*z) '' closedBall z₀ 1
  have hK : IsCompact K := (isCompact_closedBall z₀ 1).image (continuous_const.mul continuous_id)
  have hKH : K ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    have hz' : 0 < z.im := zero_lt_one.trans (source_unit_ball_height hz₀ hz)
    change 0 < ((c:ℂ)*z).im
    simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using mul_pos (show 0 < (c:ℝ) from hc) hz'
  refine ⟨K,hK,hKH,?_⟩
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let sp := sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω))
    (a.sourceScaled c hc).trace_continuous
  let A : Set C(ℝ≥0,ℂ) := {g | 0 < hausdorffGauge h (K ∩ (g '' Icc 0 δ))}
  have hA : MeasurableSet A := sourceTracePositiveMeasurable_proved h hh K hK.isClosed 0 δ
  have hm : Measurable gp := a.source_trace_path_measurable_allKappa
  have hsm : Measurable sp := (a.sourceScaled c hc).source_trace_path_measurable_allKappa
  have hmap := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ A) (a.source_scale_trace_law_allKappa hk hκ8 c hc)
  rw [Measure.map_apply hm hA,Measure.map_apply hsm hA] at hmap
  change Q E ≤ Q (gp ⁻¹' A)
  rw [hmap]
  apply measure_mono
  intro ω hω
  have hpos := (hseed ω hω).1
  have heq : K ∩ (sourceScaleTrace c (γ ω) '' Icc 0 δ) =
      (fun z : ℂ => (c:ℂ)*z) '' (closedBall z₀ 1 ∩ (γ ω '' Icc 0 T)) := by
    rw [source_scale_past c δ hc,ht, image_inter (mul_right_injective₀ (by exact_mod_cast hc.ne' : (c:ℂ) ≠ 0))]
  change 0 < hausdorffGauge h (K ∩ (sourceScaleTrace c (γ ω) '' Icc 0 δ))
  rw [heq]
  exact source_dilation_gauge_positive_allKappa κ hk hκ8 h hh hf (by exact_mod_cast hc.ne')
    ((isCompact_closedBall z₀ 1).inter_right (isCompact_Icc.image (a.trace_continuous ω)).isClosed) hpos
end
end SLEExactGauge
end

 
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_LowerRestartConditionalAllKappa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower Restart Conditional All Kappa for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.lowerRestartAllKappaRealPathMeasurable
attribute [local instance] OAI.SLEExactGauge.lowerRestartAllKappaComplexPathMeasurable
local instance lowerRestartAllKappaRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance lowerRestartAllKappaComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_translation_gauge_positive_allKappa (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (b : ℂ) {S : Set ℂ} (hS : IsCompact S)
    (hp : 0 < hausdorffGauge h S) : 0 < hausdorffGauge h ((fun z => z+b) '' S) := by
  by_contra hn
  have hz : hausdorffGauge h ((fun z => z+b) '' S) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have he := source_gauge_holomorphic_compact_null κ hκ hκ8 h hh hf
    (D := univ) (f := fun z => z-b) isOpen_univ (hS.image (continuous_id.add_const b))
    (subset_univ _) (by fun_prop) hz
  have hi : (fun z => z-b) '' ((fun z => z+b) '' S) = S := by
    rw [←image_comp]
    simp only [Function.comp_def,add_sub_cancel_right,image_id']
  change hausdorffGauge h ((fun z => z-b) '' ((fun z => z+b) '' S)) = 0 at he
  rw [hi] at he
  exact hp.ne' he

lemma source_restart_segment_positive_allKappa (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (s δ : ℝ≥0) (η : C(ℝ≥0,ℂ))
    (hid : ∀ t : ℝ≥0, η t ∈ upperHalfPlane → γ (s+t) = F s (η t + (U s:ℂ)))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (hp : 0 < hausdorffGauge h (K ∩ (η '' Icc 0 δ))) :
    0 < hausdorffGauge h (γ '' Icc s (s+δ)) := by
  let L := K ∩ (η '' Icc 0 δ)
  have hL : IsCompact L := hK.inter_right (isCompact_Icc.image η.continuous).isClosed
  have hLH : L ⊆ upperHalfPlane := inter_subset_left.trans hKH
  have htrans := source_translation_gauge_positive_allKappa κ hκ hκ8 h hh hf (U s:ℂ) hL hp
  have htrK : IsCompact ((fun z => z+(U s:ℂ)) '' L) := hL.image (continuous_id.add_const _)
  have htrH : (fun z => z+(U s:ℂ)) '' L ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    simpa only [upperHalfPlane,mem_ofPred_eq,add_im,ofReal_im,add_zero] using hLH hz
  have hpositive := source_inverse_chart_gauge_positive κ hκ hκ8 h hh hf U γ G F hw s htrK htrH htrans
  apply hpositive.trans_le (measure_mono ?_)
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  obtain ⟨u,hu,rfl⟩ := hz.2
  refine ⟨s+u,⟨le_add_of_nonneg_right hu.1,add_le_add le_rfl hu.2⟩,?_⟩
  exact hid u (hKH hz.1)

lemma RegularSLEPresentation.source_segment_positive_measurable_at_allKappa
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (h : ℝ → ℝ) (hh : IsGauge h)
    (s t : ℝ≥0) :
    MeasurableSet[a.filtration t] {ω : a.samples | 0 < hausdorffGauge h (γ ω '' Icc s t)} := by
  let f : a.samples → C(ℝ≥0,ℂ) := fun ω =>
    ⟨fun u => γ ω (min u t), (a.trace_continuous ω).comp (continuous_id.min continuous_const)⟩
  have hm : @Measurable a.samples C(ℝ≥0,ℂ) (a.filtration t) (borel _) f := by
    let : MeasurableSpace a.samples := a.filtration t
    apply source_path_measurable
    intro u
    exact (a.trace_adapted (min u t)).mono (a.filtration.mono (min_le_right u t)) le_rfl
  have heq : {ω : a.samples | 0 < hausdorffGauge h (γ ω '' Icc s t)} =
      f ⁻¹' {g : C(ℝ≥0,ℂ) | 0 < hausdorffGauge h (univ ∩ (g '' Icc s t))} := by
    ext ω
    simp only [mem_preimage,mem_ofPred_eq,univ_inter]
    have hi : γ ω '' Icc s t = f ω '' Icc s t := by
      apply image_congr
      intro u hu
      simp only [f,ContinuousMap.coe_mk,min_eq_left hu.2]
    rw [hi]
  rw [heq]
  exact (sourceTracePositiveMeasurable_proved h hh univ isClosed_univ s t).preimage hm

lemma RegularSLEPresentation.source_segment_null_measurable_at_allKappa
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (h : ℝ → ℝ) (hh : IsGauge h) (s t : ℝ≥0) :
    MeasurableSet[a.filtration t] {ω : a.samples | hausdorffGauge h (γ ω '' Icc s t) = 0} := by
  simpa only [compl_ofPred,not_lt,nonpos_iff_eq_zero] using
    (a.source_segment_positive_measurable_at_allKappa h hh s t).compl

lemma RegularSLEPresentation.source_uniform_null_slot_bound_allKappa
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧ ∀ (s δ : ℝ≥0), 0 < δ →
      ∀ A : Set a.samples, MeasurableSet[a.filtration s] A →
        (P.comap Subtype.val) (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0}) ≤
          (1-p)*(P.comap Subtype.val) A := by
  have hk : 0 < κ := by linarith
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hseed⟩ := sourceUniformInteriorSeed_proved_allKappa κ hκ hκ8 Ω m P inferInstance γ a h hh hf
  have hp1 : p ≤ 1 := by
    obtain ⟨K,hK,hKH,hKP⟩ := hseed 1 zero_lt_one
    exact hKP.trans (prob_le_one)
  refine ⟨p,hp,hp1,?_⟩
  intro s δ hδ A hA
  obtain ⟨K,hK,hKH,hKP⟩ := hseed δ hδ
  obtain ⟨Φ,hΦm,hΦe,hrestart⟩ := sourceStoppedTraceLaw κ hk hκ8 a.B a.brownian
    a.measurable_B a.continuous_B (fun ω : a.samples => γ ω) a.G a.F a.witness
  let τ : a.samples → ℝ≥0 := fun _ => s
  have hτ : IsStoppingTime a.filtration (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_const a.filtration s
  have hAstop : MeasurableSet[hτ.measurableSpace] A := by
    change MeasurableSet[(isStoppingTime_const a.filtration s).measurableSpace] A
    rw [IsStoppingTime.measurableSpace_const]
    exact hA
  obtain ⟨hlaw,hident⟩ := hrestart τ hτ
  let rp := sourceRestartDriverPath a.B a.continuous_B τ
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let C : Set C(ℝ≥0,ℂ) := {g | 0 < hausdorffGauge h (K ∩ (g '' Icc 0 δ))}
  let E : Set a.samples := (fun ω => Φ (rp ω)) ⁻¹' C
  have hC : MeasurableSet C := sourceTracePositiveMeasurable_proved h hh K hK.isClosed 0 δ
  have hrm : Measurable rp := by
    apply source_path_measurable
    intro t
    exact (a.measurable_B (s+t)).sub (a.measurable_B s)
  have hem : Measurable (fun ω => Φ (rp ω)) := hΦm.comp hrm
  have hEm : MeasurableSet E := hC.preimage hem
  have hAm : MeasurableSet A := (a.filtration.le s) A hA
  have hprob : Q (A ∩ E) = Q A * Q {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Icc 0 δ))} := by
    have he := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ C) (hlaw A hAstop)
    rw [Measure.map_apply hem hC,Measure.smul_apply,
      Measure.map_apply a.source_trace_path_measurable_allKappa hC,
      Measure.restrict_apply (hC.preimage hem)] at he
    change Q (E ∩ A) = Q A * Q {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Icc 0 δ))} at he
    simpa only [inter_comm] using he
  have hins : (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0} : Set a.samples) ≤ᵐ[Q] (A \ E : Set a.samples) := by
    filter_upwards [hident] with ω hω
    intro hx
    refine ⟨hx.1,?_⟩
    intro hsuc
    have hpositive := source_restart_segment_positive_allKappa κ hk hκ8 h hh hf
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω)
      s δ (Φ (rp ω)) hω hK hKH hsuc
    rw [hx.2] at hpositive
    exact lt_irrefl _ hpositive
  have hdiff : Q (A \ E) = Q A - Q (A ∩ E) := by
    have he : A \ E = A \ (A ∩ E) := by ext ω; simp only [Set.mem_sdiff,mem_inter_iff]; tauto
    rw [he]
    exact measure_sdiff inter_subset_left (hAm.inter hEm).nullMeasurableSet (measure_ne_top Q _)
  calc Q (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0})
      ≤ Q (A \ E) := measure_mono_ae hins
    _ = Q A - Q (A ∩ E) := hdiff
    _ ≤ Q A - Q A*p := tsub_le_tsub_left (by rw [hprob]; gcongr) _
    _ = (1-p)*Q A := by
      rw [ENNReal.sub_mul (fun _ _ => measure_ne_top Q A),one_mul,mul_comm p (Q A)]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma RegularSLEPresentation.source_positive_fixed_interval_allKappa
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ (ω : a.samples) ∂P.comap (Subtype.val : a.samples → Ω), 0 < hausdorffGauge h (γ ω '' Icc s t) := by
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hp1,hslot⟩ := a.source_uniform_null_slot_bound_allKappa hκ hκ8 h hh hf
  let c : ℝ≥0∞ := 1-p
  have hc : c < 1 := ENNReal.sub_lt_self (by simp) (by simp) hp.ne'
  have hsteps (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ) :
      Q {ω | hausdorffGauge h (γ ω '' Icc s (s+(k:ℝ≥0)*δ)) = 0} ≤ c^k := by
    induction k with
    | zero => simpa using (prob_le_one (μ := Q)
        (s := {ω | hausdorffGauge h (γ ω '' Icc s (s+(0:ℝ≥0)*δ)) = 0}))
    | succ k ih =>
      have he : s+((k+1:ℕ):ℝ≥0)*δ = (s+(k:ℝ≥0)*δ)+δ := by push_cast; ring
      rw [he,pow_succ,mul_comm (c^k) c]
      let A : Set a.samples := {ω | hausdorffGauge h (γ ω '' Icc s (s+(k:ℝ≥0)*δ)) = 0}
      have hA : MeasurableSet[a.filtration (s+(k:ℝ≥0)*δ)] A :=
        a.source_segment_null_measurable_at_allKappa h hh s _
      calc Q {ω | hausdorffGauge h (γ ω '' Icc s (s+(k:ℝ≥0)*δ+δ)) = 0}
          ≤ Q (A ∩ {ω | hausdorffGauge h (γ ω '' Icc (s+(k:ℝ≥0)*δ) (s+(k:ℝ≥0)*δ+δ)) = 0}) := by
            apply measure_mono
            intro ω hω
            constructor
            · exact measure_mono_null (image_mono (Icc_subset_Icc le_rfl (le_add_of_nonneg_right (show 0 ≤ δ from bot_le)))) hω
            · exact measure_mono_null (image_mono (Icc_subset_Icc (le_add_of_nonneg_right (by positivity)) le_rfl)) hω
        _ ≤ c * Q A := hslot _ δ hδ A hA
        _ ≤ c * c^k := by gcongr
  have hbound : ∀ᶠ n : ℕ in atTop,
      Q {ω | hausdorffGauge h (γ ω '' Icc s t) = 0} ≤ c^n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < (n:ℝ≥0) := by exact_mod_cast (show 0 < n by omega)
    let δ : ℝ≥0 := (t-s)/(n:ℝ≥0)
    have hδ : 0 < δ := div_pos (tsub_pos_iff_lt.mpr hst) hn0
    have he : s+(n:ℝ≥0)*δ = t := by
      dsimp [δ]
      rw [mul_div_cancel₀ _ hn0.ne',add_tsub_cancel_of_le hst.le]
    simpa only [he] using hsteps δ hδ n
  have hzero : Q {ω | hausdorffGauge h (γ ω '' Icc s t) = 0} = 0 :=
    le_antisymm (ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc) hbound) zero_le
  apply ae_iff.mpr
  simpa only [not_lt,nonpos_iff_eq_zero] using hzero
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma RegularSLEPresentation.source_positive_all_intervals_allKappa
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∀ᵐ (ω : a.samples) ∂P.comap (Subtype.val : a.samples → Ω),
      ∀ s t : ℝ≥0, 0 < s → s < t → 0 < hausdorffGauge h (γ ω '' Icc s t) := by
  have hrat : ∀ᵐ (ω : a.samples) ∂P.comap (Subtype.val : a.samples → Ω),
      ∀ r q : ℚ, (r:ℝ).toNNReal < (q:ℝ).toNNReal →
        0 < hausdorffGauge h (γ ω '' Icc (r:ℝ).toNNReal (q:ℝ).toNNReal) := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro hrq
    exact a.source_positive_fixed_interval_allKappa hκ hκ8 h hh hf _ _ hrq
  filter_upwards [hrat] with ω hω
  intro s t hs hst
  obtain ⟨r,hsr,hrt⟩ := exists_rat_btwn (show (s:ℝ) < (t:ℝ) from hst)
  obtain ⟨q,hrq,hqt⟩ := exists_rat_btwn hrt
  have hq : 0 < (q:ℝ) := (show 0 < (s:ℝ) from hs).trans (hsr.trans hrq)
  have hp := hω r q ((Real.toNNReal_lt_toNNReal_iff hq).mpr hrq)
  apply hp.trans_le (measure_mono (image_mono (Icc_subset_Icc ?_ ?_)))
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hsr.le
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hqt.le


theorem sourceLowerAllIntervals_proved_allKappa : SourceLowerAllIntervalsTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ hSLE h hh hf
  let : IsProbabilityMeasure P := hP
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  have ha := a.source_positive_all_intervals_allKappa hκ hκ8 h hh hf
  rw [←a.measurePreserving_val.map_eq]
  exact (MeasurableEmbedding.subtype_coe a.measurable_samples).ae_map_iff.mpr ha
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge
theorem sourceLowerAllKappa_proved : SourceLowerAllKappaTarget := sourceLowerAllIntervals_proved_allKappa
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.lowerUniverseRealPathMeasurable
attribute [local instance] OAI.SLEExactGauge.lowerUniverseComplexPathMeasurable
local instance lowerUniverseRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance lowerUniverseComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_lower_universe {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (γ ω '' Icc s t) := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let : IsProbabilityMeasure μ := a.probability
  let bp := sourceDriverPath a.B a.continuous_B
  let gp := sourceTracePath (γ ∘ Subtype.val) a.trace_continuous
  have hbm : Measurable bp := source_path_measurable bp a.measurable_B
  have hgm : Measurable gp := source_path_measurable gp (fun t => (hSLE.1 t).comp measurable_subtype_coe)
  let pair : a.samples → C(ℝ≥0,ℝ) × C(ℝ≥0,ℂ) := fun ω => (bp ω, gp ω)
  have hpair : Measurable pair := hbm.prodMk hgm
  let X := range pair
  let f : a.samples → X := fun ω => ⟨pair ω, mem_range_self ω⟩
  have hfm : Measurable f := hpair.subtype_mk
  let Q := μ.map f
  let : IsProbabilityMeasure Q := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let B : ℝ≥0 → X → ℝ := fun t x => x.val.1 t
  let η : X → ℝ≥0 → ℂ := fun x t => x.val.2 t
  have hBm (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp (measurable_fst.comp measurable_subtype_coe)
  have hηm (t : ℝ≥0) : Measurable (fun x => η x t) :=
    (continuous_eval_const t).measurable.comp (measurable_snd.comp measurable_subtype_coe)
  have hBrownian : IsBrownianReal B Q := by
    constructor
    · constructor
      intro I
      have hmI : Measurable (fun x : X => I.restrict (B · x)) :=
        Measurable.of_eval (fun index => hBm index)
      refine ⟨hmI.aemeasurable, ?_⟩
      rw [show Q = μ.map f from rfl, Measure.map_map hmI hfm]
      exact (a.brownian.hasLaw I).map_eq
    · exact Eventually.of_forall (fun x => x.val.1.continuous)
  have hη : IsOrdinaryChordalSLE κ η Q := by
    refine ⟨hηm, B, hBrownian, Eventually.of_forall ?_⟩
    intro x
    obtain ⟨ω, hω⟩ := x.property
    refine ⟨a.G ω, a.F ω, ?_⟩
    have hp : pair ω = x.val := hω
    have heB : ∀ t, B t x = a.B t ω := fun t => congrArg (fun z => z.1 t) hp.symm
    have heη : η x = γ ω := by
      exact congrArg (fun z => (z.2 : ℝ≥0 → ℂ)) hp.symm
    simpa only [heB,heη] using a.witness ω
  have hlow := sourceLowerAllKappa_proved κ hκ hκ8 X inferInstance Q inferInstance η hη h hh hf
  have hpull := ae_of_ae_map hfm.aemeasurable hlow
  rw [←a.measurePreserving_val.map_eq]
  apply (MeasurableEmbedding.subtype_coe a.measurable_samples).ae_map_iff.mpr
  exact hpull
end
end SLEExactGauge
end

 
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_LowerPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower Positivity for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge
theorem sourceLowerMain_proved_oai : SourceLowerMainTarget := by
  intro Ω m P hP κ hκ hκ8 γ hSLE h hh hf
  let : IsProbabilityMeasure P := hP
  exact source_lower_universe hκ hκ8 hSLE h hh hf
end SLEExactGauge
end

 
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SLEExactGauge.sourceLowerMain_proved_oai.{u_1} := @OAI.SLEExactGauge.sourceLowerMain_proved_oai.{u_1}
