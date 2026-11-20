-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.Supplement.divergence_increment
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:11:44.481267+00:00
-- url     : https://prove2.me/submissions/7bf4c20c-0f05-42f8-b9a5-45a3d15c2bba

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonDivergence

open LinearHashingPoissonesque.ExpectedLoads

theorem solution (mu s t : ℝ) (hmu : 0 < mu) (hs : 0 < s) (hst : s < t) :
    poissonDivergence t mu - poissonDivergence s mu =
      (∫ x in s..t, Real.log (x / mu)) ∧
    (t - s) * Real.log (s / mu) ≤ (∫ x in s..t, Real.log (x / mu)) := by
  have hpos : ∀ x ∈ Set.uIcc s t, 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hst.le] at hx; linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc s t,
      HasDerivAt (fun y => poissonDivergence y mu) (Real.log (x / mu)) x := by
    intro x hx
    have hx0 := hpos x hx
    have h1 : HasDerivAt (fun y => Real.log (y / mu)) (1 / mu / (x / mu)) x :=
      ((hasDerivAt_id x).div_const mu).log (div_pos hx0 hmu).ne'
    have h2 : HasDerivAt (fun y => y * Real.log (y / mu) - y + mu)
        (1 * Real.log (x / mu) + x * (1 / mu / (x / mu)) - 1) x :=
      (((hasDerivAt_id' x).mul h1).sub (hasDerivAt_id' x)).add_const mu
    show HasDerivAt (fun y => y * Real.log (y / mu) - y + mu) _ x
    refine h2.congr_deriv ?_
    have : x * (1 / mu / (x / mu)) = 1 := by field_simp
    rw [this]; ring
  have hcont : ContinuousOn (fun x => Real.log (x / mu)) (Set.uIcc s t) := by
    refine ContinuousOn.log (continuousOn_id.div_const mu) (fun x hx => (div_pos (hpos x hx) hmu).ne')
  have hint : IntervalIntegrable (fun x => Real.log (x / mu)) MeasureTheory.volume s t :=
    hcont.intervalIntegrable
  refine ⟨(intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm, ?_⟩
  have hmono : ∀ x ∈ Set.Icc s t, Real.log (s / mu) ≤ Real.log (x / mu) := by
    intro x hx
    exact Real.log_le_log (div_pos hs hmu) (div_le_div_of_nonneg_right hx.1 hmu.le)
  have := intervalIntegral.integral_mono_on hst.le intervalIntegrable_const hint hmono
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this
