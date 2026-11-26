-- Prove2me | solution 1 for ManyServerQED.Scheduling.independent_brownian_normalized_linear_combination
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:06:58.622901+00:00
-- url     : https://prove2.me/submissions/4d97961e-fe50-43ab-bde5-40c30ed369ba

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B C : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hI : IndepFun (fun ω t => B t ω) (fun ω t => C t ω) P)
    (a b : ℝ) (hW : a^2+b^2=1) :
    IsBrownianReal (fun t ω => a*B t ω+b*C t ω) P := by
  let X (t : ℝ≥0) (ω : Ω) := a*B t ω
  let Y (t : ℝ≥0) (ω : Ω) := b*C t ω
  let Z (t : ℝ≥0) (ω : Ω) := X t ω+Y t ω
  have hXG : IsGaussianProcess X P := hB.isGaussianProcess.smul (fun _ => a)
  have hYG : IsGaussianProcess Y P := hC.isGaussianProcess.smul (fun _ => b)
  have hind : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P := by
    exact hI.comp
      (measurable_pi_lambda _ (fun t => (measurable_pi_apply t).const_mul a))
      (measurable_pi_lambda _ (fun t => (measurable_pi_apply t).const_mul b))
  have hZ : IsGaussianProcess Z P := by
    constructor
    intro J
    let q (x : ℝ≥0 → ℝ) (t : J) := x t.val
    have hq : Measurable q := measurable_pi_lambda _ (fun t : J => measurable_pi_apply t.val)
    have hi : IndepFun (fun ω => J.restrict (X · ω)) (fun ω => J.restrict (Y · ω)) P :=
      hind.comp hq hq
    have hh := hi.hasGaussianLaw (hXG.hasGaussianLaw J) (hYG.hasGaussianLaw J)
    let L : ((J → ℝ) × (J → ℝ)) →L[ℝ] (J → ℝ) := ContinuousLinearMap.fst ℝ _ _ +
      ContinuousLinearMap.snd ℝ _ _
    exact hh.map L
  have hMemX (t : ℝ≥0) : MemLp (X t) 2 P := (hXG.hasGaussianLaw_eval t).memLp_two
  have hMemY (t : ℝ≥0) : MemLp (Y t) 2 P := (hYG.hasGaussianLaw_eval t).memLp_two
  have hcross (s t : ℝ≥0) : cov[X s,Y t;P] = 0 :=
    (hind.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero (hMemX s) (hMemY t)
  have hcross' (s t : ℝ≥0) : cov[Y s,X t;P] = 0 := by rw [covariance_comm, hcross]
  have hZmean (t : ℝ≥0) : ∫ ω, Z t ω ∂P = 0 := by
    change (∫ ω, X t ω+Y t ω ∂P) = 0
    rw [integral_add ((hMemX t).integrable (by norm_num)) ((hMemY t).integrable (by norm_num))]
    unfold X Y
    rw [integral_const_mul, integral_const_mul, hB.integral_eval, hC.integral_eval]
    ring
  have hCov (s t : ℝ≥0) (hst : s ≤ t) : cov[Z s,Z t;P] = (s:ℝ) := by
    change cov[X s + Y s, X t + Y t;P] = _
    rw [covariance_add_left (hMemX _) (hMemY _) ((hMemX _).add (hMemY _)),
      covariance_add_right (hMemX _) (hMemX _) (hMemY _),
      covariance_add_right (hMemY _) (hMemX _) (hMemY _), hcross, hcross']
    unfold X Y
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval, hC.covariance_eval]
    simp only [min_eq_left hst, min_eq_left (show (s:ℝ) ≤ t by exact_mod_cast hst)]
    calc
      _ = (a^2+b^2)*(s:ℝ) := by ring
      _ = _ := by rw [hW,one_mul]
  refine ⟨hZ.isPreBrownianReal_of_covariance hZmean hCov, ?_⟩
  filter_upwards [hB.cont,hC.cont] with ω h1 h2
  exact (h1.const_mul a).add (h2.const_mul b)
