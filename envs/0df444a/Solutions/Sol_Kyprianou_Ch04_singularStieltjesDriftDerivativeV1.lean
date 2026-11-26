-- Prove2me | solution 1 for Kyprianou.Ch04.singularStieltjesDriftDerivativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:28:35.366203+00:00
-- url     : https://prove2.me/submissions/ed53c72a-88e1-4632-a39a-ab978ca13e8b

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The difference of two singular Stieltjes functions has derivative zero almost everywhere. -/
theorem solution (p q : StieltjesFunction ℝ)
    (hp : p.measure.MutuallySingular volume)
    (hq : q.measure.MutuallySingular volume) (d : ℝ) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt (fun t : ℝ => d * t + p t - q t) d x := by
  filter_upwards [p.ae_hasDerivAt, q.ae_hasDerivAt,
    hp.rnDeriv_ae_eq_zero, hq.rnDeriv_ae_eq_zero] with x hdp hdq hzp hzq
  have h1 : HasDerivAt p 0 x := by simpa [hzp] using hdp
  have h2 : HasDerivAt q 0 x := by simpa [hzq] using hdq
  change HasDerivAt ((fun t : ℝ => d * t) + (p : ℝ → ℝ) - (q : ℝ → ℝ)) d x
  simpa only [id_eq, mul_one, add_zero, sub_zero] using
    (((hasDerivAt_id x).const_mul d).add h1).sub h2
