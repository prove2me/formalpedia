-- Prove2me | solution 1 for Kyprianou.Ch05.stableLevyDeficitOfGamma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:02:35.566685+00:00
-- url     : https://prove2.me/submissions/cd8843f1-a280-4859-9b11-e8b6a93fa47e

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (alpha t : Real) (ha0 : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < t)
    (hg : 0 < -Real.Gamma (-alpha))
    (hk : IntegrableOn (fun x : Real =>
      (Real.exp (-(t*x)) - 1) * x ^ (-alpha-1)) (Set.Ioi 0) ∧
      (∫ x in Set.Ioi (0 : Real),
        (Real.exp (-(t*x)) - 1) * x ^ (-alpha-1) ∂volume) =
        Real.Gamma (-alpha) * t ^ alpha) :
    let nu := ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
      (fun z : Real => ENNReal.ofReal (z ^ (-1-alpha) / (-Real.Gamma (-alpha))))
    IntegrableOn (fun x : Real => 1 - Real.exp (-t*x)) (Set.Ioi 0) nu ∧
    (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-t*x)) ∂nu) = t ^ alpha := by
  dsimp only
  let f (x : Real) := ENNReal.ofReal (x ^ (-1-alpha) / (-Real.Gamma (-alpha)))
  let g (x : Real) := 1 - Real.exp (-t*x)
  let m := volume.restrict (Set.Ioi (0 : Real))
  have hf : Measurable f := by fun_prop
  have hft : ∀ᵐ x ∂m, f x < ⊤ := Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hr : m.restrict (Set.Ioi (0 : Real)) = m := by
    simp [m, Measure.restrict_restrict measurableSet_Ioi]
  have he : (fun x => (f x).toReal • g x) =ᵐ[m]
      (fun x => -((Real.exp (-(t*x)) - 1) * x ^ (-alpha-1)) / (-Real.Gamma (-alpha))) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    dsimp [f, g]
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hx.le _) hg.le)]
    rw [show -1-alpha = -alpha-1 by ring]
    ring
  change Integrable g ((m.withDensity f).restrict (Set.Ioi 0)) ∧
    (∫ x, g x ∂((m.withDensity f).restrict (Set.Ioi 0))) = t ^ alpha
  rw [restrict_withDensity measurableSet_Ioi, hr]
  refine ⟨(integrable_withDensity_iff_integrable_smul' hf hft).2 ?_, ?_⟩
  · exact (hk.1.neg.div_const _).congr he.symm
  · rw [integral_withDensity_eq_integral_toReal_smul hf hft, integral_congr_ae he,
      integral_div, integral_neg, hk.2]
    have hg0 : Real.Gamma (-alpha) ≠ 0 := by linarith
    field_simp [hg0]
