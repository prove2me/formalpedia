-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_8_ii_goalV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:09:30.643098+00:00
-- url     : https://prove2.me/submissions/145400ed-3f7a-452b-8c17-c749da65cf01

import Mathlib.Probability.IdentDistrib
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_spectrallyNegativePsi_zero
import Theorems.Thm_Kyprianou_Ch04_independentExpClockEndpointSupJointLaw
import Theorems.Thm_Kyprianou_Ch04_expProductClockWienerHopfChar
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution : certificate_ex4_8_ii_v2 := by
  intro Ω _ P F L hBV hNot Psi hPsi q hq e he hlaw hi
  letI : IsProbabilityMeasure P := L.isProbability
  obtain ⟨phi, hphi, hr, hmax⟩ :=
    Kyprianou.Ch03.firstPassageTransform_maximalRootExistence P F L hNot q hq.le
  have hp := lt_of_le_of_ne hphi (by
    rintro rfl
    exact hq.ne' (hr.symm.trans (Kyprianou.Ch03.spectrallyNegativePsi_zero P F L)))
  refine ⟨phi, hp, hr, hmax, ?_⟩
  intro a b
  obtain ⟨hd, hs, hj⟩ := independentExpClockEndpointSupJointLaw P F L q hq e he hlaw hi
  have hm := levy_exponential_real_clock_extrema_drawdown_measurable L
  let g : ℝ × ℝ → ℂ := fun z =>
    Complex.exp (Complex.I * (a : ℂ) * (z.1 : ℂ) +
      Complex.I * (b : ℂ) * (z.2 : ℂ))
  have hg : Measurable g := by fun_prop
  have hi' : IdentDistrib _ _ P (P.prod (expMeasure q)) :=
    ⟨(hd.prodMk hs).aemeasurable,
      by simpa only [Pi.neg_apply, neg_sub] using (hm.snd.neg.prodMk hm.fst.fst).aemeasurable, hj⟩
  exact (hi'.comp hg).integral_eq.trans
    (expProductClockWienerHopfChar P F L Psi hPsi q hq phi hp hr a b)
