-- Prove2me | solution 1 for Kyprianou.Ch04.clockRunningInfimumWienerHopfTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:46:46.185022+00:00
-- url     : https://prove2.me/submissions/443c767c-1a81-44b1-b137-efce7b50d1ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_clockSignedInfimumLaw
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Transfer the proved drawdown transform through the signed infimum law. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (q r beta : ℝ) (hq : 0 < q) (hr : 0 < r)
    (hroot : L.ψ r = q) (hb : 0 < beta) (hne : beta ≠ r) :
    (∫ z : Ω × ℝ, Real.exp (beta * sInf ((fun s : NNReal => L.X s z.1) '' Iic z.2.toNNReal))
      ∂(P.prod (expMeasure q))) = (q/r) * ((r-beta)/(q-L.ψ beta)) := by
  let : IsProbabilityMeasure P := L.isProbability
  have h := Kyprianou.Ch04.clockSignedInfimumLaw P F L q hq
  have he : Measurable (fun x : ℝ => Real.exp (beta*x)) := by fun_prop
  have hE := (h.comp he).integral_eq
  obtain ⟨_,_,_,hWH⟩ := avram_ws01e_bt_new_original_clock_descending_mgf_all_beta L q hq r hr hroot
  have hw := hWH beta hb
  rw [if_neg hne] at hw
  unfold mgf at hw
  exact hE.symm.trans hw
