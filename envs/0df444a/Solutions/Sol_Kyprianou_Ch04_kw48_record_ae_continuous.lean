-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_record_ae_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:35:39.536551+00:00
-- url     : https://prove2.me/submissions/859c0b2f-cb3a-4a69-889d-ec5932670bd6

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealDiscontinuitiesCountableV1
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_real_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The reflected characteristic path is continuous almost everywhere for
the atomless running-record measure on every positive-time interval. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
    (a b : NNReal) :
    ∀ᵐ s ∂((dividendMeasure (runningSup L) w).restrict
      (Ioc (a:Real) (b:Real))),
      ContinuousAt (fun r : Real => Z L alpha beta r.toNNReal w) s := by
  let mu := dividendMeasure (runningSup L) w
  let D : Set NNReal := {t | ¬ ContinuousAt (fun r => L.X r w) t}
  let C : Set Real := (fun t : NNReal => (t:Real)) '' D
  have hD : D.Countable :=
    Kyprianou.Ch02.cadlagNNRealDiscontinuitiesCountableV1
      (fun t => L.X t w) (L.rightCont w) (L.leftLim w)
  letI : NullSingletonClass mu := ⟨runningSup_dividendMeasure_no_real_atoms L w⟩
  have hC : mu C = 0 := (hD.image _).measure_zero _
  have hAe : ∀ᵐ s ∂mu, s ∉ C := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hC
  filter_upwards [ae_restrict_le (s := Ioc (a:Real) (b:Real)) hAe,
    ae_restrict_mem measurableSet_Ioc] with s hs hIn
  have hspos : 0 ≤ s := (NNReal.coe_nonneg a).trans hIn.1.le
  have hx : ContinuousAt (fun t => L.X t w) s.toNNReal := by
    by_contra h
    exact hs ⟨s.toNNReal, h, Real.coe_toNNReal _ hspos⟩
  have hu := (runningSup_continuous_actual L w).continuousAt
    (x := s.toNNReal)
  have hz : ContinuousAt (fun t => Z L alpha beta t w) s.toNNReal := by
    unfold Z
    fun_prop (disch := assumption)
  exact hz.comp continuous_real_toNNReal.continuousAt
