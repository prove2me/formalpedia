-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_record_contact_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:48:41.567006+00:00
-- url     : https://prove2.me/submissions/6d577c5f-ff94-4503-8257-103931af8876

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_contact_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Under the running-record measure the reflected characteristic
integrand equals the characteristic function of the record level. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
    (a b : NNReal) :
    (∫ s in Ioc (a:Real) (b:Real), Z L alpha beta s.toNNReal w
      ∂(dividendMeasure (runningSup L) w)) =
    ∫ s in Ioc (a:Real) (b:Real),
      Complex.exp (Complex.I * (beta:Complex) *
        (runningSup L s.toNNReal w:Complex))
      ∂(dividendMeasure (runningSup L) w) := by
  let mu := dividendMeasure (runningSup L) w
  let C : Set Real := {s | 0 ≤ s ∧
    L.X s.toNNReal w < runningSup L s.toNNReal w}
  have hNull : mu C = 0 :=
    Kyprianou.Ch04.kw47_runningSup_contact_measure L w
  have hAe : ∀ᵐ s ∂mu, s ∉ C := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hNull
  apply integral_congr_ae
  change ∀ᵐ s ∂(mu.restrict (Ioc (a:Real) (b:Real))),
    Z L alpha beta s.toNNReal w =
      Complex.exp (Complex.I * (beta:Complex) *
        (runningSup L s.toNNReal w:Complex))
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hAe] with s hs
  intro hIn
  have hLe := (runningSup_monotone_and_path_le L w).2 s.toNNReal
  have hNot : ¬ L.X s.toNNReal w < runningSup L s.toNNReal w := by
    intro hLt
    exact hs ⟨(NNReal.coe_nonneg a).trans hIn.1.le,hLt⟩
  have heq := le_antisymm (le_of_not_gt hNot) hLe
  simp [Z,heq]
