-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ae_jump_summable_at_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:26:11.00481+00:00
-- url     : https://prove2.me/submissions/7fc9cc1c-8260-4769-acbd-6a53080ba80d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch04
/-- Restrict the square-summable jumps on the larger positive interval to the requested horizon by an injective inclusion. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (t : NNReal) :
    ∀ᵐ w ∂P, Summable (fun s : Ioc (0:NNReal) t => (X s w-L s w)^2) := by
  by_cases ht : 0 < t
  · exact (ito43_levy_jump_energy_localisation P X L hX tr hc hL t ht).1
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) zero_le
    subst t
    haveI : IsEmpty (Ioc (0:NNReal) 0) :=
      ⟨fun s => (not_lt_of_ge s.2.2) s.2.1⟩
    exact Eventually.of_forall (fun w => Summable.of_finite)
