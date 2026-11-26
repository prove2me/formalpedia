-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PrefixFutureMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:01.005611+00:00
-- url     : https://prove2.me/submissions/f6ea858a-c9ca-49f8-9727-8884681880ea

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixEventRawMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_rawNaturalDeterministicRestrictedPathV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Product mass follows by evaluating the restricted path-law identity. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (s : NNReal) (b : ℝ) (B : Set (NNReal → ℝ)) (hB : MeasurableSet B) :
    let A : Set Ω := {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω}
    P (A ∩ {ω | (fun u => X (s + u) ω - X s ω) ∈ B}) =
      P A * P {ω | (fun u => X u ω) ∈ B} := by
  let A : Set Ω := {ω | (∀ u : NNReal, u ≤ s → 0 ≤ X u ω) ∧ b ≤ X s ω}
  let U : Ω → (NNReal → ℝ) := fun ω u => X (s + u) ω - X s ω
  let V : Ω → (NNReal → ℝ) := fun ω u => X u ω
  have hU : Measurable U := measurable_pi_iff.mpr fun u => (hm _).sub (hm _)
  have hV : Measurable V := measurable_pi_iff.mpr hm
  have hA : MeasurableSet[PerfCorrMSQ.natFiltr X s] A :=
    Kyprianou.Ch04.exercise49PrefixEventRawMeasurableV1 X hc s b
  have hLaw : Measure.map U (P.restrict A) = P A • Measure.map V P :=
    Kyprianou.Ch03.rawNaturalDeterministicRestrictedPathV1 P X hX hm s A hA
  have hMass := congrArg (fun μ : Measure (NNReal → ℝ) => μ B) hLaw
  rw [Measure.map_apply hU hB, Measure.restrict_apply (hU hB),
    Measure.smul_apply, Measure.map_apply hV hB] at hMass
  change P (U ⁻¹' B ∩ A) = P A * P (V ⁻¹' B) at hMass
  rw [Set.inter_comm] at hMass
  exact hMass
