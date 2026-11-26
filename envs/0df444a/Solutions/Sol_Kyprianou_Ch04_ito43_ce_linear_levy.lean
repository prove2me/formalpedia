-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ce_linear_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:17:51.311804+00:00
-- url     : https://prove2.me/submissions/ca255293-3206-4e61-92e8-a1c6a3a6018a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_ito43_ce_linear_indep
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Deterministic unit drift has the unit-drift, zero-variance, zero-jump triplet. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    let X : NNReal → Ω → ℝ := fun t _ => (t : ℝ)
    ∃ tr : LevyKhintchineTriple, IsLevyProcess X P ∧ tr.gaussianVariance = 0 ∧
      ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ) := by
  classical
  intro X
  let tr : LevyKhintchineTriple := ⟨1,0,0,by simp [IsLevyMeasure]⟩
  refine ⟨tr, ⟨by funext w; rfl, ?_, ?_, ?_⟩, rfl, ?_⟩
  · exact Kyprianou.Ch04.ito43_ce_linear_indep P
  · intro s h
    have H : increment X s (s+h) = increment X 0 h := by
      funext w
      simp [increment,X,NNReal.coe_add]
    rw [H]
    apply IdentDistrib.refl
    change AEMeasurable (fun _ : Ω => (h : ℝ) - ((0 : NNReal) : ℝ)) P
    exact measurable_const.aemeasurable
  · filter_upwards [] with w
    intro t
    exact ⟨NNReal.continuous_coe.continuousWithinAt,
      ⟨(t : ℝ),NNReal.continuous_coe.continuousWithinAt⟩⟩
  · intro t ξ
    change charFun (P.map (fun _ : Ω => (t : ℝ))) ξ = _
    rw [Measure.map_const,measure_univ,one_smul,charFun_dirac]
    simp [Kyprianou.Ch01.levyTripleExponent,tr]
    congr 1
    ring
