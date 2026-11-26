-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_record_phase_change
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:53:13.563806+00:00
-- url     : https://prove2.me/submissions/673be501-d258-4eaa-876b-4f9ee268f3d4

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_record_measure_grid_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_record_phase_level_grid
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Change variables in the continuous monotone record integral by
comparing the time and record-level quadratures of the same phase. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω)
    (a b : NNReal) (hab : a ≤ b) :
    (∫ s in Ioc (a:Real) (b:Real),
      Complex.exp (Complex.I*(beta:Complex)*(runningSup L s.toNNReal w:Complex))
      ∂(dividendMeasure (runningSup L) w)) =
      S L beta b w - S L beta a w := by
  let f : Real → Complex := fun s =>
    Complex.exp (Complex.I*(beta:Complex)*(runningSup L s.toNNReal w:Complex))
  have hU := (runningSup_continuous_actual L w).comp continuous_real_toNNReal
  have hf : Continuous f := by unfold f; fun_prop (disch := exact hU)
  have hB (s : Real) : ‖f s‖ ≤ 1 := by
    simp [f,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  let u : Nat → Nat → NNReal := fun n i =>
    a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
  obtain ⟨hu,h0,hN,hT,hMesh,hDelta⟩ :=
    Kyprianou.Ch04.kw47_capped_uniform_grid a b hab
  let d : Nat → Real := fun n => ((b:Real)-(a:Real))/((n+1:Nat):Real)
  have ht := Kyprianou.Ch04.kw48_record_measure_grid_limit L w a b f 1
    hf.measurable hB u (fun n => n+1) hu h0 hN d hDelta
    (fun n i hi => le_of_eq (hMesh n i hi)) true
    (Eventually.of_forall fun x => hf.continuousAt.continuousWithinAt)
  have hl := Kyprianou.Ch04.kw48_record_phase_level_grid L beta w a b hab
    u (fun n => n+1) hu h0 hN d hDelta
    (fun n i hi => le_of_eq (hMesh n i hi)) true
  simp only [f, if_true, Real.toNNReal_coe] at ht hl
  exact tendsto_nhds_unique ht hl
