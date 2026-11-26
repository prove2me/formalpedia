-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_record_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:34:20.054466+00:00
-- url     : https://prove2.me/submissions/1723a4f2-441a-4167-889b-2a3daa816b56

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_record_measure_grid_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_record_phase_change
import Theorems.Thm_Kyprianou_Ch04_kw48_record_contact_identity
import Theorems.Thm_Kyprianou_Ch04_kw48_record_ae_continuous
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_right_path
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Both endpoint record quadratures converge to the difference
of the same record-level primitive. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
    (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n)
    (right : Bool) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
        Z L alpha beta (if right then u n (i+1) else u n i) w) atTop
      (nhds (S L beta b w-S L beta a w)) := by
  let f : Real → Complex := fun r => Z L alpha beta r.toNNReal w
  have hf : Measurable f := (Kyprianou.Ch04.kw48_Z_right_path L alpha beta w).1
  have hB (s : Real) : ‖f s‖ ≤ 1 := by
    exact le_of_eq (Kyprianou.Ch04.kw48_norm_Z L alpha beta s.toNNReal w)
  have hCont : ∀ᵐ x ∂((dividendMeasure (runningSup L) w).restrict
      (Ioc (a:Real) (b:Real))),
      ContinuousWithinAt f (if right then Ici x else Iic x) x := by
    filter_upwards [Kyprianou.Ch04.kw48_record_ae_continuous L alpha beta w a b]
      with x hx
    exact hx.continuousWithinAt
  have h := Kyprianou.Ch04.kw48_record_measure_grid_limit L w a b f 1 hf hB
    u N hu h0 hN delta hDelta hMesh right hCont
  have hContact := Kyprianou.Ch04.kw48_record_contact_identity L alpha beta w a b
  have hChange := Kyprianou.Ch04.kw48_record_phase_change L beta w a b hab
  dsimp only [f] at h
  rw [hContact,hChange] at h
  cases right <;> simpa only [if_true,if_false,Bool.false_eq_true,Real.toNNReal_coe] using h
