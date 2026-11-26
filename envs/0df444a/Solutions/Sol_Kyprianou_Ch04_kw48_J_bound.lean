-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_J_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:47:29.020354+00:00
-- url     : https://prove2.me/submissions/df85eb03-e37e-43d3-a9e2-c5abe6113143

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The complex time primitive is bounded in norm by elapsed time. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖J L alpha beta t w‖ ≤ (t:Real) := by
  let mu := volume.restrict (Icc (0:Real) (t:Real))
  letI : IsFiniteMeasure mu :=
    ⟨by dsimp only [mu]; rw [Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have h := norm_integral_le_of_norm_le_const (μ := mu)
    (C := (1:Real)) (f := fun s : Real => Z L alpha beta s.toNNReal w)
    (Eventually.of_forall fun s => le_of_eq
      (Kyprianou.Ch04.kw48_norm_Z L alpha beta s.toNNReal w))
  have hm : mu.real univ = (t:Real) := by
    simp only [mu,Measure.real_def,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal,NNReal.coe_nonneg]
  simpa only [J,mu,hm,one_mul,mul_one] using h
