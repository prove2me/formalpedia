-- Prove2me | solution 1 for Kyprianou.Ch01.passageLaplaceMeasurableFromTimePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:30:40.091188+00:00
-- url     : https://prove2.me/submissions/2d4e6a29-8310-4306-9122-7a4a8e9813a5

import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The option-style payoff definition agrees with the Borel two-branch expression. -/
private theorem passageLaplace_match_eq_ite
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (q : ℝ) :
    passageLaplace τ q =
      (fun ω => if τ ω = ⊤ then (0 : ℝ)
        else Real.exp (-q * (((τ ω).untopD (0 : ℝ≥0) : ℝ≥0) : ℝ))) := by
    funext ω
    unfold passageLaplace
    cases hz : τ ω with
    | top => simp [hz] <;> rfl
    | coe t => simp [hz, WithTop.untopD] <;> rfl

/-- The discounted passage payoff is measurable when its extended time is measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : Ω → WithTop ℝ≥0) (q : ℝ)
    (hτ : Measurable τ) :
    Measurable (passageLaplace τ q) := by
  have hUntop : Measurable
      (fun z : WithTop ℝ≥0 => ((z.untopD (0 : ℝ≥0) : ℝ≥0) : ℝ)) :=
    (WithTop.measurable_untopD (0 : ℝ≥0)).coe_nnreal_real
  have hExp : Measurable (fun z : WithTop ℝ≥0 =>
      Real.exp (-q * ((z.untopD (0 : ℝ≥0) : ℝ≥0) : ℝ))) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul hUntop)
  have hRaw : Measurable (fun z : WithTop ℝ≥0 =>
      if z = ⊤ then (0 : ℝ) else Real.exp (-q * ((z.untopD (0 : ℝ≥0) : ℝ≥0) : ℝ))) :=
    Measurable.ite (measurableSet_singleton (⊤ : WithTop ℝ≥0))
      measurable_const hExp
  rw [passageLaplace_match_eq_ite τ q]
  exact hRaw.comp hτ
