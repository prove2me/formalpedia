-- Prove2me | solution 1 for Kyprianou.Ch03.expMoment_reverse_positiveTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:56:19.411201+00:00
-- url     : https://prove2.me/submissions/aa5b0664-8b55-414c-ba50-2a243936b4b1

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_submulMoment_forward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real) :
    (IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure) -> ((forall (t : NNReal), 0 < t ->
      Integrable (fun omega => Real.exp (beta * X t omega)) P)) := by
  intro htail
  have hSub : Kyprianou.Ch03.IsSubmultiplicative
      (fun x : ℝ => Real.exp (beta * x)) := by
    constructor
    · intro x
      exact (Real.exp_pos _).le
    · refine ⟨1, by norm_num, ?_⟩
      intro x y
      simp [mul_add, Real.exp_add]
  have hMeas : Measurable (fun x : ℝ => Real.exp (beta * x)) := by
    fun_prop
  have hBound :
      ∀ R : ℝ, 0 ≤ R →
        ∃ M : ℝ, ∀ x : ℝ,
          |x| ≤ R → Real.exp (beta * x) ≤ M := by
    intro R hR
    refine ⟨Real.exp (|beta| * R), ?_⟩
    intro x hx
    apply Real.exp_le_exp.mpr
    calc
      beta * x ≤ |beta * x| := le_abs_self _
      _ = |beta| * |x| := abs_mul _ _
      _ ≤ |beta| * R :=
        mul_le_mul_of_nonneg_left hx (abs_nonneg beta)
  exact Kyprianou.Ch03.submulMoment_forward
    P X hX T hLK (fun x : ℝ => Real.exp (beta * x))
    hSub hMeas hBound htail

