-- Prove2me | solution 1 for Kyprianou.Ch03.expMoment_forward
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:56:32.222984+00:00
-- url     : https://prove2.me/submissions/31529f2d-ea84-4486-b7fc-7c97dc273830
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_submulMoment_reverse
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
    ((forall (t : NNReal),
      Integrable (fun omega => Real.exp (beta * X t omega)) P)) -> (IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure) := by
  intro hAll
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
  have hPositive : ∀ t : NNReal, 0 < t →
      Integrable (fun omega => Real.exp (beta * X t omega)) P :=
    fun t _ => hAll t
  exact Kyprianou.Ch03.submulMoment_reverse
    P X hX T hLK (fun x : ℝ => Real.exp (beta * x))
    hSub hMeas hBound hPositive

