-- Prove2me | solution 2 for Kyprianou.Ch02.nonnegLaplaceFactorIndepFunAEV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:41:33.909448+00:00
-- url     : https://prove2.me/submissions/96faeeb6-c17e-4172-bec8-c7d9bd65a660
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceFactorIndepFunV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
AE Laplace factorisation ⇒ IndepFun: replace A,B by nonnegative measurable
modifications `max (mk ·) 0`, transfer the product identity by AE congruence,
invoke the measurable criterion, then `IndepFun.congr` back.
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hmA : AEMeasurable A P) (hmB : AEMeasurable B P)
    (hnA : ∀ᵐ ω ∂P, 0 ≤ A ω) (hnB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (h : ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u * A ω + v * B ω)) ∂P) =
      (∫ ω, Real.exp (-(u * A ω)) ∂P) * (∫ ω, Real.exp (-(v * B ω)) ∂P)) :
    IndepFun A B P := by
  let a := fun ω => max (hmA.mk A ω) 0
  let b := fun ω => max (hmB.mk B ω) 0
  have ha : Measurable a := hmA.measurable_mk.max measurable_const
  have hb : Measurable b := hmB.measurable_mk.max measurable_const
  have ea : A =ᵐ[P] a := by
    filter_upwards [hmA.ae_eq_mk, hnA] with ω he hn
    dsimp [a]
    rw [← he, max_eq_left hn]
  have eb : B =ᵐ[P] b := by
    filter_upwards [hmB.ae_eq_mk, hnB] with ω he hn
    dsimp [b]
    rw [← he, max_eq_left hn]
  have hfac (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      (∫ ω, Real.exp (-(u * a ω + v * b ω)) ∂P) =
      (∫ ω, Real.exp (-(u * a ω)) ∂P) * (∫ ω, Real.exp (-(v * b ω)) ∂P) := by
    have e1 : (∫ ω, Real.exp (-(u * A ω + v * B ω)) ∂P) =
        ∫ ω, Real.exp (-(u * a ω + v * b ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards [ea, eb] with ω h1 h2
      rw [h1, h2]
    have e2 : (∫ ω, Real.exp (-(u * A ω)) ∂P) =
        ∫ ω, Real.exp (-(u * a ω)) ∂P :=
      integral_congr_ae (ea.fun_comp fun x => Real.exp (-(u * x)))
    have e3 : (∫ ω, Real.exp (-(v * B ω)) ∂P) =
        ∫ ω, Real.exp (-(v * b ω)) ∂P :=
      integral_congr_ae (eb.fun_comp fun x => Real.exp (-(v * x)))
    rw [← e1, ← e2, ← e3]
    exact h u v hu hv
  exact (Kyprianou.Ch02.nonnegLaplaceFactorIndepFunV1 P a b ha hb
    (fun _ => le_max_right _ _) (fun _ => le_max_right _ _) hfac).congr ea.symm eb.symm
