-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_levy_negative_grid_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:37:27.963773+00:00
-- url     : https://prove2.me/submissions/4c8577d8-0f88-4f3c-9944-14b457a0cdf1

import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
/-- Independent increment reduction. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess X P →
      ∀ (t : ℝ≥0) (c : ℝ) (n : ℕ),
      (∫ ω, ∏ i : Fin n, (if X (((i.val+1 : ℕ):ℝ≥0)*t) ω -
          X ((i.val:ℝ≥0)*t) ω < c then (1:ℝ) else 0) ∂P) =
        (∫ ω, if X t ω < c then (1:ℝ) else 0 ∂P)^n := by
  intro Ω mΩ P hP X hX t c n
  let T : Fin (n+1) → ℝ≥0 := fun i => (i.val:ℝ≥0)*t
  have hT : Monotone T := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  let D (i : Fin n) : Ω → ℝ := increment X (T i.castSucc) (T i.succ)
  have hind : iIndepFun D P := hX.indep_increments n T hT
  have hc := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hD (i : Fin n) : AEMeasurable (D i) P :=
    (hc (T i.succ)).sub (hc (T i.castSucc))
  let f : ℝ → ℝ := fun z => if z<c then 1 else 0
  have hf : Measurable f := Measurable.ite
    (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  have hprod := hind.integral_prod_comp hD (fun i =>
    (hf.aemeasurable : AEMeasurable f (P.map (D i))).aestronglyMeasurable)
  have hstat (i : Fin n) : IdentDistrib (D i) (X t) P P := by
    have hh : T i.succ = T i.castSucc + t := by simp [T,Nat.cast_add,add_mul]
    have he : increment X 0 t = X t := by funext ω; simp [increment,hX.start_zero]
    change IdentDistrib (increment X (T i.castSucc) (T i.succ)) (X t) P P
    rw [hh,← he]
    exact hX.stationary_increments _ _
  have hfactor (i : Fin n) : (∫ ω, f (D i ω) ∂P) = ∫ ω, f (X t ω) ∂P :=
    ((hstat i).comp hf).integral_eq
  change (∫ ω, ∏ i : Fin n, f (D i ω) ∂P) = (∫ ω, f (X t ω) ∂P)^n
  rw [show (∫ ω, ∏ i : Fin n, f (D i ω) ∂P) =
      ∏ i : Fin n, ∫ ω, f (D i ω) ∂P by simpa [Function.comp_def] using hprod]
  simp [hfactor]
