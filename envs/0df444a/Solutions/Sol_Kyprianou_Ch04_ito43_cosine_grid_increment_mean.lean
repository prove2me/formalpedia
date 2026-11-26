-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_grid_increment_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:58:20.005438+00:00
-- url     : https://prove2.me/submissions/d5fd52b1-d9c8-4338-9963-4a2ed6350a5f

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution   {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega))) :
    ∀ T : NNReal,
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let μ : ℕ → ℕ → ℝ := fun m n =>
      ∫ w, q m (X (T/(n:NNReal)) w) ∂P
    ∀ (m n k : ℕ), (∫ w, q m
      (X (T*((k+1:ℕ):NNReal)/(n:NNReal)) w-X (T*(k:NNReal)/(n:NNReal)) w) ∂P) = μ m n := by
  intro T q μ m n k
  let s : NNReal := T*(k:NNReal)/(n:NNReal)
  let h : NNReal := T/(n:NNReal)
  have he : s+h = T*((k+1:ℕ):NNReal)/(n:NNReal) := by
    dsimp [s,h]
    push_cast
    ring
  let U : Omega → ℝ := fun w => X (s+h) w-X s w
  have hLaw : P.map U = P.map (X h) := by
    have H := (hLevy.stationary_increments s h).map_eq
    change P.map (fun w => X (s+h) w-X s w) = P.map (fun w => X h w-X 0 w) at H
    simpa only [U,hLevy.start_zero,sub_zero] using H
  have hx := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hLevy
  have hU : AEMeasurable U P := (hx _).sub (hx _)
  have hq : Continuous (q m) := by dsimp [q]; fun_prop
  change (∫ w, q m (X (T*((k+1:ℕ):NNReal)/(n:NNReal)) w-X s w) ∂P) = _
  rw [← he]
  change (∫ w, q m (U w) ∂P) = ∫ w, q m (X h w) ∂P
  rw [← integral_map hU hq.measurable.aestronglyMeasurable,hLaw,
    integral_map (hx h) hq.measurable.aestronglyMeasurable]
