-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42NegativeAtomicJumpBridgeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:51:43.645749+00:00
-- url     : https://prove2.me/submissions/aadc9afd-1d65-4c92-8946-4b1164432e80

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvPositiveJumpSupportCountableV1
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
import Theorems.Thm_Kyprianou_Ch04_bvHorizonJumpSeriesReindexV1
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega)
    (hNeg : ∀ t : NNReal, 0 < t → X t omega ≤ Xleft t omega)
    (hSum : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|))
    (U : NNReal → Real) (f : Real × Real → Real) (t : NNReal) :
    (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) (Set.Iio (0 : Real)),
      (f (U z.1.toNNReal, Xleft z.1.toNNReal omega + z.2) -
        f (U z.1.toNNReal, Xleft z.1.toNNReal omega))
        ∂(pathJumpMeasure X Xleft omega)) =
      ∑' s : Set.Ioc (0 : NNReal) t,
        (f (U s, X s omega) - f (U s, Xleft s omega)) := by
  classical
  have hJ := bvPositiveJumpSupportCountableV1 X Xleft omega hSum
  let J : Set NNReal := {s | 0 < s ∧ X s omega ≠ Xleft s omega}
  letI : Countable J := hJ.to_subtype
  let φ : J → ℝ × ℝ := fun s => ((s : NNReal), X s omega - Xleft s omega)
  let g : ℝ × ℝ → ℝ := fun z => f (U z.1.toNNReal, Xleft z.1.toNNReal omega + z.2) -
    f (U z.1.toNNReal, Xleft z.1.toNNReal omega)
  let B : Set (ℝ × ℝ) := Icc 0 (t : ℝ) ×ˢ Iio 0
  let A : Set (ℝ × ℝ) := Set.prod (Icc 0 (t : ℝ)) (Set.univ : Set ℝ)
  rw [bvPathJumpMeasureAtomicV1 X Xleft omega hJ]
  change (∫ z in B, g z ∂(Measure.sum fun s : J => Measure.dirac (φ s))) = _
  rw [bvRestrictedDiracIntegralV1 φ B (measurableSet_Icc.prod measurableSet_Iio) g]
  calc
    _ = ∑' s : J, A.indicator g (φ s) := by
      apply tsum_congr
      intro s
      have hmark : (φ s).2 < 0 :=
        sub_neg.mpr (lt_of_le_of_ne (hNeg s s.property.1) s.property.2)
      have hmem : φ s ∈ A ↔ φ s ∈ B := by
        change ((φ s).1 ∈ Icc 0 (t : ℝ) ∧ (φ s).2 ∈ (Set.univ : Set ℝ)) ↔
          ((φ s).1 ∈ Icc 0 (t : ℝ) ∧ (φ s).2 ∈ Iio 0)
        simp [hmark]
      simp only [Set.indicator_apply, hmem]
    _ = _ := by
      simpa [A, J, φ, g] using
        bvHorizonJumpSeriesReindexV1 X Xleft omega
          (fun z : ℝ × ℝ => f (U z.1.toNNReal, z.2)) t
