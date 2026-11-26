-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:33:35.356786+00:00
-- url     : https://prove2.me/submissions/ed196638-0d64-4fcb-afe7-0b5ad4316101

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
import Theorems.Thm_Kyprianou_Ch04_ito43_jump_kernel_finite_abs_sum_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_restricted_dirac_abs_integral_bound
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Any jump kernel dominated by squared jump energy on a compact horizon is integrable,
and its integral is bounded by that energy. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hJ : ({s : NNReal | 0 < s ∧ X s w ≠ L s w}).Countable)
    (T t : NNReal) (ht : t ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hE : Summable (fun s : Ioc (0 : NNReal) T => (X s w-L s w)^2))
    (F : ℝ × ℝ → ℝ)
    (hb : ∀ s : NNReal, 0 < s → s ≤ t →
      |F ((s : ℝ), X s w-L s w)| ≤ C*(X s w-L s w)^2) :
    let B : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ univ
    IntegrableOn F B (pathJumpMeasure X L w) ∧
      |∫ z in B, F z ∂(pathJumpMeasure X L w)| ≤
        C * ∑' s : Ioc (0 : NNReal) T, (X s w-L s w)^2 := by
  classical
  intro B
  let J : Set NNReal := {s | 0 < s ∧ X s w ≠ L s w}
  let : Countable J := hJ.to_subtype
  let φ : J → ℝ × ℝ := fun s => (((s : NNReal) : ℝ), X s w-L s w)
  let G : J → ℝ := fun s => B.indicator F (φ s)
  let E : Ioc (0 : NNReal) T → ℝ := fun s => (X s w-L s w)^2
  have hfin := Kyprianou.Ch04.ito43_jump_kernel_finite_abs_sum_bound X L w hJ T t ht C hC hE F hb
  rw [bvPathJumpMeasureAtomicV1 X L w hJ]
  exact Kyprianou.Ch04.ito43_restricted_dirac_abs_integral_bound φ B
    (measurableSet_Icc.prod MeasurableSet.univ) F _ hfin
