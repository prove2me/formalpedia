-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzAffineFderivIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:00:55.942574+00:00
-- url     : https://prove2.me/submissions/94915a1b-4a62-4f37-8f83-26745eefec3e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvFullFderivEqWithinPositiveV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Each first- or second-coordinate fderiv component is interval integrable
along a Lipschitz-affine path, even when the left endpoint lies on x=0. -/
theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hNonneg : ∀ s ∈ Icc l r, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s)
    (v : ℝ × ℝ) :
    IntervalIntegrable
      (fun s : ℝ => fderiv ℝ f (U s, a + c * s) v) volume l r := by
  let H : Set (ℝ × ℝ) := (Ici (0 : ℝ)).prod univ
  let D : ℝ × ℝ → ℝ := fun z => fderivWithin ℝ f H z v
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn D H :=
    (hf.continuousOn_fderivWithin hUnique le_rfl).clm_apply continuousOn_const
  have hPath : ContinuousOn (fun s : ℝ => (U s, a + c * s)) (Icc l r) :=
    (hU.continuous.prodMk (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  have hMap : MapsTo (fun s : ℝ => (U s, a + c * s)) (Icc l r) H :=
    fun s hs => ⟨hNonneg s hs, mem_univ _⟩
  have hC : ContinuousOn (fun s : ℝ => D (U s, a + c * s)) (Icc l r) :=
    hD.comp hPath hMap
  have hi : IntervalIntegrable (fun s : ℝ => D (U s, a + c * s))
      volume l r := hC.intervalIntegrable_of_Icc hlr
  apply hi.congr_ae
  rw [uIoc_of_le hlr]
  change ∀ᵐ s ∂volume.restrict (Ioc l r),
    fderivWithin ℝ f H (U s, a + c * s) v =
      fderiv ℝ f (U s, a + c * s) v
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [] with s
  intro hs
  have hh := Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1
    f hf (U s) (a + c * s) (hPositive s hs)
  simpa only [H] using congrArg (fun L => L v) hh
