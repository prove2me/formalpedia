-- Prove2me | solution 1 for HunterPDE.Compactness.IsSmoothCompactClosedHalfSpace.memW
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T16:38:53.95124+00:00
-- url     : https://prove2.me/submissions/1ff11600-ead6-4b2d-a6e2-b434ce66b823

import Theorems.Thm_HunterPDE_Shared_hasWeakDeriv_multiDeriv_of_contDiffOn
import Theorems.Thm_HunterPDE_Shared_multiDeriv_bound_of_contDiffOn_closed
import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Seminorm

open MeasureTheory HunterPDE.Compactness HunterPDE.Shared
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem solution {m k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) : MemW k p (upperHalfSpace m) f := by
  have hΩ : IsOpen (upperHalfSpace m) :=
    isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hS : IsClosed (closedUpperHalfSpace m) :=
    isClosed_le continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hsub : upperHalfSpace m ⊆ closedUpperHalfSpace m := fun x hx =>
    (show 0 ≤ x (Fin.last m) from le_of_lt hx)
  have hconv : Convex ℝ (closedUpperHalfSpace m) := by
    intro x hx y hy a b ha hb _
    change 0 ≤ (a • x + b • y) (Fin.last m)
    change 0 ≤ a * x (Fin.last m) + b * y (Fin.last m)
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hne : (interior (closedUpperHalfSpace m)).Nonempty := by
    refine ⟨EuclideanSpace.single (Fin.last m) 1, ?_⟩
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hΩ.mem_nhds ?_) hsub
    simp [upperHalfSpace]
  have hSd := uniqueDiffOn_convex hconv hne
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (upperHalfSpace m) := hf.1.mono hsub
  obtain ⟨K, hK, hz⟩ := hf.2
  intro α _
  refine ⟨multiDeriv f α, hasWeakDeriv_multiDeriv_of_contDiffOn hΩ f hc α, ?_⟩
  obtain ⟨C, _, hC⟩ := multiDeriv_bound_of_contDiffOn_closed hS hSd hΩ hsub hK f
    hf.1 (fun x hx hxK => hz x (hsub hx) hxK) α
  have hind : MemLp (K.indicator (fun _ => C)) p volume :=
    memLp_indicator_const p hK.measurableSet C (Or.inr hK.measure_lt_top.ne)
  have hmeas : AEStronglyMeasurable (multiDeriv f α) (volume.restrict (upperHalfSpace m)) :=
    (contDiffOn_iteratedPartial hΩ hc (multiIndexList α)).continuousOn.aestronglyMeasurable
      hΩ.measurableSet
  exact (hind.mono_measure Measure.restrict_le_self).mono' hmeas
    (ae_restrict_of_forall_mem hΩ.measurableSet hC)
