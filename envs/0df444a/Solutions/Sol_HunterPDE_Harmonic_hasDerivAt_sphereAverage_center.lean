-- Prove2me | solution 1 for HunterPDE.Harmonic.hasDerivAt_sphereAverage_center
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T14:58:30.223261+00:00
-- url     : https://prove2.me/submissions/b4fc7702-4e02-427d-8c62-2789203d3aaa

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology
open HunterPDE.Harmonic

theorem solution {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r)
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 u y)
    (v : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun t : ℝ => sphereAverage u (x + t • v) r)
      (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ u (x + r • ω.1) v ∂(volume.toSphere)) 0 := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let p : ℝ × S → EuclideanSpace ℝ (Fin n) := fun z => x + z.1 • v + r • z.2.1
  let F : ℝ → S → ℝ := fun t ω => u (p (t, ω))
  let D : ℝ → S → ℝ := fun t ω => fderiv ℝ u (p (t, ω)) v
  have hp : Continuous p := by fun_prop
  have hbase (ω : S) : ContDiffAt ℝ 1 u (p (0, ω)) := by
    apply hu
    have hω : ‖ω.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ω.property
    simp [p, Metric.mem_closedBall, dist_eq_norm, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, hω]
  have hDc (t : ℝ) (ω : S) (h : ContDiffAt ℝ 1 u (p (t, ω))) :
      ContinuousAt D.uncurry (t, ω) := by
    exact ((h.continuousAt_fderiv (by simp)).comp hp.continuousAt).clm_apply
      (by fun_prop)
  have hDr : Continuous (D 0) := by
    rw [continuous_iff_continuousAt]
    intro ω
    exact (hDc 0 ω (hbase ω)).comp (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (univ : Set S)).exists_bound_of_continuousOn
    hDr.continuousOn
  have hnear : ∀ᶠ t in 𝓝 0, ∀ ω : S,
      ContDiffAt ℝ 1 u (p (t, ω)) ∧ ‖D t ω‖ ≤ C + 1 := by
    have h := (isCompact_univ : IsCompact (univ : Set S)).eventually_forall_of_forall_eventually
      (x₀ := (0 : ℝ)) (P := fun t ω => ContDiffAt ℝ 1 u (p (t, ω)) ∧ ‖D t ω‖ ≤ C + 1) ?_
    · simpa using h
    intro ω _
    have hreg : ∀ᶠ z : ℝ × S in 𝓝 (0, ω), ContDiffAt ℝ 1 u (p z) :=
      hp.continuousAt.eventually ((hbase ω).eventually (by simp))
    have hlt : ‖D 0 ω‖ < C + 1 := lt_of_le_of_lt (hC ω (mem_univ _)) (lt_add_one C)
    have hbd := (hDc 0 ω (hbase ω)).norm.eventually (gt_mem_nhds hlt)
    filter_upwards [hreg, hbd] with z hz hb
    exact ⟨hz, hb.le⟩
  let s := {t : ℝ | ∀ ω : S, ContDiffAt ℝ 1 u (p (t, ω)) ∧ ‖D t ω‖ ≤ C + 1}
  have hs : s ∈ 𝓝 0 := hnear
  have hFc (t : ℝ) (ht : t ∈ s) : Continuous (F t) := by
    rw [continuous_iff_continuousAt]
    intro ω
    have hpt : ContinuousAt (fun v : S => p (t, v)) ω := by fun_prop
    exact (ht ω).1.continuousAt.comp (f := fun v : S => p (t, v)) hpt
  have hrmem : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  have hdiff (t : ℝ) (ω : S) (ht : t ∈ s) : HasDerivAt (F · ω) (D t ω) t := by
    have hpath : HasDerivAt (fun a : ℝ => x + a • v + r • ω.1) v t := by
      simpa using (((hasDerivAt_id t).smul_const v).const_add x).add_const (r • ω.1)
    exact ((ht ω).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hpath
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume.toSphere : Measure S)) (F := F) (F' := D) (bound := fun _ => C + 1) hs
    ((show ∀ᶠ t in 𝓝 0, t ∈ s from hs).mono fun t ht => (hFc t ht).aestronglyMeasurable)
    ((hFc 0 hrmem).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hDr.aestronglyMeasurable
    (Eventually.of_forall fun ω t ht => (ht ω).2)
    (integrable_const (C + 1))
    (Eventually.of_forall fun ω t ht => hdiff t ω ht)
  have hD0 : (fun ω : S => D 0 ω) =
      (fun ω : S => fderiv ℝ u (x + r • ω.1) v) := by
    funext ω
    simp [D, p]
  rw [← hD0]
  change HasDerivAt (fun t => ⨍ ω : S, F t ω ∂volume.toSphere)
    (⨍ ω : S, D 0 ω ∂volume.toSphere) 0
  have havg : (fun t => ⨍ ω : S, F t ω ∂volume.toSphere) =
      (fun t => ((volume.toSphere : Measure S).real univ)⁻¹ •
        ∫ ω : S, F t ω ∂volume.toSphere) := by
    funext t
    exact MeasureTheory.average_eq (volume.toSphere : Measure S) (F t)
  rw [havg, MeasureTheory.average_eq (volume.toSphere : Measure S) (D 0)]
  exact hi.2.const_smul (((volume.toSphere : Measure S).real univ)⁻¹)
