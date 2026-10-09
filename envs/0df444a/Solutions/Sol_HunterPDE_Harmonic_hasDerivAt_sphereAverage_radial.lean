-- Prove2me | solution 1 for HunterPDE.Harmonic.hasDerivAt_sphereAverage_radial
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T22:51:51.82049+00:00
-- url     : https://prove2.me/submissions/62aa8424-19e1-4543-8d7e-adb504f5cf77

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
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 u y) :
    HasDerivAt (sphereAverage u x)
      (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ u (x + r • ω.1) ω.1 ∂(volume.toSphere)) r := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let p : ℝ × S → EuclideanSpace ℝ (Fin n) := fun z => x + z.1 • z.2.1
  let F : ℝ → S → ℝ := fun t ω => u (p (t, ω))
  let D : ℝ → S → ℝ := fun t ω => fderiv ℝ u (p (t, ω)) ω.1
  have hp : Continuous p := by fun_prop
  have hbase (ω : S) : ContDiffAt ℝ 1 u (p (r, ω)) := by
    apply hu
    have hω : ‖ω.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ω.property
    simp [p, Metric.mem_closedBall, dist_eq_norm, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, hω]
  have hDc (t : ℝ) (ω : S) (h : ContDiffAt ℝ 1 u (p (t, ω))) :
      ContinuousAt D.uncurry (t, ω) := by
    exact ((h.continuousAt_fderiv (by simp)).comp hp.continuousAt).clm_apply
      (by fun_prop)
  have hDr : Continuous (D r) := by
    rw [continuous_iff_continuousAt]
    intro ω
    exact (hDc r ω (hbase ω)).comp (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (univ : Set S)).exists_bound_of_continuousOn
    hDr.continuousOn
  have hnear : ∀ᶠ t in 𝓝 r, ∀ ω : S,
      ContDiffAt ℝ 1 u (p (t, ω)) ∧ ‖D t ω‖ ≤ C + 1 := by
    have h := (isCompact_univ : IsCompact (univ : Set S)).eventually_forall_of_forall_eventually
      (x₀ := r) (P := fun t ω => ContDiffAt ℝ 1 u (p (t, ω)) ∧ ‖D t ω‖ ≤ C + 1) ?_
    · simpa using h
    intro ω _
    have hreg : ∀ᶠ z : ℝ × S in 𝓝 (r, ω), ContDiffAt ℝ 1 u (p z) :=
      hp.continuousAt.eventually ((hbase ω).eventually (by simp))
    have hlt : ‖D r ω‖ < C + 1 := lt_of_le_of_lt (hC ω (mem_univ _)) (lt_add_one C)
    have hbd := (hDc r ω (hbase ω)).norm.eventually (gt_mem_nhds hlt)
    filter_upwards [hreg, hbd] with z hz hb
    exact ⟨hz, hb.le⟩
  let s := {t : ℝ | ∀ ω : S, ContDiffAt ℝ 1 u (p (t, ω)) ∧ ‖D t ω‖ ≤ C + 1}
  have hs : s ∈ 𝓝 r := hnear
  have hFc (t : ℝ) (ht : t ∈ s) : Continuous (F t) := by
    rw [continuous_iff_continuousAt]
    intro ω
    have hpt : ContinuousAt (fun v : S => p (t, v)) ω := by fun_prop
    exact (ht ω).1.continuousAt.comp (f := fun v : S => p (t, v)) hpt
  have hrmem : r ∈ s := mem_of_mem_nhds hs
  have hdiff (t : ℝ) (ω : S) (ht : t ∈ s) : HasDerivAt (F · ω) (D t ω) t := by
    have hpath : HasDerivAt (fun a : ℝ => x + a • ω.1) ω.1 t := by
      simpa using ((hasDerivAt_id t).smul_const ω.1).const_add x
    exact ((ht ω).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hpath
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume.toSphere : Measure S)) (F := F) (F' := D) (bound := fun _ => C + 1) hs
    ((show ∀ᶠ t in 𝓝 r, t ∈ s from hs).mono fun t ht => (hFc t ht).aestronglyMeasurable)
    ((hFc r hrmem).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hDr.aestronglyMeasurable
    (Eventually.of_forall fun ω t ht => (ht ω).2)
    (integrable_const (C + 1))
    (Eventually.of_forall fun ω t ht => hdiff t ω ht)
  change HasDerivAt (fun t => ⨍ ω : S, F t ω ∂volume.toSphere)
    (⨍ ω : S, D r ω ∂volume.toSphere) r
  have havg : (fun t => ⨍ ω : S, F t ω ∂volume.toSphere) =
      (fun t => ((volume.toSphere : Measure S).real univ)⁻¹ •
        ∫ ω : S, F t ω ∂volume.toSphere) := by
    funext t
    exact MeasureTheory.average_eq (volume.toSphere : Measure S) (F t)
  rw [havg, MeasureTheory.average_eq (volume.toSphere : Measure S) (D r)]
  exact hi.2.const_smul (((volume.toSphere : Measure S).real univ)⁻¹)
