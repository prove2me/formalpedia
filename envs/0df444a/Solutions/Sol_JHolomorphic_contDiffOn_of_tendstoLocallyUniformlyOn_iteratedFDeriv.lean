-- Prove2me | solution 1 for JHolomorphic.contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T15:35:44.556775+00:00
-- url     : https://prove2.me/submissions/06773118-b206-4aa4-b4d4-fc067f058b53

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv



namespace JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

theorem contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv_aux
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → Y) (hf : ∀ ν, ContDiffOn ℝ ∞ (f ν) U)
    (v : X → Y) (hv : ∀ x ∈ U, Tendsto (fun ν => f ν x) atTop (𝓝 (v x)))
    (g : (m : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y)
    (hg : ∀ m, TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (f ν)) (g m) atTop U) :
    ContDiffOn ℝ ∞ v U ∧ ∀ m, EqOn (iteratedFDeriv ℝ m v) (g m) U := by
  have hder : ∀ m : ℕ, ∀ x ∈ U, HasFDerivAt (g m)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) Y (g (m + 1) x)) x := by
    intro m x hx
    set L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) Y
    have hfd : ∀ ν y, fderiv ℝ (iteratedFDeriv ℝ m (f ν)) y =
        L (iteratedFDeriv ℝ (m + 1) (f ν) y) := by
      intro ν y
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply]
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn (f := fun ν => iteratedFDeriv ℝ m (f ν))
      (f' := fun ν y => L (iteratedFDeriv ℝ (m + 1) (f ν) y))
      (g' := fun y => L (g (m + 1) y)) hU ?_ ?_
      (fun y hy => (hg m).tendsto_at hy) hx
    · exact L.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn (hg (m + 1))
    · intro ν y hy
      rw [← hfd]
      exact (((hf ν).contDiffAt (hU.mem_nhds hy)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.coe_lt_top m)).hasFDerivAt
  have heq : ∀ m, EqOn (iteratedFDeriv ℝ m v) (g m) U := by
    intro m
    induction m with
    | zero =>
      intro x hx
      have h1 : Tendsto (fun ν => iteratedFDeriv ℝ 0 (f ν) x) atTop
          (𝓝 (iteratedFDeriv ℝ 0 v x)) := by
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact ((continuousMultilinearCurryFin0 ℝ X Y).symm.continuous.tendsto _).comp (hv x hx)
      exact tendsto_nhds_unique h1 ((hg 0).tendsto_at hx)
    | succ m ih =>
      intro x hx
      have hloc : iteratedFDeriv ℝ m v =ᶠ[𝓝 x] g m :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hloc.fderiv_eq,
        (hder m x hx).fderiv, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨?_, heq⟩
  have hdg : ∀ m : ℕ, DifferentiableOn ℝ (iteratedFDerivWithin ℝ m v U) U := fun m x hx =>
    (hder m x hx).differentiableAt.differentiableWithinAt.congr
      (fun y hy => (iteratedFDerivWithin_of_isOpen m hU hy).trans (heq m hy))
      ((iteratedFDerivWithin_of_isOpen m hU hx).trans (heq m hx))
  exact contDiffOn_of_continuousOn_differentiableOn (fun m _ => (hdg m).continuousOn)
    (fun m _ => hdg m)

end JHolomorphic

open JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

theorem solution
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → Y) (hf : ∀ ν, ContDiffOn ℝ ∞ (f ν) U)
    (v : X → Y) (hv : ∀ x ∈ U, Tendsto (fun ν => f ν x) atTop (𝓝 (v x)))
    (g : (m : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y)
    (hg : ∀ m, TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (f ν)) (g m) atTop U) :
    ContDiffOn ℝ ∞ v U ∧ ∀ m, EqOn (iteratedFDeriv ℝ m v) (g m) U :=
  contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv_aux hU f hf v hv g hg
