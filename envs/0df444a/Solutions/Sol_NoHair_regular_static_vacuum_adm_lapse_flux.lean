-- Prove2me | solution 1 for NoHair.regular_static_vacuum_adm_lapse_flux
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:53:22.531879+00:00
-- url     : https://prove2.me/submissions/e6f6ca05-60b2-49fb-a699-ca346478957b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_adm_zero_of_linearized_einstein_decay
import Theorems.Thm_NoHair_static_vacuum_linearized_einstein_decay
open Set Metric MeasureTheory Filter NoHair
open scoped ContDiff Manifold Topology

private abbrev X := ADMPoint
private abbrev S := ADMSphere

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    Tendsto (fun r : ℝ => staticADMFlux c.h r - staticLapseFlux c.N r) atTop (𝓝 0) := by
  classical
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.subset_closedBall (0 : X)
  have cover (x : X) (hx : B < ‖x‖) : x ∈ c.W := by
    apply c.extendsAcross
    apply subset_closure
    by_contra hn
    have h := Metric.mem_closedBall.mp (hB hn)
    exact hx.not_ge (by simpa only [dist_zero_right] using h)
  have cn (x : X) (hx : B < ‖x‖) : ContDiffAt ℝ ∞ c.N x :=
    c.smoothLapse.contDiffAt (c.openExtension.mem_nhds (cover x hx))
  have ch (x : X) (hx : B < ‖x‖) (i j : Fin 3) : ContDiffAt ℝ ∞ (fun y => c.h y i j) x :=
    (c.smoothMetric i j).contDiffAt (c.openExtension.mem_nhds (cover x hx))
  let K := lapseCorrectedADMMetric c.N c.h
  have ck (x : X) (hx : B < ‖x‖) (i j : Fin 3) : ContDiffAt ℝ ∞ (fun y => K y i j) x :=
    (ch x hx i j).add ((contDiffAt_const.mul ((cn x hx).sub contDiffAt_const)).mul contDiffAt_const)
  have lower := adm_zero_of_linearized_einstein_decay K ⟨B,ck⟩ (static_vacuum_linearized_einstein_decay g φ D c)
  apply lower.congr'
  filter_upwards [eventually_gt_atTop (max B 0)] with r hr
  have rp := (max_lt_iff.mp hr).2
  have pos (n : S) : B < ‖r • (n:X)‖ := by
    have hn : ‖(n:X)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos rp,hn,mul_one]
    exact (max_lt_iff.mp hr).1
  have id (n:S) : staticADMDensity K r n =
      staticADMDensity c.h r n - 4*staticLapseDensity c.N r n := by
    let x := r • (n:X)
    let D0 := (1 : Matrix (Fin 3) (Fin 3) ℝ)
    let Dh := fun l i j => spatialADMPartial l (fun z => c.h z i j) x
    let Dk := fun (l i j : Fin 3) => spatialADMPartial l (fun y => K y i j) x
    let DN := fun i => spatialADMPartial i c.N x
    have jet (l i j : Fin 3) : Dk l i j = Dh l i j + 2*D0 i j*DN l := by
      have dh := ((ch x (pos n) i j).differentiableAt (by simp)).hasFDerivAt
      have dn := ((cn x (pos n)).differentiableAt (by simp)).hasFDerivAt
      have deriv := (dh.add (((dn.sub_const 1).const_mul 2).mul_const (D0 i j))).fderiv
      change fderiv ℝ (fun y => K y i j) x = _ at deriv
      dsimp only [Dk,Dh,DN,spatialADMPartial]
      rw [deriv]
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,smul_eq_mul]
      ring
    change (∑ i : Fin 3, ∑ j : Fin 3, (r^2*Dk j i j-r^2*Dk i j j)*(n:X) i) =
      (∑ i : Fin 3, ∑ j : Fin 3, (r^2*Dh j i j-r^2*Dh i j j)*(n:X) i) -
        4*(∑ i : Fin 3, r^2*DN i*(n:X) i)
    rw [show Dk = (fun l i j => Dh l i j+2*D0 i j*DN l) from
      funext fun l => funext fun i => funext fun j => jet l i j]
    simp +decide [Fin.sum_univ_three,D0,Matrix.one_apply] <;> ring
  have sm (f : X → ℝ) (cf : ∀ n : S, ContDiffAt ℝ ∞ f (r • (n:X))) (i : Fin 3) :
      Continuous (fun n : S => spatialADMPartial i f (r • (n:X))) := by
    apply continuous_iff_continuousAt.mpr
    intro n
    have pc : ContinuousAt (spatialADMPartial i f) (r • (n:X)) :=
      ((cf n).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
    exact pc.comp (f:=fun n : S => r • (n:X)) ((continuous_const_smul r).comp continuous_subtype_val).continuousAt
  have hcont : Continuous (staticADMDensity c.h r) := by
    unfold staticADMDensity
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_const.mul (sm _ (fun n => ch _ (pos n) i j) j)).sub
      (continuous_const.mul (sm _ (fun n => ch _ (pos n) j j) i))).mul
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  have ncont : Continuous (staticLapseDensity c.N r) := by
    unfold staticLapseDensity
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_const.mul (sm _ (fun n => cn _ (pos n)) i)).mul
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  have hi := hcont.integrable_of_hasCompactSupport (μ:=admSurfaceMeasure) (HasCompactSupport.of_compactSpace _)
  have ni := ncont.integrable_of_hasCompactSupport (μ:=admSurfaceMeasure) (HasCompactSupport.of_compactSpace _)
  have ni4 : Integrable (fun n : S => 4*staticLapseDensity c.N r n) admSurfaceMeasure := ni.const_mul 4
  change staticADMFlux K r = staticADMFlux c.h r - staticLapseFlux c.N r
  unfold staticADMFlux staticLapseFlux
  simp_rw [id]
  rw [integral_sub hi ni4,integral_const_mul]
  ring
