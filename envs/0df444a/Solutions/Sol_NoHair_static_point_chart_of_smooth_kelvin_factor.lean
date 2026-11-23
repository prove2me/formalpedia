-- Prove2me | solution 1 for NoHair.static_point_chart_of_smooth_kelvin_factor
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:47:03.973463+00:00
-- url     : https://prove2.me/submissions/dca9ac7c-88c6-4ade-aa7a-9fb0162e57c3

import Definitions.Def_NoHair_staticReflectionAndCap
open NoHair Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace
private abbrev X := ADMPoint
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
private lemma pair_id (v w : X) :
    (∑ i : Fin 3, ∑ j : Fin 3,(1:Mat) i j*v i*w j)=inner ℝ v w := by
  simp [Matrix.one_apply,ite_mul,PiLp.inner_apply,Real.inner_apply,mul_comm]
private lemma flat_quadratic (a : ℝ) (v : X) :
    (∑ i : Fin 3, ∑ j : Fin 3,(a • (1:Mat)) i j * v i * v j)=a*‖v‖^2 := by
  rw [←real_inner_self_eq_norm_sq,←pair_id v v]
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem solution (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (R : ℝ) (hR : 0 < R)
    (f : ADMPoint → ℝ) (sf : ContDiffOn ℝ ∞ f (ball 0 (1/R)))
    (pf : ∀ y ∈ ball (0:ADMPoint) (1/R), 0<f y)
    (inside : ∀ x : ADMPoint, R<‖x‖ → x∈Ω)
    (tail : ∀ x : ADMPoint, R<‖x‖ → staticPositiveMetric (fun z => -N z) h x =
      (f (EuclideanGeometry.inversion (0:ADMPoint) 1 x)/‖x‖)^4 • (1:Matrix (Fin 3) (Fin 3) ℝ)) :
    ∃ a : StaticMinusPointChart Ω N h, a.radius = 1/R ∧
      (∀ y, a.change y = EuclideanGeometry.inversion (0:ADMPoint) 1 y) ∧
      ∀ y, a.coeff y = (f y)^4 • (1:Matrix (Fin 3) (Fin 3) ℝ) := by
  let I := EuclideanGeometry.inversion (0:X) 1
  let S := ball (0:X) (1/R) ∩ ({0}:Set X)ᶜ
  let T := {x:X | R<‖x‖}
  have nr (y : X) : ‖I y‖=1/‖y‖ := by
    simpa only [dist_zero_right,one_pow] using EuclideanGeometry.dist_inversion_center (0:X) y 1
  have inv2 (y : X) : I (I y)=y := EuclideanGeometry.inversion_inversion _ one_ne_zero _
  have smI {y:X} (hy : y≠0) : ContDiffAt ℝ ∞ I y :=
    contDiffAt_const.inversion contDiffAt_const contDiffAt_id hy
  have mf : MapsTo I S T := by
    intro y hy
    have sz : ‖y‖ < 1/R := by simpa only [mem_ball,dist_zero_right] using hy.1
    have pos := norm_pos_iff.mpr (show y≠0 from hy.2)
    change R < ‖I y‖
    rw [nr,lt_div_iff₀ pos]
    simpa only [mul_comm] using (lt_div_iff₀ hR).mp sz
  have mb : MapsTo I T S := by
    intro x hx
    have far : R<‖x‖ := hx
    have pos := hR.trans far
    constructor
    · change dist (I x) 0 < 1/R
      rw [dist_zero_right,nr]
      exact one_div_lt_one_div_of_lt hR far
    · exact norm_pos_iff.mp ((nr x) ▸ one_div_pos.mpr pos)
  let e : OpenPartialHomeomorph X X := {
    toFun := I
    invFun := I
    source := S
    target := T
    map_source' := fun {_} hy => mf hy
    map_target' := fun {_} hx => mb hx
    left_inv' := fun {x} _ => inv2 x
    right_inv' := fun {x} _ => inv2 x
    open_source := isOpen_ball.inter isClosed_singleton.isOpen_compl
    open_target := isOpen_lt continuous_const continuous_norm
    continuousOn_toFun := fun y hy => (smI (show y≠0 from hy.2)).continuousAt.continuousWithinAt
    continuousOn_invFun := fun x hx => (smI (norm_pos_iff.mp (hR.trans hx))).continuousAt.continuousWithinAt }
  have out : Tendsto I (𝓝[≠] (0:X)) (Bornology.cobounded X) :=
    EuclideanGeometry.tendsto_inversion_nhdsNE_center_cobounded one_ne_zero
  have inward : Tendsto I (comap (fun x:X => ‖x‖) atTop) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh : Tendsto (fun x:X => ‖x‖) (comap (fun z:X => ‖z‖) atTop) atTop := tendsto_comap
    simpa only [Function.comp_def,nr,one_div] using tendsto_inv_atTop_zero.comp hh
  have pull (y:X) (hy:y∈S) (v:X) :
      staticChartQuadratic (fun z => f z^4 • (1:Mat)) y v =
      staticChartQuadratic (staticPositiveMetric (fun x => -N x) h) (I y) (fderiv ℝ I y v) := by
    have nz : y≠0 := hy.2
    have dy : ‖fderiv ℝ I y v‖=(1/‖y‖)^2*‖v‖ := by
      change ‖fderiv ℝ (EuclideanGeometry.inversion (0:X) 1) y v‖=_
      rw [(EuclideanGeometry.hasFDerivAt_inversion (R:=1) nz).fderiv,
        ContinuousLinearMap.smul_apply,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      congr 1
      exact ((ℝ ∙ (y-(0:X)))ᗮ.reflection).norm_map v
    unfold staticChartQuadratic
    rw [tail _ (mf hy),flat_quadratic,flat_quadratic,dy,nr,show EuclideanGeometry.inversion (0:X) 1 (I y)=y from inv2 y]
    field_simp [norm_ne_zero_iff.mpr nz] <;> ring
  refine ⟨{
    radius := 1/R
    positive := one_div_pos.mpr hR
    change := e
    source := rfl
    inside := fun {x} hx => inside x hx
    smoothChange := fun y hy => (smI (show y≠0 from hy.2)).contDiffWithinAt
    smoothInverse := fun x hx => (smI (norm_pos_iff.mp (hR.trans hx))).contDiffWithinAt
    tendsOut := tendsto_norm_atTop_iff_cobounded.mpr out
    tendsIn := inward
    coversInfinity := ⟨R,Subset.rfl⟩
    coeff := fun y => f y^4 • (1:Mat)
    smooth := fun i j => (sf.pow 4).mul contDiffOn_const
    definite := fun y hy => Matrix.PosDef.one.smul (pow_pos (pf y hy) 4)
    pullsBack := pull },rfl,fun y => rfl,fun y => rfl⟩
