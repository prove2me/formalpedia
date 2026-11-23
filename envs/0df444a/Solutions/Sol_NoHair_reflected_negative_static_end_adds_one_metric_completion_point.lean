-- Prove2me | solution 1 for NoHair.reflected_negative_static_end_adds_one_metric_completion_point
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:07:50.662967+00:00
-- url     : https://prove2.me/submissions/c622bfd3-9357-4374-94fa-c699d2fa35d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_bounded_differential_punctured_ball_has_unique_limit
import Theorems.Thm_NoHair_negative_static_end_inversion_bound
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric UniformSpace
private abbrev X := ADMPoint
private abbrev I := 𝓘(ℝ,X)
private abbrev A := Fin 3
private noncomputable abbrev e (i:A) : X := EuclideanSpace.single i 1

private lemma norm_in_chart {Q:Type} [MetricSpace Q] [ChartedSpace X Q] [IsManifold I ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace I q)]
    (f : X → Q) (x v : X) : ‖mfderiv I I f x v‖^2 = staticChartQuadratic (riemannianEndCoeffs f) x v := by
  let D := mfderiv I I f x
  have rep : (∑ i : A, v i • e i) = v := by
    rw [Fin.sum_univ_three]
    ext j
    fin_cases j <;> simp +decide [e,EuclideanSpace.single,PiLp.single_apply]
  have dr : D v=∑ i : A, v i • D (e i) := by
    let P : X →ₗ[ℝ] TangentSpace I (f x) := D.toLinearMap
    change P v=∑ i:A, v i • P (e i)
    calc _ = P (∑ i:A, v i • e i) := congrArg P rep.symm
         _ = _ := by simp only [map_sum,map_smul]
  change ‖D v‖^2 = _
  rw [←real_inner_self_eq_norm_sq,dr]
  simp only [staticChartQuadratic,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [riemannianEndCoeffs,D,e]
  simp only [real_inner_comm]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) :
    ∃ p : UniformSpace.Completion d.carrier, (∀ q : d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) ∧
      Tendsto (fun x : ADMPoint => ((d.side false).symm x : UniformSpace.Completion d.carrier))
        (cocompact ADMPoint) (𝓝 p) := by
  classical
  obtain ⟨R,C,rp,cp,_,bound⟩ := negative_static_end_inversion_bound Ω W N h c
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.exists_norm_le
  let T := max R B+1
  have tpos : 0<T := by dsimp [T]; linarith only [le_max_left R B,rp]
  let r := 1/T
  let J := EuclideanGeometry.inversion (0:X) 1
  let f := (d.side false).symm ∘ J
  let S := ball (0:X) r ∩ ({0}:Set X)ᶜ
  have jnorm (x:X) : ‖J x‖=1/‖x‖ := by
    simpa only [J,one_pow,dist_zero_right] using EuclideanGeometry.dist_inversion_center (0:X) x 1
  have mem {x:X} (hx:x∈S) : J x∈Ω ∧ ‖x‖<1/R := by
    have xp : 0<‖x‖ := norm_pos_iff.mpr hx.2
    have b := mem_ball_zero_iff.mp hx.1
    change ‖x‖<1/T at b
    have far : T<‖J x‖ := by
      rw [jnorm,lt_div_iff₀ xp]
      simpa only [mul_comm] using (lt_div_iff₀ tpos).mp b
    constructor
    · by_contra hn
      have o := hB (J x) hn
      dsimp only [T] at far
      linarith only [far,o,le_max_right R B]
    · exact b.trans_le (one_div_le_one_div_of_le rp (by dsimp [T]; linarith only [le_max_left R B]))
  have jsm {x:X} (hx:x∈S) : ContMDiffAt I I 1 J x :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx.2)
  have dsm {x:X} (hx:x∈Ω) : ContMDiffAt I I 1 (d.side false).symm x := by
    apply ((d.smoothInverse false).of_le (by simp : (1:ℕ∞ω)≤∞)).contMDiffAt
    rw [d.target]; exact c.openSlice.mem_nhds hx
  have sm : ContMDiffOn I I 1 f S := fun x hx => ((dsm (mem hx).1).comp x (jsm hx)).contMDiffWithinAt
  have bd (x:X) (hx:x∈S) (v:X) : ‖mfderiv I I f x v‖ ≤ Real.sqrt C*‖v‖ := by
    have q := bound x (norm_pos_iff.mpr hx.2) (mem hx).2 v
    have dcomp := mfderiv_comp (I':=I) x ((dsm (mem hx).1).mdifferentiableAt one_ne_zero) ((jsm hx).mdifferentiableAt one_ne_zero)
    have n := norm_in_chart (d.side false).symm (J x) (fderiv ℝ J x v)
    have met : riemannianEndCoeffs (d.side false).symm (J x) = staticPositiveMetric (fun y => -N y) h (J x) := by
      simpa using d.sideMetric false (J x) (mem hx).1
    change staticChartQuadratic (staticPositiveMetric (fun y => -N y) h) (J x) (fderiv ℝ J x v) ≤ C*‖v‖^2 at q
    have n' : ‖mfderiv I I f x v‖^2 ≤ C*‖v‖^2 := by
      have eq1 := congrArg (fun L : X →L[ℝ] TangentSpace I (f x) => ‖L v‖^2) dcomp
      change ‖mfderiv I I f x v‖^2 =
        ‖mfderiv I I (d.side false).symm (J x) (mfderiv I I J x v)‖^2 at eq1
      have eq2 : (mfderiv I I J x : X →L[ℝ] X) = fderiv ℝ J x := mfderiv_eq_fderiv
      rw [eq2] at eq1
      apply eq1.le.trans
      apply n.le.trans
      simpa only [staticChartQuadratic,met] using q
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt cp.le] using n'
  have rp' : 0<r := one_div_pos.mpr tpos
  obtain ⟨p,lim⟩ := bounded_differential_punctured_ball_has_unique_limit d.carrier f r (Real.sqrt C) rp' (Real.sqrt_pos.mpr cp) sm bd
  have far (a:ℝ) : ∀ᶠ x:X in cocompact X, a<‖x‖ := tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop a)
  have jlim : Tendsto J (cocompact X) (𝓝[≠] (0:X)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [jnorm] using (tendsto_const_nhds.div_atTop (tendsto_norm_cocompact_atTop (E:=X)) : Tendsto (fun x:X => 1/‖x‖) (cocompact X) (𝓝 0))
    · filter_upwards [far 0] with x hx
      exact (EuclideanGeometry.inversion_eq_center (one_ne_zero : (1:ℝ)≠0)).not.mpr (norm_pos_iff.mp hx)
  have li : Tendsto (fun x:X => ((d.side false).symm x : Completion d.carrier)) (cocompact X) (𝓝 p) := by
    simpa only [Function.comp_def,f,J,EuclideanGeometry.inversion_inversion _ one_ne_zero] using lim.comp jlim
  refine ⟨p,?_,li⟩
  intro q eq
  rw [←eq] at li
  have lc : Tendsto (d.side false).symm (cocompact X) (𝓝 q) :=
    (Completion.isUniformInducing_coe d.carrier).isInducing.tendsto_nhds_iff.mpr li
  have lc' := d.smoothLapse.continuous.continuousAt.tendsto.comp lc
  have lapse : Tendsto (fun x:X => d.lapse ((d.side false).symm x)) (cocompact X) (𝓝 (-1)) := by
    obtain ⟨R₀,C₀,_,_,h₀⟩ := c.falloff 0
    have decay : Tendsto (fun x:X => N x-1) (cocompact X) (𝓝 0) := by
      apply squeeze_zero_norm' (a:=fun x:X => C₀/‖x‖)
      · filter_upwards [far R₀] with x hx
        simpa only [norm_iteratedFDeriv_zero,Nat.zero_add,pow_one] using (h₀ x hx).1
      · exact tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
    have nl : Tendsto N (cocompact X) (𝓝 1) := by simpa only [sub_add_cancel,zero_add] using (decay.add_const 1)
    apply nl.neg.congr'
    filter_upwards [far B] with x hx
    have ox : x∈Ω := by by_contra hn; exact hx.not_ge (hB x hn)
    rw [d.inverseOnSide false x ox,d.signed]
    simp
  have bad : d.lapse q = -1 := tendsto_nhds_unique lc' lapse
  exact (d.lower q).ne' bad
