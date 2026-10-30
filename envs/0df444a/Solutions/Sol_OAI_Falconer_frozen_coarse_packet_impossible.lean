-- Prove2me | solution 1 for OAI.Falconer.frozen_coarse_packet_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:28:09.008622+00:00
-- url     : https://prove2.me/submissions/a70cbb35-e5ca-4286-bd8d-fb7415cc3056

import Mathlib
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_centered_packet_product_power

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularSamples
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite sampled direction families

Ball counts for the sampled direction labels control both multiplicities
and normalized ball counts of the rounded incident line families. The
estimates below retain the original labels, including repeated directions.
-/

namespace Falconer
open Set
open scoped BigOperators

/-- A finite map can lose only the maximum multiplicity of its fibers. -/
theorem card_le_image_card_mul_fiber_bound {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (S : Finset ι) (F : ι → α) {L : ℝ}
    (hF : ∀ a ∈ S.image F, ((S.filter (fun i => F i = a)).card : ℝ) ≤ L) :
    (S.card : ℝ) ≤ ((S.image F).card : ℝ) * L := by
  rw [Finset.card_eq_sum_card_image F S, Nat.cast_sum]
  exact (Finset.sum_le_sum hF).trans_eq (by simp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubeSecondMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite incidence identities before the geometric common-tube bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_tube_membership (U S : Finset (Space 2)) (hS : S ⊆ U) :
    (∑ l ∈ U, if l ∈ S then (1 : ℝ) else 0) = S.card := by
  rw [← Finset.sum_filter]
  have he : U.filter (fun l => l ∈ S) = S := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hl => hS hl)
  rw [he]
  simp

theorem sum_tubeDegree (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, tubeDegree P T l) = ∑ x ∈ P, ((T x).card : ℝ) := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_tube_membership _ _ (Finset.subset_biUnion_of_mem T hx)

theorem sum_tubeDegree_sq (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) =
      ∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ) := by
  let U := P.biUnion T
  calc
    _ = ∑ l ∈ U, ∑ x ∈ P, ∑ y ∈ P,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      simp only [tubeDegree, pow_two, Finset.sum_mul_sum, U]
    _ = ∑ x ∈ P, ∑ y ∈ P, ∑ l ∈ U,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y _
      have he (l : Space 2) :
          (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) =
          if l ∈ T x ∩ T y then 1 else 0 := by
        by_cases hx : l ∈ T x <;> by_cases hy : l ∈ T y <;> simp [hx,hy]
      simp_rw [he]
      exact sum_tube_membership U _ (fun l hl =>
        Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hl).1⟩)

theorem tube_union_second_moment (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ x ∈ P, ((T x).card : ℝ))^2 ≤
      ((P.biUnion T).card : ℝ) * (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ)) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (P.biUnion T)
    (fun _ => (1 : ℝ)) (tubeDegree P T)
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    sum_tubeDegree, sum_tubeDegree_sq] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoPointTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point localization of actual bounded-chart tube parameters.
This is the elementary incidence kernel used in the multiscale Furstenberg proof. -/
namespace Falconer
open Set

theorem planar_dist_le_coordinate_sum (x y : Space 2) :
    dist x y ≤ |x 0-y 0| + |x 1-y 1| := by
  have he := EuclideanSpace.dist_sq_eq x y
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at he
  nlinarith [dist_nonneg (x := x) (y := y), abs_nonneg (x 0-y 0),
    abs_nonneg (x 1-y 1), sq_abs (x 0-y 0), sq_abs (x 1-y 1),
    mul_nonneg (abs_nonneg (x 0-y 0)) (abs_nonneg (x 1-y 1))]

theorem tube_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l : Space 2}
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) :
    |x 1-l 0*x 0-l 1| ≤ 2*δ := by
  have hs : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1+(l 0)^2) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    have hsq := (sq_le_sq₀ (abs_nonneg (l 0)) zero_le_one).mpr hl
    nlinarith [sq_abs (l 0)]
  exact ((div_le_iff₀ hs).mp hi).trans (by nlinarith)

theorem tube_pair_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l m : Space 2}
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hil : TubeIncident δ x l) (him : TubeIncident δ x m) :
    |(l 0-m 0)*x 0+(l 1-m 1)| ≤ 4*δ := by
  calc
    _ = |(x 1-m 0*x 0-m 1)-(x 1-l 0*x 0-l 1)| := by congr 1; ring
    _ ≤ |x 1-m 0*x 0-m 1|+|x 1-l 0*x 0-l 1| := abs_sub _ _
    _ ≤ _ := by linarith [tube_residual_le hδ hm him, tube_residual_le hδ hl hil]

theorem tube_point_coordinate_lower {δ r : ℝ} (hδ : 0 ≤ δ) (_hr : 0 < r)
    (hsmall : 16*δ ≤ r) {x y l : Space 2} (hl : |l 0| ≤ 1)
    (hx : TubeIncident δ x l) (hy : TubeIncident δ y l) (hxy : r ≤ dist x y) :
    r/4 ≤ |x 0-y 0| := by
  have he : |x 1-y 1| ≤ |x 0-y 0|+4*δ := by
    calc
      _ = |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)-(y 1-l 0*y 0-l 1)| := by congr 1; ring
      _ ≤ |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)|+|y 1-l 0*y 0-l 1| := abs_sub _ _
      _ ≤ |l 0| * |x 0-y 0|+|x 1-l 0*x 0-l 1|+|y 1-l 0*y 0-l 1| := by
        rw [← abs_mul]
        linarith [abs_add_le (l 0*(x 0-y 0)) (x 1-l 0*x 0-l 1)]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hl (abs_nonneg (x 0-y 0))
        linarith [tube_residual_le hδ hl hx, tube_residual_le hδ hl hy]
  linarith [planar_dist_le_coordinate_sum x y]

theorem two_point_tube_parameters_close {δ r : ℝ} (hδ : 0 ≤ δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    {x y l m : Space 2} (hx0 : |x 0| ≤ 1)
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hxl : TubeIncident δ x l) (hyl : TubeIncident δ y l)
    (hxm : TubeIncident δ x m) (hym : TubeIncident δ y m)
    (hxy : r ≤ dist x y) : dist l m ≤ 80*δ/r := by
  have hcoord := tube_point_coordinate_lower hδ hr hsmall hl hxl hyl hxy
  have hs : |l 0-m 0| * |x 0-y 0| ≤ 8*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-((l 0-m 0)*y 0+(l 1-m 1))| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*y 0+(l 1-m 1)| := abs_sub _ _
      _ ≤ _ := by linarith [tube_pair_residual_le hδ hl hm hxl hxm,
        tube_pair_residual_le hδ hl hm hyl hym]
  have hslope : |l 0-m 0| ≤ 32*δ/r := by
    apply (le_div_iff₀ hr).2
    have hh := mul_le_mul_of_nonneg_left hcoord (abs_nonneg (l 0-m 0))
    nlinarith
  have hinter : |l 1-m 1| ≤ |l 0-m 0|+4*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-(l 0-m 0)*x 0| := by congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*x 0| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul]
        have hh := mul_le_mul_of_nonneg_left hx0 (abs_nonneg (l 0-m 0))
        linarith [tube_pair_residual_le hδ hl hm hxl hxm]
  apply (le_div_iff₀ hr).2
  have hdist : dist l m ≤ 2*|l 0-m 0|+4*δ :=
    (planar_dist_le_coordinate_sum l m).trans (by linarith [hinter])
  have hsum := mul_le_mul_of_nonneg_right hdist hr.le
  have hsl := (le_div_iff₀ hr).mp hslope
  have hd := mul_le_mul_of_nonneg_left hr1 hδ
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The row geometry in Orponen--Shmerkin, Appendix A.7, expressed in the
original line chart. A line is incident to only a bounded number of points
on a separated row. Its parameter projection stays close to that row point. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem rowPoint_dist (y x z : ℝ) : dist (rowPoint y x) (rowPoint y z) = |x-z| := by
  have he := EuclideanSpace.dist_sq_eq (rowPoint y x) (rowPoint y z)
  simp only [Fin.sum_univ_two,rowPoint_zero,rowPoint_one,Real.dist_eq,sq_abs] at he
  nlinarith [dist_nonneg (x := rowPoint y x) (y := rowPoint y z),abs_nonneg (x-z),sq_abs (x-z)]

theorem row_dist_projection {x : Space 2} {y : ℝ} (hy : x 0 = y) (v : ℝ) :
    dist x (rowPoint y v) = |x 1-v| := by
  have hx : x = rowPoint y (x 1) := by
    ext i
    fin_cases i
    · exact hy
    · rfl
  rw [hx,rowPoint_dist]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ScalarAffineExceptions
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional coefficient counts for separated scalar clusters. This is
 the finite real-variable separation estimate in the porous amplification
 argument; the coefficient distribution is the original finite set. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_affine_small_subset {μ R u v : ℝ} (hμ : 0 < μ)
    (hv : μ ≤ |v|) (hR : 0 ≤ R) (B : Finset ℝ) :
    B.filter (fun b => |u+b*v| ≤ R) ⊆
      B.filter (fun b => |b-(-u/v)| ≤ R/μ) := by
  intro b hb
  obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨hb,?_⟩
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv; linarith
  have hid : b-(-u/v) = (u+b*v)/v := by field_simp; ring
  rw [hid,abs_div]
  exact (div_le_div_of_nonneg_right he (abs_nonneg v)).trans
    (div_le_div_of_nonneg_left hR hμ hv)

 theorem scalar_affine_small_card {δ μ R K κ : ℝ} (hμ : 0 < μ)
    (hR : 0 ≤ R) (hscale : δ ≤ R/μ) (hscale1 : R/μ ≤ 1)
    (B : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass B u r ≤ K*r^κ*(B.card : ℝ))
    {u v : ℝ} (hv : μ ≤ |v|) :
    ((B.filter fun b => |u+b*v| ≤ R).card : ℝ) ≤
      K*(R/μ)^κ*(B.card : ℝ) := by
  calc
    _ ≤ scalarBallMass B (-u/v) (R/μ) := by
      change ((B.filter fun b => |u+b*v| ≤ R).card : ℝ) ≤
        ((B.filter fun b => |b-(-u/v)| ≤ R/μ).card : ℝ)
      exact_mod_cast Finset.card_le_card (scalar_affine_small_subset (u := u) hμ hv hR B)
    _ ≤ _ := hball _ _ hscale hscale1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FiniteProjectionSublevels
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Kaufman sublevel bound for the actual slope projections. This
is the geometric estimate used to find regular projections inside the
coarse tube packet, before extracting its product rows. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem finite_projection_sublevel {δ r s K : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hs : 0 ≤ s) (hK : 1 ≤ K) (I : Finset ℝ)
    (hI : ∀ c ∈ I, |c| ≤ 1)
    (hball : ∀ u t : ℝ, δ ≤ t → t ≤ 1 →
      scalarBallMass I u t ≤ K*t^s*(I.card:ℝ))
    (p q : Space 2) (hdiam : dist p q ≤ 4) :
    ((I.filter fun c => |lineParameterProjection c p-lineParameterProjection c q| ≤ r).card:ℝ) ≤
      K*(8*r/max (dist p q) δ)^s*(I.card:ℝ) := by
  let B := I.filter fun c => |lineParameterProjection c p-lineParameterProjection c q| ≤ r
  let D := max (dist p q) δ
  have hD : 0 < D := hδ.trans_le (le_max_right _ _)
  have hr0 : 0 < r := hδ.trans_le hr
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  by_cases hcoarse : D ≤ 8*r
  · have hratio : 1 ≤ 8*r/D := (le_div_iff₀ hD).2 (by simpa using hcoarse)
    have hpow : 1 ≤ (8*r/D)^s := Real.one_le_rpow hratio hs
    have hprod : 1 ≤ K*(8*r/D)^s := by
      simpa only [one_mul] using mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) hK0
    exact (Nat.cast_le.mpr (Finset.card_filter_le I _)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg I.card))
  have hfar : 8*r < D := lt_of_not_ge hcoarse
  have hdδ : δ < dist p q := by
    by_contra hh
    have he : D = δ := max_eq_right (le_of_not_gt hh)
    rw [he] at hfar
    linarith only [hfar,hr,hδ]
  have heD : D = dist p q := max_eq_left hdδ.le
  have hd : 0 < dist p q := hδ.trans hdδ
  let u := p 1-q 1
  let v := p 0-q 0
  have he (c : ℝ) : lineParameterProjection c p-lineParameterProjection c q = u+c*v := by
    dsimp [lineParameterProjection,u,v]
    ring
  by_cases hB : B.Nonempty
  · obtain ⟨c,hc⟩ := hB
    obtain ⟨hcI,hcproj⟩ := Finset.mem_filter.mp hc
    rw [he] at hcproj
    have hcv : |c*v| ≤ |v| := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hI c hcI) (abs_nonneg v)
    have hu : |u| ≤ r+|v| := by
      have hh : |u| ≤ |u+c*v|+|c*v| := by
        simpa only [add_sub_cancel_right] using abs_sub (u+c*v) (c*v)
      linarith only [hh,hcproj,hcv]
    have hdp : dist p q ≤ |v|+|u| := planar_dist_le_coordinate_sum p q
    have hv : dist p q/4 ≤ |v| := by rw [heD] at hfar; linarith only [hfar,hdp,hu,hd]
    have hμ : 0 < dist p q/4 := by positivity
    have hscale : δ ≤ r/(dist p q/4) := by
      apply (le_div_iff₀ hμ).2
      have hh := mul_le_mul_of_nonneg_left (show dist p q/4 ≤ 1 by linarith only [hdiam]) hδ.le
      have hh' : δ*(dist p q/4) ≤ δ := by simpa only [mul_one] using hh
      exact hh'.trans hr
    have hscale1 : r/(dist p q/4) ≤ 1 := by
      apply (div_le_one hμ).2
      rw [heD] at hfar
      linarith only [hfar,hr0]
    have hb := scalar_affine_small_card hμ hr0.le hscale hscale1 I hball (u := u) hv
    have heB : B = I.filter (fun c => |u+c*v| ≤ r) := by
      dsimp [B]
      simp_rw [he]
    rw [← heB] at hb
    have hrat : r/(dist p q/4) ≤ 8*r/D := by
      rw [heD]
      apply (div_le_div_iff₀ hμ hd).2
      nlinarith only [mul_nonneg hr0.le hd.le]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hrat hs) hK0)
      (Nat.cast_nonneg I.card))
  · have heB : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (B.card:ℝ) ≤ _
    rw [heB,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and nonemptiness consequences for the normalized finite sets
appearing in the published planar incidence statement. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem finite_ball_bound_card_lower {δ s K : ℝ} {P : Finset (Space 2)}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hP : P.Nonempty)
    (hball : NormalizedFiniteBallBound δ s K P) :
    1 ≤ K*δ^s*(P.card : ℝ) := by
  obtain ⟨x,hx⟩ := hP
  have hx' : x ∈ P.filter (fun y => dist y x ≤ δ) := by simp [hx,hδ.le]
  have hc : 1 ≤ (P.filter (fun y => dist y x ≤ δ)).card :=
    Finset.one_le_card.mpr ⟨x,hx'⟩
  have hcR : (1 : ℝ) ≤ (P.filter (fun y => dist y x ≤ δ)).card := by exact_mod_cast hc
  exact hcR.trans (hball x δ le_rfl hδ1)

theorem normalized_finite_ball_bound_subset {δ s K C : ℝ}
    {P S : Finset (Space 2)} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hS : S ⊆ P) (hsize : (P.card : ℝ) ≤ C*(S.card : ℝ))
    (hball : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound δ s (K*C) S := by
  intro z r hdr hr1
  have hsub : S.filter (fun x => dist x z ≤ r) ⊆ P.filter (fun x => dist x z ≤ r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  calc
    _ ≤ ((P.filter (fun x => dist x z ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K*r^s*(P.card : ℝ) := hball z r hdr hr1
    _ ≤ K*r^s*(C*(S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg (hδ.trans hdr) _))
    _ = _ := by ring

theorem finiteSeparatedAt_subset {δ : ℝ} {P S : Finset (Space 2)}
    (hS : S ⊆ P) (hP : FiniteSeparatedAt δ P) : FiniteSeparatedAt δ S :=
  fun x hx y hy hxy => hP x (hS hx) y (hS hy) hxy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InversePowerSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic inverse-power sums at the critical ambient exponent -/

namespace Falconer

theorem inverse_power_dyadic {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ r) :
    (1/r)^s ≤ ((2:ℝ)^g)^s + ∑ j ∈ Finset.range k,
      if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply Real.rpow_le_rpow (by positivity) _ hs
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : 1/(2:ℝ)^(g+k) ≤ r
    · have hh := ih hc
      have hn : 0 ≤ (if r < 1/(2:ℝ)^(g+k) then ((2:ℝ)^(g+k+1))^s else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hc)]
      have hinv : 1/r ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hr).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/r) hinv hs
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hz : 0 ≤ ((2:ℝ)^g)^s := by positivity
      linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RegularizedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale inverse-distance potentials for the slicing kernels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_dyadic (μ : Measure X)
    (x : X) {s : ℝ} (hs : 0 ≤ s) (g k : ℕ) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
    ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g))+
      ∑ j ∈ Finset.range k, ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*
        μ (ball x (1/(2:ℝ)^(g+j))) := by
  let B := ball x (1/(2:ℝ)^g)
  let f : X → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s)
  let F : X → ℝ≥0∞ := fun y =>
    B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k,
        (ball x (1/(2:ℝ)^(g+j))).indicator
          (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
  have hpoint : B.indicator f ≤ F := by
    intro y
    change B.indicator f y ≤ B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy,show B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y =
        ENNReal.ofReal (((2:ℝ)^g)^s) from indicator_of_mem hy _]
      have hi := inverse_power_dyadic (s := s)
        (by positivity : 0 < dist x y+1/(2:ℝ)^(g+k)) hs g k
        (by linarith [dist_nonneg (x := x) (y := y)])
      have hh := ENNReal.ofReal_le_ofReal hi
      rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)] at hh
      apply hh.trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      by_cases hdist : dist x y+1/(2:ℝ)^(g+k) < 1/(2:ℝ)^(g+j)
      · rw [ite_eq_left hdist]
        have hyj : y ∈ ball x (1/(2:ℝ)^(g+j)) := by
          rw [mem_ball,dist_comm]
          linarith [show (0:ℝ) < 1/(2:ℝ)^(g+k) by positivity]
        rw [indicator_of_mem hyj]
      · rw [ite_eq_right hdist,ENNReal.ofReal_zero]
        exact bot_le
    · rw [indicator_of_notMem hy]
      exact bot_le
  rw [← lintegral_indicator measurableSet_ball]
  apply (lintegral_mono hpoint).trans_eq
  change (∫⁻ y, B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y ∂μ) = _
  rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
    lintegral_indicator_const measurableSet_ball,
    lintegral_finsetSum _ (fun j _ => measurable_const.indicator measurableSet_ball)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_indicator_const measurableSet_ball _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric summation above the inverse-kernel exponent -/

namespace Falconer

theorem dyadic_potential_weight (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^(n+1))^s)*(1/(2:ℝ)^n)^q =
      (2:ℝ)^s*(((2:ℝ)^n)^(s-q)) := by
  rw [pow_succ,Real.mul_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2),
    one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_start (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^n)^s)*(1/(2:ℝ)^n)^q = (((2:ℝ)^n)^(s-q)) := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_series (g k : ℕ) {s q : ℝ} (hsq : s < q) :
    (∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q))) ≤
      (((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q)) := by
  let a := (2:ℝ)^(s-q)
  have ha : 0 ≤ a := by positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsq)
  have hsum : ∑ j ∈ Finset.range k, a^j ≤ (1-a)⁻¹ := by
    rw [← tsum_geometric_of_lt_one ha ha1]
    exact (summable_geometric_of_lt_one ha ha1).sum_le_tsum _ (fun _ _ => pow_nonneg ha _)
  have he (j : ℕ) : (((2:ℝ)^(g+j))^(s-q)) = (((2:ℝ)^g)^(s-q))*a^j := by
    rw [pow_add,Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    dsimp [a]
    rw [← Real.rpow_natCast_mul (by norm_num),← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by rw [div_eq_mul_inv])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialFrostman
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale ball bounds control the regularized slicing potential -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_frostman (μ : Measure X) (x : X)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  apply (regularized_potential_dyadic μ x hs g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^s)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^s)*(1/(2:ℝ)^g)^q) := by ring
          _ = _ := by rw [dyadic_potential_start]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^s)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = _ := by rw [dyadic_potential_weight]; ring
  calc
    _ ≤ ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q)))+
        ∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))+
        K*(2:ℝ)^s*(∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q)))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),Finset.mul_sum]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (dyadic_potential_series g k hsq)
        (show 0 ≤ K*(2:ℝ)^s by positivity)
      calc
        _ ≤ K*(((2:ℝ)^g)^(s-q))+K*(2:ℝ)^s*
            ((((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q))) := add_le_add le_rfl hh
        _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic inverse potentials of a nonnegative measurable geometric statistic -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem regularized_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  have hpre (j : ℕ) : a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^j) = {x | a x < 1/(2:ℝ)^j} := by
    ext x
    simp only [mem_preimage,mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (ha0 x),mem_ofPred_eq]
  have hball (j : ℕ) (hj : j ≤ g+k) :
      (Measure.map a μ) (ball (0:ℝ) (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (K*(1/(2:ℝ)^j)^q) := by
    rw [Measure.map_apply ha measurableSet_ball,hpre]
    exact hsmall j hj
  have hh := regularized_potential_frostman (Measure.map a μ) (0:ℝ) hK hs hsq g k hball
  have hf : Measurable (fun z : ℝ =>
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s)) := by fun_prop
  have he : (∫⁻ z in ball (0:ℝ) (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s) ∂Measure.map a μ) =
      ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,lintegral_map
      (hf.indicator measurableSet_ball) ha,
      ← lintegral_indicator (measurableSet_lt ha measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : a x < 1/(2:ℝ)^g
    · have hz : a x ∈ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∈ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_mem hz,indicator_of_mem (show x ∈ {x | a x < 1/(2:ℝ)^g} from hx)]
      simp only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (ha0 x)]
    · have hz : a x ∉ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∉ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_notMem hz,indicator_of_notMem (show x ∉ {x | a x < 1/(2:ℝ)^g} from hx)]
  rw [he] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TruncatedScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The maximum-truncated kernel and its dyadic sublevel bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem inverse_max_le_two_inverse_add {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    1/max x r ≤ 2/(x+r) := by
  apply (div_le_div_iff₀ (hr.trans_le (le_max_right x r)) (by positivity)).mpr
  have h₁ := le_max_left x r
  have h₂ := le_max_right x r
  linarith

theorem truncated_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (a x) (1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal ((2:ℝ)^s*(K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q))))) := by
  have hp (x : X) : (1/max (a x) (1/(2:ℝ)^(g+k)))^s ≤
      (2:ℝ)^s*(1/(a x+1/(2:ℝ)^(g+k)))^s := by
    have hax := ha0 x
    calc
      _ ≤ (2/(a x+1/(2:ℝ)^(g+k)))^s := Real.rpow_le_rpow (by positivity)
        (inverse_max_le_two_inverse_add (ha0 x) (by positivity)) hs
      _ = _ := by
        rw [show 2/(a x+1/(2:ℝ)^(g+k)) = 2*(1/(a x+1/(2:ℝ)^(g+k))) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal ((2:ℝ)^s)*(∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal
        (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) :=
      mul_le_mul' le_rfl (regularized_scalar_potential μ a ha ha0 hK hs hsq g k hsmall)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteCountingPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite point potential needed by the elementary planar incidence bound. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem planarCountingMeasure_apply (P : Finset (Space 2)) (A : Set (Space 2)) :
    planarCountingMeasure P A = (P.filter (fun x => x ∈ A)).card := by
  rw [planarCountingMeasure,Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  rw [← Finset.sum_filter]
  simp

theorem planarCountingMeasure_lintegral (P : Finset (Space 2)) (f : Space 2 → ℝ≥0∞) :
    (∫⁻ x, f x ∂planarCountingMeasure P) = ∑ x ∈ P, f x := by
  rw [planarCountingMeasure,lintegral_finsetSum_measure]
  simp only [lintegral_dirac]

theorem finite_dyadic_truncated_potential (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)) ≤
      P.card + ENNReal.ofReal ((2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f)))) := by
  let μ := planarCountingMeasure P
  have hsmall (j : ℕ) (hj : j ≤ 0+N) :
      μ {y | dist x y < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((K*(P.card : ℝ))*(1/(2:ℝ)^j)^f) := by
    rw [planarCountingMeasure_apply]
    have hr0 : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by simpa using hj)
    have hr1 : 1/(2:ℝ)^j ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact one_le_pow₀ (by norm_num)
    have hs : P.filter (fun y => dist x y < 1/(2:ℝ)^j) ⊆
        P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j) := by
      intro y hy
      obtain ⟨hyP,hy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyP,by simpa only [dist_comm] using hy.le⟩
    have hc := (show ((P.filter (fun y => dist x y < 1/(2:ℝ)^j)).card : ℝ) ≤
      (P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j)).card from by exact_mod_cast Finset.card_le_card hs)
    have hh := hc.trans (hball x _ hr0 hr1)
    rw [show (K*(P.card : ℝ))*(1/(2:ℝ)^j)^f = K*(1/(2:ℝ)^j)^f*(P.card : ℝ) by ring]
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hlocal := truncated_scalar_potential μ (fun y => dist x y) (by fun_prop)
    (fun _ => dist_nonneg) (mul_nonneg hK (Nat.cast_nonneg _)) hb hbf 0 N hsmall
  simp only [pow_zero,one_div_one,zero_add,Real.one_rpow,mul_one] at hlocal
  let A := {y : Space 2 | dist x y < 1}
  let F := fun y : Space 2 => ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)
  have hfar : (∫⁻ y in Aᶜ, F y ∂μ) ≤ P.card := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by measurability)
        intro y hy
        change ¬ dist x y < 1 at hy
        have hd : 1 ≤ max (dist x y) (1/(2:ℝ)^N) :=
          (le_of_not_gt hy).trans (le_max_left _ _)
        have hinv : 1/max (dist x y) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr ((Real.rpow_le_rpow (by positivity) hinv hb).trans_eq (Real.one_rpow _))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = P.card := by rw [planarCountingMeasure_apply]; simp
  rw [← planarCountingMeasure_lintegral]
  change (∫⁻ y, F y ∂μ) ≤ _
  rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
  simpa only [mul_assoc,add_comm] using add_le_add hlocal hfar

theorem planarPotentialConstant_pos {b f : ℝ} (hbf : b < f) :
    0 < planarPotentialConstant b f := by
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  unfold planarPotentialConstant
  positivity

theorem finite_dyadic_truncated_potential_real (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 1 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, (1/max (dist x y) (1/(2:ℝ)^N))^b) ≤
      K*planarPotentialConstant b f*(P.card : ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  have hR : 0 ≤ (P.card : ℝ)+(2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by
    positivity
  have hh := finite_dyadic_truncated_potential P x N hK0 hb hbf hball
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity),
    ← ENNReal.ofReal_natCast P.card, ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity)] at hh
  have hh' := (ENNReal.ofReal_le_ofReal_iff hR).mp hh
  apply hh'.trans
  unfold planarPotentialConstant
  have hC : 0 ≤ (2:ℝ)^b*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) P.card]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic potential bound at the critical ball exponent

Unlike the strictly subcritical energy estimate, the finite critical estimate
has one bounded contribution per dyadic scale. It is used on the outer
intervals of the radial profile argument.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_critical (μ : Measure X) (x : X)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q) := by
  apply (regularized_potential_dyadic μ x hq g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^q)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal K := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^q)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^q)*(1/(2:ℝ)^g)^q) := by ring
          _ = K := by rw [dyadic_potential_start,sub_self,Real.rpow_zero,mul_one]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^q) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*
          ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^q)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = K*(2:ℝ)^q := by
            rw [dyadic_potential_weight,sub_self,Real.rpow_zero,mul_one]
  calc
    _ ≤ ENNReal.ofReal K+∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^q) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = _ := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Critical dyadic inverse potentials of a nonnegative statistic -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem regularized_scalar_potential_critical (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q) := by
  have hpre (j : ℕ) : a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^j) = {x | a x < 1/(2:ℝ)^j} := by
    ext x
    simp only [mem_preimage,mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (ha0 x),mem_ofPred_eq]
  have hball (j : ℕ) (hj : j ≤ g+k) :
      (Measure.map a μ) (ball (0:ℝ) (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (K*(1/(2:ℝ)^j)^q) := by
    rw [Measure.map_apply ha measurableSet_ball,hpre]
    exact hsmall j hj
  have hh := regularized_potential_critical (Measure.map a μ) (0:ℝ) hq g k hball
  have hf : Measurable (fun z : ℝ =>
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^q)) := by fun_prop
  have he : (∫⁻ z in ball (0:ℝ) (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^q) ∂Measure.map a μ) =
      ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,lintegral_map
      (hf.indicator measurableSet_ball) ha,
      ← lintegral_indicator (measurableSet_lt ha measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : a x < 1/(2:ℝ)^g
    · have hz : a x ∈ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∈ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_mem hz,indicator_of_mem (show x ∈ {x | a x < 1/(2:ℝ)^g} from hx)]
      simp only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (ha0 x)]
    · have hz : a x ∉ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∉ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_notMem hz,indicator_of_notMem (show x ∉ {x | a x < 1/(2:ℝ)^g} from hx)]
  rw [he] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalTruncatedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Critical maximum-truncated potentials with logarithmic scale loss -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem truncated_scalar_potential_critical (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (a x) (1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal ((2:ℝ)^q)*
        (ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q)) := by
  have hp (x : X) : (1/max (a x) (1/(2:ℝ)^(g+k)))^q ≤
      (2:ℝ)^q*(1/(a x+1/(2:ℝ)^(g+k)))^q := by
    have hax := ha0 x
    calc
      _ ≤ (2/(a x+1/(2:ℝ)^(g+k)))^q := Real.rpow_le_rpow (by positivity)
        (inverse_max_le_two_inverse_add (ha0 x) (by positivity)) hq
      _ = _ := by
        rw [show 2/(a x+1/(2:ℝ)^(g+k)) = 2*(1/(a x+1/(2:ℝ)^(g+k))) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((2:ℝ)^q)*ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal ((2:ℝ)^q)*(∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl
      (regularized_scalar_potential_critical μ a ha ha0 hq g k hsmall)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteCriticalPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The critical dyadic potential of a finite scalar statistic, with one
explicit contribution per scale. This is used for the average projected
energy of a planar point set. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem scalarCountingMeasure_apply (I : Finset ℝ) (A : Set ℝ) :
    scalarCountingMeasure I A = (I.filter (fun c => c ∈ A)).card := by
  rw [scalarCountingMeasure,Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  rw [← Finset.sum_filter]
  simp

theorem scalarCountingMeasure_lintegral (I : Finset ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ c, f c ∂scalarCountingMeasure I) = ∑ c ∈ I, f c := by
  rw [scalarCountingMeasure,lintegral_finsetSum_measure]
  simp only [lintegral_dirac]

theorem finite_critical_statistic (I : Finset ℝ) (a : ℝ → ℝ)
    (ha : Measurable a) (ha0 : ∀ c, 0 ≤ a c) (N : ℕ) {s C : ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hsmall : ∀ j : ℕ, j ≤ N →
      ((I.filter fun c => a c < 1/(2:ℝ)^j).card:ℝ) ≤ C*(1/(2:ℝ)^j)^s) :
    (∑ c ∈ I, (1/max (a c) (1/(2:ℝ)^N))^s) ≤
      (I.card:ℝ)+(2:ℝ)^s*(C+(N:ℝ)*(C*(2:ℝ)^s)) := by
  let μ := scalarCountingMeasure I
  let A := {c : ℝ | a c < 1}
  let F := fun c => ENNReal.ofReal ((1/max (a c) (1/(2:ℝ)^N))^s)
  have hcounts (j : ℕ) (hj : j ≤ 0+N) :
      μ {c | a c < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (C*(1/(2:ℝ)^j)^s) := by
    rw [scalarCountingMeasure_apply]
    have hh := ENNReal.ofReal_le_ofReal (hsmall j (by simpa using hj))
    simpa only [ENNReal.ofReal_natCast,Set.mem_ofPred_eq] using hh
  have hnear := truncated_scalar_potential_critical μ a ha ha0 hs 0 N hcounts
  simp only [pow_zero,one_div_one,zero_add] at hnear
  have hfar : (∫⁻ c in Aᶜ, F c ∂μ) ≤ (I.card:ℝ≥0∞) := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1:ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by dsimp [A]; measurability)
        intro c hc
        have hc1 : 1 ≤ a c := le_of_not_gt hc
        have hd : 1 ≤ max (a c) (1/(2:ℝ)^N) := hc1.trans (le_max_left _ _)
        have hi : 1/max (a c) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr
          ((Real.rpow_le_rpow (by positivity) hi hs).trans_eq (Real.one_rpow s))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = I.card := by rw [scalarCountingMeasure_apply]; simp
  have htotal : (∑ c ∈ I, F c) ≤ (I.card:ℝ≥0∞)+
      ENNReal.ofReal ((2:ℝ)^s)*(ENNReal.ofReal C+(N:ℝ≥0∞)*ENNReal.ofReal (C*(2:ℝ)^s)) := by
    rw [← scalarCountingMeasure_lintegral]
    change (∫⁻ c, F c ∂μ) ≤ _
    rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
    exact (add_le_add hnear hfar).trans_eq (add_comm _ _)
  change (∑ c ∈ I, ENNReal.ofReal ((1/max (a c) (1/(2:ℝ)^N))^s)) ≤ _ at htotal
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)] at htotal
  have he : ENNReal.ofReal ((I.card:ℝ)+(2:ℝ)^s*(C+(N:ℝ)*(C*(2:ℝ)^s))) =
      (I.card:ℝ≥0∞)+ENNReal.ofReal ((2:ℝ)^s)*
        (ENNReal.ofReal C+(N:ℝ≥0∞)*ENNReal.ofReal (C*(2:ℝ)^s)) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity),
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add hC (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    simp only [ENNReal.ofReal_natCast]
  rw [← he] at htotal
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htotal

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteProjectionPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite projected-energy average used for the good projections in
Orponen--Shmerkin, Appendix A.4. The critical directional loss is linear in
the dyadic depth; the planar point potential is strictly subcritical. -/
namespace Falconer
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_projection_potential (N : ℕ) {s K : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (I : Finset ℝ) (hI : ∀ c ∈ I, |c| ≤ 1)
    (hball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass I u r ≤ K*r^s*(I.card:ℝ))
    (p q : Space 2) (hdiam : dist p q ≤ 4) :
    (∑ c ∈ I, (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s) ≤
      (I.card:ℝ)+(2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*
        (K*(8/max (dist p q) (1/(2:ℝ)^N))^s*(I.card:ℝ)) := by
  let δ := 1/(2:ℝ)^N
  let D := max (dist p q) δ
  let C := K*(8/D)^s*(I.card:ℝ)
  let a := fun c => |lineParameterProjection c p-lineParameterProjection c q|
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hD : 0 < D := hδ.trans_le (le_max_right _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcounts (j : ℕ) (hj : j ≤ N) :
      ((I.filter fun c => a c < 1/(2:ℝ)^j).card:ℝ) ≤ C*(1/(2:ℝ)^j)^s := by
    have hr : δ ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hj
    have hh := finite_projection_sublevel hδ hr hs hK I hI hball p q hdiam
    have hsub : I.filter (fun c => a c < 1/(2:ℝ)^j) ⊆
        I.filter (fun c => a c ≤ 1/(2:ℝ)^j) :=
      by
        intro c hc
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2.le⟩
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    apply hh.trans_eq
    change K*(8*(1/(2:ℝ)^j)/D)^s*(I.card:ℝ) = _
    rw [show 8*(1/(2:ℝ)^j)/D = (8/D)*(1/(2:ℝ)^j) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    dsimp [C]
    ring
  have ha : Measurable a := by dsimp [a,lineParameterProjection]; fun_prop
  have hh := finite_critical_statistic I a ha (fun _ => abs_nonneg _) N hs hC hcounts
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [C,D,δ]
  ring

theorem finite_projection_energy_average (N : ℕ) {s t KI KP : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 1 ≤ KI) (hKP : 1 ≤ KP)
    (I : Finset ℝ) (P : Finset (Space 2))
    (hI : ∀ c ∈ I, |c| ≤ 1) (hP : InBoundedLineChart P)
    (hIball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass I u r ≤ KI*r^s*(I.card:ℝ))
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP P) :
    (∑ c ∈ I, planarProjectionEnergy N s c P) ≤
      (I.card:ℝ)*(P.card:ℝ)^2*
        (1+((2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*KI*(8:ℝ)^s)*KP*planarPotentialConstant s t) := by
  let A := (2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*KI*(8:ℝ)^s
  let k := fun p q : Space 2 => (1/max (dist p q) (1/(2:ℝ)^N))^s
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpair (p : Space 2) (hp : p ∈ P) (q : Space 2) (hq : q ∈ P) :
      (∑ c ∈ I, (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s) ≤
        (I.card:ℝ)+A*(I.card:ℝ)*k p q := by
    have hd : dist p q ≤ 4 := by
      have h0 := abs_sub (p 0) (q 0)
      have h1 := abs_sub (p 1) (q 1)
      have hg := planar_dist_le_coordinate_sum p q
      linarith only [h0,h1,hg,(hP p hp).1,(hP p hp).2,(hP q hq).1,(hP q hq).2]
    have hh := finite_projection_potential N hs hKI I hI hIball p q hd
    apply hh.trans_eq
    rw [show 8/max (dist p q) (1/(2:ℝ)^N) = 8*(1/max (dist p q) (1/(2:ℝ)^N)) by ring,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (by positivity)]
    dsimp [A,k]
    ring
  have hpoint (p : Space 2) : (∑ q ∈ P, k p q) ≤ KP*planarPotentialConstant s t*(P.card:ℝ) :=
    finite_dyadic_truncated_potential_real P p N hKP hs hst hPball
  have hpotential : (∑ p ∈ P, ∑ q ∈ P, k p q) ≤ KP*planarPotentialConstant s t*(P.card:ℝ)^2 := by
    calc
      _ ≤ ∑ _p ∈ P, KP*planarPotentialConstant s t*(P.card:ℝ) := Finset.sum_le_sum fun p _ => hpoint p
      _ = _ := by simp; ring
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ c ∈ I,
        (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s := by
      unfold planarProjectionEnergy
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((I.card:ℝ)+A*(I.card:ℝ)*k p q) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hpair p hp q hq
    _ = (I.card:ℝ)*(P.card:ℝ)^2+A*(I.card:ℝ)*(∑ p ∈ P, ∑ q ∈ P, k p q) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
      ring
    _ ≤ (I.card:ℝ)*(P.card:ℝ)^2+A*(I.card:ℝ)*(KP*planarPotentialConstant s t*(P.card:ℝ)^2) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hpotential (mul_nonneg hA (Nat.cast_nonneg I.card))) _
    _ = _ := by dsimp [A]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GoodProjectionDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At least half of the original direction labels have bounded projected
energy. No direction is replaced and the estimate is uniform over later
subsets of the planar point set. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_low_half {α : Type*} (I : Finset α) (f : α → ℝ) {B : ℝ}
    (hB : 0 < B) (hf : ∀ c ∈ I, 0 ≤ f c)
    (hmean : (∑ c ∈ I, f c) ≤ B*(I.card:ℝ)) :
    (I.card:ℝ)/2 ≤ ((I.filter fun c => f c ≤ 2*B).card:ℝ) := by
  let G := I.filter fun c => f c ≤ 2*B
  let D := I.filter fun c => ¬f c ≤ 2*B
  have hbad : 2*B*(D.card:ℝ) ≤ B*(I.card:ℝ) := by
    calc
      _ = ∑ _c ∈ D, 2*B := by simp; ring
      _ ≤ ∑ c ∈ D, f c := Finset.sum_le_sum fun c hc => (lt_of_not_ge (Finset.mem_filter.mp hc).2).le
      _ ≤ ∑ c ∈ I, f c := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun c hc _ => hf c hc)
      _ ≤ _ := hmean
  have hpart : (G.card:ℝ)+(D.card:ℝ) = I.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := I) (fun c => f c ≤ 2*B)
  have hd : 2*(D.card:ℝ) ≤ I.card := by
    apply (mul_le_mul_iff_right₀ hB).1
    nlinarith only [hbad]
  change (I.card:ℝ)/2 ≤ (G.card:ℝ)
  linarith only [hpart,hd]

theorem projectionEnergyBudget_pos (N : ℕ) {s t KI KP : ℝ}
    (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) :
    0 < projectionEnergyBudget N s t KI KP := by
  have hC := planarPotentialConstant_pos hst
  unfold projectionEnergyBudget
  positivity

theorem good_projection_directions (N : ℕ) {s t KI KP : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 1 ≤ KI) (hKP : 1 ≤ KP)
    (I : Finset ℝ) (P : Finset (Space 2)) (hPne : P.Nonempty)
    (hI : ∀ c ∈ I, |c| ≤ 1) (hP : InBoundedLineChart P)
    (hIball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass I u r ≤ KI*r^s*(I.card:ℝ))
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP P) :
    ∃ J ⊆ I, (I.card:ℝ)/2 ≤ (J.card:ℝ) ∧
      ∀ c ∈ J, planarProjectionEnergy N s c P ≤
        2*projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2 := by
  let B := projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2
  have hPcard : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hPne.card_pos
  have hB : 0 < B := mul_pos
    (projectionEnergyBudget_pos N hst (zero_le_one.trans hKI) (zero_le_one.trans hKP))
    (sq_pos_of_pos hPcard)
  have hmean : (∑ c ∈ I, planarProjectionEnergy N s c P) ≤ B*(I.card:ℝ) := by
    have hh := finite_projection_energy_average N hs hst hKI hKP I P hI hP hIball hPball
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B,projectionEnergyBudget]
    ring
  refine ⟨I.filter (fun c => planarProjectionEnergy N s c P ≤ 2*B),Finset.filter_subset _ _,
    finite_low_half I _ hB (fun c _ => ?_) hmean,?_⟩
  · unfold planarProjectionEnergy
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by positivity
  · intro c hc
    have hh := (Finset.mem_filter.mp hc).2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B]
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ProjectedSubsetRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded projected energy controls every large original subset.
After discarding at most half its labels, its projected counting law has
an explicit Frostman bound. Repeated projected coordinates are retained. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem projected_subset_weighted_regular (N : ℕ) {s c B ρ : ℝ}
    (hs : 0 ≤ s) (hB : 0 < B) (hρ : 0 < ρ)
    (P A : Finset (Space 2)) (hP : P.Nonempty) (hAP : A ⊆ P)
    (hsize : ρ*(P.card:ℝ) ≤ (A.card:ℝ))
    (henergy : planarProjectionEnergy N s c P ≤ B*(P.card:ℝ)^2) :
    ∃ S ⊆ A, S.Nonempty ∧ (A.card:ℝ)/2 ≤ (S.card:ℝ) ∧
      ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r →
        ((S.filter fun p => |lineParameterProjection c p-u| ≤ r).card:ℝ) ≤
          ((2*B/ρ)*(2/ρ)*(2:ℝ)^s)*r^s*(S.card:ℝ) := by
  let δ := 1/(2:ℝ)^N
  let k := fun p q : Space 2 =>
    (1/max |lineParameterProjection c p-lineParameterProjection c q| δ)^s
  let f := fun p => ∑ q ∈ P, k p q
  let b := B*(P.card:ℝ)/ρ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hAc : 0 < (A.card:ℝ) := (mul_pos hρ hPc).trans_le hsize
  have hb : 0 < b := by dsimp [b]; positivity
  have hf : ∀ p, 0 ≤ f p := fun p => Finset.sum_nonneg fun q _ => by dsimp [k]; positivity
  have hsum : (∑ p ∈ A, f p) ≤ b*(A.card:ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, f p := Finset.sum_le_sum_of_subset_of_nonneg hAP (fun p _ _ => hf p)
      _ ≤ B*(P.card:ℝ)^2 := henergy
      _ = b*(ρ*(P.card:ℝ)) := by dsimp [b]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize hb.le
  let S := A.filter fun p => f p ≤ 2*b
  have hhalf : (A.card:ℝ)/2 ≤ (S.card:ℝ) := finite_low_half A f hb (fun p _ => hf p) hsum
  have hSc : 0 < (S.card:ℝ) := by linarith only [hhalf,hAc]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSc)
  have hSP : S ⊆ P := (Finset.filter_subset _ _).trans hAP
  have hPSc : (P.card:ℝ) ≤ (2/ρ)*(S.card:ℝ) := by
    calc
      _ ≤ (2*(S.card:ℝ))/ρ := (le_div_iff₀ hρ).2 (by linarith only [hsize,hhalf])
      _ = _ := by ring
  refine ⟨S,Finset.filter_subset _ _,hS,hhalf,?_⟩
  intro u r hr
  have hr0 : 0 < r := hδ.trans_le hr
  let F := S.filter fun p => |lineParameterProjection c p-u| ≤ r
  by_cases hF : F.Nonempty
  · obtain ⟨p,hpF⟩ := hF
    obtain ⟨hpS,hpu⟩ := Finset.mem_filter.mp hpF
    have hfp : f p ≤ 2*b := (Finset.mem_filter.mp hpS).2
    have hweight (q : Space 2) (hqF : q ∈ F) : 1 ≤ (2*r)^s*k p q := by
      have hqu := (Finset.mem_filter.mp hqF).2
      have hd : |lineParameterProjection c p-lineParameterProjection c q| ≤ 2*r := by
        have hh := abs_sub_le (lineParameterProjection c p) u (lineParameterProjection c q)
        rw [abs_sub_comm u (lineParameterProjection c q)] at hh
        linarith only [hh,hpu,hqu]
      have hmax : max |lineParameterProjection c p-lineParameterProjection c q| δ ≤ 2*r :=
        max_le hd (by linarith only [hr,hδ])
      have hmaxpos : 0 < max |lineParameterProjection c p-lineParameterProjection c q| δ :=
        hδ.trans_le (le_max_right _ _)
      have hbase : 1 ≤ (2*r)*(1/max |lineParameterProjection c p-lineParameterProjection c q| δ) := by
        rw [mul_one_div]
        exact (le_div_iff₀ hmaxpos).2 (by simpa only [one_mul] using hmax)
      dsimp [k]
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.one_le_rpow hbase hs
    have hcount : (F.card:ℝ) ≤ (2*r)^s*f p := by
      calc
        _ = ∑ _q ∈ F, (1:ℝ) := by simp
        _ ≤ ∑ q ∈ F, (2*r)^s*k p q := Finset.sum_le_sum hweight
        _ = (2*r)^s*∑ q ∈ F, k p q := by rw [Finset.mul_sum]
        _ ≤ (2*r)^s*f p := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hSP)
            (fun q _ _ => by dsimp [k]; positivity)) (by positivity)
    calc
      _ ≤ (2*r)^s*f p := hcount
      _ ≤ (2*r)^s*(2*b) := mul_le_mul_of_nonneg_left hfp (by positivity)
      _ = ((2*r)^s*(2*B/ρ))*(P.card:ℝ) := by dsimp [b]; ring
      _ ≤ ((2*r)^s*(2*B/ρ))*((2/ρ)*(S.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hPSc (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le]; ring
  · change (F.card:ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PointSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Separated point sets from samples with repeated coordinates

A maximal separated subfamily covers the sampled coordinates. The bound
on the multiplicity in a small ball then controls the loss in cardinality.
This is the point-selection step of `ang:planar-measures`.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem exists_separated_cover (S : Finset (Space 2)) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ P : Finset (Space 2), P ⊆ S ∧ FiniteSeparatedAt δ P ∧
      ∀ x ∈ S, ∃ y ∈ P, dist x y ≤ δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp [FiniteSeparatedAt], by simp⟩
  | @insert x S _ ih =>
    obtain ⟨P, hPS, hsep, hcover⟩ := ih
    by_cases hx : ∃ y ∈ P, dist x y ≤ δ
    · refine ⟨P, hPS.trans (Finset.subset_insert _ _), hsep, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact hcover z hz
    · refine ⟨insert x P, Finset.insert_subset_insert x hPS, ?_, ?_⟩
      · intro u hu v hv hne
        rcases Finset.mem_insert.mp hu with hue | huP
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · exact (hne (hue.trans hve.symm)).elim
          · rw [hue]
            exact (lt_of_not_ge (fun h => hx ⟨v, hvP, h⟩)).le
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · rw [hve, dist_comm]
            exact (lt_of_not_ge (fun h => hx ⟨u, huP, h⟩)).le
          · exact hsep u huP v hvP hne
      · intro z hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · exact ⟨x, Finset.mem_insert_self _ _, by simpa only [hzx, dist_self] using hδ⟩
        · obtain ⟨y, hy, hdist⟩ := hcover z hz
          exact ⟨y, Finset.mem_insert_of_mem hy, hdist⟩

/-- Distinct selected coordinates in a ball cannot outnumber the original
sample labels in that ball. -/
theorem selected_points_ball_count {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    (hP : P ⊆ D.image p) (z : Space 2) (r : ℝ) :
    (P.filter (fun x => dist x z ≤ r)).card ≤
      (D.filter (fun i => dist (p i) z ≤ r)).card := by
  classical
  have hsub : P.filter (fun x => dist x z ≤ r) ⊆
      (D.filter (fun i => dist (p i) z ≤ r)).image p := by
    intro x hx
    obtain ⟨hxP, hdist⟩ := Finset.mem_filter.mp hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hP hxP)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hdist⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Covering the original labels by the selected point balls gives the
lower cardinality bound, with all repeated labels counted. -/
theorem selected_points_card_lower {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ L : ℝ} (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hcount : ∀ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) ≤ L) :
    (D.card : ℝ) ≤ (P.card : ℝ) * L := by
  classical
  have hsub : D ⊆ P.biUnion (fun x => D.filter (fun i => dist (p i) x ≤ δ)) := by
    intro i hi
    obtain ⟨x, hx, hdist⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hi, hdist⟩⟩
  calc
    (D.card : ℝ) ≤ ((P.biUnion (fun x => D.filter
        (fun i => dist (p i) x ≤ δ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ P, L := Finset.sum_le_sum hcount
    _ = (P.card : ℝ) * L := by simp

/-- The selected separated point set has the normalized finite ball
bound required by the published Furstenberg theorem. -/
theorem selected_points_normalized_ball_bound {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ K f : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hD : D.Nonempty)
    (hP : P ⊆ D.image p)
    (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hsize : (D.card : ℝ) * δ ^ f ≤ 2)
    (hcount : ∀ z r, δ ≤ r → ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) ≤
      K * (D.card : ℝ) * r ^ f) :
    NormalizedFiniteBallBound δ f (2 * K^2) P := by
  have hn : 0 < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  have hlow := selected_points_card_lower D p P hcover (fun x _ => hcount x δ le_rfl)
  have hbase : 1 ≤ (P.card : ℝ) * K * δ ^ f := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [hlow]
  have hcoef : K * (D.card : ℝ) ≤ (2 * K^2) * (P.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hbase (show 0 ≤ K * (D.card : ℝ) by positivity)
    have hupper := mul_le_mul_of_nonneg_left hsize
      (show 0 ≤ (P.card : ℝ) * K^2 by positivity)
    nlinarith
  intro z r hδr _
  calc
    ((P.filter (fun x => dist x z ≤ r)).card : ℝ) ≤
        ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) := by
      exact_mod_cast selected_points_ball_count D p P hP z r
    _ ≤ K * (D.card : ℝ) * r ^ f := hcount z r hδr
    _ ≤ ((2 * K^2) * (P.card : ℝ)) * r ^ f :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    _ = _ := by ring

theorem exists_separated_point_sample {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) {δ K f : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hD : D.Nonempty)
    (hsize : (D.card : ℝ) * δ ^ f ≤ 2)
    (hcount : ∀ z r, δ ≤ r → ((D.filter (fun i => dist (p i) z ≤ r)).card : ℝ) ≤
      K * (D.card : ℝ) * r ^ f) :
    ∃ P : Finset (Space 2), P.Nonempty ∧ P ⊆ D.image p ∧
      FiniteSeparatedAt δ P ∧ NormalizedFiniteBallBound δ f (2 * K^2) P := by
  obtain ⟨P, hP, hsep, hcover⟩ := exists_separated_cover (D.image p) hδ.le
  have hcover' : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ :=
    fun i hi => hcover (p i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  obtain ⟨i, hi⟩ := hD
  obtain ⟨x, hx, _⟩ := hcover' i hi
  exact ⟨P, ⟨x, hx⟩, hP, hsep,
    selected_points_normalized_ball_bound D p P hδ hK ⟨i, hi⟩ hP hcover' hsize hcount⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SamplingTail
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential tails for sampled incidence counts

The sample-count estimate in `ang:planar-measures` needs an exponential
tail even when the expected count is bounded. Applying Chernoff at the
fixed parameter one gives a sufficient bound without an asymptotic
binomial formula.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators

private theorem exp_indicator_one {Ω : Type*} (A : Set Ω) (ω : Ω) :
    exp (A.indicator (fun _ => (1 : ℝ)) ω) =
      1 + (exp 1 - 1) * A.indicator (fun _ => (1 : ℝ)) ω := by
  classical
  by_cases h : ω ∈ A <;> simp [h]

/-- The exponential moment of a Bernoulli indicator at parameter one. -/
theorem indicator_mgf_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    mgf (A.indicator (fun _ => (1 : ℝ))) μ 1 = 1 + (exp 1 - 1) * μ.real A := by
  classical
  have hI : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  simp only [mgf, one_mul, exp_indicator_one]
  rw [integral_add (integrable_const 1) (hI.const_mul (exp 1 - 1)),
    integral_const_mul, integral_indicator_const (1 : ℝ) hA]
  simp

/-- The tail bound retains the actual small mean of each indicator. -/
theorem independent_indicator_sum_tail {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : iIndepFun (fun i => (A i).indicator (fun _ => (1 : ℝ))) μ)
    (S : Finset ι) {p T : ℝ} (_hp : 0 ≤ p) (hprob : ∀ i ∈ S, μ.real (A i) ≤ p) :
    μ.real {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
      exp ((S.card : ℝ) * (exp 1 - 1) * p - T) := by
  classical
  let X : ι → Ω → ℝ := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hmeas : ∀ i, Measurable (X i) := fun i => measurable_const.indicator (hA i)
  have hint : ∀ i ∈ S, Integrable (fun ω => exp (1 * X i ω)) μ := by
    intro i _
    apply integrable_exp_mul_of_le 1 1 (by norm_num) (hmeas i).aemeasurable
    exact ae_of_all _ fun ω => by
      by_cases h : ω ∈ A i <;> simp [X, h]
  have hsumint := hindep.integrable_exp_mul_sum hmeas hint
  have hexp : 0 ≤ exp 1 - 1 := by
    have := exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
    rw [exp_zero] at this
    linarith
  have hbound : ∀ i ∈ S, mgf (X i) μ 1 ≤ exp ((exp 1 - 1) * p) := by
    intro i hi
    rw [indicator_mgf_one μ (A i) (hA i)]
    calc
      1 + (exp 1 - 1) * μ.real (A i) ≤ 1 + (exp 1 - 1) * p := by
        gcongr
        exact hprob i hi
      _ ≤ exp ((exp 1 - 1) * p) := by simpa [add_comm] using add_one_le_exp ((exp 1 - 1) * p)
  have hprod : mgf (∑ i ∈ S, X i) μ 1 ≤ exp ((S.card : ℝ) * (exp 1 - 1) * p) := by
    rw [hindep.mgf_sum hmeas]
    calc
      ∏ i ∈ S, mgf (X i) μ 1 ≤ ∏ _i ∈ S, exp ((exp 1 - 1) * p) :=
        Finset.prod_le_prod (fun _ _ => mgf_nonneg) hbound
      _ = exp ((S.card : ℝ) * (exp 1 - 1) * p) := by
        rw [← exp_sum]
        simp [mul_assoc]
  have htail := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ S, X i) T
    (show (0 : ℝ) ≤ 1 by norm_num) hsumint
  calc
    μ.real {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
        exp (-1 * T) * mgf (∑ i ∈ S, X i) μ 1 := by
      simpa only [Finset.sum_apply, X] using htail
    _ ≤ exp (-1 * T) * exp ((S.card : ℝ) * (exp 1 - 1) * p) :=
      mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp ((S.card : ℝ) * (exp 1 - 1) * p - T) := by
      rw [← exp_add]
      congr 1
      ring

/-- A threshold exceeding the exponential-moment mean by `L` fails with
probability at most `exp (-L)`. -/
theorem independent_indicator_sum_tail_le {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hindep : iIndepFun (fun i => (A i).indicator (fun _ => (1 : ℝ))) μ)
    (S : Finset ι) {p T L : ℝ} (hp : 0 ≤ p) (hprob : ∀ i ∈ S, μ.real (A i) ≤ p)
    (hT : (S.card : ℝ) * (exp 1 - 1) * p + L ≤ T) :
    μ {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
      ENNReal.ofReal (exp (-L)) := by
  have h := (independent_indicator_sum_tail μ A hA hindep S hp hprob).trans
    (exp_le_exp.mpr (by linarith : (S.card : ℝ) * (exp 1 - 1) * p - T ≤ -L))
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal h

/-- Simultaneous sample-count bounds over any fixed finite collection of
cells. Independence is required only among the draws for each cell. -/
theorem finite_sample_count_failure {Ω ι κ : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Finset κ) (S : Finset ι) (A : κ → ι → Set Ω)
    (hA : ∀ j i, MeasurableSet (A j i))
    (hindep : ∀ j ∈ B,
      iIndepFun (fun i => (A j i).indicator (fun _ => (1 : ℝ))) μ)
    (p T : κ → ℝ) (L : ℝ) (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, ∀ i ∈ S, μ.real (A j i) ≤ p j)
    (hT : ∀ j ∈ B, (S.card : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
    μ (⋃ j ∈ B, {ω | T j ≤ ∑ i ∈ S, (A j i).indicator (fun _ => (1 : ℝ)) ω}) ≤
      ENNReal.ofReal ((B.card : ℝ) * exp (-L)) := by
  calc
    _ ≤ ∑ j ∈ B,
        μ {ω | T j ≤ ∑ i ∈ S, (A j i).indicator (fun _ => (1 : ℝ)) ω} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ B, ENNReal.ofReal (exp (-L)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact independent_indicator_sum_tail_le μ (A j) (hA j) (hindep j hj) S
        (hp j hj) (hprob j hj) (hT j hj)
    _ = _ := by simp [ENNReal.ofReal_mul, Nat.cast_nonneg]

/-- A small exceptional family of samples cannot carry all the expected
incidence. This is the probabilistic-method selection used after the
simultaneous count bound. -/
theorem exists_good_sample_incidence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Ω → ℝ) (hJ : Integrable J μ)
    (hJone : ∀ ω, J ω ≤ 1) (B : Set Ω) (hB : MeasurableSet B)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ ω, J ω ∂μ)
    (hbad : μ.real B ≤ I / 4) :
    ∃ ω ∉ B, I / 2 ≤ J ω := by
  classical
  by_contra h
  push Not at h
  have hpoint : ∀ ω, J ω ≤ I / 2 + B.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · simp only [indicator_of_mem hω]
      linarith [hJone ω]
    · simp only [indicator_of_notMem hω, add_zero]
      exact (h ω hω).le
  have hbound : (∫ ω, J ω ∂μ) ≤ I / 2 + μ.real B := by
    calc
      (∫ ω, J ω ∂μ) ≤ ∫ ω, I / 2 + B.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_mono hJ ((integrable_const _).add ((integrable_const 1).indicator hB)) hpoint
      _ = _ := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hB),
          integral_indicator_const (1 : ℝ) hB]
        simp
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_IidSampling
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent sampling of direction and point labels

The finite product law below samples the original labels, before their
geometric coordinates are taken. Repeated coordinates therefore retain
their original incidence fibers, as required by `ang:planar-measures`.
-/

namespace Falconer
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators

theorem measurable_iidCount {X : Type*} [MeasurableSpace X] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) : Measurable (iidCount A (n := n)) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hA).comp (measurable_pi_apply i)

private theorem iid_cell_mass {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) (i : Fin n) (A : Set X) (hA : MeasurableSet A) :
    (iidLaw ν n).real {ω | ω i ∈ A} = (ν : Measure X).real A := by
  have hmass : iidLaw ν n {ω | ω i ∈ A} = (ν : Measure X) A := by
    calc
      iidLaw ν n {ω | ω i ∈ A} =
          ((iidLaw ν n).map (Function.eval i)) A :=
        (Measure.map_apply (measurable_pi_apply i) hA).symm
      _ = (ν : Measure X) A := by
        simpa only [iidLaw] using congrArg (fun μ : Measure X => μ A)
          (measurePreserving_eval (fun _ : Fin n => (ν : Measure X)) i).map_eq
  exact congrArg ENNReal.toReal hmass

private theorem iid_indicators_independent {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (n : ℕ) (A : Set X) (hA : MeasurableSet A) :
    iIndepFun (fun i : Fin n => {ω : Fin n → X | ω i ∈ A}.indicator
      (fun _ => (1 : ℝ))) (iidLaw ν n) := by
  have h := iIndepFun_pi (μ := fun _ : Fin n => (ν : Measure X))
    (X := fun _ : Fin n => A.indicator (fun _ => (1 : ℝ)))
    (fun _ => (measurable_const.indicator hA).aemeasurable)
  have heq : (fun (i : Fin n) (ω : Fin n → X) =>
      {ω : Fin n → X | ω i ∈ A}.indicator (fun _ => (1 : ℝ)) ω) =
      (fun (i : Fin n) (ω : Fin n → X) => A.indicator (fun _ => (1 : ℝ)) (ω i)) := by
    funext i ω
    by_cases hω : ω i ∈ A <;> simp [hω]
  rw [heq]
  exact h

/-- Counts are simultaneously controlled on every prescribed measurable
cell, with an exponentially small failure probability. -/
theorem iid_finite_cells_tail {X κ : Type*} [MeasurableSpace X] [DecidableEq κ]
    (ν : ProbabilityMeasure X) (n : ℕ) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
    (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ p j)
    (hT : ∀ j ∈ B, (n : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
    iidLaw ν n (⋃ j ∈ B, {ω | T j ≤ iidCount (A j) ω}) ≤
      ENNReal.ofReal ((B.card : ℝ) * exp (-L)) := by
  classical
  have h := finite_sample_count_failure (iidLaw ν n) B (Finset.univ : Finset (Fin n))
    (fun j i => {ω : Fin n → X | ω i ∈ A j})
    (fun j i => (hA j).preimage (measurable_pi_apply i))
    (fun j _ => iid_indicators_independent ν n (A j) (hA j)) p T L hp
    (fun j hj i _ => (iid_cell_mass ν n i (A j) (hA j)).trans_le (hprob j hj))
    (by simpa using hT)
  have heq : ∀ j (ω : Fin n → X),
      (∑ i : Fin n, {ω : Fin n → X | ω i ∈ A j}.indicator (fun _ => (1 : ℝ)) ω) =
      iidCount (A j) ω := by
    intro j ω
    apply Finset.sum_congr rfl
    intro i _
    by_cases hω : ω i ∈ A j <;> simp [hω]
  simpa only [heq] using h

theorem integrable_iidAverage {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) {f : X → ℝ} (hf : Integrable f (ν : Measure X)) (n : ℕ) :
    Integrable (iidAverage f (n := n)) (iidLaw ν n) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact integrable_comp_eval hf

theorem integral_iidAverage {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) {f : X → ℝ} (hf : Integrable f (ν : Measure X))
    {n : ℕ} (hn : 0 < n) :
    (∫ ω, iidAverage f ω ∂iidLaw ν n) = ∫ x, f x ∂(ν : Measure X) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heval (i : Fin n) : (∫ ω, f (ω i) ∂iidLaw ν n) = ∫ x, f x ∂(ν : Measure X) := by
    exact integral_comp_eval (μ := fun _ : Fin n => (ν : Measure X)) hf.aestronglyMeasurable
  simp only [iidAverage]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [heval]
    simp [hnR]
  · intro i _
    exact integrable_comp_eval hf

theorem iidAverage_le_one {X : Type*} (f : X → ℝ) (hf : ∀ x, f x ≤ 1)
    {n : ℕ} (hn : 0 < n) (ω : Fin n → X) : iidAverage f ω ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold iidAverage
  calc
    (n : ℝ)⁻¹ * ∑ i : Fin n, f (ω i) ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ => hf _)) (inv_nonneg.mpr hnR.le)
    _ = 1 := by simp [hnR.ne']

/-- Simultaneous cell bounds and at least half the expected incidence can
be achieved by one sample of the original labels. -/
theorem exists_iid_sample_with_counts_and_incidence {X κ : Type*}
    [MeasurableSpace X] [DecidableEq κ] (ν : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
    (hp : ∀ j ∈ B, 0 ≤ p j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ p j)
    (hT : ∀ j ∈ B, (n : ℝ) * (exp 1 - 1) * p j + L ≤ T j)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (B.card : ℝ) * exp (-L) ≤ I / 4) :
    ∃ ω : Fin n → X,
      (∀ j ∈ B, iidCount (A j) ω < T j) ∧ I / 2 ≤ iidAverage f ω := by
  classical
  let Bad : Set (Fin n → X) := ⋃ j ∈ B, {ω | T j ≤ iidCount (A j) ω}
  have hBad : MeasurableSet Bad := MeasurableSet.biUnion B.countable_toSet fun j _ =>
    measurableSet_le measurable_const (measurable_iidCount (hA j) n)
  have hmass : (iidLaw ν n).real Bad ≤ I / 4 := by
    have h := (iid_finite_cells_tail ν n B A hA p T L hp hprob hT).trans
      (ENNReal.ofReal_le_ofReal hsmall)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [Bad, measureReal_def,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ I / 4)] using hr
  obtain ⟨ω, hω, hinc⟩ := exists_good_sample_incidence (iidLaw ν n) (iidAverage f)
    (integrable_iidAverage ν hf n) (iidAverage_le_one f hf1 hn) Bad hBad hI
    (by simpa only [integral_iidAverage ν hf hn] using hmean) hmass
  refine ⟨ω, ?_, hinc⟩
  intro j hj
  apply lt_of_not_ge
  intro hbad
  exact hω (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hbad⟩⟩)

/-- For cell masses at most `K * s`, only the additive term `L` in the
sampling constant is needed to pay for simultaneous control, provided
the expected scale count `n * s` is at least one. -/
theorem exists_iid_sample_scale_counts {X κ : Type*}
    [MeasurableSpace X] [DecidableEq κ] (ν : ProbabilityMeasure X)
    {n : ℕ} (hn : 0 < n) (B : Finset κ) (A : κ → Set X)
    (hA : ∀ j, MeasurableSet (A j)) (s : κ → ℝ) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hscale : ∀ j ∈ B, 1 ≤ (n : ℝ) * s j)
    (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ K * s j)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    {I : ℝ} (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (B.card : ℝ) * exp (-L) ≤ I / 4) :
    ∃ ω : Fin n → X,
      (∀ j ∈ B, iidCount (A j) ω < ((exp 1 - 1) * K + L) * (n : ℝ) * s j) ∧
      I / 2 ≤ iidAverage f ω := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply exists_iid_sample_with_counts_and_incidence ν hn B A hA (fun j => K * s j)
    (fun j => ((exp 1 - 1) * K + L) * (n : ℝ) * s j) L _ hprob _ f hf hf1 hI hmean hsmall
  · intro j hj
    have hs : 0 ≤ s j := by nlinarith [hscale j hj]
    exact mul_nonneg hK hs
  · intro j hj
    have hLs := mul_le_mul_of_nonneg_left (hscale j hj) hL
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SamplingGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite planar query balls for simultaneous iid estimates

Rounding one point of a ball to the spatial mesh and rounding its radius
up to an integer mesh multiple gives a query ball with radius at most
eight times the original radius. The number of queries is polynomial in
the reciprocal mesh. This is the finite-grid step in `ang:sample-caps`.
-/

namespace Falconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem planarGrid_card (L : ℕ) : (planarGrid L).card = (2*L+1)^2 := by
  have hc : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  simp [planarGrid, Fintype.card_piFinset, hc]

theorem planar_mesh_approximation {δ : ℝ} (hδ : 0 < δ) {L : ℕ}
    (hL : δ⁻¹ + 1 ≤ L) (x : Space 2) (hx : ∀ i, |x i| ≤ 1) :
    ∃ z ∈ planarGrid L, dist x (planarMesh δ z) ≤ 2*δ := by
  let z : Fin 2 → ℤ := fun i => ⌊x i / δ⌋
  have hcoord (i : Fin 2) : 0 ≤ x i - δ * (z i : ℝ) ∧
      x i - δ * (z i : ℝ) ≤ δ := by
    have hf := Int.floor_le (x i / δ)
    have hg := Int.lt_floor_add_one (x i / δ)
    have hf' := (le_div_iff₀ hδ).mp hf
    have hg' := (div_lt_iff₀ hδ).mp hg
    change 0 ≤ x i - δ * (⌊x i / δ⌋ : ℝ) ∧ _
    constructor <;> nlinarith
  have hz : z ∈ planarGrid L := by
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hf := Int.floor_le (x i / δ)
    have hg := Int.lt_floor_add_one (x i / δ)
    have hxb := abs_le.mp (hx i)
    have hd := (div_le_div_iff_of_pos_right hδ).mpr hxb.2
    have hd' := (div_le_div_iff_of_pos_right hδ).mpr hxb.1
    have hr : (-(L : ℝ)) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ L := by
      dsimp [z]
      rw [one_div] at hd
      norm_num only [neg_div, one_div] at hd'
      constructor <;> linarith
    exact_mod_cast hr
  refine ⟨z, hz, ?_⟩
  have hsq (i : Fin 2) : dist (x i) (planarMesh δ z i)^2 ≤ δ^2 := by
    rw [Real.dist_eq, sq_abs]
    change (x i - δ * (z i : ℝ))^2 ≤ δ^2
    exact (sq_le_sq₀ (hcoord i).1 hδ.le).mpr (hcoord i).2
  have hd := EuclideanSpace.dist_sq_eq x (planarMesh δ z)
  simp only [Fin.sum_univ_two] at hd
  nlinarith [hsq 0, hsq 1, dist_nonneg (x := x) (y := planarMesh δ z)]

theorem planarQueries_card (L H : ℕ) :
    (planarQueries L H).card = (2*L+1)^2 * H := by
  simp [planarQueries, planarGrid_card, Int.card_Icc]

theorem planar_ball_query {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr : r ≤ 1)
    {L H : ℕ} (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    {X : Type*} (p : X → Space 2) (hp : ∀ x i, |p x i| ≤ 1)
    (c : Space 2) (x₀ : X) (hx₀ : dist (p x₀) c ≤ r) :
    ∃ j ∈ planarQueries L H,
      {x | dist (p x) c ≤ r} ⊆ {x | dist (p x) (planarMesh δ j.1) ≤ 4*(j.2 : ℝ)*δ} ∧
      δ ≤ 4*(j.2 : ℝ)*δ ∧ 4*(j.2 : ℝ)*δ ≤ 8*r := by
  obtain ⟨z, hz, hclose⟩ := planar_mesh_approximation hδ hL (p x₀) (hp x₀)
  let m : ℤ := ⌈r/δ⌉
  have hmlo : (1 : ℤ) ≤ m := by
    have hh : (0 : ℝ) < r/δ := div_pos (hδ.trans_le hδr) hδ
    exact Int.add_one_le_iff.mpr (Int.ceil_pos.mpr hh)
  have hmhi : m ≤ (H : ℤ) := by
    apply Int.ceil_le.mpr
    have hh := (div_le_div_iff_of_pos_right hδ).mpr hr
    rw [one_div] at hh
    exact hh.trans hH
  have hmr : r ≤ (m : ℝ)*δ :=
    (div_le_iff₀ hδ).mp (Int.le_ceil (r/δ))
  have hmr' : (m : ℝ)*δ ≤ 2*r := by
    have hh := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (r/δ)) hδ
    rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at hh
    change (⌈r/δ⌉ : ℝ)*δ ≤ 2*r
    nlinarith
  refine ⟨(z,m), Finset.mem_product.mpr ⟨hz, Finset.mem_Icc.mpr ⟨hmlo,hmhi⟩⟩, ?_, ?_, ?_⟩
  · intro x hx
    change dist (p x) c ≤ r at hx
    have ht := dist_triangle (p x) c (planarMesh δ z)
    have ht' := dist_triangle c (p x₀) (planarMesh δ z)
    rw [dist_comm c (p x₀)] at ht'
    change dist (p x) (planarMesh δ z) ≤ 4*(m : ℝ)*δ
    nlinarith
  · dsimp only
    nlinarith
  · dsimp only
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_UniformSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform ball bounds for the original sampled labels

The finite query estimate is transferred to every ball, without identifying
labels that happen to have the same spatial coordinate.
-/

namespace Falconer
open Set Metric MeasureTheory Real
attribute [local instance] Classical.propDecidable

theorem iidCount_mono {X : Type*} {A B : Set X} (hAB : A ⊆ B)
    {n : ℕ} (ω : Fin n → X) : iidCount A ω ≤ iidCount B ω := by
  apply Finset.sum_le_sum
  intro i _
  by_cases h : ω i ∈ A
  · simp [h, hAB h]
  · simp only [Set.indicator_of_notMem h]
    by_cases h' : ω i ∈ B <;> simp [h']

theorem iidCount_le_card {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) :
    iidCount A ω ≤ n := by
  have hh : iidCount A ω ≤ iidCount Set.univ ω := iidCount_mono (subset_univ A) ω
  simpa [iidCount] using hh

theorem iidCount_eq_card_filter {X : Type*} (A : Set X) {n : ℕ} (ω : Fin n → X) :
    iidCount A ω = ((Finset.univ.filter (fun i => ω i ∈ A)).card : ℝ) := by
  simp [iidCount, Set.indicator_apply]

theorem uniform_ball_count_of_queries {X : Type*} {n L H : ℕ}
    (ω : Fin n → X) (p : X → Space 2) (hp : ∀ x i, |p x i| ≤ 1)
    {δ s T : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hT : 1 ≤ T)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hq : ∀ j ∈ planarQueries L H,
      iidCount {x | dist (p x) (planarMesh δ j.1) ≤ 4*(j.2 : ℝ)*δ} ω ≤
        T * (n : ℝ) * (4*(j.2 : ℝ)*δ)^s) :
    ∀ c r, δ ≤ r → iidCount {x | dist (p x) c ≤ r} ω ≤
      (T * 8^s) * (n : ℝ) * r^s := by
  intro c r hδr
  have hr0 : 0 < r := hδ.trans_le hδr
  have h8 : (1 : ℝ) ≤ 8^s := Real.one_le_rpow (by norm_num) hs
  by_cases hr : r ≤ 1
  · by_cases hex : ∃ i : Fin n, dist (p (ω i)) c ≤ r
    · obtain ⟨i, hi⟩ := hex
      obtain ⟨j, hj, hsub, hjpos, hjrad⟩ := planar_ball_query hδ hδr hr hL hH p hp c (ω i) hi
      have hh := (iidCount_mono hsub ω).trans (hq j hj)
      have hrpow := Real.rpow_le_rpow (hδ.le.trans hjpos) hjrad hs
      have he : (8*r)^s = (8 : ℝ)^s * r^s := Real.mul_rpow (by norm_num) hr0.le
      calc
        _ ≤ T * (n : ℝ) * (4*(j.2 : ℝ)*δ)^s := hh
        _ ≤ T * (n : ℝ) * (8*r)^s :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ = _ := by rw [he]; ring
    · have hz : iidCount {x | dist (p x) c ≤ r} ω = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        apply Set.indicator_of_notMem
        exact fun hi => hex ⟨i,hi⟩
      rw [hz]
      positivity
  · have hr1 : 1 ≤ r := le_of_not_ge hr
    have hrpow : 1 ≤ r^s := Real.one_le_rpow hr1 hs
    have hcoef : 1 ≤ (T * 8^s) * r^s := by
      have hh : (1 : ℝ) ≤ T * 8^s := one_le_mul_of_one_le_of_one_le hT h8
      exact one_le_mul_of_one_le_of_one_le hh hrpow
    calc
      _ ≤ (n : ℝ) := iidCount_le_card _ ω
      _ ≤ (n : ℝ) * ((T * 8^s) * r^s) := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg n) hcoef
      _ = _ := by ring

/-- Simultaneous ball control and retained empirical incidence. The explicit
failure budget depends only on the polynomial number of grid queries. -/
theorem exists_uniform_ball_sample {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure X) (p : X → Space 2) (hp : Measurable p)
    (hpbound : ∀ x i, |p x i| ≤ 1)
    {n L H : ℕ} (hn : 0 < n) {δ s K B I : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s)
    (hprob : ∀ c r, δ ≤ r →
      (ν : Measure X).real {x | dist (p x) c ≤ r} ≤ K * r^s)
    (f : X → ℝ) (hf : Integrable f (ν : Measure X)) (hf1 : ∀ x, f x ≤ 1)
    (hI : 0 < I) (hmean : I ≤ ∫ x, f x ∂(ν : Measure X))
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ I/4) :
    ∃ ω : Fin n → X,
      (∀ c r, δ ≤ r → iidCount {x | dist (p x) c ≤ r} ω ≤
        (((exp 1 - 1)*K+B) * 8^s) * (n : ℝ) * r^s) ∧
      I/2 ≤ iidAverage f ω := by
  let radius := fun j : (Fin 2 → ℤ) × ℤ => 4*(j.2 : ℝ)*δ
  let A := fun j => {x | dist (p x) (planarMesh δ j.1) ≤ radius j}
  have hrad (j) (hj : j ∈ planarQueries L H) : δ ≤ radius j := by
    have hm : (1 : ℤ) ≤ j.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hj).2).1
    have hm' : (1 : ℝ) ≤ j.2 := by exact_mod_cast hm
    dsimp [radius]
    nlinarith
  have hA (j) : MeasurableSet (A j) :=
    measurableSet_le (hp.dist measurable_const) measurable_const
  obtain ⟨ω, hω, hinc⟩ := exists_iid_sample_scale_counts ν hn
    (planarQueries L H) A hA (fun j => radius j ^ s) hK (zero_le_one.trans hB)
    (fun j hj => hsize.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hδ.le (hrad j hj) hs) (Nat.cast_nonneg n)))
    (fun j hj => hprob _ _ (hrad j hj)) f hf hf1 hI hmean
    (by simpa only [planarQueries_card] using hsmall)
  refine ⟨ω, ?_, hinc⟩
  have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hT : 1 ≤ (exp 1 - 1)*K+B := le_add_of_nonneg_left (mul_nonneg he hK) |>.trans' hB
  exact uniform_ball_count_of_queries ω p hpbound hδ hs hT hL hH
    (fun j hj => (hω j hj).le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform sampling with incidence and good point labels

Both sampling stages use original probability laws. In the point stage,
the good labels are selected after sampling, so no measurable selection or
identification of coincident spatial coordinates is required.
-/

namespace Falconer
open Set MeasureTheory Real
attribute [local instance] Classical.propDecidable

/-- Sample from the original point law, retain the labels in a positive
mass set, and extract a separated point set. Repeated coordinates cost only
the proved ball-count factor. -/
theorem exists_good_separated_point_sample {X : Type*} [MeasurableSpace X]
    (μ : ProbabilityMeasure X) (p : X → Space 2) (hp : Measurable p)
    (hpbound : ∀ x i, |p x i| ≤ 1)
    (G : Set X) (hG : MeasurableSet G) {J : ℝ} (hJ : 0 < J)
    (hGmass : J ≤ (μ : Measure X).real G)
    {n L H : ℕ} (hn : 0 < n) {δ s K B : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hL : δ⁻¹+1 ≤ L) (hH : δ⁻¹ ≤ H)
    (hsize : 1 ≤ (n : ℝ) * δ^s) (hsize' : (n : ℝ) * δ^s ≤ 2)
    (hprob : ∀ c r, δ ≤ r →
      (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ K * r^s)
    (hsmall : (((2*L+1)^2 * H : ℕ) : ℝ) * exp (-B) ≤ J/4) :
    ∃ (ω : Fin n → X) (D : Finset (Fin n)) (P : Finset (Space 2)),
      D.Nonempty ∧ (∀ i ∈ D, ω i ∈ G) ∧ P.Nonempty ∧ P ⊆ D.image (p ∘ ω) ∧
      FiniteSeparatedAt δ P ∧
      NormalizedFiniteBallBound δ s
        (2 * (2 * (((exp 1-1)*K+B) * 8^s) / J)^2) P := by
  classical
  let f := G.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f (μ : Measure X) := (integrable_const 1).indicator hG
  have hf1 (x : X) : f x ≤ 1 := by
    by_cases hx : x ∈ G <;> simp [f, hx]
  have hmean : J ≤ ∫ x, f x ∂(μ : Measure X) := by
    simpa only [f, integral_indicator_const (1 : ℝ) hG, smul_eq_mul, mul_one] using hGmass
  obtain ⟨ω, hcount, havg⟩ := exists_uniform_ball_sample μ p hp hpbound hn
    hδ hs hK hB hL hH hsize hprob f hf hf1 hJ hmean hsmall
  let D := Finset.univ.filter (fun i => ω i ∈ G)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDlow : J / 2 * n ≤ (D.card : ℝ) := by
    have he : iidAverage f ω = (n : ℝ)⁻¹ * (D.card : ℝ) := by
      change (n : ℝ)⁻¹ * iidCount G ω = _
      rw [iidCount_eq_card_filter]
    rw [he] at havg
    have hh := mul_le_mul_of_nonneg_left havg hnR.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul, mul_comm] using hh
  have hDn : D.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos (div_pos hJ (by norm_num)) hnR).trans_le hDlow
  let T : ℝ := ((exp 1-1)*K+B)*8^s
  have hT : 0 < T := by
    have he : 0 ≤ exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
    have hh : 0 < (exp 1-1)*K+B := lt_of_lt_of_le zero_lt_one
      (hB.trans (le_add_of_nonneg_left (mul_nonneg he hK)))
    exact mul_pos hh (Real.rpow_pos_of_pos (by norm_num) _)
  have hcoef : T * n ≤ (2*T/J) * (D.card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hJ).mpr
    have hh := mul_le_mul_of_nonneg_left hDlow (by positivity : 0 ≤ 2*T)
    nlinarith
  have hDC (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
      ((D.filter (fun i => dist ((p ∘ ω) i) c ≤ r)).card : ℝ) ≤
        (2*T/J) * (D.card : ℝ) * r^s := by
    have hsub : D.filter (fun i => dist ((p ∘ ω) i) c ≤ r) ⊆
        Finset.univ.filter (fun i => dist (p (ω i)) c ≤ r) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    calc
      _ ≤ iidCount {x | dist (p x) c ≤ r} ω := by
        rw [iidCount_eq_card_filter]
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ T * (n : ℝ) * r^s := hcount c r hr
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (hδ.le.trans hr) _)
  have hDs : (D.card : ℝ) * δ^s ≤ 2 := by
    have hcard : (D.card : ℝ) ≤ n := by
      have hh := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => ω i ∈ G)
      have hh' : D.card ≤ n := by simpa only [Finset.card_univ, Fintype.card_fin] using hh
      exact_mod_cast hh'
    exact (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hδ.le _)).trans hsize'
  obtain ⟨P, hPn, hPD, hsep, hballs⟩ := exists_separated_point_sample D (p ∘ ω)
    hδ (div_pos (mul_pos (by norm_num) hT) hJ) hDn hDs hDC
  exact ⟨ω, D, P, hDn, fun i hi => (Finset.mem_filter.mp hi).2, hPn, hPD, hsep, hballs⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SamplingScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rounding and scale budgets for planar sampling

The sample sizes are ceilings of the reciprocal dimension powers. Query
counts grow at most cubically in the reciprocal scale, while the chosen
exponential tail decays with the tenth power of that scale.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem sampling_ceil_size {δ s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) :
    0 < Nat.ceil (δ^(-s)) ∧
      1 ≤ (Nat.ceil (δ^(-s)) : ℝ)*δ^s ∧
      (Nat.ceil (δ^(-s)) : ℝ)*δ^s ≤ 2 := by
  have hp : 0 < δ^(-s) := Real.rpow_pos_of_pos hδ _
  have hδs : δ^s ≤ 1 := Real.rpow_le_one hδ.le hδ1 hs
  have hprod : δ^(-s)*δ^s = 1 := by
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  refine ⟨Nat.ceil_pos.mpr hp, ?_, ?_⟩
  · exact hprod ▸ mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Real.rpow_nonneg hδ.le _)
  · have hh := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hp.le).le
      (Real.rpow_nonneg hδ.le s)
    rw [add_mul, hprod, one_mul] at hh
    linarith

theorem sampling_query_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) ≤ 98*δ⁻¹^3 := by
  have hi : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hL := (Nat.ceil_lt_add_one (by positivity : 0 ≤ δ⁻¹+1)).le
  have hH := (Nat.ceil_lt_add_one (inv_nonneg.mpr hδ.le)).le
  have hLb : (2 * Nat.ceil (δ⁻¹+1)+1 : ℝ) ≤ 7*δ⁻¹ := by linarith
  have hHb : (Nat.ceil δ⁻¹ : ℝ) ≤ 2*δ⁻¹ := by linarith
  push_cast
  calc
    _ ≤ (7*δ⁻¹)^2 * (2*δ⁻¹) := mul_le_mul
      (pow_le_pow_left₀ (by positivity) hLb 2) hHb (by positivity) (by positivity)
    _ = _ := by ring

theorem sampling_exponential_tail {δ : ℝ} (hδ : 0 < δ) :
    exp (-(-10*log δ)) = δ^10 := by
  rw [show -(-10*log δ) = (10 : ℕ)*log δ by ring, Real.exp_nat_mul, Real.exp_log hδ]

theorem sampling_failure_bound {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/4) :
    (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) *
      exp (-(-10*log δ)) ≤ δ/16 := by
  rw [sampling_exponential_tail hδ]
  have hb := mul_le_mul_of_nonneg_right (sampling_query_card_bound hδ (by linarith))
    (pow_nonneg hδ.le 10)
  have he : (98*δ⁻¹^3)*δ^10 = 98*δ^7 := by
    field_simp
  rw [he] at hb
  have hh := pow_le_pow_left₀ hδ.le hδsmall 6
  have hf : 98*δ^7 ≤ δ/16 := by nlinarith [mul_le_mul_of_nonneg_left hh hδ.le]
  exact hb.trans hf

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FiniteWeightedProjectionSample
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite weighted projection contains an actual separated Frostman
set. Sampling uses only the original finite labels, so every selected
projected point has an original witness. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem finite_weighted_projection_sample {δ s C c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hC : 0 ≤ C) (hc : |c| ≤ 1)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hchart : InBoundedLineChart S)
    (hball : ∀ u r : ℝ, δ ≤ r →
      ((S.filter fun x => |lineParameterProjection c x-u| ≤ r).card:ℝ) ≤
        C*r^s*(S.card:ℝ)) :
    let γ := δ/4
    let B := 1-10*Real.log γ
    ∃ Q : Finset (Space 2), Q.Nonempty ∧
      Q ⊆ S.image (fun x => rowPoint 0 (lineParameterProjection c x/4)) ∧
      FiniteSeparatedAt γ Q ∧
      NormalizedFiniteBallBound γ s
        (2*(2*(((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s))^2) Q ∧
      Q.card ≤ Nat.ceil (γ^(-s)) := by
  dsimp only
  let γ := δ/4
  let B := 1-10*Real.log γ
  let μ : ProbabilityMeasure (Space 2) := ⟨(PMF.uniformOfFinset S hS).toMeasure,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let p : Space 2 → Space 2 := fun x =>
    if x ∈ S then rowPoint 0 (lineParameterProjection c x/4) else 0
  have hSc : 0 < (S.card:ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγsmall : γ ≤ 1/4 := by dsimp [γ]; linarith only [hδ1]
  have hγ1 : γ ≤ 1 := hγsmall.trans (by norm_num)
  have hB : 1 ≤ B := by
    have hh := Real.log_nonpos hγ.le hγ1
    dsimp [B]
    linarith only [hh]
  have hSmeas : MeasurableSet (S : Set (Space 2)) := S.finite_toSet.measurableSet
  have hp : Measurable p := by
    apply Measurable.ite hSmeas
    · dsimp [rowPoint,lineParameterProjection]
      fun_prop
    · exact measurable_const
  have hpbound : ∀ x i, |p x i| ≤ 1 := by
    intro x i
    by_cases hx : x ∈ S
    · have hproj : |lineParameterProjection c x| ≤ 2 := by
        unfold lineParameterProjection
        have hm := mul_le_mul hc (hchart x hx).1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        rw [← abs_mul] at hm
        exact (abs_add_le _ _).trans (by linarith only [hm,(hchart x hx).2])
      fin_cases i
      · change |(if x ∈ S then rowPoint 0 (lineParameterProjection c x/4) else 0) 0| ≤ 1
        simp only [ite_eq_left hx,rowPoint_zero,abs_zero]
        norm_num
      · change |(if x ∈ S then rowPoint 0 (lineParameterProjection c x/4) else 0) 1| ≤ 1
        simp only [ite_eq_left hx,rowPoint_one,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
        linarith only [hproj]
    · simp only [p,ite_eq_right hx,PiLp.zero_apply,abs_zero]; norm_num
  have hreal (A : Set (Space 2)) (hA : MeasurableSet A) :
      (μ : Measure (Space 2)).real A = ((S.filter fun x => x ∈ A).card:ℝ)/(S.card:ℝ) := by
    change ((PMF.uniformOfFinset S hS).toMeasure A).toReal = _
    rw [PMF.toMeasure_uniformOfFinset_apply hS A hA,ENNReal.toReal_div,
      ENNReal.toReal_natCast,ENNReal.toReal_natCast]
  have hGmass : 1 ≤ (μ : Measure (Space 2)).real (S:Set (Space 2)) := by
    rw [hreal _ hSmeas]
    apply (le_div_iff₀ hSc).2
    simp only [one_mul]
    exact_mod_cast Finset.card_le_card (show S ⊆ _ from fun x hx =>
      Finset.mem_filter.mpr ⟨hx,hx⟩)
  have hprob : ∀ z : Space 2, ∀ r : ℝ, γ ≤ r →
      (μ : Measure (Space 2)).real {x | dist (p x) z ≤ r} ≤ (C*(4:ℝ)^s)*r^s := by
    intro z r hr
    have hr0 : 0 < r := hγ.trans_le hr
    rw [hreal _ (measurableSet_le (hp.dist measurable_const) measurable_const)]
    apply (div_le_iff₀ hSc).2
    have hsub : S.filter (fun x => dist (p x) z ≤ r) ⊆
        S.filter (fun x => |lineParameterProjection c x-4*z 1| ≤ 4*r) := by
      intro x hx
      obtain ⟨hxS,hxz⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxS,?_⟩
      have he : p x = rowPoint 0 (lineParameterProjection c x/4) := by simp only [p,ite_eq_left hxS]
      have hh := (PiLp.dist_apply_le (p x) z 1).trans hxz
      rw [he] at hh
      simp only [rowPoint_one,Real.dist_eq] at hh
      have hid : |lineParameterProjection c x-4*z 1| = 4*|lineParameterProjection c x/4-z 1| := by
        rw [← abs_of_pos (by norm_num : (0:ℝ) < 4),← abs_mul]
        congr 1
        ring
      rw [hid]
      linarith only [hh]
    calc
      _ ≤ ((S.filter fun x => |lineParameterProjection c x-4*z 1| ≤ 4*r).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ C*(4*r)^s*(S.card:ℝ) := hball _ _ (by dsimp [γ] at hr; linarith only [hr])
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring
  let n := Nat.ceil (γ^(-s))
  let L := Nat.ceil (γ⁻¹+1)
  let H := Nat.ceil γ⁻¹
  obtain ⟨hn,hnlo,hnhi⟩ := sampling_ceil_size hγ hγ1 hs
  have hfail : (((2*L+1)^2*H:ℕ):ℝ)*Real.exp (-B) ≤ 1/4 := by
    have he : Real.exp (-B) ≤ Real.exp (-(-10*Real.log γ)) := by
      apply Real.exp_le_exp.mpr
      dsimp [B]
      linarith
    have hh := (mul_le_mul_of_nonneg_left he
      (Nat.cast_nonneg (α := ℝ) ((2*L+1)^2*H))).trans (sampling_failure_bound hγ hγsmall)
    exact hh.trans (by linarith only [hγ1])
  obtain ⟨ω,D,Q,hD,hDS,hQ,hQD,hsep,hreg⟩ := exists_good_separated_point_sample μ p hp hpbound
    (S:Set (Space 2)) hSmeas (by norm_num : (0:ℝ) < 1) hGmass hn hγ hs
    (by positivity : 0 ≤ C*(4:ℝ)^s) hB (Nat.le_ceil _) (Nat.le_ceil _)
    hnlo hnhi hprob hfail
  refine ⟨Q,hQ,?_,hsep,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (hQD hx)
    have hiS : ω i ∈ S := hDS i hi
    exact Finset.mem_image.mpr ⟨ω i,hiS,by simp only [Function.comp_apply,p,ite_eq_left hiS]⟩
  · simpa only [div_one] using hreg
  · exact (Finset.card_le_card hQD).trans
      (Finset.card_image_le.trans (by simpa using Finset.card_le_univ D))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RobustProjectionSets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A good original direction works for every later large point subset.
The output is an actual separated projected set, with original witnesses,
explicit regularity cost and a quantitative cardinality lower bound. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem robust_projection_subset (N : ℕ) {s t KI KP c ρ : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP)
    (hc : |c| ≤ 1) (hρ : 0 < ρ)
    (P A : Finset (Space 2)) (hP : P.Nonempty) (hchart : InBoundedLineChart P)
    (hAP : A ⊆ P) (hsize : ρ*(P.card:ℝ) ≤ (A.card:ℝ))
    (henergy : planarProjectionEnergy N s c P ≤
      2*projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2) :
    let γ := (1/(2:ℝ)^N)/4
    let K := projectedSubsetSampleConstant N s t KI KP ρ
    ∃ Q : Finset (Space 2), Q.Nonempty ∧
      Q ⊆ A.image (fun x => rowPoint 0 (lineParameterProjection c x/4)) ∧
      FiniteSeparatedAt γ Q ∧ NormalizedFiniteBallBound γ s K Q ∧
      1 ≤ K*γ^s*(Q.card:ℝ) ∧ Q.card ≤ Nat.ceil (γ^(-s)) ∧
      ∀ x ∈ Q, x 0 = 0 ∧ |x 1| ≤ 1/2 := by
  dsimp only
  have hbudget := projectionEnergyBudget_pos N hst hKI hKP
  obtain ⟨S,hSA,hS,_,hball⟩ := projected_subset_weighted_regular N hs
    (mul_pos (by norm_num) hbudget) hρ P A hP hAP hsize henergy
  let C := (2*(2*projectionEnergyBudget N s t KI KP)/ρ)*(2/ρ)*(2:ℝ)^s
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδ1 : 1/(2:ℝ)^N ≤ 1 := by
    exact (div_le_one (by positivity : (0:ℝ) < (2:ℝ)^N)).2
      (one_le_pow₀ (by norm_num))
  obtain ⟨Q,hQ,hQS,hsep,hreg,hcard⟩ := finite_weighted_projection_sample hδ hδ1 hs
    (show 0 ≤ C by dsimp [C]; positivity) hc S hS
    (fun x hx => hchart x (hAP (hSA hx))) hball
  have hQA : Q ⊆ A.image (fun x => rowPoint 0 (lineParameterProjection c x/4)) :=
    hQS.trans (Finset.image_subset_image hSA)
  have hreg' : NormalizedFiniteBallBound ((1/(2:ℝ)^N)/4) s
      (projectedSubsetSampleConstant N s t KI KP ρ) Q := hreg
  refine ⟨Q,hQ,hQA,hsep,hreg',finite_ball_bound_card_lower
    (by positivity) (by linarith only [hδ1]) hQ hreg',hcard,?_⟩
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hQA hx)
  have hpchart := hchart p (hAP hp)
  have hproj : |lineParameterProjection c p| ≤ 2 := by
    have hm := mul_le_mul hc hpchart.1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    rw [← abs_mul] at hm
    unfold lineParameterProjection
    exact (abs_add_le _ _).trans (by linarith only [hm,hpchart.2])
  refine ⟨rfl,?_⟩
  simp only [rowPoint_one,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
  linarith only [hproj]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ProjectedPacketRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Undo the harmless quarter scaling used in the projection sampler.
These are actual common-row points, with witnesses in the original packet. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem rowUnquarter_injOn (y a : ℝ) (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) : Set.InjOn (rowUnquarter y a) Q := by
  intro p hp q hq he
  have h1 := congrArg (fun z : Space 2 => z 1) he
  change a+4*p 1 = a+4*q 1 at h1
  ext i
  fin_cases i
  · exact (hrow p hp).trans (hrow q hq).symm
  · change p 1 = q 1
    linarith only [h1]

theorem rowUnquarter_card (y a : ℝ) (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) : (Q.image (rowUnquarter y a)).card = Q.card :=
  Finset.card_image_iff.mpr (rowUnquarter_injOn y a Q hrow)

theorem rowUnquarter_dist (y a : ℝ) {p q : Space 2}
    (hp : p 0 = 0) (hq : q 0 = 0) :
    dist (rowUnquarter y a p) (rowUnquarter y a q) = 4*dist p q := by
  have hp' : p = rowPoint 0 (p 1) := by ext i; fin_cases i; exact hp; rfl
  have hq' : q = rowPoint 0 (q 1) := by ext i; fin_cases i; exact hq; rfl
  conv_rhs => rw [hp',hq',rowPoint_dist]
  rw [rowUnquarter,rowUnquarter,rowPoint_dist]
  rw [show a+4*p 1-(a+4*q 1) = 4*(p 1-q 1) by ring,abs_mul]
  norm_num

theorem rowUnquarter_separated {δ y a : ℝ} (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) (hsep : FiniteSeparatedAt δ Q) :
    FiniteSeparatedAt (4*δ) (Q.image (rowUnquarter y a)) := by
  intro p hp q hq hpq
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rw [rowUnquarter_dist y a (hrow u hu) (hrow v hv)]
  exact mul_le_mul_of_nonneg_left (hsep u hu v hv (fun h => hpq (congrArg _ h)))
    (by norm_num)

theorem rowUnquarter_regular {δ y a s K : ℝ} (hδ : 0 ≤ δ) (Q : Finset (Space 2))
    (hrow : ∀ p ∈ Q, p 0 = 0) (hreg : NormalizedFiniteBallBound δ s K Q) :
    NormalizedFiniteBallBound (4*δ) s (K/(4:ℝ)^s) (Q.image (rowUnquarter y a)) := by
  intro z r hr hr1
  let w := rowPoint 0 ((z 1-a)/4)
  have hsub : (Q.image (rowUnquarter y a)).filter (fun p => dist p z ≤ r) ⊆
      (Q.filter (fun p => dist p w ≤ r/4)).image (rowUnquarter y a) := by
    intro p hp
    obtain ⟨hp,hpz⟩ := Finset.mem_filter.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,?_⟩,rfl⟩
    have hc := (PiLp.dist_apply_le (rowUnquarter y a q) z 1).trans hpz
    change |a+4*q 1-z 1| ≤ r at hc
    rw [row_dist_projection (hrow q hq)]
    change |q 1-(z 1-a)/4| ≤ r/4
    have he : q 1-(z 1-a)/4 = (a+4*q 1-z 1)/4 := by ring
    rw [he,abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
    exact div_le_div_of_nonneg_right hc (by norm_num)
  rw [rowUnquarter_card y a Q hrow]
  calc
    _ ≤ ((Q.filter fun p => dist p w ≤ r/4).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(r/4)^s*(Q.card:ℝ) := hreg w (r/4) (by linarith only [hr])
      (by linarith only [hr1])
    _ = _ := by rw [Real.div_rpow (by linarith only [hδ,hr]) (by norm_num)]; ring

theorem projected_packet_row {Δ y a s K : ℝ} (hΔ : 0 < Δ)
    (S Q : Finset (Space 2)) (hQ : Q.Nonempty)
    (hQS : Q ⊆ S.image (fun p => rowPoint 0 ((p 1-a)/(4*Δ))))
    (hnear : ∀ p ∈ S, |p 0-y| ≤ Δ)
    (hsep : FiniteSeparatedAt (Δ/4) Q)
    (hreg : NormalizedFiniteBallBound (Δ/4) s K Q) :
    ∃ R : Finset (Space 2), R.Nonempty ∧ R.card = Q.card ∧
      FiniteSeparatedAt Δ R ∧ NormalizedFiniteBallBound Δ s (K/(4:ℝ)^s) R ∧
      ∀ x ∈ R, x 0 = y ∧ ∃ p ∈ S, p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
  have hrow : ∀ q ∈ Q, q 0 = 0 := by
    intro q hq
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp (hQS hq)
    rfl
  let R := Q.image (rowUnquarter y (a/Δ))
  have hscale : 4*(Δ/4) = Δ := by ring
  refine ⟨R,hQ.image _,rowUnquarter_card _ _ Q hrow,?_,?_,?_⟩
  · simpa only [hscale] using rowUnquarter_separated (y := y) (a := a/Δ) Q hrow hsep
  · simpa only [hscale] using rowUnquarter_regular (y := y) (a := a/Δ)
      (by positivity : 0 ≤ Δ/4) Q hrow hreg
  · intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hQS hq)
    refine ⟨rfl,p,hp,?_,?_⟩
    · change p 1 = Δ*(a/Δ+4*((p 1-a)/(4*Δ)))
      field_simp
      ring
    · exact hnear p hp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPacketRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The robust projection theorem in the original coordinates of one
coarse cell. No projected point or fine-scale witness is replaced. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_injective {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.Injective (localPacketPoint Δ y a) := by
  intro p q he
  have h0 := congrArg (fun z : Space 2 => z 0) he
  have h1 := congrArg (fun z : Space 2 => z 1) he
  change (p 0-y)/Δ = (q 0-y)/Δ at h0
  change (p 1-a)/Δ = (q 1-a)/Δ at h1
  have he0 := (div_left_inj' hΔ.ne').1 h0
  have he1 := (div_left_inj' hΔ.ne').1 h1
  ext i
  fin_cases i
  · change p 0 = q 0
    linarith only [he0]
  · change p 1 = q 1
    linarith only [he1]

theorem localPacketPoint_chart {Δ y a : ℝ} (hΔ : 0 < Δ)
    (P : Finset (Space 2))
    (hP : ∀ p ∈ P, |p 0-y| ≤ Δ ∧ |p 1-a| ≤ Δ) :
    InBoundedLineChart (P.image (localPacketPoint Δ y a)) := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  constructor
  · change |(p 0-y)/Δ| ≤ 1
    rw [abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hP p hp).1
  · change |(p 1-a)/Δ| ≤ 1
    rw [abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hP p hp).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphBallCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual graph edges in a narrow Cartesian strip are covered by planar
balls. The count retains every neighbor, rather than only one witness. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem normalized_ball_bound_all_radii {δ t K : ℝ} {G : Finset (Space 2)}
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hG : NormalizedFiniteBallBound δ t K G)
    (z : Space 2) (r : ℝ) (hr : δ ≤ r) :
    ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ K*r^t*(G.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hG z r hr hr1
  · have hrpos : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hp : 1 ≤ r^t := Real.one_le_rpow hrpos ht
    have hc : ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ (G.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hk : 1 ≤ K*r^t := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) G.card])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DirectedPacketRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Use an arbitrary good local direction to construct rows for the
centered packet. The witnesses remain points of the original cell subset. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem directed_local_packet_row (N : ℕ) {s t KI KP ρ y a c b : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) (hρ : 0 < ρ)
    (hc : |c| ≤ 1) (P A : Finset (Space 2)) (hP : P.Nonempty) (hAP : A ⊆ P)
    (hsize : ρ*(P.card:ℝ) ≤ (A.card:ℝ))
    (hcell : ∀ p ∈ P, |p 0-y| ≤ 1/(2:ℝ)^N ∧ |p 1-a| ≤ 1/(2:ℝ)^N)
    (henergy : planarProjectionEnergy N s c
      (P.image (localPacketPoint (1/(2:ℝ)^N) y a)) ≤
      2*projectionEnergyBudget N s t KI KP*(P.card:ℝ)^2) :
    let Δ := 1/(2:ℝ)^N
    let K := projectedSubsetSampleConstant N s t KI KP ρ/(4:ℝ)^s
    ∃ R : Finset (Space 2), R.Nonempty ∧
      R.card ≤ Nat.ceil ((Δ/4)^(-s)) ∧ FiniteSeparatedAt Δ R ∧
      NormalizedFiniteBallBound Δ s K R ∧ 1 ≤ K*Δ^s*(R.card:ℝ) ∧
      ∀ x ∈ R, x 0 = y ∧ ∃ p ∈ A,
        p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
  dsimp only
  let Δ := 1/(2:ℝ)^N
  let F := localPacketPoint Δ y a
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ1 : Δ ≤ 1 := (div_le_one (by positivity : (0:ℝ) < (2:ℝ)^N)).2
    (one_le_pow₀ (by norm_num))
  have hcardP : (P.image F).card = P.card :=
    Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)
  have hcardA : (A.image F).card = A.card :=
    Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)
  have hsize' : ρ*((P.image F).card:ℝ) ≤ ((A.image F).card:ℝ) := by
    rwa [hcardP,hcardA]
  have henergy' : planarProjectionEnergy N s c (P.image F) ≤
      2*projectionEnergyBudget N s t KI KP*((P.image F).card:ℝ)^2 := by
    rwa [hcardP]
  obtain ⟨Q,hQ,hQA,hsep,hreg,_,hcardQ,_⟩ := robust_projection_subset N hs hst hKI hKP hc hρ
    (P.image F) (A.image F) (hP.image _)
    (localPacketPoint_chart hΔ P hcell) (Finset.image_subset_image hAP) hsize' henergy'
  let S := A.image (packetCenterPoint c b)
  let a' := a+c*y-b
  have hQS : Q ⊆ S.image (fun p => rowPoint 0 ((p 1-a')/(4*Δ))) := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp (hQA hq)
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨packetCenterPoint c b p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    have he : lineParameterProjection c (F p)/4 =
        (packetCenterPoint c b p 1-a')/(4*Δ) := by
      dsimp [F,localPacketPoint,lineParameterProjection,packetCenterPoint,a']
      field_simp
      ring
    rw [he]
  have hnear : ∀ p ∈ S, |p 0-y| ≤ Δ := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact (hcell q (hAP hq)).1
  obtain ⟨R,hR,hRQ,hRsep,hRreg,hrep⟩ := projected_packet_row hΔ S Q hQ hQS hnear hsep hreg
  refine ⟨R,hR,?_,hRsep,hRreg,finite_ball_bound_card_lower hΔ hΔ1 hR hRreg,?_⟩
  · rwa [hRQ]
  · intro x hx
    obtain ⟨hx0,p,hp,hp1,hp0⟩ := hrep x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hx0,q,hq,hp1,hp0⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DirectedSampledRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous row construction from the actual large subsets of the
coarse cells. Cardinality and regularity use a common explicit budget. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem directed_sampled_packet_rows (n : ℕ) {s t KI KP ρ D c b : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) (hρ : 0 < ρ)
    (hc : |c| ≤ 1) (hD : 0 ≤ D) (hbudget : projectedSubsetSampleConstant n s t KI KP ρ ≤ D)
    (Y : Finset ℝ) (P A : ℝ → Finset (Space 2)) (a : ℝ → ℝ)
    (S : Finset (Space 2))
    (hdata : ∀ y ∈ Y, (P y).Nonempty ∧ A y ⊆ P y ∧ A y ⊆ S ∧
      ρ*((P y).card:ℝ) ≤ ((A y).card:ℝ) ∧
      (∀ p ∈ P y, |p 0-y| ≤ 1/(2:ℝ)^n ∧ |p 1-a y| ≤ 1/(2:ℝ)^n) ∧
      planarProjectionEnergy n s c ((P y).image (localPacketPoint (1/(2:ℝ)^n) y (a y))) ≤
        2*projectionEnergyBudget n s t KI KP*((P y).card:ℝ)^2) :
    let Δ := 1/(2:ℝ)^n
    let α := Δ/4
    ∃ R : ℝ → Finset (Space 2), ∀ y ∈ Y,
      (R y).Nonempty ∧ FiniteSeparatedAt Δ (R y) ∧
      NormalizedFiniteBallBound Δ s D (R y) ∧
      1 ≤ D*α^s*((R y).card:ℝ) ∧ (R y).card ≤ Nat.ceil (α^(-s)) ∧
      ∀ x ∈ R y, x 0 = y ∧ ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
  dsimp only
  let Δ := 1/(2:ℝ)^n
  let α := Δ/4
  let K := projectedSubsetSampleConstant n s t KI KP ρ
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have h4 : (1:ℝ) ≤ (4:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have h4p : 0 < (4:ℝ)^s := Real.rpow_pos_of_pos (by norm_num) _
  have hK : K/(4:ℝ)^s ≤ D := (div_le_iff₀ h4p).2
    (hbudget.trans (le_mul_of_one_le_right hD h4))
  have hlocal (y : ℝ) (hy : y ∈ Y) := directed_local_packet_row n (c := c) (b := b) hs hst hKI hKP hρ hc
    (P y) (A y) (hdata y hy).1 (hdata y hy).2.1 (hdata y hy).2.2.2.1
    (hdata y hy).2.2.2.2.1 (hdata y hy).2.2.2.2.2
  let R : ℝ → Finset (Space 2) := fun y =>
    if hy : y ∈ Y then Classical.choose (hlocal y hy) else ∅
  refine ⟨R,?_⟩
  intro y hy
  have hr := Classical.choose_spec (hlocal y hy)
  have heR : R y = Classical.choose (hlocal y hy) := dite_eq_left hy
  rw [← heR] at hr
  obtain ⟨hne,hcard,hsep,hreg,hlow,hrep⟩ := hr
  have hcoef : (K/(4:ℝ)^s)*Δ^s = K*α^s := by
    have he : Δ = 4*α := by dsimp [α]; ring
    rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hα.le]
    field_simp
  have hlow' : 1 ≤ K*α^s*((R y).card:ℝ) := by
    change 1 ≤ (K/(4:ℝ)^s)*Δ^s*((R y).card:ℝ) at hlow
    rwa [hcoef] at hlow
  refine ⟨hne,hsep,?_,?_,hcard,?_⟩
  · intro z r hdr hr1
    have hr0 : 0 ≤ r := hΔ.le.trans hdr
    exact (hreg z r hdr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))
  · exact hlow'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hα.le _)) (Nat.cast_nonneg _))
  · intro x hx
    obtain ⟨hx0,p,hp,hp1,hp0⟩ := hrep x hx
    exact ⟨hx0,p,(hdata y hy).2.2.1 hp,hp1,hp0⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SampledRowCardinality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the sampler's exact cardinality bounds to the dyadic lower
and upper powers used by the regular product theorem. -/
namespace Falconer

theorem half_power_rpow_exp (N : ℕ) (s : ℝ) :
    ((1/2:ℝ)^N)^s = Real.exp (-s*(N:ℝ)*Real.log 2) := by
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,
    Real.log_div (by norm_num) (by norm_num),Real.log_one]
  congr 1
  ring

theorem sampled_row_cardinality_bounds (N : ℕ) {s ε : ℝ} (hs : 0 ≤ s)
    (hD : 2 ≤ Real.exp (ε*(N:ℝ)*Real.log 2)) :
    let α := (1/2:ℝ)^N
    let D := Real.exp (ε*(N:ℝ)*Real.log 2)
    ((Nat.ceil (α^(-s)):ℕ):ℝ) ≤ Real.exp ((s+ε)*(N:ℝ)*Real.log 2) ∧
      ∀ m : ℝ, 1 ≤ D*α^s*m → Real.exp ((s-ε)*(N:ℝ)*Real.log 2) ≤ m := by
  dsimp only
  let α := (1/2:ℝ)^N
  let D := Real.exp (ε*(N:ℝ)*Real.log 2)
  let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
  let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hαs : 0 < α^s := Real.rpow_pos_of_pos hα _
  have hU : U*α^s = D := by
    change Real.exp ((s+ε)*(N:ℝ)*Real.log 2)*((1/2:ℝ)^N)^s = _
    rw [half_power_rpow_exp,← Real.exp_add]
    congr 1
    ring
  have hL : (D*α^s)*L = 1 := by
    change (Real.exp (ε*(N:ℝ)*Real.log 2)*((1/2:ℝ)^N)^s)*
      Real.exp ((s-ε)*(N:ℝ)*Real.log 2) = 1
    rw [half_power_rpow_exp,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  constructor
  · have hh := (sampling_ceil_size hα hα1 hs).2.2
    apply (mul_le_mul_iff_left₀ hαs).1
    change ((Nat.ceil (α^(-s)):ℕ):ℝ)*α^s ≤ U*α^s
    rw [hU]
    exact hh.trans hD
  · intro m hm
    have hc : 0 < D*α^s := mul_pos (Real.exp_pos _) hαs
    apply (mul_le_mul_iff_right₀ hc).1
    change (D*α^s)*L ≤ (D*α^s)*m
    rwa [hL]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CenteredPacketGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coarse-cell projections yield the product gain for the original
packet. The projected rows are constructed in the proof; neither product
structure nor a separated output pencil family is assumed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_gain_of_local_energy {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let L := fun s : ℝ => Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2)
      let U := fun s : ℝ => Real.exp ((s+ε)*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t KI KP ρ c b : ℝ) (Y : Finset ℝ)
        (P A : ℝ → Finset (Space 2)) (a : ℝ → ℝ)
        (S : Finset (Space 2)) (T : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → s < t → 0 ≤ KI → 0 ≤ KP → 0 < ρ → |c| ≤ 1 →
      Y.Nonempty → (∀ y ∈ Y, |y| ≤ 1) → 2 ≤ D →
      projectedSubsetSampleConstant n s t KI KP ρ ≤ D →
      (∀ y ∈ Y, (P y).Nonempty ∧ A y ⊆ P y ∧ A y ⊆ S ∧
        ρ*((P y).card:ℝ) ≤ ((A y).card:ℝ) ∧
        (∀ p ∈ P y, |p 0-y| ≤ Δ ∧ |p 1-a y| ≤ Δ) ∧
        planarProjectionEnergy n s c ((P y).image (localPacketPoint Δ y (a y))) ≤
          2*projectionEnergyBudget n s t KI KP*((P y).card:ℝ)^2) →
      (∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
        NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T p) ∧
        L s ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ U s ∧
        ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
      (∀ u r : ℝ, Δ/4 ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((S.biUnion T).card:ℝ) := by
  obtain ⟨ε,η,N0,hε,hη,hN0,hmain⟩ := centered_packet_product_power hκ hκ1
  refine ⟨ε,η,N0,hε,hη,hN0,?_⟩
  intro n hn
  dsimp only
  intro s t KI KP ρ c b Y P A a S T hs hs1 hst hKI hKP hρ hc hY hYbound hD2 hbudget hdata hT hYball
  let Δ := 1/(2:ℝ)^n
  let α := (1/2:ℝ)^(n+2)
  let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let NP := Nat.ceil (α^(-s))
  have hscale : Δ = 4*α := by
    dsimp [Δ,α]
    rw [pow_add]
    norm_num
    rw [div_pow,one_pow]
    ring
  have hαeq : Δ/4 = α := by rw [hscale]; ring
  have hscale' : 1/(2:ℝ)^n = 4*(1/2:ℝ)^(n+2) := hscale
  have hs0 : 0 ≤ s := hκ.le.trans hs
  obtain ⟨R,hR⟩ := directed_sampled_packet_rows n (c := c) (b := b) hs0 hst hKI hKP hρ hc
    (zero_le_two.trans hD2) hbudget Y P A a S hdata
  obtain ⟨hNPup,hsize⟩ := sampled_row_cardinality_bounds (n+2) hs0 hD2
  have hNP : 0 < NP := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by dsimp [α]; positivity) _)
  have hrows : ∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt (4*α) (R y) ∧
      NormalizedFiniteBallBound (4*α) s D (R y) ∧
      Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((R y).card:ℝ) ∧
      (R y).card ≤ NP ∧ ∀ x ∈ R y, x 0 = y := by
    intro y hy
    obtain ⟨_,hsep,hreg,hlow,hup,hrep⟩ := hR y hy
    have hlow' : 1 ≤ D*α^s*((R y).card:ℝ) := by
      change 1 ≤ D*(Δ/4)^s*((R y).card:ℝ) at hlow
      rwa [hαeq] at hlow
    have hlo := hsize ((R y).card:ℝ) hlow'
    refine ⟨hYbound y hy,?_,?_,hlo,?_,?_⟩
    · simpa only [← hscale] using hsep
    · simpa only [← hscale] using hreg
    · simpa only [NP,← hαeq] using hup
    · exact fun x hx => (hrep x hx).1
  have hrep : ∀ y ∈ Y, ∀ x ∈ R y, ∃ p ∈ S,
      p 1+c*p 0-b = (4*α)*x 1 ∧ |p 0-y| ≤ 4*α := by
    intro y hy x hx
    obtain ⟨hx0,p,hp,hp1,hp0⟩ := (hR y hy).2.2.2.2.2 x hx
    rw [hx0] at hp0
    exact ⟨p,hp,by simpa only [← hscale] using hp1,by simpa only [← hscale] using hp0⟩
  apply hmain (n+2) hn s c b Y R S T NP hs hs1 hY hNP hNPup hrows hrep
  · simpa only [← hscale'] using hT
  · intro u r hr hr1
    apply hYball u r ?_ hr1
    change Δ/4 ≤ r
    rwa [hαeq]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CommonTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized two-point common-tube kernel in the actual line chart. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem common_tube_card_bound {δ r b K : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    (hR1 : 80*δ/r ≤ 1) (hK : 0 ≤ K)
    (T : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hxy : r ≤ dist x y) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/r)^b*(T.card : ℝ) := by
  let S := T.filter (fun l => TubeIncident δ y l)
  by_cases hS : S.Nonempty
  · obtain ⟨m,hm⟩ := hS
    have hmT := (Finset.mem_filter.mp hm).1
    have hmy := (Finset.mem_filter.mp hm).2
    have hsub : S ⊆ T.filter (fun l => dist l m ≤ 80*δ/r) := by
      intro l hl
      obtain ⟨hlT,hly⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,two_point_tube_parameters_close hδ.le hr hr1 hsmall
        hx0 (hchart l hlT).1 (hchart m hmT).1 (hinc l hlT) hly (hinc m hmT) hmy hxy⟩
    have hR0 : δ ≤ 80*δ/r := by
      apply (le_div_iff₀ hr).2
      nlinarith [mul_le_mul_of_nonneg_left hr1 hδ.le]
    exact (show (S.card : ℝ) ≤ (T.filter (fun l => dist l m ≤ 80*δ/r)).card by
      exact_mod_cast Finset.card_le_card hsub).trans (hball m _ hR0 hR1)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) (Nat.cast_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubeKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common-tube kernel valid at all point separations, including the diagonal. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem truncatedPlanarDistance_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x y : Space 2) :
    0 < truncatedPlanarDistance δ x y ∧ truncatedPlanarDistance δ x y ≤ 1 :=
  ⟨hδ.trans_le (le_max_left _ _),max_le hδ1 (min_le_left _ _)⟩

theorem common_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  let r := truncatedPlanarDistance δ x y
  obtain ⟨hr,hr1⟩ := truncatedPlanarDistance_bounds hδ hδ1 x y
  change 0 < r at hr
  change r ≤ 1 at hr1
  by_cases hsmall : 80*δ ≤ r
  · have hlow : 16*δ ≤ r := by linarith
    have hR : 80*δ/r ≤ 1 := (div_le_one hr).2 hsmall
    have hrδ : δ < r := by linarith
    have hdist : r ≤ dist x y := by
      have hm : δ < min 1 (dist x y) := (lt_max_iff.mp hrδ).resolve_left (lt_irrefl _)
      change max δ (min 1 (dist x y)) ≤ dist x y
      rw [max_eq_right hm.le]
      exact min_le_right _ _
    exact common_tube_card_bound hδ hr hr1 hlow hR (zero_le_one.trans hK)
      T x y hx0 hdist hchart hinc hball
  · have hR : 1 ≤ 80*δ/r := (le_div_iff₀ hr).2 (by linarith)
    have hp : 1 ≤ (80*δ/r)^b := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hR hb
    have hm : 1 ≤ K*(80*δ/r)^b := by nlinarith
    calc
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_filter_le T _
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) T.card]

theorem intersect_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤ K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  have hsub : T ∩ U ⊆ T.filter (fun l => TubeIncident δ y l) := by
    intro l hl
    obtain ⟨hlT,hlU⟩ := Finset.mem_inter.mp hl
    exact Finset.mem_filter.mpr ⟨hlT,hy l hlU⟩
  exact (show ((T ∩ U).card : ℝ) ≤ (T.filter (fun l => TubeIncident δ y l)).card by
    exact_mod_cast Finset.card_le_card hsub).trans
      (common_tube_kernel_bound hδ hδ1 hb hK T x y hx0 hchart hx hball)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubePower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separating the scale power from the truncated common-tube kernel. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem truncatedPlanarDistance_inverse_power_le {δ b : ℝ} (_hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (x y : Space 2) :
    (1/truncatedPlanarDistance δ x y)^b ≤
      1+(1/max (dist x y) δ)^b := by
  rcases le_total (dist x y) 1 with hd | hd
  · simp only [truncatedPlanarDistance,min_eq_right hd,max_comm δ (dist x y)]
    linarith
  · simp only [truncatedPlanarDistance,min_eq_left hd,max_eq_right hδ1,
      div_one,Real.one_rpow]
    have hp : 0 ≤ (1/max (dist x y) δ)^b := by positivity
    linarith

theorem intersect_tube_power_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤
      (K*(80*δ)^b*(T.card : ℝ))*(1+(1/max (dist x y) δ)^b) := by
  have hr := (truncatedPlanarDistance_bounds hδ hδ1 x y).1
  have he : (80*δ/truncatedPlanarDistance δ x y)^b =
      (80*δ)^b*(1/truncatedPlanarDistance δ x y)^b := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have hh := intersect_tube_kernel_bound hδ hδ1 hb hK T U x y hx0 hchart hx hy hball
  rw [he] at hh
  apply hh.trans
  have hp := mul_le_mul_of_nonneg_left (truncatedPlanarDistance_inverse_power_le hδ hδ1 x y (b := b))
    (show 0 ≤ K*(80*δ)^b*(T.card : ℝ) by positivity)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PlanarCriticalPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical finite planar potential with the exact linear depth loss.
This is used to control the distribution of cells along a selected tube. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_dyadic_critical_potential (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K t : ℝ} (_hK : 0 ≤ K) (ht : 0 ≤ t)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P) :
    (∑ y ∈ P, ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^t)) ≤
      P.card + ENNReal.ofReal ((2:ℝ)^t)*
        (ENNReal.ofReal (K*(P.card:ℝ))+(N:ℝ≥0∞)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) := by
  let μ := planarCountingMeasure P
  have hsmall (j : ℕ) (hj : j ≤ 0+N) :
      μ {y | dist x y < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((K*(P.card : ℝ))*(1/(2:ℝ)^j)^t) := by
    rw [planarCountingMeasure_apply]
    have hr0 : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by simpa using hj)
    have hr1 : 1/(2:ℝ)^j ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact one_le_pow₀ (by norm_num)
    have hs : P.filter (fun y => dist x y < 1/(2:ℝ)^j) ⊆
        P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j) := by
      intro y hy
      obtain ⟨hyP,hy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyP,by simpa only [dist_comm] using hy.le⟩
    have hc := (show ((P.filter (fun y => dist x y < 1/(2:ℝ)^j)).card : ℝ) ≤
      (P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j)).card from by exact_mod_cast Finset.card_le_card hs)
    have hh := hc.trans (hball x _ hr0 hr1)
    rw [show (K*(P.card : ℝ))*(1/(2:ℝ)^j)^t = K*(1/(2:ℝ)^j)^t*(P.card : ℝ) by ring]
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hlocal := truncated_scalar_potential_critical μ (fun y => dist x y) (by fun_prop)
    (fun _ => dist_nonneg) ht 0 N hsmall
  simp only [pow_zero,one_div_one,zero_add] at hlocal
  let A := {y : Space 2 | dist x y < 1}
  let F := fun y : Space 2 => ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^t)
  have hfar : (∫⁻ y in Aᶜ, F y ∂μ) ≤ P.card := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by measurability)
        intro y hy
        change ¬ dist x y < 1 at hy
        have hd : 1 ≤ max (dist x y) (1/(2:ℝ)^N) :=
          (le_of_not_gt hy).trans (le_max_left _ _)
        have hinv : 1/max (dist x y) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr ((Real.rpow_le_rpow (by positivity) hinv ht).trans_eq (Real.one_rpow _))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = P.card := by rw [planarCountingMeasure_apply]; simp
  rw [← planarCountingMeasure_lintegral]
  change (∫⁻ y, F y ∂μ) ≤ _
  rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
  simpa only [mul_assoc,add_comm] using add_le_add hlocal hfar

theorem finite_dyadic_critical_potential_real (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K t : ℝ} (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P) :
    (∑ y ∈ P, (1/max (dist x y) (1/(2:ℝ)^N))^t) ≤
      K*planarCriticalConstant N t*(P.card:ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hh := finite_dyadic_critical_potential P x N hK0 ht hball
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity)] at hh
  have he : (P.card:ℝ≥0∞)+ENNReal.ofReal ((2:ℝ)^t)*
      (ENNReal.ofReal (K*(P.card:ℝ))+(N:ℝ≥0∞)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) =
      ENNReal.ofReal ((P.card:ℝ)+(2:ℝ)^t*(K*(P.card:ℝ)+(N:ℝ)*((K*(P.card:ℝ))*(2:ℝ)^t))) := by
    symm
    calc
      _ = ENNReal.ofReal (P.card:ℝ) + ENNReal.ofReal ((2:ℝ)^t) *
          (ENNReal.ofReal (K*(P.card:ℝ)) +
            ENNReal.ofReal (N:ℝ)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) := by
        conv_lhs =>
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity),
            ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      _ = _ := by simp only [ENNReal.ofReal_natCast]
  rw [he] at hh
  have hb := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hh
  have hc := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (α := ℝ) P.card)
  unfold planarCriticalConstant
  nlinarith only [hb,hc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilFiberEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Average critical energy of the point fibers of a tube family.
This is the finite form of Orponen--Shmerkin, Appendix A, equation (A.18). -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_pencilFiberEnergy (N : ℕ) (τ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, pencilFiberEnergy N τ P T l) =
      ∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)*
        (1/max (dist x y) (1/(2:ℝ)^N))^τ := by
  unfold pencilFiberEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have he (l : Space 2) :
      (if l ∈ T x ∧ l ∈ T y then (1/max (dist x y) (1/(2:ℝ)^N))^τ else 0) =
      (if l ∈ T x ∩ T y then (1:ℝ) else 0)*(1/max (dist x y) (1/(2:ℝ)^N))^τ := by
    by_cases hlx : l ∈ T x <;> by_cases hly : l ∈ T y <;> simp [hlx,hly]
  simp_rw [he]
  rw [← Finset.sum_mul,sum_tube_membership (P.biUnion T) (T x ∩ T y)
    (fun l hl => Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hl).1⟩)]

theorem nonnegative_power_le_one_add {a u v : ℝ} (ha : 0 < a)
    (hu : 0 ≤ u) (huv : u ≤ v) : a^u ≤ 1+a^v := by
  by_cases hsmall : a ≤ 1
  · exact (Real.rpow_le_one ha.le hsmall hu).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hsmall)) huv).trans
      (le_add_of_nonneg_left (by norm_num))

theorem common_tube_weighted_bound {δ s t K M : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hst : s ≤ t)
    (hK : 1 ≤ K) (hM : 0 ≤ M) (P Q : Finset (Space 2)) (x y : Space 2)
    (hx : |x 0| ≤ 1) (hchart : InBoundedLineChart P)
    (hincx : ∀ l ∈ P, TubeIncident δ x l) (hincy : ∀ l ∈ Q, TubeIncident δ y l)
    (hreg : NormalizedFiniteBallBound δ s K P) (hcard : (P.card:ℝ) ≤ M) :
    ((P ∩ Q).card:ℝ)*(1/max (dist x y) δ)^(t-s) ≤
      (K*(80*δ)^s*M)*(1+2*(1/max (dist x y) δ)^t) := by
  let a := 1/max (dist x y) δ
  have ha : 0 < a := one_div_pos.mpr (hδ.trans_le (le_max_right _ _))
  have hk := intersect_tube_power_bound hδ hδ1 hs hK P Q x y hx hchart hincx hincy hreg
  have hkm : (K*(80*δ)^s*(P.card:ℝ)) ≤ K*(80*δ)^s*M :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  have hpower : a^(t-s)*(1+a^s) ≤ 1+2*a^t := by
    have hlo := nonnegative_power_le_one_add ha (sub_nonneg.mpr hst)
      (show t-s ≤ t by linarith only [hs])
    have he : a^(t-s)*a^s = a^t := by
      rw [← Real.rpow_add ha]
      congr 1
      ring
    rw [mul_add,mul_one,he]
    linarith only [hlo]
  calc
    _ ≤ ((K*(80*δ)^s*(P.card:ℝ))*(1+a^s))*a^(t-s) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ ≤ ((K*(80*δ)^s*M)*(1+a^s))*a^(t-s) := by gcongr
    _ = (K*(80*δ)^s*M)*(a^(t-s)*(1+a^s)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

theorem pencil_fiber_energy_average (N : ℕ) {s t K M : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ l ∈ P.biUnion T, pencilFiberEnergy N (t-s) P T l) ≤
      (K*(80*(1/(2:ℝ)^N))^s*M)*(1+2*K*planarCriticalConstant N t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let C := K*(80*δ)^s*M
  let k := fun x y : Space 2 => (1/max (dist x y) δ)^t
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have ht : 0 ≤ t := hs.trans hst
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpotential : (∑ x ∈ P, ∑ y ∈ P, k x y) ≤
      K*planarCriticalConstant N t*(P.card:ℝ)^2 := by
    calc
      _ ≤ ∑ _x ∈ P, K*planarCriticalConstant N t*(P.card:ℝ) :=
        Finset.sum_le_sum fun x _ => finite_dyadic_critical_potential_real P x N hK ht hPball
      _ = _ := by simp; ring
  rw [sum_pencilFiberEnergy]
  calc
    _ ≤ ∑ x ∈ P, ∑ y ∈ P, C*(1+2*k x y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact common_tube_weighted_bound hδ hδ1 hs hst hK hM (T x) (T y) x y
        (hPchart x hx).1 (hT x hx).1 (hT x hx).2.2.2 (hT y hy).2.2.2
        (hT x hx).2.1 (hT x hx).2.2.1
    _ = C*((P.card:ℝ)^2+2*(∑ x ∈ P, ∑ y ∈ P, k x y)) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
        mul_one,← Finset.mul_sum]
      ring
    _ ≤ C*((P.card:ℝ)^2+2*(K*planarCriticalConstant N t*(P.card:ℝ)^2)) := by gcongr
    _ = _ := by dsimp [C]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteEnergyRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A low-energy tube fiber contains a large regular set of original cells. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_planar_energy_regular_subset (N : ℕ) {τ B : ℝ}
    (hτ : 0 ≤ τ) (hB : 0 < B) (P : Finset (Space 2)) (hP : P.Nonempty)
    (henergy : (∑ x ∈ P, ∑ y ∈ P,
      (1/max (dist x y) (1/(2:ℝ)^N))^τ) ≤ B*(P.card:ℝ)^2) :
    ∃ S ⊆ P, S.Nonempty ∧ (P.card:ℝ)/2 ≤ (S.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) τ (4*B*(2:ℝ)^τ) S := by
  let δ := 1/(2:ℝ)^N
  let k := fun x y : Space 2 => (1/max (dist x y) δ)^τ
  let f := fun x => ∑ y ∈ P, k x y
  let S := P.filter fun x => f x ≤ 2*(B*(P.card:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hb : 0 < B*(P.card:ℝ) := mul_pos hB hPc
  have hf (x : Space 2) : 0 ≤ f x := Finset.sum_nonneg fun y _ => by dsimp [k]; positivity
  have hhalf : (P.card:ℝ)/2 ≤ (S.card:ℝ) := by
    apply finite_low_half P f hb (fun x _ => hf x)
    change (∑ x ∈ P, ∑ y ∈ P, k x y) ≤ _
    convert henergy using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hSc : 0 < (S.card:ℝ) := by linarith only [hhalf,hPc]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSc)
  have hSP : S ⊆ P := Finset.filter_subset _ _
  refine ⟨S,hSP,hS,hhalf,?_⟩
  intro u r hr _
  have hr0 : 0 < r := hδ.trans_le hr
  let F := S.filter fun x => dist x u ≤ r
  by_cases hF : F.Nonempty
  · obtain ⟨x,hxF⟩ := hF
    obtain ⟨hxS,hxu⟩ := Finset.mem_filter.mp hxF
    have hfx : f x ≤ 2*(B*(P.card:ℝ)) := (Finset.mem_filter.mp hxS).2
    have hweight (y : Space 2) (hyF : y ∈ F) : 1 ≤ (2*r)^τ*k x y := by
      have hyu := (Finset.mem_filter.mp hyF).2
      have hd : dist x y ≤ 2*r := by
        have hh := dist_triangle x u y
        rw [dist_comm u y] at hh
        linarith only [hh,hxu,hyu]
      have hmax : max (dist x y) δ ≤ 2*r := max_le hd (by linarith only [hr,hδ])
      have hmaxpos : 0 < max (dist x y) δ := hδ.trans_le (le_max_right _ _)
      have hbase : 1 ≤ (2*r)*(1/max (dist x y) δ) := by
        rw [mul_one_div]
        exact (le_div_iff₀ hmaxpos).2 (by simpa only [one_mul] using hmax)
      dsimp [k]
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.one_le_rpow hbase hτ
    have hcount : (F.card:ℝ) ≤ (2*r)^τ*f x := by
      calc
        _ = ∑ _y ∈ F, (1:ℝ) := by simp
        _ ≤ ∑ y ∈ F, (2*r)^τ*k x y := Finset.sum_le_sum hweight
        _ = (2*r)^τ*∑ y ∈ F, k x y := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hSP)
            (fun y _ _ => by dsimp [k]; positivity)) (by positivity)
    calc
      _ ≤ (2*r)^τ*f x := hcount
      _ ≤ (2*r)^τ*(2*(B*(P.card:ℝ))) := mul_le_mul_of_nonneg_left hfx (by positivity)
      _ ≤ (2*r)^τ*(2*(B*(2*(S.card:ℝ)))) := by gcongr; linarith only [hhalf]
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr0.le]; ring
  · change (F.card:ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

theorem pencilFiber_card (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) :
    ((pencilFiber P T l).card:ℝ) = tubeDegree P T l := by
  simp only [pencilFiber,tubeDegree,← Finset.sum_filter,Finset.sum_const,
    nsmul_eq_mul,mul_one]

theorem pencilFiber_energy (N : ℕ) (τ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) :
    (∑ x ∈ pencilFiber P T l, ∑ y ∈ pencilFiber P T l,
      (1/max (dist x y) (1/(2:ℝ)^N))^τ) = pencilFiberEnergy N τ P T l := by
  simp only [pencilFiber,pencilFiberEnergy,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : l ∈ T x <;> simp [hx]

theorem pencil_fiber_regular_subset (N : ℕ) {τ B : ℝ}
    (hτ : 0 ≤ τ) (hB : 0 < B) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2)
    (hdegree : 0 < tubeDegree P T l)
    (henergy : pencilFiberEnergy N τ P T l ≤ B*(tubeDegree P T l)^2) :
    ∃ S ⊆ P, S.Nonempty ∧ tubeDegree P T l/2 ≤ (S.card:ℝ) ∧
      (∀ x ∈ S, l ∈ T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) τ (4*B*(2:ℝ)^τ) S := by
  have hF : (pencilFiber P T l).Nonempty := by
    apply Finset.card_pos.mp
    have hc : (0:ℝ) < (pencilFiber P T l).card := by
      rw [pencilFiber_card]
      exact hdegree
    exact Nat.cast_pos.mp hc
  obtain ⟨S,hSF,hS,hhalf,hreg⟩ := finite_planar_energy_regular_subset N hτ hB
    (pencilFiber P T l) hF (by simpa only [pencilFiber_energy,pencilFiber_card] using henergy)
  exact ⟨S,hSF.trans (Finset.filter_subset _ _),hS,
    by simpa only [pencilFiber_card] using hhalf,
    fun x hx => (Finset.mem_filter.mp (hSF hx)).2,hreg⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilEnergyPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discard high-energy tubes while preserving a positive fraction of every
retained cell's pencil. All energy and incidence budgets are explicit. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem high_energy_incidence_bound (U : Finset (Space 2)) (f g : Space 2 → ℝ)
    {Q E H : ℝ} (hQ : 0 ≤ Q) (hg : ∀ l ∈ U, 0 ≤ g l)
    (hE : (∑ l ∈ U, g l) ≤ E) (hH : (∑ l ∈ U, (f l)^2) ≤ H) :
    Q*(∑ l ∈ U.filter (fun l => Q < g l), f l)^2 ≤ E*H := by
  let B := U.filter fun l => Q < g l
  have hH0 : 0 ≤ H := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hH
  have hc : Q*(B.card:ℝ) ≤ E := by
    calc
      _ = ∑ _l ∈ B, Q := by simp; ring
      _ ≤ ∑ l ∈ B, g l := Finset.sum_le_sum fun l hl => (Finset.mem_filter.mp hl).2.le
      _ ≤ ∑ l ∈ U, g l := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun l hl _ => hg l hl)
      _ ≤ E := hE
  have hs : (∑ l ∈ B, f l)^2 ≤ (B.card:ℝ)*H := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1:ℝ)) f
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun l _ _ => sq_nonneg (f l))).trans hH) (Nat.cast_nonneg _))
  calc
    _ ≤ Q*((B.card:ℝ)*H) := mul_le_mul_of_nonneg_left hs hQ
    _ = (Q*(B.card:ℝ))*H := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hH0

theorem sum_pencil_intersection (P B : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) :
    (∑ x ∈ P, ((T x ∩ B).card:ℝ)) = ∑ l ∈ B, tubeDegree P T l := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 2
  ext l
  simp only [Finset.mem_inter,Finset.mem_filter,and_comm]

theorem prune_high_energy_pencils (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (g : Space 2 → ℝ)
    {m Q E H : ℝ} (hP : P.Nonempty) (hm : 0 < m) (hQ : 0 < Q)
    (hcard : ∀ x ∈ P, m ≤ ((T x).card:ℝ))
    (hg : ∀ l ∈ P.biUnion T, 0 ≤ g l)
    (hE : (∑ l ∈ P.biUnion T, g l) ≤ E)
    (hH : (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) ≤ H)
    (hbudget : 16*E*H ≤ Q*(m*(P.card:ℝ))^2) :
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ)/2 ≤ (R.card:ℝ) ∧
      ∀ x ∈ R, m/2 ≤ ((T x |>.filter fun l => g l ≤ Q).card:ℝ) := by
  let U := P.biUnion T
  let B := U.filter fun l => Q < g l
  let bad := fun x => ((T x ∩ B).card:ℝ)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hI0 : 0 ≤ ∑ l ∈ B, tubeDegree P T l :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun x _ => by split <;> norm_num
  have hweighted := high_energy_incidence_bound U (tubeDegree P T) g hQ.le hg hE hH
  have hI : (∑ l ∈ B, tubeDegree P T l) ≤ m*(P.card:ℝ)/4 := by
    have hh : Q*(16*(∑ l ∈ B, tubeDegree P T l)^2) ≤ Q*(m*(P.card:ℝ))^2 := by
      calc
        _ = 16*(Q*(∑ l ∈ B, tubeDegree P T l)^2) := by ring
        _ ≤ 16*(E*H) := mul_le_mul_of_nonneg_left hweighted (by norm_num)
        _ ≤ _ := by nlinarith only [hbudget]
    have hh' := (mul_le_mul_iff_right₀ hQ).mp hh
    have hmP : 0 < m*(P.card:ℝ) := mul_pos hm hPc
    nlinarith only [hh',hI0,hmP]
  have hsum : (∑ x ∈ P, bad x) ≤ (m/4)*(P.card:ℝ) := by
    rw [show (∑ x ∈ P, bad x) = ∑ l ∈ B, tubeDegree P T l from sum_pencil_intersection P B T]
    nlinarith only [hI]
  let R := P.filter fun x => bad x ≤ 2*(m/4)
  have hhalf : (P.card:ℝ)/2 ≤ (R.card:ℝ) :=
    finite_low_half P bad (by positivity) (fun x _ => Nat.cast_nonneg _) hsum
  have hRc : 0 < (R.card:ℝ) := by linarith only [hhalf,hPc]
  refine ⟨R,Finset.filter_subset _ _,Finset.card_pos.mp (Nat.cast_pos.mp hRc),hhalf,?_⟩
  intro x hx
  obtain ⟨hxP,hxb⟩ := Finset.mem_filter.mp hx
  have he : T x ∩ B = (T x).filter fun l => ¬ g l ≤ Q := by
    ext l
    simp only [B,U,Finset.mem_inter,Finset.mem_filter,not_le]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,Finset.mem_biUnion.mpr ⟨x,hxP,h.1⟩,h.2⟩
  have hp : (((T x).filter fun l => g l ≤ Q).card:ℝ) + bad x = (T x).card := by
    dsimp [bad]
    rw [he]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := T x) (fun l => g l ≤ Q)
  linarith only [hp,hxb,hcard x hxP]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilSecondMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric second-moment bound, allowing unequal pencil sizes. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_second_moment_bound (N : ℕ) {s t K M : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) ≤
      (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let C := K*(80*δ)^s*M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤ C*(1+K*planarPotentialConstant s t)*(P.card:ℝ) := by
    have hM : 0 ≤ M := (Nat.cast_nonneg (T x).card).trans (hT x hx).2.2.1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hpot := finite_dyadic_truncated_potential_real P x N hK hs hst hPball
    calc
      _ ≤ ∑ y ∈ P, C*(1+(1/max (dist x y) δ)^s) := by
        apply Finset.sum_le_sum
        intro y hy
        apply (intersect_tube_power_bound hδ hδ1 hs hK (T x) (T y) x y
          (hPchart x hx).1 (hT x hx).1 (hT x hx).2.2.2
          (hT y hy).2.2.2 (hT x hx).2.1).trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT x hx).2.2.1
          (by positivity)) (by positivity)
      _ = C*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^s) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ C*((P.card:ℝ)+K*planarPotentialConstant s t*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hC
      _ = _ := by ring
  rw [sum_tubeDegree_sq]
  calc
    _ ≤ ∑ _x ∈ P, C*(1+K*planarPotentialConstant s t)*(P.card:ℝ) :=
      Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [C]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RegularEnergyPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-energy deletion with its geometric budgets discharged. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem prune_pencil_fiber_energy (N : ℕ) {s t K M m : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    let Q := pencilEnergyCutoff N s t K M m P
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ)/2 ≤ (R.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t (2*K) R ∧
      ∀ x ∈ R,
        m/2 ≤ (((T x).filter fun l => pencilFiberEnergy N (t-s) P T l ≤ Q).card:ℝ) ∧
        NormalizedFiniteBallBound (1/(2:ℝ)^N) s (K*(2*M/m))
          ((T x).filter fun l => pencilFiberEnergy N (t-s) P T l ≤ Q) := by
  let Q := pencilEnergyCutoff N s t K M m P
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  obtain ⟨p,hp⟩ := hP.exists_mem
  have hM : 0 < M := hm.trans_le ((hT p hp).1.trans (hT p hp).2.1)
  have hpot : 0 < planarPotentialConstant s t := planarPotentialConstant_pos hst
  have hcrit : 0 < planarCriticalConstant N t := by unfold planarCriticalConstant; positivity
  have hE : 0 < pencilEnergyBudget N s t K M P := by unfold pencilEnergyBudget; positivity
  have hH : 0 < pencilMomentBudget N s t K M P := by unfold pencilMomentBudget; positivity
  have hQ : 0 < Q := by dsimp [Q,pencilEnergyCutoff]; positivity
  have hgeom : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l :=
    fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.1,(hT x hx).2.2.2.2⟩
  have hbudget : 16*pencilEnergyBudget N s t K M P*pencilMomentBudget N s t K M P ≤
      Q*(m*(P.card:ℝ))^2 := by
    dsimp [Q,pencilEnergyCutoff]
    rw [div_mul_cancel₀ _ (by positivity : (m*(P.card:ℝ))^2 ≠ 0)]
  obtain ⟨R,hRP,hR,hhalf,hgood⟩ := prune_high_energy_pencils P T
    (pencilFiberEnergy N (t-s) P T) hP hm hQ (fun x hx => (hT x hx).1)
    (fun l _ => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
      split <;> positivity)
    (pencil_fiber_energy_average N hs hst.le hK hM.le P T hPchart hPball hgeom)
    (pencil_second_moment_bound N hs hst hK P T hPchart hPball hgeom) hbudget
  refine ⟨R,hRP,hR,hhalf,?_,?_⟩
  · simpa only [mul_comm K 2] using normalized_finite_ball_bound_subset
      (by positivity : 0 ≤ 1/(2:ℝ)^N) hK0.le hRP
      (show (P.card:ℝ) ≤ 2*(R.card:ℝ) by linarith only [hhalf]) hPball
  · intro x hx
    refine ⟨hgood x hx,?_⟩
    apply normalized_finite_ball_bound_subset (by positivity : 0 ≤ 1/(2:ℝ)^N)
      hK0.le (Finset.filter_subset _ _) _ (hT x (hRP hx)).2.2.2.1
    calc
      _ ≤ M := (hT x (hRP hx)).2.1
      _ = (2*M/m)*(m/2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgood x hx) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SelectedRegularFiber
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select an actual incident tube and a regular subset of its point fiber. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencilFiberEnergy_mono (N : ℕ) (τ : ℝ)
    (P R : Finset (Space 2)) (T U : Space 2 → Finset (Space 2))
    (hRP : R ⊆ P) (hUT : ∀ x ∈ R, U x ⊆ T x) (l : Space 2) :
    pencilFiberEnergy N τ R U l ≤ pencilFiberEnergy N τ P T l := by
  unfold pencilFiberEnergy
  apply (Finset.sum_le_sum_of_subset_of_nonneg hRP (fun x _ _ =>
    Finset.sum_nonneg fun y _ => by split <;> positivity)).trans'
  apply Finset.sum_le_sum
  intro x hx
  apply (Finset.sum_le_sum_of_subset_of_nonneg hRP (fun y _ _ => by split <;> positivity)).trans'
  apply Finset.sum_le_sum
  intro y hy
  by_cases h : l ∈ U x ∧ l ∈ U y
  · rw [ite_eq_left h,ite_eq_left ⟨hUT x hx h.1,hUT y hy h.2⟩]
  · rw [ite_eq_right h]
    split <;> positivity

theorem regular_fiber_of_pencil_degree (N : ℕ) {τ m L Q : ℝ}
    (hτ : 0 ≤ τ) (hm : 0 < m) (hL : 0 < L) (hQ : 0 < Q)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hcard : ∀ x ∈ P, m ≤ ((T x).card:ℝ))
    (hunion : ((P.biUnion T).card:ℝ) ≤ L)
    (henergy : ∀ l ∈ P.biUnion T, pencilFiberEnergy N τ P T l ≤ Q) :
    ∃ l ∈ P.biUnion T, ∃ S ⊆ P, S.Nonempty ∧
      m*(P.card:ℝ)/(2*L) ≤ (S.card:ℝ) ∧ (∀ x ∈ S, l ∈ T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) τ
        (4*Q*(L/(m*(P.card:ℝ)))^2*(2:ℝ)^τ) S := by
  let V := P.biUnion T
  let D := m*(P.card:ℝ)/L
  let B := Q*(L/(m*(P.card:ℝ)))^2
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hI : m*(P.card:ℝ) ≤ ∑ l ∈ V, tubeDegree P T l := by
    rw [sum_tubeDegree]
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hcard
  have hV : V.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty] at hI
    exact (mul_pos hm hPc).not_ge hI
  have hmean : (∑ _l ∈ V, D) ≤ ∑ l ∈ V, tubeDegree P T l := by
    calc
      _ = D*(V.card:ℝ) := by simp; ring
      _ ≤ D*L := mul_le_mul_of_nonneg_left hunion hD.le
      _ = m*(P.card:ℝ) := by dsimp [D]; field_simp
      _ ≤ _ := hI
  obtain ⟨l,hl,hdegree⟩ := Finset.exists_le_of_sum_le hV hmean
  have hBD : B*D^2 = Q := by dsimp [B,D]; field_simp
  have henergy' : pencilFiberEnergy N τ P T l ≤ B*(tubeDegree P T l)^2 := by
    calc
      _ ≤ Q := henergy l hl
      _ = B*D^2 := hBD.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_le_sq₀ hD.le (hD.le.trans hdegree) |>.2 hdegree) hB.le
  obtain ⟨S,hSP,hS,hhalf,hinc,hreg⟩ := pencil_fiber_regular_subset N hτ hB P T l
    (hD.trans_le hdegree) henergy'
  refine ⟨l,hl,S,hSP,hS,?_,hinc,?_⟩
  · calc
      _ = D/2 := by dsimp [D]; ring
      _ ≤ tubeDegree P T l/2 := by gcongr
      _ ≤ _ := hhalf
  · convert hreg using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B]
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeometricRegularFiber
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected regular fiber with all energy and incidence estimates
supplied by the original geometric configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem geometric_regular_fiber (N : ℕ) {s t K M m L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m) (hL : 0 < L)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ L) :
    ∃ l ∈ P.biUnion T, ∃ S ⊆ P, S.Nonempty ∧
      m*(P.card:ℝ)/(8*L) ≤ (S.card:ℝ) ∧ (∀ x ∈ S, l ∈ T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) (t-s)
        (4*pencilEnergyCutoff N s t K M m P*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s)) S := by
  let Q := pencilEnergyCutoff N s t K M m P
  let U := fun x => (T x).filter fun l => pencilFiberEnergy N (t-s) P T l ≤ Q
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨p,hp⟩ := hP.exists_mem
  have hM : 0 < M := hm.trans_le ((hT p hp).1.trans (hT p hp).2.1)
  have hpot : 0 < planarPotentialConstant s t := planarPotentialConstant_pos hst
  have hcrit : 0 < planarCriticalConstant N t := by unfold planarCriticalConstant; positivity
  have hQ : 0 < Q := by
    dsimp [Q,pencilEnergyCutoff,pencilEnergyBudget,pencilMomentBudget]
    positivity
  obtain ⟨R,hRP,hR,hhalf,_,hgood⟩ := prune_pencil_fiber_energy N hs hst hK hm
    P T hP hPchart hPball hT
  have hUR : R.biUnion U ⊆ P.biUnion T := by
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hRP hx,(Finset.mem_filter.mp hl).1⟩
  have hRcard : 0 < (R.card:ℝ) := Nat.cast_pos.mpr hR.card_pos
  obtain ⟨l,hl,S,hSR,hS,hsize,hinc,hreg⟩ := regular_fiber_of_pencil_degree N
    (sub_nonneg.mpr hst.le) (show 0 < m/2 by positivity) hL hQ R U hR
    (fun x hx => (hgood x hx).1)
    ((Nat.cast_le.mpr (Finset.card_le_card hUR)).trans hunion) (by
      intro l hl
      obtain ⟨x,hx,hlx⟩ := Finset.mem_biUnion.mp hl
      exact (pencilFiberEnergy_mono N (t-s) P R T U hRP
        (fun _ _ => Finset.filter_subset _ _) l).trans (Finset.mem_filter.mp hlx).2)
  refine ⟨l,hUR hl,S,hSR.trans hRP,hS,?_,?_,?_⟩
  · apply le_trans _ hsize
    apply (div_le_div_iff₀ (by positivity : 0 < 8*L) (by positivity : 0 < 2*L)).2
    have hh := mul_le_mul_of_nonneg_left hhalf hm.le
    nlinarith only [hh,hL]
  · exact fun x hx => (Finset.mem_filter.mp (hinc x hx)).1
  · have hd : m*(P.card:ℝ)/4 ≤ (m/2)*(R.card:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hhalf hm.le
      linarith only [hh]
    have hratio : L/((m/2)*(R.card:ℝ)) ≤ 4*L/(m*(P.card:ℝ)) := by
      calc
        _ ≤ L/(m*(P.card:ℝ)/4) := div_le_div_of_nonneg_left hL.le (by positivity) hd
        _ = _ := by field_simp
    have hC : 4*Q*(L/((m/2)*(R.card:ℝ)))^2*(2:ℝ)^(t-s) ≤
        4*Q*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s) := by gcongr
    intro z r hr hr1
    have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^N by positivity).trans hr
    exact (hreg z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionSampleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial costs for the robust projection step. These bounds
keep every loss explicit before the dyadic exponential absorption. -/
namespace Falconer

theorem projectionGapConstant_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < projectionGapConstant κ := by
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  unfold projectionGapConstant
  positivity

theorem planarPotentialConstant_gap {κ s t : ℝ} (hκ : 0 < κ)
    (hs : s ≤ 1) (hgap : κ ≤ t-s) :
    planarPotentialConstant s t ≤ projectionGapConstant κ := by
  have hp : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have hq : (2:ℝ)^(s-t) ≤ (2:ℝ)^(-κ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap])
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  have hden : 1-(2:ℝ)^(-κ) ≤ 1-(2:ℝ)^(s-t) := by linarith only [hq]
  have hquot : (2:ℝ)^s/(1-(2:ℝ)^(s-t)) ≤ 2/(1-(2:ℝ)^(-κ)) :=
    (div_le_div_of_nonneg_right hp (hd.le.trans hden)).trans
      (div_le_div_of_nonneg_left (by norm_num) hd hden)
  have hden0 : 0 < 1-(2:ℝ)^(s-t) := hd.trans_le hden
  have hq0 : 0 ≤ (2:ℝ)^s/(1-(2:ℝ)^(s-t)) := by positivity
  unfold planarPotentialConstant projectionGapConstant
  gcongr

 theorem projectionEnergyBudget_upper (N : ℕ) {s t KI KP D H : ℝ}
    (hst : s < t) (hs : s ≤ 1) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) (hD : 1 ≤ D)
    (hKIup : KI ≤ D) (hKPup : KP ≤ D)
    (hpotential : planarPotentialConstant s t ≤ H) :
    projectionEnergyBudget N s t KI KP ≤ (1+32*H)*((N:ℝ)+1)*D^2 := by
  have h2 : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have h8 : (8:ℝ)^s ≤ 8 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hs
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hpotential0 : 0 < planarPotentialConstant s t := planarPotentialConstant_pos hst
  have hpoly : 1 ≤ ((N:ℝ)+1)*D^2 := by
    have hh : 1 ≤ D^2 := one_le_pow₀ hD
    nlinarith only [hN,hh]
  have hlarge : 1+(N:ℝ)*(2:ℝ)^s ≤ 2*((N:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_left h2 hN
    linarith only [hh]
  unfold projectionEnergyBudget
  calc
    _ ≤ 1+(2*(2*((N:ℝ)+1))*D*8)*D*H := by gcongr
    _ = 1+32*H*((N:ℝ)+1)*D^2 := by ring
    _ ≤ _ := by nlinarith only [hpoly]

theorem projection_sample_log_budget (N : ℕ) :
    1-10*Real.log ((1/(2:ℝ)^N)/4) ≤ 100*((N:ℝ)+1) := by
  have he : (1/(2:ℝ)^N)/4 = 1/(2:ℝ)^(N+2) := by
    rw [pow_add]
    norm_num
    ring
  rw [he,Real.log_div one_ne_zero (by positivity),Real.log_one,Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  push_cast
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  nlinarith only [hlog,hN,mul_le_mul_of_nonneg_left hlog (show 0 ≤ (N:ℝ)+2 by positivity)]

theorem projectedSubsetSampleConstant_upper (N : ℕ) {s t KI KP ρ D H : ℝ}
    (hst : s < t) (hs : s ≤ 1) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP)
    (hD : 1 ≤ D) (hKIup : KI ≤ D) (hKPup : KP ≤ D)
    (hρ : 0 < ρ) (hρlow : 1/D ≤ ρ) (hH : 0 ≤ H)
    (hpotential : planarPotentialConstant s t ≤ H) :
    projectedSubsetSampleConstant N s t KI KP ρ ≤
      (512*(64*Real.exp 1*(1+32*H)+100)^2)*((N:ℝ)+1)^2*D^8 := by
  let E := projectionEnergyBudget N s t KI KP
  let A := 1+32*H
  let C := (2*(2*E)/ρ)*(2/ρ)*(2:ℝ)^s
  let B := 1-10*Real.log ((1/(2:ℝ)^N)/4)
  have hE : 0 < E := projectionEnergyBudget_pos N hst hKI hKP
  have hA : 0 < A := by dsimp [A]; positivity
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hD4 : 1 ≤ D^4 := one_le_pow₀ hD
  have hinv : 1/ρ ≤ D := by
    apply (div_le_iff₀ hρ).2
    have hh := (div_le_iff₀ hD0).1 hρlow
    linarith only [hh]
  have h2 : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have h4 : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) hs
  have h8 : (8:ℝ)^s ≤ 8 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 8) hs
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 16*A*((N:ℝ)+1)*D^4 := by
    have hfirst : 2*(2*E)/ρ ≤ 4*E*D := by
      calc
        _ = 4*E*(1/ρ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
    have hsecond : 2/ρ ≤ 2*D := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ) ≤ 2)
    calc
      C ≤ (4*E*D)*(2*D)*2 := by dsimp [C]; gcongr
      _ = 16*E*D^2 := by ring
      _ ≤ 16*(A*((N:ℝ)+1)*D^2)*D^2 := by
        gcongr
        exact projectionEnergyBudget_upper N hst hs hKI hKP hD hKIup hKPup hpotential
      _ = _ := by ring
  have hB : B ≤ 100*((N:ℝ)+1)*D^4 := by
    have hh := mul_le_mul_of_nonneg_left hD4
      (show 0 ≤ 100*((N:ℝ)+1) by positivity)
    exact (projection_sample_log_budget N).trans
      (by simpa only [mul_one] using hh)
  have hγ : 0 < (1/(2:ℝ)^N)/4 := by positivity
  have hγ1 : (1/(2:ℝ)^N)/4 ≤ 1 := by
    have hh : 1/(2:ℝ)^N ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
    linarith only [hh]
  have hB0 : 0 ≤ B := by
    have hh := Real.log_nonpos hγ.le hγ1
    dsimp [B]
    linarith only [hh]
  have hexp : 0 ≤ Real.exp 1-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hT : ((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s ≤
      8*(64*Real.exp 1*A+100)*((N:ℝ)+1)*D^4 := by
    calc
      _ ≤ (Real.exp 1*((16*A*((N:ℝ)+1)*D^4)*4)+100*((N:ℝ)+1)*D^4)*8 := by
        gcongr
        linarith only
      _ = _ := by ring
  have hT0 : 0 ≤ ((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s := by positivity
  change 2*(2*(((Real.exp 1-1)*(C*(4:ℝ)^s)+B)*(8:ℝ)^s))^2 ≤ _
  calc
    _ ≤ 2*(2*(8*(64*Real.exp 1*A+100)*((N:ℝ)+1)*D^4))^2 := by gcongr
    _ = _ := by dsimp [A]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionPowerBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit quadratic depth loss in projection sampling fits into
any prescribed positive dyadic power, uniformly over a fixed exponent gap. -/
namespace Falconer

theorem dyadic_quadratic_loss {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*((N:ℝ)+1)^2 ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  let a := η*Real.log 2
  have ha : 0 < a := mul_pos hη (Real.log_pos (by norm_num))
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1 (24*C/a^3))
  have hN01 : (1:ℝ) ≤ N0 := (le_max_left _ _).trans hN0.le
  refine ⟨N0,by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN01),?_⟩
  intro N hN
  have hNN : (N0:ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN1 : (1:ℝ) ≤ N := hN01.trans hNN
  have hscale : 24*C ≤ a^3*(N:ℝ) := by
    have hh := (le_max_right _ _).trans (hN0.le.trans hNN)
    have he := (div_le_iff₀ (pow_pos ha 3)).1 hh
    nlinarith only [he]
  have hsize : ((N:ℝ)+1)^2 ≤ (2*(N:ℝ))^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hN1]) 2
  have hcub := mul_le_mul_of_nonneg_right hscale (sq_nonneg (N:ℝ))
  calc
    _ ≤ C*(2*(N:ℝ))^2 := mul_le_mul_of_nonneg_left hsize hC
    _ ≤ (a*(N:ℝ))^3/6 := by nlinarith only [hcub]
    _ ≤ Real.exp (a*(N:ℝ)) := by
      simpa only [Nat.factorial_succ,Nat.factorial_zero,Nat.reduceAdd,Nat.reduceMul,
        Nat.cast_ofNat] using Real.pow_div_factorial_le_exp (a*(N:ℝ))
          (by positivity : 0 ≤ a*(N:ℝ)) 3
    _ = _ := by congr 1; dsimp [a]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiberRegularityBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial loss for the regular fiber selected from coarse pencils. -/
namespace Falconer

theorem planarCriticalConstant_upper (N : ℕ) {t : ℝ} (ht : t ≤ 2) :
    planarCriticalConstant N t ≤ 21*((N:ℝ)+1) := by
  have h2 : (2:ℝ)^t ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
      _ = 4 := by norm_num
  unfold planarCriticalConstant
  calc
    _ ≤ 1+4*(1+(N:ℝ)*4) := by gcongr
    _ ≤ _ := by have := Nat.cast_nonneg (α := ℝ) N; linarith

theorem regular_fiber_constant_eq (N : ℕ) (s t K M m L : ℝ)
    (P : Finset (Space 2)) (hm : m ≠ 0) (hP : (P.card:ℝ) ≠ 0) :
    4*pencilEnergyCutoff N s t K M m P*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s) =
      1024*(K*(80*(1/(2:ℝ)^N))^s*M)^2*(L/m^2)^2*
        (1+2*K*planarCriticalConstant N t)*(1+K*planarPotentialConstant s t)*
        (2:ℝ)^(t-s) := by
  unfold pencilEnergyCutoff pencilEnergyBudget pencilMomentBudget
  field_simp
  ring

theorem regular_fiber_constant_upper (N : ℕ) {κ s t K M m L D : ℝ}
    (hκ : 0 < κ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : t ≤ 2) (hgap : κ ≤ t-s)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hm : 0 < m) (hL : 0 ≤ L)
    (hD : 1 ≤ D) (hKD : K ≤ D)
    (hMD : M ≤ D/(1/(2:ℝ)^N)^s)
    (hmD : 1/(D*(1/(2:ℝ)^N)^s) ≤ m)
    (hLD : L ≤ D/((1/(2:ℝ)^N)^s)^2)
    (P : Finset (Space 2)) (hP : P.Nonempty) :
    4*pencilEnergyCutoff N s t K M m P*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s) ≤
      (1127219200*(1+projectionGapConstant κ))*((N:ℝ)+1)*D^12 := by
  have hst : s < t := by linarith only [hκ,hgap]
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hδ _
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hs1
  have hA : K*(80*(1/(2:ℝ)^N))^s*M ≤ 80*D^2 := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le]
    calc
      _ ≤ D*(80*(1/(2:ℝ)^N)^s)*(D/(1/(2:ℝ)^N)^s) := by gcongr
      _ = _ := by field_simp
  have hB : L/m^2 ≤ D^3 := by
    calc
      _ ≤ (D/((1/(2:ℝ)^N)^s)^2)/(1/(D*(1/(2:ℝ)^N)^s))^2 := by
        gcongr
      _ = _ := by field_simp
  have hcrit0 : 0 ≤ planarCriticalConstant N t := by
    unfold planarCriticalConstant
    positivity
  have hpot0 : 0 ≤ planarPotentialConstant s t := (planarPotentialConstant_pos hst).le
  have hcrit : 1+2*K*planarCriticalConstant N t ≤ 43*D*((N:ℝ)+1) := by
    calc
      _ ≤ 1+2*D*(21*((N:ℝ)+1)) := by
        gcongr
        exact planarCriticalConstant_upper N ht
      _ ≤ _ := by
        have hh : 1 ≤ D*((N:ℝ)+1) := by
          calc
            1 ≤ D := hD
            _ ≤ D*((N:ℝ)+1) := by nlinarith only [mul_nonneg hD0.le (Nat.cast_nonneg (α := ℝ) N)]
        nlinarith only [hh]
  have hH : 0 < projectionGapConstant κ := projectionGapConstant_pos hκ
  have hpot : 1+K*planarPotentialConstant s t ≤ (1+projectionGapConstant κ)*D := by
    calc
      _ ≤ 1+D*projectionGapConstant κ := by
        gcongr
        exact planarPotentialConstant_gap hκ hs1 hgap
      _ ≤ _ := by nlinarith only [hD]
  have h2 : (2:ℝ)^(t-s) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith only [ht,hs])
      _ = 4 := by norm_num
  rw [regular_fiber_constant_eq N s t K M m L P (ne_of_gt hm)
    (ne_of_gt (Nat.cast_pos.mpr hP.card_pos))]
  calc
    _ ≤ 1024*(80*D^2)^2*(D^3)^2*(43*D*((N:ℝ)+1))*
        ((1+projectionGapConstant κ)*D)*4 := by
      gcongr
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direction sets of separated pencils. The fixed multiplicity and
regularity costs are proved from the original point-line incidence. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem pencil_slope_fiber_card {δ : ℝ} (hδ : 0 < δ) (p : Space 2)
    (T : Finset (Space 2)) (hsep : FiniteSeparatedAt δ T)
    (hchart : InBoundedLineChart T) (hinc : ∀ l ∈ T, TubeIncident δ p l) (a : ℝ) :
    ((T.filter fun l => l 0 = a).card:ℝ) ≤ 25 := by
  let S := T.filter fun l => l 0 = a
  let z := rowPoint a (p 1-a*p 0)
  have hwithin : ∀ l ∈ S, dist l z ≤ 2*δ := by
    intro l hl
    obtain ⟨hlT,hl0⟩ := Finset.mem_filter.mp hl
    rw [row_dist_projection hl0]
    have hh := tube_residual_le hδ.le (hchart l hlT).1 (hinc l hlT)
    rw [hl0] at hh
    change |l 1-(p 1-a*p 0)| ≤ 2*δ
    rw [abs_sub_comm]
    exact hh
  have hb := separated_ball_card S z hδ (r := 2*δ) (by positivity)
    (finiteSeparatedAt_subset (Finset.filter_subset _ _) hsep) hwithin
  have he : (2*(2*δ)/δ+1)^2 = (25:ℝ) := by field_simp; ring
  rwa [he] at hb

theorem pencil_slope_card {δ : ℝ} (hδ : 0 < δ) (p : Space 2)
    (T : Finset (Space 2)) (hsep : FiniteSeparatedAt δ T)
    (hchart : InBoundedLineChart T) (hinc : ∀ l ∈ T, TubeIncident δ p l) :
    (T.card:ℝ) ≤ 25*((T.image fun l => l 0).card:ℝ) := by
  have hh := card_le_image_card_mul_fiber_bound T (fun l => l 0)
    (fun a _ => pencil_slope_fiber_card hδ p T hsep hchart hinc a)
  simpa only [mul_comm] using hh

theorem pencil_slope_strip_card {δ r s K u : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (p : Space 2) (hp : |p 0| ≤ 1)
    (T : Finset (Space 2)) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ p l) (hreg : NormalizedFiniteBallBound δ s K T) :
    ((T.filter fun l => |l 0-u| ≤ r).card:ℝ) ≤ K*(4*r)^s*(T.card:ℝ) := by
  let z := rowPoint u (p 1-u*p 0)
  have hsub : T.filter (fun l => |l 0-u| ≤ r) ⊆ T.filter (fun l => dist l z ≤ 4*r) := by
    intro l hl
    obtain ⟨hlT,hlu⟩ := Finset.mem_filter.mp hl
    refine Finset.mem_filter.mpr ⟨hlT,?_⟩
    have hres := tube_residual_le hδ.le (hchart l hlT).1 (hinc l hlT)
    have hres' : |l 1-(p 1-l 0*p 0)| ≤ 2*δ := by
      rw [abs_sub_comm]
      exact hres
    have hprod : |(p 1-l 0*p 0)-(p 1-u*p 0)| ≤ r := by
      rw [show (p 1-l 0*p 0)-(p 1-u*p 0) = -(l 0-u)*p 0 by ring,abs_mul,abs_neg]
      exact (mul_le_mul hlu hp (abs_nonneg _) (hδ.le.trans hr)).trans_eq (mul_one r)
    have h1 : |l 1-(p 1-u*p 0)| ≤ 3*r := by
      have hh := (abs_sub_le (l 1) (p 1-l 0*p 0) (p 1-u*p 0)).trans (add_le_add hres' hprod)
      linarith only [hh,hr]
    have hd := planar_dist_le_coordinate_sum l z
    change dist l z ≤ |l 0-u|+|l 1-(p 1-u*p 0)| at hd
    linarith only [hd,hlu,h1]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (normalized_ball_bound_all_radii hs hK hreg z (4*r) (by linarith only [hr,hδ]))

theorem pencil_slope_regular {δ s K : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (p : Space 2) (hp : |p 0| ≤ 1) (T : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ T) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ p l) (hreg : NormalizedFiniteBallBound δ s K T) :
    ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (T.image fun l => l 0) u r ≤
        (25*K*(4:ℝ)^s)*r^s*((T.image fun l => l 0).card:ℝ) := by
  intro u r hr _
  have hsub : (T.image fun l => l 0).filter (fun a => |a-u| ≤ r) ⊆
      (T.filter fun l => |l 0-u| ≤ r).image (fun l => l 0) := by
    intro a ha
    obtain ⟨haT,har⟩ := Finset.mem_filter.mp ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp haT
    exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,har⟩,rfl⟩
  have hc := pencil_slope_card hδ p T hsep hchart hinc
  have hr0 : 0 ≤ r := hδ.le.trans hr
  calc
    _ ≤ ((T.filter fun l => |l 0-u| ≤ r).card:ℝ) := by
      unfold scalarBallMass
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(4*r)^s*(T.card:ℝ) := pencil_slope_strip_card hδ hr hs hK p hp T hchart hinc hreg
    _ ≤ K*(4*r)^s*(25*((T.image fun l => l 0).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GoodPencilDirections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain actual coarse tubes whose transverse directions have good
projected energy. The fiber multiplicity costs at most the fixed factor 50. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem scalarBallMass_neg (I : Finset ℝ) (u r : ℝ) :
    scalarBallMass (I.image Neg.neg) u r = scalarBallMass I (-u) r := by
  unfold scalarBallMass
  rw [Finset.filter_image,Finset.card_image_of_injective _ neg_injective]
  congr 2
  apply Finset.filter_congr
  intro x _
  have he : |-x-u| = |x-(-u)| := by
    rw [show -x-u = -(x-(-u)) by ring,abs_neg]
  rw [he]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarserPencilDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good projected directions for a packet eight times wider than its
coarse grid cells, at the actual normalized fine-point resolution. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem good_pencil_projection_directions_coarser (N : ℕ) {s t K KP : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hKP : 1 ≤ KP)
    (p : Space 2) (hp : |p 0| ≤ 1) (T : Finset (Space 2)) (hT : T.Nonempty)
    (hsep : FiniteSeparatedAt (1/(2:ℝ)^(N+3)) T) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident (1/(2:ℝ)^(N+3)) p l)
    (hreg : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s K T)
    (P : Finset (Space 2)) (hP : P.Nonempty) (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP P) :
    ∃ U ⊆ T, U.Nonempty ∧ (T.card:ℝ) ≤ 50*(U.card:ℝ) ∧
      FiniteSeparatedAt (1/(2:ℝ)^(N+3)) U ∧ InBoundedLineChart U ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s (50*K) U ∧
      ∀ l ∈ U, planarProjectionEnergy N s (-l 0) P ≤
        2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*(P.card:ℝ)^2 := by
  let I := T.image (fun l => l 0)
  let D := I.image Neg.neg
  have hδ : 0 < 1/(2:ℝ)^(N+3) := by positivity
  have hKI : 1 ≤ 25*K*(4:ℝ)^s := by
    have h4 : (1:ℝ) ≤ (4:ℝ)^s := Real.one_le_rpow (by norm_num) hs
    have hm := mul_le_mul hK h4 (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
    nlinarith only [hm]
  have hscale : 1/(2:ℝ)^(N+3) ≤ 1/(2:ℝ)^N := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hDcard : D.card = I.card := Finset.card_image_of_injective _ neg_injective
  have hDbound : ∀ c ∈ D, |c| ≤ 1 := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
    simpa only [abs_neg] using (hchart l hl).1
  have hDball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass D u r ≤ (25*K*(4:ℝ)^s)*r^s*(D.card:ℝ) := by
    intro u r hr hr1
    change scalarBallMass (I.image Neg.neg) u r ≤ _
    rw [scalarBallMass_neg,hDcard]
    exact pencil_slope_regular hδ hs hK p hp T hsep hchart hinc hreg (-u) r (hscale.trans hr) hr1
  obtain ⟨J,hJD,hhalf,henergy⟩ := good_projection_directions N hs hst hKI hKP
    D P hP hDbound hPchart hDball hPball
  let U := T.filter (fun l => -l 0 ∈ J)
  have hUT : U ⊆ T := Finset.filter_subset _ _
  have hJU : J ⊆ U.image (fun l => -l 0) := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hJD hc)
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,hc⟩,rfl⟩
  have hJUcard : (J.card:ℝ) ≤ (U.card:ℝ) :=
    Nat.cast_le.mpr ((Finset.card_le_card hJU).trans Finset.card_image_le)
  have hTcard := pencil_slope_card hδ p T hsep hchart hinc
  have hloss : (T.card:ℝ) ≤ 50*(U.card:ℝ) := by
    change (T.card:ℝ) ≤ 25*(I.card:ℝ) at hTcard
    rw [hDcard] at hhalf
    linarith only [hhalf,hTcard,hJUcard]
  have hUne : U.Nonempty := by
    have htpos : 0 < (T.card:ℝ) := Nat.cast_pos.mpr hT.card_pos
    apply Finset.card_pos.mp
    exact Nat.cast_pos.mp (show 0 < (U.card:ℝ) by linarith only [htpos,hloss])
  refine ⟨U,hUT,hUne,hloss,finiteSeparatedAt_subset hUT hsep,
    (fun l hl => hchart l (hUT hl)),?_,?_⟩
  · simpa only [mul_comm K 50] using normalized_finite_ball_bound_subset hδ.le
      (zero_le_one.trans hK) hUT hloss hreg
  · intro l hl
    exact henergy (-l 0) (Finset.mem_filter.mp hl).2


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketGoodRegularFiber
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single original coarse tube with a regular family of incident cells,
all of whose local point sets have good transverse projected energy. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem packet_good_regular_fiber (N : ℕ) {s t K KP m M L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hKP : 1 ≤ KP)
    (hm : 0 < m) (hL : 0 < L)
    (C : Finset (Space 2)) (T Q : Space 2 → Finset (Space 2)) (hC : C.Nonempty)
    (hCchart : InBoundedLineChart C)
    (hCball : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t K C)
    (hT : ∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^(N+3)) x l)
    (hQ : ∀ x ∈ C, (Q x).Nonempty ∧ InBoundedLineChart (Q x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP (Q x))
    (hunion : ((C.biUnion T).card:ℝ) ≤ L) :
    ∃ l ∈ C.biUnion T, ∃ S ⊆ C, S.Nonempty ∧
      m*(C.card:ℝ)/(400*L) ≤ (S.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) (t-s)
        (4*pencilEnergyCutoff (N+3) s t (50*K) M (m/50) C*
          (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s)) S ∧
      ∀ x ∈ S, l ∈ T x ∧
        planarProjectionEnergy N s (-l 0) (Q x) ≤
          2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*((Q x).card:ℝ)^2 := by
  have hchoice (x : Space 2) (hx : x ∈ C) := good_pencil_projection_directions_coarser N hs hst
    hK hKP x (hCchart x hx).1 (T x)
    (Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le (hT x hx).1)))
    (hT x hx).2.2.2.1 (hT x hx).2.2.1 (hT x hx).2.2.2.2.2
    (hT x hx).2.2.2.2.1 (Q x) (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2
  let U := fun x => if hx : x ∈ C then Classical.choose (hchoice x hx) else ∅
  have hU (x : Space 2) (hx : x ∈ C) :
      U x ⊆ T x ∧ (U x).Nonempty ∧ ((T x).card:ℝ) ≤ 50*((U x).card:ℝ) ∧
      FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (U x) ∧ InBoundedLineChart (U x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s (50*K) (U x) ∧
      ∀ l ∈ U x, planarProjectionEnergy N s (-l 0) (Q x) ≤
        2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*((Q x).card:ℝ)^2 := by
    simpa only [U,dite_eq_left hx] using Classical.choose_spec (hchoice x hx)
  have hUU : C.biUnion U ⊆ C.biUnion T := by
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hx,(hU x hx).1 hl⟩
  have hK' : 1 ≤ 50*K := by linarith only [hK]
  have hCb : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t (50*K) C := by
    intro z r hr hr1
    have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^(N+3) by positivity).trans hr
    exact (hCball z r hr hr1).trans (by
      gcongr
      linarith only [hK])
  obtain ⟨l,hl,S,hSC,hS,hsize,hinc,hreg⟩ := geometric_regular_fiber (N+3) hs hst hK'
    (show 0 < m/50 by positivity) hL C U hC hCchart hCb (by
      intro x hx
      have hu := hU x hx
      refine ⟨?_,?_,hu.2.2.2.2.1,hu.2.2.2.2.2.1,?_⟩
      · have hh := (hT x hx).1
        linarith only [hh,hu.2.2.1]
      · exact (Nat.cast_le.mpr (Finset.card_le_card hu.1)).trans (hT x hx).2.1
      · exact fun a ha => (hT x hx).2.2.2.2.2 a (hu.1 ha))
    ((Nat.cast_le.mpr (Finset.card_le_card hUU)).trans hunion)
  refine ⟨l,hUU hl,S,hSC,hS,?_,hreg,?_⟩
  · convert hsize using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro x hx
    exact ⟨(hU x (hSC hx)).1 (hinc x hx),(hU x (hSC hx)).2.2.2.2.2.2 l (hinc x hx)⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TubeFiberCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection of a regular point fiber along its incident tube. The
coordinate set consists of original horizontal coordinates. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem tube_point_coordinate_fiber_card {δ : ℝ} (hδ : 0 < δ) (l : Space 2)
    (hl : |l 0| ≤ 1) (P : Finset (Space 2)) (hsep : FiniteSeparatedAt δ P)
    (hinc : ∀ p ∈ P, TubeIncident δ p l) (a : ℝ) :
    ((P.filter fun p => p 0 = a).card:ℝ) ≤ 25 := by
  let S := P.filter fun p => p 0 = a
  let z := rowPoint a (l 0*a+l 1)
  have hwithin : ∀ p ∈ S, dist p z ≤ 2*δ := by
    intro p hp
    obtain ⟨hpP,hp0⟩ := Finset.mem_filter.mp hp
    rw [row_dist_projection hp0]
    have hh := tube_residual_le hδ.le hl (hinc p hpP)
    change |p 1-(l 0*a+l 1)| ≤ 2*δ
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [hp0]
    congr 1
    ring
  have hb := separated_ball_card S z hδ (r := 2*δ) (by positivity)
    (finiteSeparatedAt_subset (Finset.filter_subset _ _) hsep) hwithin
  have he : (2*(2*δ)/δ+1)^2 = (25:ℝ) := by field_simp; ring
  rwa [he] at hb

theorem tube_point_coordinate_card {δ : ℝ} (hδ : 0 < δ) (l : Space 2)
    (hl : |l 0| ≤ 1) (P : Finset (Space 2)) (hsep : FiniteSeparatedAt δ P)
    (hinc : ∀ p ∈ P, TubeIncident δ p l) :
    (P.card:ℝ) ≤ 25*((P.image fun p => p 0).card:ℝ) := by
  have hh := card_le_image_card_mul_fiber_bound P (fun p => p 0)
    (fun a _ => tube_point_coordinate_fiber_card hδ l hl P hsep hinc a)
  simpa only [mul_comm] using hh

theorem tube_point_strip_card {δ r s K u : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (l : Space 2) (hl : |l 0| ≤ 1)
    (P : Finset (Space 2)) (hinc : ∀ p ∈ P, TubeIncident δ p l)
    (hreg : NormalizedFiniteBallBound δ s K P) :
    ((P.filter fun p => |p 0-u| ≤ r).card:ℝ) ≤ K*(4*r)^s*(P.card:ℝ) := by
  let z := rowPoint u (l 0*u+l 1)
  have hsub : P.filter (fun p => |p 0-u| ≤ r) ⊆ P.filter (fun p => dist p z ≤ 4*r) := by
    intro p hp
    obtain ⟨hpP,hpu⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpP,?_⟩
    have hres := tube_residual_le hδ.le hl (hinc p hpP)
    have hres' : |p 1-(l 0*p 0+l 1)| ≤ 2*δ := by convert hres using 1; congr 1; ring
    have hprod : |(l 0*p 0+l 1)-(l 0*u+l 1)| ≤ r := by
      rw [show (l 0*p 0+l 1)-(l 0*u+l 1) = l 0*(p 0-u) by ring,abs_mul]
      exact (mul_le_mul hl hpu (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul r)
    have h1 : |p 1-(l 0*u+l 1)| ≤ 3*r := by
      have hh := (abs_sub_le (p 1) (l 0*p 0+l 1) (l 0*u+l 1)).trans (add_le_add hres' hprod)
      linarith only [hh,hr]
    have hd := planar_dist_le_coordinate_sum p z
    change dist p z ≤ |p 0-u|+|p 1-(l 0*u+l 1)| at hd
    linarith only [hd,hpu,h1]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (normalized_ball_bound_all_radii hs hK hreg z (4*r) (by linarith only [hr,hδ]))

theorem tube_point_coordinates_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (l : Space 2) (hl : |l 0| ≤ 1)
    (P : Finset (Space 2)) (hsep : FiniteSeparatedAt δ P)
    (hinc : ∀ p ∈ P, TubeIncident δ p l) (hreg : NormalizedFiniteBallBound δ s K P) :
    ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass (P.image fun p => p 0) u r ≤
        (25*K*(4:ℝ)^s)*r^s*((P.image fun p => p 0).card:ℝ) := by
  intro u r hr _
  have hsub : (P.image fun p => p 0).filter (fun a => |a-u| ≤ r) ⊆
      (P.filter fun p => |p 0-u| ≤ r).image (fun p => p 0) := by
    intro a ha
    obtain ⟨haP,har⟩ := Finset.mem_filter.mp ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp haP
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,har⟩,rfl⟩
  have hc := tube_point_coordinate_card hδ l hl P hsep hinc
  have hr0 : 0 ≤ r := hδ.le.trans hr
  calc
    _ ≤ ((P.filter fun p => |p 0-u| ≤ r).card:ℝ) := by
      unfold scalarBallMass
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(4*r)^s*(P.card:ℝ) := tube_point_strip_card hδ hr hs hK l hl P hinc hreg
    _ ≤ K*(4*r)^s*(25*((P.image fun p => p 0).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RegularCoordinateRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select original cell representatives for the scalar row set of a
regular tube fiber. No new projected row labels are introduced. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem regular_coordinate_rows {δ τ K : ℝ} (hδ : 0 < δ)
    (hτ : 0 ≤ τ) (hK : 1 ≤ K) (l : Space 2) (hl : |l 0| ≤ 1)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hchart : InBoundedLineChart S)
    (hsep : FiniteSeparatedAt δ S) (hinc : ∀ p ∈ S, TubeIncident δ p l)
    (hreg : NormalizedFiniteBallBound δ τ K S) :
    let Y := S.image fun p => p 0
    Y.Nonempty ∧ (S.card:ℝ) ≤ 25*(Y.card:ℝ) ∧
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 →
        scalarBallMass Y u r ≤ (25*K*(4:ℝ)^τ)*r^τ*(Y.card:ℝ)) ∧
      ∃ c : ℝ → Space 2, ∀ y ∈ Y, c y ∈ S ∧ c y 0 = y ∧ |y| ≤ 1 := by
  let Y := S.image fun p => p 0
  have hrep (y : ℝ) (hy : y ∈ Y) : ∃ p ∈ S, p 0 = y := Finset.mem_image.mp hy
  let c := fun y => if hy : y ∈ Y then Classical.choose (hrep y hy) else 0
  refine ⟨hS.image _,tube_point_coordinate_card hδ l hl S hsep hinc,
    tube_point_coordinates_regular hδ hτ hK l hl S hsep hinc hreg,c,?_⟩
  intro y hy
  have hh := Classical.choose_spec (hrep y hy)
  have he : c y = Classical.choose (hrep y hy) := dite_eq_left hy
  refine ⟨he ▸ hh.1,he ▸ hh.2,?_⟩
  rw [← hh.2]
  exact (hchart _ hh.1).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GoodCoarseRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original coarse-cell rows on a tube with good local projection energies. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem good_coarse_rows (N : ℕ) {s t K KP m M L R τ : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hτ1 : τ ≤ 1) (hτ : τ ≤ t-s)
    (hK : 1 ≤ K) (hKP : 1 ≤ KP) (hm : 0 < m) (hL : 0 < L) (hR : 1 ≤ R)
    (C : Finset (Space 2)) (T Q : Space 2 → Finset (Space 2)) (hC : C.Nonempty)
    (hCchart : InBoundedLineChart C)
    (hCsep : FiniteSeparatedAt (1/(2:ℝ)^(N+3)) C)
    (hCball : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t K C)
    (hT : ∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^(N+3)) x l)
    (hQ : ∀ x ∈ C, (Q x).Nonempty ∧ InBoundedLineChart (Q x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP (Q x))
    (hunion : ((C.biUnion T).card:ℝ) ≤ L)
    (hbudget : 4*pencilEnergyCutoff (N+3) s t (50*K) M (m/50) C*
      (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s) ≤ R) :
    ∃ l ∈ C.biUnion T, ∃ Y : Finset ℝ, Y.Nonempty ∧
      m*(C.card:ℝ)/(10000*L) ≤ (Y.card:ℝ) ∧
      (∀ u r : ℝ, 1/(2:ℝ)^(N+3) ≤ r → r ≤ 1 →
        scalarBallMass Y u r ≤ (100*R)*r^τ*(Y.card:ℝ)) ∧
      ∃ c : ℝ → Space 2, ∀ y ∈ Y,
        c y ∈ C ∧ c y 0 = y ∧ |y| ≤ 1 ∧ l ∈ T (c y) ∧
        planarProjectionEnergy N s (-l 0) (Q (c y)) ≤
          2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*((Q (c y)).card:ℝ)^2 := by
  obtain ⟨l,hl,S,hSC,hS,hsize,hreg,hgood⟩ := packet_good_regular_fiber N hs hst hK hKP
    hm hL C T Q hC hCchart hCball hT hQ hunion
  have hregR : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) (t-s) R S := by
    intro z r hr hr1
    exact (hreg z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg ((by positivity : 0 ≤ 1/(2:ℝ)^(N+3)).trans hr) _))
      (Nat.cast_nonneg _))
  let v := min (t-s) 1
  have hv : 0 ≤ v := le_min (sub_nonneg.mpr hst.le) zero_le_one
  have hτv : τ ≤ v := le_min hτ hτ1
  have hregU : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) v R S := by
    intro z r hr hr1
    have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^(N+3)).trans_le hr
    exact (hregR z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr0 hr1
        (min_le_left _ _)) (zero_le_one.trans hR)) (Nat.cast_nonneg _))
  obtain ⟨x,hx,hlx⟩ := Finset.mem_biUnion.mp hl
  have hl0 : |l 0| ≤ 1 := ((hT x hx).2.2.1 l hlx).1
  obtain ⟨hY,hcard,hYball,c,hc⟩ := regular_coordinate_rows
    (by positivity : 0 < 1/(2:ℝ)^(N+3)) hv hR l hl0 S hS
    (fun x hx => hCchart x (hSC hx)) (finiteSeparatedAt_subset hSC hCsep)
    (fun x hx => (hT x (hSC hx)).2.2.2.2.2 l (hgood x hx).1) hregU
  refine ⟨l,hl,S.image (fun p => p 0),hY,?_,?_,c,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 10000*L)).2
    have hh := (div_le_iff₀ (by positivity : 0 < 400*L)).1 hsize
    have hh' := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 400*L by positivity)
    nlinarith only [hh,hh']
  · intro u r hr hr1
    have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^(N+3)).trans_le hr
    have h4 : (4:ℝ)^v ≤ 4 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ) ≤ 4) (min_le_right (t-s) (1:ℝ))
    have hp : r^v ≤ r^τ := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hτv
    calc
      _ ≤ (25*R*(4:ℝ)^v)*r^v*((S.image fun p => p 0).card:ℝ) := hYball u r hr hr1
      _ ≤ (25*R*4)*r^τ*((S.image fun p => p 0).card:ℝ) := by gcongr
      _ = _ := by ring
  · intro y hy
    have hh := hc y hy
    exact ⟨hSC hh.1,hh.2.1,hh.2.2,(hgood (c y) hh.1).1,(hgood (c y) hh.1).2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarsePacketPoints
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract many original points that retain many fine tubes in one coarse
packet. Both losses follow from the actual incidence count. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_large_weight_subset (P : Finset (Space 2)) (w : Space 2 → ℝ)
    {H B : ℝ} (hP : P.Nonempty) (hH : 0 < H) (hB : 0 < B)
    (hcap : ∀ x ∈ P, w x ≤ B) (hsum : H ≤ ∑ x ∈ P, w x) :
    ∃ A ⊆ P, A.Nonempty ∧ H/(2*B) ≤ (A.card:ℝ) ∧
      ∀ x ∈ A, H/(2*(P.card:ℝ)) ≤ w x := by
  let c := H/(2*(P.card:ℝ))
  let A := P.filter fun x => c ≤ w x
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound (x : Space 2) (hx : x ∈ P) :
      w x ≤ (if c ≤ w x then B else 0)+c := by
    by_cases h : c ≤ w x
    · rw [ite_eq_left h]
      exact (hcap x hx).trans (le_add_of_nonneg_right hc.le)
    · rw [ite_eq_right h,zero_add]
      exact (lt_of_not_ge h).le
  have htotal : H ≤ B*(A.card:ℝ)+H/2 := by
    calc
      _ ≤ ∑ x ∈ P, w x := hsum
      _ ≤ ∑ x ∈ P, ((if c ≤ w x then B else 0)+c) := Finset.sum_le_sum hbound
      _ = B*(A.card:ℝ)+H/2 := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
        dsimp [A,c]
        field_simp
  have hsize : H/(2*B) ≤ (A.card:ℝ) := (div_le_iff₀ (by positivity)).2 (by linarith only [htotal])
  have hAc : 0 < (A.card:ℝ) := (div_pos hH (by positivity)).trans_le hsize
  exact ⟨A,Finset.filter_subset _ _,Finset.card_pos.mp (Nat.cast_pos.mp hAc),hsize,
    fun x hx => (Finset.mem_filter.mp hx).2⟩

theorem coarse_packet_points {δ Δ s K M H : ℝ}
    (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hM : 0 < M) (hH : 0 < H)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (q : Space 2 → Space 2) (a : Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ Δ)
    (hball : ∀ x ∈ P, NormalizedFiniteBallBound δ s K (T x))
    (hcard : ∀ x ∈ P, ((T x).card:ℝ) ≤ M)
    (hweight : H ≤ (coarsePencilWeight P T q a:ℝ)) :
    ∃ A ⊆ P, A.Nonempty ∧ H/(2*(K*Δ^s*M)) ≤ (A.card:ℝ) ∧
      ∀ x ∈ A, H/(2*(P.card:ℝ)) ≤ (((T x).filter fun l => q l = a).card:ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  apply finite_large_weight_subset P (fun x => (((T x).filter fun l => q l = a).card:ℝ))
    hP hH (by positivity)
  · intro x hx
    have hsub : (T x).filter (fun l => q l = a) ⊆ (T x).filter (fun l => dist l a ≤ Δ) := by
      intro l hl
      obtain ⟨hlT,hla⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,by simpa only [hla] using hnear x hx l hlT⟩
    calc
      _ ≤ (((T x).filter fun l => dist l a ≤ Δ).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ K*Δ^s*((T x).card:ℝ) := normalized_ball_bound_all_radii hs hK (hball x hx) a Δ hδΔ
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcard x hx) (by positivity)
  · simpa only [coarsePencilWeight,Nat.cast_sum] using hweight

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuantitativePacketPoints
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit fine-point fractions and pencil bounds in a selected coarse
packet. These are the inputs used by the centered packet-growth theorem. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quantitative_packet_points {δ Δ s K m M J B : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hm : 0 < m) (hM : 0 < M) (hJ : 0 < J) (hB : 0 < B)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (q : Space 2 → Space 2) (a : Space 2)
    (hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ Δ)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ s K (T x) ∧
      ∀ l ∈ T x, |l 0| ≤ 1 ∧ TubeIncident δ x l)
    (hweight : ((∑ x ∈ P, (T x).card):ℝ) ≤ 2*J*B*(coarsePencilWeight P T q a:ℝ)) :
    ∃ A ⊆ P, A.Nonempty ∧
      (m/(4*J*B*(K*Δ^s*M)))*(P.card:ℝ) ≤ (A.card:ℝ) ∧
      ∀ x ∈ A,
        let U := (T x).filter fun l => q l = a
        U.Nonempty ∧ m/(4*J*B) ≤ (U.card:ℝ) ∧ (U.card:ℝ) ≤ K*Δ^s*M ∧
        FiniteSeparatedAt δ U ∧ NormalizedFiniteBallBound δ s (K*(4*J*B*M/m)) U ∧
        ∀ l ∈ U, |l 0| ≤ 1 ∧ |l 0-a 0| ≤ Δ ∧ |l 1-a 1| ≤ Δ ∧ TubeIncident δ x l := by
  let H := m*(P.card:ℝ)/(2*J*B)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hH : 0 < H := by dsimp [H]; positivity
  have hI : m*(P.card:ℝ) ≤ ((∑ x ∈ P, (T x).card):ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hHw : H ≤ (coarsePencilWeight P T q a:ℝ) :=
    (div_le_iff₀ (by positivity)).2 (by nlinarith only [hI,hweight])
  obtain ⟨A,hAP,hA,hsize,hlarge⟩ := coarse_packet_points hΔ hδΔ hs hK hM hH P T hP q a hnear
    (fun x hx => (hT x hx).2.2.2.1) (fun x hx => (hT x hx).2.1) hHw
  have hlow (x : Space 2) (hx : x ∈ A) :
      m/(4*J*B) ≤ (((T x).filter fun l => q l = a).card:ℝ) := by
    convert hlarge x hx using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [H]
    field_simp
    norm_num
  have hup (x : Space 2) (hx : x ∈ A) :
      (((T x).filter fun l => q l = a).card:ℝ) ≤ K*Δ^s*M := by
    have hsub : (T x).filter (fun l => q l = a) ⊆ (T x).filter (fun l => dist l a ≤ Δ) := by
      intro l hl
      obtain ⟨hlT,hla⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,by simpa only [hla] using hnear x (hAP hx) l hlT⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((normalized_ball_bound_all_radii hs hK (hT x (hAP hx)).2.2.2.1 a Δ hδΔ).trans
        (mul_le_mul_of_nonneg_left (hT x (hAP hx)).2.1 (by positivity)))
  refine ⟨A,hAP,hA,?_,?_⟩
  · convert hsize using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [H]
    field_simp
    ring
  · intro x hx
    dsimp only
    have hl := hlow x hx
    have hUc : 0 < (((T x).filter fun l => q l = a).card:ℝ) := (by positivity : 0 < m/(4*J*B)).trans_le hl
    have hratio : ((T x).card:ℝ) ≤ (4*J*B*M/m)*(((T x).filter fun l => q l = a).card:ℝ) := by
      calc
        _ ≤ M := (hT x (hAP hx)).2.1
        _ = (4*J*B*M/m)*(m/(4*J*B)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
    refine ⟨Finset.card_pos.mp (Nat.cast_pos.mp hUc),hl,hup x hx,
      finiteSeparatedAt_subset (Finset.filter_subset _ _) (hT x (hAP hx)).2.2.1,
      normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK)
        (Finset.filter_subset _ _) hratio (hT x (hAP hx)).2.2.2.1,?_⟩
    intro l hl
    obtain ⟨hlT,hla⟩ := Finset.mem_filter.mp hl
    have hd : dist l a ≤ Δ := by simpa only [hla] using hnear x (hAP hx) l hlT
    exact ⟨((hT x (hAP hx)).2.2.2.2 l hlT).1,
      (show |l 0-a 0| ≤ dist l a by simpa only [Real.dist_eq] using PiLp.dist_apply_le l a 0).trans hd,
      (show |l 1-a 1| ≤ dist l a by simpa only [Real.dist_eq] using PiLp.dist_apply_le l a 1).trans hd,
      ((hT x (hAP hx)).2.2.2.2 l hlT).2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketParameterBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All four losses in weighted fine-packet extraction are polynomial in
the original weak-regularity loss. -/
namespace Falconer

theorem packet_parameter_bounds {Δ s E KF J B m M : ℝ}
    (hΔ : 0 < Δ) (hE : 1 ≤ E) (hKF : 1 ≤ KF) (hKFup : KF ≤ E)
    (hJ : 0 < J) (hJup : J ≤ E) (hB : 0 < B) (hBup : B ≤ E/Δ^s)
    (hm : 1/(E*(Δ^s)^2) ≤ m) (hM : 0 < M) (hMup : M ≤ E/(Δ^s)^2) :
    1/(4*E^3*Δ^s) ≤ m/(4*J*B) ∧
    KF*Δ^s*M ≤ E^2/Δ^s ∧
    KF*(4*J*B*M/m) ≤ 4*E^5/Δ^s ∧
    1/(4*E^5) ≤ m/(4*J*B*(KF*Δ^s*M)) := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hpow : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hm0 : 0 < m := (by positivity : 0 < 1/(E*(Δ^s)^2)).trans_le hm
  have hKF0 : 0 < KF := zero_lt_one.trans_le hKF
  constructor
  · calc
      _ = (1/(E*(Δ^s)^2))/(4*E*(E/Δ^s)) := by field_simp
      _ ≤ _ := by gcongr
  constructor
  · calc
      _ ≤ E*Δ^s*(E/(Δ^s)^2) := by gcongr
      _ = _ := by field_simp
  constructor
  · calc
      _ ≤ E*(4*E*(E/Δ^s)*(E/(Δ^s)^2)/(1/(E*(Δ^s)^2))) := by gcongr
      _ = _ := by field_simp
  · calc
      _ = (1/(E*(Δ^s)^2))/(4*E*(E/Δ^s)*(E*Δ^s*(E/(Δ^s)^2))) := by
        field_simp
      _ ≤ _ := by gcongr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketCardinalityScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cardinality exponents in the packet theorem follow from the
polynomial loss bounds, including the two-level scale shift. -/
namespace Falconer

theorem shifted_packet_powers (N : ℕ) (s ε : ℝ) :
    Real.exp ((s-ε)*((N+2:ℕ):ℝ)*Real.log 2) =
      (4:ℝ)^s/(Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)*(1/(2:ℝ)^N)^s) ∧
    Real.exp ((s+ε)*((N+2:ℕ):ℝ)*Real.log 2) =
      (4:ℝ)^s*Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)/(1/(2:ℝ)^N)^s := by
  have hpow : (1/(2:ℝ)^N)^s = Real.exp (-s*(N:ℝ)*Real.log 2) := by
    simpa only [div_pow,one_pow] using half_power_rpow_exp N s
  have h4 : (4:ℝ)^s = Real.exp (2*s*Real.log 2) := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.rpow_def_of_pos (by positivity),Real.log_pow]
    congr 1
    ring
  rw [hpow,h4]
  constructor
  · rw [← Real.exp_add,← Real.exp_sub]
    congr 1
    push_cast
    ring
  · rw [← Real.exp_add,← Real.exp_sub]
    congr 1
    push_cast
    ring

theorem packet_cardinality_scales (N : ℕ) {s ε E KF J B m M : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hE : 1 ≤ E) (hKF : 1 ≤ KF) (hKFup : KF ≤ E)
    (hJ : 0 < J) (hJup : J ≤ E) (hB : 0 < B) (hBup : B ≤ E/(1/(2:ℝ)^N)^s)
    (hm : 1/(E*((1/(2:ℝ)^N)^s)^2) ≤ m)
    (hM : 0 < M) (hMup : M ≤ E/((1/(2:ℝ)^N)^s)^2)
    (hloss : 16*E^5 ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)) :
    Real.exp ((s-ε)*((N+2:ℕ):ℝ)*Real.log 2) ≤ m/(4*J*B) ∧
    KF*(1/(2:ℝ)^N)^s*M ≤ Real.exp ((s+ε)*((N+2:ℕ):ℝ)*Real.log 2) ∧
    KF*(4*J*B*M/m) ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)/(1/(2:ℝ)^N)^s := by
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hδ _
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hE3 : E^3 ≤ E^5 := pow_le_pow_right₀ hE (by norm_num)
  have hE2 : E^2 ≤ E^5 := pow_le_pow_right₀ hE (by norm_num)
  have h4up : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 4) hs1
  have h4lo : (1:ℝ) ≤ 4^s := Real.one_le_rpow (by norm_num) hs
  obtain ⟨hlo,hup,hreg,_⟩ := packet_parameter_bounds hδ hE hKF hKFup hJ hJup hB hBup hm hM hMup
  obtain ⟨hshiftlo,hshiftup⟩ := shifted_packet_powers N s ε
  refine ⟨?_,?_,?_⟩
  · rw [hshiftlo]
    apply le_trans _ hlo
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hL : 16*E^3 ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2) :=
      (mul_le_mul_of_nonneg_left hE3 (by norm_num)).trans hloss
    have hh := mul_le_mul_of_nonneg_left h4up (show 0 ≤ 4*E^3 by positivity)
    have hh' : (4:ℝ)^s*(4*E^3) ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2) := by
      nlinarith only [hh,hL]
    nlinarith only [mul_le_mul_of_nonneg_right hh' hδs.le]
  · apply hup.trans
    rw [hshiftup]
    apply div_le_div_of_nonneg_right _ hδs.le
    have hD : E^2 ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2) := by
      have hh : E^5 ≤ 16*E^5 := by nlinarith only [pow_nonneg hE0.le 5]
      exact hE2.trans (hh.trans hloss)
    exact hD.trans (le_mul_of_one_le_left (Real.exp_pos _).le h4lo)
  · exact hreg.trans (div_le_div_of_nonneg_right
      ((show 4*E^5 ≤ 16*E^5 by nlinarith only [pow_nonneg hE0.le 5]).trans hloss) hδs.le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketPolynomialLoss
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One choice of a weak exponent absorbs every polynomial packet loss,
including the fortieth power arising in projection sampling. -/
namespace Falconer

theorem packet_polynomial_loss {θ C : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let E := Real.exp (ε*(N:ℝ)*Real.log 2)
      let D := Real.exp (θ*(N:ℝ)*Real.log 2)
      1 ≤ E ∧ 100 ≤ D ∧ 16*E^5 ≤ D ∧ C*((N:ℝ)+1)^2*E^48 ≤ D := by
  let A := 100+16+C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_quadratic_loss (by positivity : 0 < θ/2) hA
  refine ⟨θ/96,N0,by positivity,hN0,?_⟩
  intro N hN
  dsimp only
  let E := Real.exp ((θ/96)*(N:ℝ)*Real.log 2)
  let D := Real.exp (θ*(N:ℝ)*Real.log 2)
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpoly1 : (1:ℝ) ≤ ((N:ℝ)+1)^2 := by
    have hh : (1:ℝ) ≤ (N:ℝ)+1 := by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
    exact one_le_pow₀ hh
  have hE48 : E^48 = Real.exp ((θ/2)*(N:ℝ)*Real.log 2) := by
    dsimp [E]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hcost : A*((N:ℝ)+1)^2*E^48 ≤ D := by
    calc
      _ ≤ Real.exp ((θ/2)*(N:ℝ)*Real.log 2)*E^48 :=
        mul_le_mul_of_nonneg_right (hpoly N hN) (pow_nonneg hE0 _)
      _ = D := by rw [hE48,← Real.exp_add]; congr 1; ring
  have h48 : (1:ℝ) ≤ E^48 := one_le_pow₀ hE
  have h5 : E^5 ≤ E^48 := pow_le_pow_right₀ hE (by norm_num)
  refine ⟨hE,?_,?_,?_⟩
  · apply le_trans _ hcost
    calc
      (100:ℝ) ≤ A := by dsimp [A]; linarith only [hC]
      _ ≤ A*((N:ℝ)+1)^2 := le_mul_of_one_le_right hA hpoly1
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hA (sq_nonneg _)) h48
  · apply le_trans _ hcost
    calc
      16*E^5 ≤ 16*E^48 := mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ ≤ A*E^48 := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith only [hC]) (pow_nonneg hE0 _)
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right hA hpoly1
        exact mul_le_mul_of_nonneg_right hh (pow_nonneg hE0 _)
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith : C ≤ A) (sq_nonneg _))
      (pow_nonneg hE0 _)).trans hcost

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketGrowthGap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frozen-packet upper bound contradicts the packet power gain
once the input weak exponent is chosen sufficiently small. -/
namespace Falconer

theorem packet_growth_gap {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ ε0 : ℝ, ∃ N0 : ℕ, 0 < ε0 ∧ 0 < N0 ∧
      ∀ (n : ℕ) (ε s B : ℝ), N0 ≤ n+2 → 0 ≤ ε → ε ≤ ε0 → 0 ≤ s →
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ B →
      B ≤ C*(Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2))^6/((1/(2:ℝ)^n)^s)^2 → False := by
  obtain ⟨ε0,N0,hε0,hN0,hcost⟩ := packet_polynomial_loss (by positivity : 0 < η/2) hC
  refine ⟨ε0,N0,hε0,hN0,?_⟩
  intro n ε s B hn hε hεup hs hlo hup
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let E0 := Real.exp (ε0*((n+2:ℕ):ℝ)*Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdepth : (0:ℝ) < (n+2:ℕ) := by positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hEE : E ≤ E0 := Real.exp_le_exp.mpr (by gcongr)
  have hE6 : E^6 ≤ E0^48 := (pow_le_pow_left₀ (Real.exp_pos _).le hEE _).trans
    (pow_le_pow_right₀ (hE.trans hEE) (by norm_num))
  have hc := (hcost (n+2) hn).2.2.2
  have hpoly : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by
    have := Nat.cast_nonneg (α := ℝ) (n+2)
    linarith)
  have hCE : C*E^6 ≤ Real.exp ((η/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply le_trans _ hc
    calc
      C*E^6 ≤ C*E0^48 := mul_le_mul_of_nonneg_left hE6 hC
      _ ≤ C*((((n+2:ℕ):ℝ)+1)^2)*E0^48 := by
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hpoly) (pow_nonneg (Real.exp_pos _).le _)
  have hstrict : C*E^6 < Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) := hCE.trans_lt
    (Real.exp_lt_exp.mpr (by nlinarith only [mul_pos (mul_pos hη hdepth) hlog]))
  have hpow : (1/(2:ℝ)^n)^s = Real.exp (-s*(n:ℝ)*Real.log 2) := by
    simpa only [div_pow,one_pow] using half_power_rpow_exp n s
  have heq : Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2)*((1/(2:ℝ)^n)^s)^2 =
      Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2+4*s*Real.log 2) := by
    rw [hpow,← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    push_cast
    ring
  have hscale : 0 < ((1/(2:ℝ)^n)^s)^2 := by positivity
  have hlower : Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) ≤
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2)*((1/(2:ℝ)^n)^s)^2 := by
    rw [heq]
    exact Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity))
  have hupper : Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2)*((1/(2:ℝ)^n)^s)^2 ≤ C*E^6 :=
    (mul_le_mul_of_nonneg_right hlo hscale.le).trans ((le_div_iff₀ hscale).1 hup)
  exact hstrict.not_ge (hlower.trans hupper)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketSamplingBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained point fraction supplies the projection-sampling
budget; it is not an additional regularity assumption. -/
namespace Falconer

theorem packet_sampling_budget (N : ℕ) {κ s t E K KP KF J B m M : ℝ}
    (hκ : 0 < κ) (hs : s ≤ 1) (hgap : κ ≤ t-s)
    (hE : 1 ≤ E) (hK : 0 ≤ K) (hKup : K ≤ E) (hKP : 0 ≤ KP) (hKPup : KP ≤ E)
    (hKF : 1 ≤ KF) (hKFup : KF ≤ E) (hJ : 0 < J) (hJup : J ≤ E)
    (hB : 0 < B) (hBup : B ≤ E/(1/(2:ℝ)^N)^s)
    (hm : 1/(E*((1/(2:ℝ)^N)^s)^2) ≤ m)
    (hM : 0 < M) (hMup : M ≤ E/((1/(2:ℝ)^N)^s)^2) :
    projectedSubsetSampleConstant N s t (25*K*(4:ℝ)^s) KP
      (m/(4*J*B*(KF*(1/(2:ℝ)^N)^s*M))) ≤
        ((100:ℝ)^8*(512*(64*Real.exp 1*(1+32*projectionGapConstant κ)+100)^2))*
          ((N:ℝ)+1)^2*E^40 := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hE5 : E ≤ E^5 := by simpa only [pow_one] using pow_le_pow_right₀ hE (by norm_num : 1 ≤ 5)
  have hE51 : 1 ≤ E^5 := one_le_pow₀ hE
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hδ _
  have hm0 : 0 < m := (by positivity : 0 < 1/(E*((1/(2:ℝ)^N)^s)^2)).trans_le hm
  have h4 : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 4) hs
  have hKI : 25*K*(4:ℝ)^s ≤ 100*E^5 := by
    calc
      _ ≤ 25*E*4 := by gcongr
      _ ≤ _ := by nlinarith only [hE5]
  have hKPI : KP ≤ 100*E^5 := by
    have hh : E^5 ≤ 100*E^5 := by nlinarith only [hE51]
    exact hKPup.trans (hE5.trans hh)
  have hρ := (packet_parameter_bounds hδ hE hKF hKFup hJ hJup hB hBup hm hM hMup).2.2.2
  have hρ' : 1/(100*E^5) ≤ m/(4*J*B*(KF*(1/(2:ℝ)^N)^s*M)) := by
    apply le_trans _ hρ
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith only [hE51] : 4*E^5 ≤ 100*E^5)
  have hst : s < t := by linarith only [hκ,hgap]
  have hH := projectionGapConstant_pos hκ
  have hb := projectedSubsetSampleConstant_upper N hst hs (by positivity) hKP
    (show 1 ≤ 100*E^5 by nlinarith only [hE51]) hKI hKPI
    (by positivity : 0 < m/(4*J*B*(KF*(1/(2:ℝ)^N)^s*M))) hρ' hH.le
    (planarPotentialConstant_gap hκ hs hgap)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LocalPencilPacketGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the separately selected original cell pencils into one
packet. The pointwise choice preserves the common original tube cover. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_gain_from_local_pencils {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let L := fun s : ℝ => Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2)
      let U := fun s : ℝ => Real.exp ((s+ε)*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t KI KP ρ c b : ℝ) (Y : Finset ℝ)
        (P A : ℝ → Finset (Space 2)) (a : ℝ → ℝ)
        (T : ℝ → Space 2 → Finset (Space 2)) (G : Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → s < t → 0 ≤ KI → 0 ≤ KP → 0 < ρ → |c| ≤ 1 →
      Y.Nonempty → (∀ y ∈ Y, |y| ≤ 1) → 2 ≤ D →
      projectedSubsetSampleConstant n s t KI KP ρ ≤ D →
      (∀ y ∈ Y, (P y).Nonempty ∧ A y ⊆ P y ∧
        ρ*((P y).card:ℝ) ≤ ((A y).card:ℝ) ∧
        (∀ p ∈ P y, |p 0-y| ≤ Δ ∧ |p 1-a y| ≤ Δ) ∧
        planarProjectionEnergy n s c ((P y).image (localPacketPoint Δ y (a y))) ≤
          2*projectionEnergyBudget n s t KI KP*((P y).card:ℝ)^2) →
      (∀ y ∈ Y, ∀ p ∈ A y, T y p ⊆ G ∧ FiniteSeparatedAt (Δ^2) (T y p) ∧
        NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T y p) ∧
        L s ≤ ((T y p).card:ℝ) ∧ ((T y p).card:ℝ) ≤ U s ∧
        ∀ l ∈ T y p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
      (∀ u r : ℝ, Δ/4 ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ (G.card:ℝ) := by
  obtain ⟨ε,η,N0,hε,hη,hN0,hmain⟩ := centered_packet_gain_of_local_energy hκ hκ1
  refine ⟨ε,η,N0,hε,hη,hN0,?_⟩
  intro n hn
  dsimp only
  intro s t KI KP ρ c b Y P A a T G hs hs1 hst hKI hKP hρ hc hY hYbound hD hbudget hdata hT hYball
  let S := Y.biUnion A
  have hrep (p : Space 2) (hp : p ∈ S) : ∃ y ∈ Y, p ∈ A y := Finset.mem_biUnion.mp hp
  let V := fun p => if hp : p ∈ S then T (Classical.choose (hrep p hp)) p else ∅
  have hV (p : Space 2) (hp : p ∈ S) := by
    have hw := Classical.choose_spec (hrep p hp)
    have ht := hT (Classical.choose (hrep p hp)) hw.1 p hw.2
    have he : V p = T (Classical.choose (hrep p hp)) p := dite_eq_left hp
    rw [← he] at ht
    exact ht
  have hgain := hmain n hn s t KI KP ρ c b Y P A a S V hs hs1 hst hKI hKP hρ hc hY hYbound hD hbudget
    (by
      intro y hy
      obtain ⟨hp,hap,hsize,hcell,henergy⟩ := hdata y hy
      exact ⟨hp,hap,Finset.subset_biUnion_of_mem A hy,hsize,hcell,henergy⟩)
    (fun p hp => (hV p hp).2) hYball
  have hcover : S.biUnion V ⊆ G := by
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    exact (hV p hp).1 hl
  exact hgain.trans (Nat.cast_le.mpr (Finset.card_le_card hcover))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarsePacketGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packet growth from actual coarse incidences and their weighted fine pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coarse_packet_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let Lo := fun s : ℝ => Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2)
      let Up := fun s : ℝ => Real.exp ((s+ε)*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t K KP KF m M mF MF L J B R : ℝ) (C : Finset (Space 2))
        (T P : Space 2 → Finset (Space 2))
        (V : Space 2 → Space 2 → Finset (Space 2)) (q : Space 2 → Space 2 → Space 2)
        (G : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      1 ≤ K → 1 ≤ KP → 1 ≤ KF → 0 < m → 0 < L → 0 < mF → 0 < MF →
      0 < J → 0 < B → 1 ≤ R → C.Nonempty → InBoundedLineChart C →
      FiniteSeparatedAt (1/(2:ℝ)^(n+3)) C →
      NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) t K C →
      (∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
        InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(n+3)) (T x) ∧
        NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) s K (T x) ∧
        ∀ a ∈ T x, TubeIncident (1/(2:ℝ)^(n+3)) x a) →
      ((C.biUnion T).card:ℝ) ≤ L →
      (∀ x ∈ C, (P x).Nonempty ∧
        (∀ p ∈ P x, |p 0-x 0| ≤ Δ ∧ |p 1-x 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t KP ((P x).image (localPacketPoint Δ (x 0) (x 1)))) →
      (∀ x ∈ C, ∀ p ∈ P x, mF ≤ ((V x p).card:ℝ) ∧ ((V x p).card:ℝ) ≤ MF ∧
        FiniteSeparatedAt (Δ^2) (V x p) ∧ NormalizedFiniteBallBound (Δ^2) s KF (V x p) ∧
        ∀ l ∈ V x p, |l 0| ≤ 1 ∧ TubeIncident (Δ^2) p l) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, dist l (q x l) ≤ Δ) →
      (∀ x ∈ C, ∀ a ∈ T x,
        ((∑ p ∈ P x, (V x p).card):ℝ) ≤ 2*J*B*(coarsePencilWeight (P x) (V x) (q x) a:ℝ)) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, l ∈ G (q x l)) →
      4*pencilEnergyCutoff (n+3) s t (50*K) M (m/50) C*
        (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s) ≤ R →
      100*R ≤ D → 2 ≤ D →
      Lo s ≤ mF/(4*J*B) → KF*Δ^s*MF ≤ Up s → KF*(4*J*B*MF/mF) ≤ D/Δ^s →
      projectedSubsetSampleConstant n s t (25*K*(4:ℝ)^s) KP
        (mF/(4*J*B*(KF*Δ^s*MF))) ≤ D →
      ∃ a ∈ C.biUnion T,
        Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((G a).card:ℝ) := by
  obtain ⟨ε,η,N0,hε,hη,hN0,hmain⟩ := centered_packet_gain_from_local_pencils hκ hκ1
  refine ⟨ε,η,N0,hε,hη,hN0,?_⟩
  intro n hn
  dsimp only
  intro s t K KP KF m M mF MF L J B R C T P V q G
    hs hs1 hgap ht hK hKP hKF hm hL hmF hMF hJ hB hR hC hCchart hCsep hCball
    hT hunion hP hV hnear hweight hG hfiber hrow hD hlo hup hreg hsample
  let Δ := 1/(2:ℝ)^n
  let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Q := fun x => (P x).image (localPacketPoint Δ (x 0) (x 1))
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ1 : Δ ≤ 1 := (div_le_one (by positivity : (0:ℝ) < 2^n)).2
    (one_le_pow₀ (by norm_num))
  have hδΔ : Δ^2 ≤ Δ := by nlinarith only [hΔ,hΔ1]
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hst : s < t := by linarith only [hκ,hgap]
  obtain ⟨a,ha,Y,hY,_,hYball,c,hc⟩ := good_coarse_rows n hs0 hst
    (show 2*κ ≤ 1 by linarith only [hs,hs1]) hgap hK hKP hm hL hR
    C T Q hC hCchart hCsep hCball hT (by
      intro x hx
      exact ⟨(hP x hx).1.image _,localPacketPoint_chart hΔ (P x) (hP x hx).2.1,(hP x hx).2.2⟩)
    hunion hfiber
  have chooseA (x : Space 2) (hx : x ∈ C ∧ a ∈ T x) :=
    quantitative_packet_points (pow_pos hΔ 2) hΔ hδΔ hs0 hKF hmF hMF hJ hB
      (P x) (V x) (hP x hx.1).1 (q x) a (hnear x hx.1) (hV x hx.1) (hweight x hx.1 a hx.2)
  let A := fun x => if hx : x ∈ C ∧ a ∈ T x then Classical.choose (chooseA x hx) else ∅
  have hA (x : Space 2) (hx : x ∈ C ∧ a ∈ T x) := by
    have hh := Classical.choose_spec (chooseA x hx)
    have he : A x = Classical.choose (chooseA x hx) := dite_eq_left hx
    rw [← he] at hh
    exact hh
  have ha0 : |a 0| ≤ 1 := by
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    exact ((hT x hx).2.2.1 a hax).1
  refine ⟨a,ha,?_⟩
  apply hmain n hn s t (25*K*(4:ℝ)^s) KP (mF/(4*J*B*(KF*Δ^s*MF)))
    (-a 0) (a 1) Y (fun y => P (c y)) (fun y => A (c y)) (fun y => c y 1)
    (fun y p => (V (c y) p).filter fun l => q (c y) l = a) (G a)
    hs hs1 hst (by positivity) (zero_le_one.trans hKP) (by positivity)
    (by simpa only [abs_neg] using ha0) hY (fun y hy => (hc y hy).2.2.1) hD hsample
  · intro y hy
    have hcy := hc y hy
    have hh := hA (c y) ⟨hcy.1,hcy.2.2.2.1⟩
    refine ⟨(hP (c y) hcy.1).1,hh.1,hh.2.2.1,?_,?_⟩
    · intro p hp
      simpa only [hcy.2.1] using (hP (c y) hcy.1).2.1 p hp
    · have he := hcy.2.2.2.2
      dsimp only [Q] at he
      rw [Finset.card_image_of_injective _ (localPacketPoint_injective hΔ _ _)] at he
      simpa only [hcy.2.1] using he
  · intro y hy p hp
    have hcy := hc y hy
    have hh := hA (c y) ⟨hcy.1,hcy.2.2.2.1⟩
    obtain ⟨_,hlo',hup',hsep',hball',hinc'⟩ := hh.2.2.2 p hp
    refine ⟨?_,hsep',?_,hlo.trans hlo',hup'.trans hup,?_⟩
    · intro l hl
      obtain ⟨hlV,hlq⟩ := Finset.mem_filter.mp hl
      simpa only [hlq] using hG (c y) hcy.1 p (hh.1 hp) l hlV
    · intro z r hr hr1
      exact (hball' z r hr hr1).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hreg (Real.rpow_nonneg ((pow_nonneg hΔ.le 2).trans hr) _))
        (Nat.cast_nonneg _))
    · intro l hl
      simpa only [sub_eq_add_neg] using hinc' l hl
  · intro u r hr hr1
    have hscale : 1/(2:ℝ)^(n+3) = Δ/8 := by
      dsimp [Δ]
      rw [pow_add]
      norm_num
      ring
    have hr' : 1/(2:ℝ)^(n+3) ≤ r := by rw [hscale]; linarith only [hr,hΔ]
    exact (hYball u r hr' hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg (le_trans (by positivity : 0 ≤ (1/(2:ℝ)^n)/4) hr) _))
      (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarsePacketParameters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single weak exponent pays for the complete coarse-packet application. -/
namespace Falconer

theorem coarse_packet_parameters {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let δ := 1/(2:ℝ)^(n+3)
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let D := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
      1 ≤ E ∧ 100 ≤ D ∧ ∀ s t K KP KF m M mF MF L J B : ℝ,
      0 ≤ s → s ≤ 1 → t ≤ 2 → κ ≤ t-s → 1 ≤ K → K ≤ E → 0 ≤ KP → KP ≤ E →
      1 ≤ KF → KF ≤ E → 0 < m → 0 ≤ M → M ≤ E/δ^s → 1/(E*δ^s) ≤ m →
      0 ≤ L → L ≤ E/(δ^s)^2 → 0 < J → J ≤ E → 0 < B → B ≤ E/Δ^s →
      1/(E*(Δ^s)^2) ≤ mF → 0 < MF → MF ≤ E/(Δ^s)^2 →
      (∀ C : Finset (Space 2), C.Nonempty →
        4*pencilEnergyCutoff (n+3) s t (50*K) M (m/50) C*
          (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s) ≤ D/100) ∧
      Real.exp ((s-θ)*((n+2:ℕ):ℝ)*Real.log 2) ≤ mF/(4*J*B) ∧
      KF*Δ^s*MF ≤ Real.exp ((s+θ)*((n+2:ℕ):ℝ)*Real.log 2) ∧
      KF*(4*J*B*MF/mF) ≤ D/Δ^s ∧
      projectedSubsetSampleConstant n s t (25*K*(4:ℝ)^s) KP
        (mF/(4*J*B*(KF*Δ^s*MF))) ≤ D := by
  let H := projectionGapConstant κ
  let CF := 2*100*1127219200*(1+H)*(50:ℝ)^12
  let CS := (100:ℝ)^8*(512*(64*Real.exp 1*(1+32*H)+100)^2)
  let A := CF+CS
  have hH : 0 < H := projectionGapConstant_pos hκ
  have hCF : 0 ≤ CF := by dsimp [CF]; positivity
  have hCS : 0 ≤ CS := by dsimp [CS]; positivity
  obtain ⟨ε,N0,hε,hN0,hcost⟩ := packet_polynomial_loss hθ (show 0 ≤ A by dsimp [A]; positivity)
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro n hn
  dsimp only
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  obtain ⟨hE,hD,h16,hall⟩ := hcost (n+2) hn
  refine ⟨hE,hD,?_⟩
  intro s t K KP KF m M mF MF L J B hs hs1 ht hgap hK hKE hKP hKPE hKF hKFE hm hM hME hmE
    hL hLE hJ hJE hB hBE hmFE hMF hMFE
  have hst : s < t := by linarith only [hκ,hgap]
  have hE0 : 0 < E := Real.exp_pos _
  have hN : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hE12 : E^12 ≤ E^48 := pow_le_pow_right₀ hE (by norm_num)
  have hE40 : E^40 ≤ E^48 := pow_le_pow_right₀ hE (by norm_num)
  have hdepth : (n:ℝ)+4 ≤ 2*((n:ℝ)+3)^2 := by nlinarith only [hN]
  have hall' : A*((n:ℝ)+3)^2*E^48 ≤ D := by
    have heq : (n:ℝ)+3 = ((n+2:ℕ):ℝ)+1 := by push_cast; ring
    rw [heq]
    exact hall
  have hCFall : CF*((n:ℝ)+3)^2*E^48 ≤ D := by
    apply le_trans _ hall'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show CF ≤ A by dsimp [A]; linarith only [hCS]) (sq_nonneg _)) (pow_nonneg hE0.le _)
  have hCSall : CS*((n:ℝ)+3)^2*E^48 ≤ D := by
    apply le_trans _ hall'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show CS ≤ A by dsimp [A]; linarith only [hCF]) (sq_nonneg _)) (pow_nonneg hE0.le _)
  obtain ⟨hlo,hup,hreg⟩ := packet_cardinality_scales n hs hs1 hE hKF hKFE hJ hJE hB hBE hmFE hMF hMFE h16
  refine ⟨?_,hlo,hup,hreg,?_⟩
  · intro C hC
    have hδs : 0 < (1/(2:ℝ)^(n+3))^s := by positivity
    have hE50 : 1 ≤ 50*E := by linarith only [hE]
    have hM50 : M ≤ (50*E)/(1/(2:ℝ)^(n+3))^s := hME.trans
      (div_le_div_of_nonneg_right (by linarith only [hE]) hδs.le)
    have hm50 : 1/((50*E)*(1/(2:ℝ)^(n+3))^s) ≤ m/50 := by
      have hh := div_le_div_of_nonneg_right hmE (by norm_num : (0:ℝ) ≤ 50)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hL50 : L ≤ (50*E)/((1/(2:ℝ)^(n+3))^s)^2 := hLE.trans
      (div_le_div_of_nonneg_right (by linarith only [hE]) (sq_nonneg _))
    have hf := regular_fiber_constant_upper (n+3) hκ hs hs1 ht hgap
      (show 0 ≤ 50*K by linarith only [hK]) hM (show 0 < m/50 by positivity) hL hE50
      (show 50*K ≤ 50*E by linarith only [hKE]) hM50 hm50 hL50 C hC
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 100)).2
    calc
      _ ≤ (1127219200*(1+H))*(((n+3:ℕ):ℝ)+1)*(50*E)^12*100 :=
        mul_le_mul_of_nonneg_right hf (by norm_num)
      _ = (100*1127219200*(1+H)*(50:ℝ)^12)*((n:ℝ)+4)*E^12 := by push_cast; ring
      _ ≤ (100*1127219200*(1+H)*(50:ℝ)^12)*(2*((n:ℝ)+3)^2)*E^48 := by gcongr
      _ = CF*((n:ℝ)+3)^2*E^48 := by dsimp [CF]; ring
      _ ≤ D := hCFall
  · have hb := packet_sampling_budget n hκ hs1 hgap hE (zero_le_one.trans hK) hKE hKP hKPE
      hKF hKFE hJ hJE hB hBE hmFE hMF hMFE
    apply hb.trans
    change CS*((n:ℝ)+1)^2*E^40 ≤ D
    calc
      _ ≤ CS*((n:ℝ)+3)^2*E^48 := by gcongr; linarith only [hN]
      _ ≤ D := hCSall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_VariableBaselineIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The baseline incidence estimate for unequal pencil sizes, as needed
before and after weighted packet freezing. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planar_variable_baseline_incidence (N : ℕ) {s t K m M : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      ((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)) := by
  let C := (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hH := pencil_second_moment_bound N hs hst hK P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.1,(hT x hx).2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(C*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun x _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ = ((P.biUnion T).card:ℝ)*(∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) := by
        rw [sum_tubeDegree_sq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

theorem packet_size_from_variable_incidence (N : ℕ) {s t K m M n B : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m) (hM : 0 ≤ M) (hn : 0 ≤ n)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (b : Space 2 → ℕ) (hb : ∀ l ∈ P.biUnion T, n ≤ (b l:ℝ))
    (htotal : (∑ l ∈ P.biUnion T, (b l:ℝ)) ≤ B) :
    n*m^2 ≤ B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)) := by
  let C := (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)
  have hC : 0 ≤ C := by
    have hp := planarPotentialConstant_pos hst
    have hk : 0 ≤ K := zero_le_one.trans hK
    dsimp [C]
    positivity
  have hc : n*((P.biUnion T).card:ℝ) ≤ B := by
    calc
      _ = ∑ _l ∈ P.biUnion T, n := by simp; ring
      _ ≤ ∑ l ∈ P.biUnion T, (b l:ℝ) := Finset.sum_le_sum hb
      _ ≤ _ := htotal
  calc
    _ ≤ n*(((P.biUnion T).card:ℝ)*C) := mul_le_mul_of_nonneg_left
      (planar_variable_baseline_incidence N hs hst hK hm P T hP hPchart hPball hT) hn
    _ = (n*((P.biUnion T).card:ℝ))*C := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hC

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenPacketUpper
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fine packet sizes after dyadic freezing are bounded by the
original total fine-tube count and the geometric coarse incidence estimate. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_packet_card_upper (N k : ℕ) {s t K m M B : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m) (hM : 0 ≤ M)
    (P : Finset (Space 2)) (T G : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hband : ∀ a ∈ P.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1))
    (htotal : (∑ a ∈ P.biUnion T, ((G a).card:ℝ)) ≤ B) :
    ∀ a ∈ P.biUnion T, ((G a).card:ℝ) ≤
      2*B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2 := by
  have hb := packet_size_from_variable_incidence N hs hst hK hm.le hM
    (show 0 ≤ (2:ℝ)^k by positivity) P T hP hPchart hPball hT (fun a => (G a).card)
    (fun a ha => by exact_mod_cast (hband a ha).1) htotal
  intro a ha
  have hu : ((G a).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hband a ha).2
  have hk : (2:ℝ)^k ≤ B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2 :=
    (le_div_iff₀ (sq_pos_of_pos hm)).2 hb
  calc
    _ ≤ 2*(2:ℝ)^k := by simpa only [pow_succ,mul_comm] using hu.le
    _ ≤ 2*(B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2) :=
      mul_le_mul_of_nonneg_left hk (by norm_num)
    _ = _ := by ring

theorem frozen_packet_upper_power (N : ℕ) {κ s t K m M B E Δ : ℝ}
    (hκ : 0 < κ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hgap : κ ≤ t-s)
    (hK : 0 ≤ K) (hKup : K ≤ E) (_hm : 0 < m) (hM : 0 ≤ M)
    (hMup : M ≤ E/(1/(2:ℝ)^N)^s) (hmlo : 1/(E*(1/(2:ℝ)^N)^s) ≤ m)
    (_hB : 0 ≤ B) (hBup : B ≤ E/(Δ^s)^4)
    (hE : 1 ≤ E) (hΔ : 0 < Δ) (hρΔ : 1/(2:ℝ)^N ≤ Δ) :
    2*B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t))/m^2 ≤
      (160*(1+projectionGapConstant κ))*E^6/(Δ^s)^2 := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hρ : 0 < 1/(2:ℝ)^N := by positivity
  have hρs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hρ _
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have hscale : (1/(2:ℝ)^N)^s ≤ Δ^s := Real.rpow_le_rpow hρ.le hρΔ hs
  have hst : s < t := by linarith only [hκ,hgap]
  have hp := planarPotentialConstant_pos hst
  have hH := projectionGapConstant_pos hκ
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hs1
  have hA : K*(80*(1/(2:ℝ)^N))^s*M ≤ 80*E^2 := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hρ.le]
    calc
      _ ≤ E*(80*(1/(2:ℝ)^N)^s)*(E/(1/(2:ℝ)^N)^s) := by gcongr
      _ = _ := by field_simp
  have hpot : 1+K*planarPotentialConstant s t ≤ (1+projectionGapConstant κ)*E := by
    calc
      _ ≤ 1+E*projectionGapConstant κ := by
        gcongr
        exact planarPotentialConstant_gap hκ hs1 hgap
      _ ≤ _ := by nlinarith only [hE]
  calc
    _ ≤ 2*(E/(Δ^s)^4)*((80*E^2)*((1+projectionGapConstant κ)*E))/
        (1/(E*(1/(2:ℝ)^N)^s))^2 := by gcongr
    _ = (160*(1+projectionGapConstant κ))*E^6*((1/(2:ℝ)^N)^s)^2/(Δ^s)^4 := by field_simp; ring
    _ ≤ (160*(1+projectionGapConstant κ))*E^6*(Δ^s)^2/(Δ^s)^4 := by gcongr
    _ = _ := by field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WeakCoarsePacketGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarse packet gain with all numerical application costs absorbed
into a single weak-regularity exponent. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weak_coarse_packet_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let δ := 1/(2:ℝ)^(n+3)
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t m M mF MF L J B : ℝ) (C : Finset (Space 2))
        (T P : Space 2 → Finset (Space 2))
        (V : Space 2 → Space 2 → Finset (Space 2)) (q : Space 2 → Space 2 → Space 2)
        (G : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      0 < m → 0 ≤ M → M ≤ E/δ^s → 1/(E*δ^s) ≤ m →
      0 < L → L ≤ E/(δ^s)^2 → 0 < J → J ≤ E → 0 < B → B ≤ E/Δ^s →
      1/(E*(Δ^s)^2) ≤ mF → 0 < MF → MF ≤ E/(Δ^s)^2 →
      C.Nonempty → InBoundedLineChart C → FiniteSeparatedAt δ C →
      NormalizedFiniteBallBound δ t E C →
      (∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
        InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
        NormalizedFiniteBallBound δ s E (T x) ∧ ∀ a ∈ T x, TubeIncident δ x a) →
      ((C.biUnion T).card:ℝ) ≤ L →
      (∀ x ∈ C, (P x).Nonempty ∧
        (∀ p ∈ P x, |p 0-x 0| ≤ Δ ∧ |p 1-x 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t E ((P x).image (localPacketPoint Δ (x 0) (x 1)))) →
      (∀ x ∈ C, ∀ p ∈ P x, mF ≤ ((V x p).card:ℝ) ∧ ((V x p).card:ℝ) ≤ MF ∧
        FiniteSeparatedAt (Δ^2) (V x p) ∧ NormalizedFiniteBallBound (Δ^2) s E (V x p) ∧
        ∀ l ∈ V x p, |l 0| ≤ 1 ∧ TubeIncident (Δ^2) p l) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, dist l (q x l) ≤ Δ) →
      (∀ x ∈ C, ∀ a ∈ T x,
        ((∑ p ∈ P x, (V x p).card):ℝ) ≤ 2*J*B*(coarsePencilWeight (P x) (V x) (q x) a:ℝ)) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, l ∈ G (q x l)) →
      ∃ a ∈ C.biUnion T,
        Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((G a).card:ℝ) := by
  obtain ⟨θ,η,N1,hθ,hη,hN1,hmain⟩ := coarse_packet_gain hκ hκ1
  obtain ⟨ε,N2,hε,hN2,hpar⟩ := coarse_packet_parameters hκ hθ
  refine ⟨ε,η,max N1 N2,hε,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m M mF MF L J B C T P V q G hs hs1 hgap ht hm hM hME hmE hL hLE
    hJ hJE hB hBE hmFE hMF hMFE hC hCchart hCsep hCball hT hunion hP hV hnear hweight hG
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hgap' : κ ≤ t-s := by linarith only [hκ,hgap]
  obtain ⟨hE,hD,hcost⟩ := hpar n ((le_max_right _ _).trans hn)
  obtain ⟨hfiber,hlo,hup,hreg,hsample⟩ := hcost s t E E E m M mF MF L J B hs0 hsone ht hgap'
    hE le_rfl (Real.exp_pos _).le le_rfl hE le_rfl hm hM hME hmE hL.le hLE hJ hJE hB hBE hmFE hMF hMFE
  have hmF : 0 < mF := (by positivity : 0 < 1/(E*((1/(2:ℝ)^n)^s)^2)).trans_le hmFE
  exact hmain n ((le_max_left _ _).trans hn) s t E E E m M mF MF L J B (D/100)
    C T P V q G hs hs1 hgap ht hE hE hE hm hL hmF hMF hJ hB
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 100)).2 (by simpa only [one_mul] using hD))
    hC hCchart hCsep hCball hT hunion hP hV hnear hweight hG (hfiber C hC)
    (by dsimp [D]; linarith) ((by norm_num : (2:ℝ) ≤ 100).trans hD) hlo hup hreg hsample

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenCoarseObstruction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final contradiction for a regular coarse configuration whose
original fine packets have been frozen to comparable sizes. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_coarse_packet_impossible_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let δ := 1/(2:ℝ)^(n+3)
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t m M mF MF L J B : ℝ) (C : Finset (Space 2))
        (T P : Space 2 → Finset (Space 2))
        (V : Space 2 → Space 2 → Finset (Space 2)) (q : Space 2 → Space 2 → Space 2)
        (G : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 →
      0 < m → 0 ≤ M → M ≤ E/δ^s → 1/(E*δ^s) ≤ m →
      0 < L → L ≤ E/(δ^s)^2 → 0 < J → J ≤ E → 0 < B → B ≤ E/Δ^s →
      1/(E*(Δ^s)^2) ≤ mF → 0 < MF → MF ≤ E/(Δ^s)^2 →
      C.Nonempty → InBoundedLineChart C → FiniteSeparatedAt δ C →
      NormalizedFiniteBallBound δ t E C →
      (∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
        InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
        NormalizedFiniteBallBound δ s E (T x) ∧ ∀ a ∈ T x, TubeIncident δ x a) →
      ((C.biUnion T).card:ℝ) ≤ L →
      (∀ x ∈ C, (P x).Nonempty ∧
        (∀ p ∈ P x, |p 0-x 0| ≤ Δ ∧ |p 1-x 1| ≤ Δ) ∧
        NormalizedFiniteBallBound Δ t E ((P x).image (localPacketPoint Δ (x 0) (x 1)))) →
      (∀ x ∈ C, ∀ p ∈ P x, mF ≤ ((V x p).card:ℝ) ∧ ((V x p).card:ℝ) ≤ MF ∧
        FiniteSeparatedAt (Δ^2) (V x p) ∧ NormalizedFiniteBallBound (Δ^2) s E (V x p) ∧
        ∀ l ∈ V x p, |l 0| ≤ 1 ∧ TubeIncident (Δ^2) p l) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, dist l (q x l) ≤ Δ) →
      (∀ x ∈ C, ∀ a ∈ T x,
        ((∑ p ∈ P x, (V x p).card):ℝ) ≤ 2*J*B*(coarsePencilWeight (P x) (V x) (q x) a:ℝ)) →
      (∀ x ∈ C, ∀ p ∈ P x, ∀ l ∈ V x p, l ∈ G (q x l)) →
      (∃ k : ℕ, ∀ a ∈ C.biUnion T, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1)) →
      (∑ a ∈ C.biUnion T, ((G a).card:ℝ)) ≤ E/(Δ^s)^4 → False := by
  obtain ⟨εg,η,N1,hεg,hη,hN1,hgain⟩ := weak_coarse_packet_gain hκ hκ1
  let C0 := 160*(1+projectionGapConstant κ)
  have hC0 : 0 ≤ C0 := by
    have := projectionGapConstant_pos hκ
    dsimp [C0]
    positivity
  obtain ⟨εb,N2,hεb,hN2,hgapmain⟩ := packet_growth_gap hη hC0
  let ε := min εg εb
  refine ⟨ε,max N1 N2,lt_min hεg hεb,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m M mF MF L J B C T P V q G hs hs1 hgap ht hm hM hME hmE hL hLE
    hJ hJE hB hBE hmFE hMF hMFE hC hCchart hCsep hCball hT hunion hP hV hnear hweight hG hband htotal
  let Δ := 1/(2:ℝ)^n
  let δ := 1/(2:ℝ)^(n+3)
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Eg := Real.exp (εg*((n+2:ℕ):ℝ)*Real.log 2)
  have hε : 0 < ε := lt_min hεg hεb
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hEE : E ≤ Eg := Real.exp_le_exp.mpr (by
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hδs : 0 < δ^s := Real.rpow_pos_of_pos hδ _
  have hΔs : 0 < Δ^s := Real.rpow_pos_of_pos hΔ _
  have ball_mono {d u : ℝ} (hd : 0 ≤ d) {F : Finset (Space 2)}
      (h : NormalizedFiniteBallBound d u E F) : NormalizedFiniteBallBound d u Eg F := by
    intro z r hr hr1
    exact (h z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEE (Real.rpow_nonneg (hd.trans hr) _)) (Nat.cast_nonneg _))
  have hMEg : M ≤ Eg/δ^s := hME.trans (div_le_div_of_nonneg_right hEE hδs.le)
  have hmEg : 1/(Eg*δ^s) ≤ m := le_trans (by gcongr) hmE
  have hLEg : L ≤ Eg/(δ^s)^2 := hLE.trans (div_le_div_of_nonneg_right hEE (sq_nonneg _))
  have hBEg : B ≤ Eg/Δ^s := hBE.trans (div_le_div_of_nonneg_right hEE hΔs.le)
  have hmFEg : 1/(Eg*(Δ^s)^2) ≤ mF := le_trans (by gcongr) hmFE
  have hMFEg : MF ≤ Eg/(Δ^s)^2 := hMFE.trans (div_le_div_of_nonneg_right hEE (sq_nonneg _))
  obtain ⟨a,ha,hlarge⟩ := hgain n ((le_max_left _ _).trans hn) s t m M mF MF L J B C T P V q G
    hs hs1 hgap ht hm hM hMEg hmEg hL hLEg hJ (hJE.trans hEE) hB hBEg hmFEg hMF hMFEg
    hC hCchart hCsep (ball_mono hδ.le hCball) (by
      intro x hx
      obtain ⟨hlo,hup,hchart,hsep,hball,hinc⟩ := hT x hx
      exact ⟨hlo,hup,hchart,hsep,ball_mono hδ.le hball,hinc⟩) hunion (by
      intro x hx
      obtain ⟨hp,hcell,hball⟩ := hP x hx
      exact ⟨hp,hcell,ball_mono hΔ.le hball⟩) (by
      intro x hx p hp
      obtain ⟨hlo,hup,hsep,hball,hinc⟩ := hV x hx p hp
      exact ⟨hlo,hup,hsep,ball_mono (sq_nonneg _) hball,hinc⟩) hnear hweight hG
  obtain ⟨k,hband⟩ := hband
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hsone : s ≤ 1 := by linarith only [hs1,hκ]
  have hst : s < t := by linarith only [hgap,hκ]
  have hge : κ ≤ t-s := by linarith only [hgap,hκ]
  have hfrozen := frozen_packet_card_upper (n+3) k hs0 hst hE hm hM C T G hC hCchart hCball
    (fun x hx => ⟨(hT x hx).1,(hT x hx).2.1,(hT x hx).2.2.1,
      (hT x hx).2.2.2.2.1,(hT x hx).2.2.2.2.2⟩) hband htotal a ha
  have hρΔ : δ ≤ Δ := by
    dsimp [δ,Δ]
    exact one_div_le_one_div_of_le (pow_pos (by norm_num : (0:ℝ) < 2) n)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right n 3))
  have hsmall := frozen_packet_upper_power (n+3) hκ hs0 hsone hge (zero_le_one.trans hE)
    le_rfl hm hM hME hmE (by positivity : 0 ≤ E/(Δ^s)^4) le_rfl hE hΔ hρΔ
  exact hgapmain n ε s ((G a).card:ℝ) ((le_max_right _ _).trans hn) hε.le (min_le_right _ _)
    hs0 hlarge (hfrozen.trans hsmall)

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.frozen_coarse_packet_impossible_oai := @OAI.Falconer.frozen_coarse_packet_impossible_oai
