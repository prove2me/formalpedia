-- Prove2me | solution 1 for OAI.CubicTorus.minimizing_planar_product_halfplane
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:35:20.744997+00:00
-- url     : https://prove2.me/submissions/00f0eea5-ec5c-441d-ab18-988c4fd3fdca

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma divergence_zero (x : Cover) : divergence (fun _ => 0) x = 0 := by
  simp [divergence]

lemma divergence_neg (F : Cover → Cover) (x : Cover) :
    divergence (fun x => -F x) x = -divergence F x := by
  unfold divergence
  change ∑ i : Fin 3, (fderiv ℝ (-F) x (EuclideanSpace.single i 1)) i = _
  rw [fderiv_neg]
  simp

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_halfspaceIndicator (n : Cover) : Measurable (halfspaceIndicator n) :=
  measurable_const.indicator (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet

lemma halfspaceIndicator_bound (n x : Cover) : |halfspaceIndicator n x| ≤ 1 := by
  classical
  by_cases hx : ⟪n, x⟫ < 0 <;> simp [halfspaceIndicator, hx]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_tsupport_subset (F : Cover → Cover) :
    tsupport (divergence F) ⊆ tsupport F := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (divergence_of_notMem_tsupport hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProductChart_measurePreserving (n : Cover) :
    MeasurePreserving (normalProductChart n) := by
  exact (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _).trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm).trans
    (normalRotation n).measurePreserving

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma integral_compact_fderiv_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (v : X) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hi : Integrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : X ↦ (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hi) (by simpa using hf.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ ↦ differentiableAt_const 1) (fun _ _ ↦ hf.differentiable (by simp) |>.differentiableAt)
  simpa using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
attribute [-instance] _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeProductCoordinates_measurePreserving : MeasurePreserving planeProductCoordinates :=
  Complex.volume_preserving_equiv_real_prod.comp Complex.orthonormalBasisOneI.repr.symm.measurePreserving

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma triangle_piola_derivatives {X Y : ℝ × ℝ → ℝ}
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) (s t : ℝ) :
    deriv (fun v : ℝ ↦ X (s*v,s)-v*Y (s*v,s)) t +
      deriv (fun u : ℝ ↦ u*Y (u*t,u)) s =
      s*planarCoordinateDivergence X Y (s*t,s) := by
  have ht : HasDerivAt (fun v : ℝ ↦ (s*v,s)) (s,0) t :=
    by simpa using ((hasDerivAt_id t).const_mul s).prodMk (hasDerivAt_const t s)
  have hs : HasDerivAt (fun u : ℝ ↦ (u*t,u)) (t,1) s :=
    by simpa using ((hasDerivAt_id s).mul_const t).prodMk (hasDerivAt_id s)
  have hxt := (hX (s*t,s)).hasFDerivAt.comp_hasDerivAt t ht
  have hyt := (hY (s*t,s)).hasFDerivAt.comp_hasDerivAt t ht
  have hys := (hY ((fun u : ℝ ↦ (u*t,u)) s)).hasFDerivAt.comp_hasDerivAt (f := fun u : ℝ ↦ (u*t,u)) s hs
  have hd1 := (hxt.sub ((hasDerivAt_id t).mul hyt)).deriv
  have hd2 := ((hasDerivAt_id s).mul hys).deriv
  simp only [Function.comp_def,id_eq] at hd1 hd2
  erw [hd1,hd2]
  have he1 : ((s,0) : ℝ × ℝ) = s • ((1,0) : ℝ × ℝ) := by ext <;> simp
  have he2 : ((t,1) : ℝ × ℝ) = t • ((1,0) : ℝ × ℝ)+((0,1) : ℝ × ℝ) := by ext <;> simp
  rw [he1,he2,map_smul,map_smul,map_add,map_smul]
  dsimp [planarCoordinateDivergence]
  ring

lemma continuous_interval_integral_swap {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, f (x,y)) = ∫ y in c..d, ∫ x in a..b, f (x,y) := by
  simp only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict,← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma hasDerivAt_coordinate_left {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ f (t,y)) (fderiv ℝ f (x,y) (1,0)) x := by
  simpa only [Function.comp_def,id_eq] using
    (hf (x,y)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

lemma hasDerivAt_coordinate_right {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ f (x,t)) (fderiv ℝ f (x,y) (0,1)) y := by
  simpa only [Function.comp_def,id_eq] using
    (hf (x,y)).hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

lemma rectangle_coordinate_divergence {X Y : ℝ × ℝ → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, planarCoordinateDivergence X Y (x,y)) =
      (∫ y in c..d, X (b,y)-X (a,y)) + (∫ x in a..b, Y (x,d)-Y (x,c)) := by
  have hDX : Continuous (fun z : ℝ × ℝ ↦ fderiv ℝ X z (1,0)) :=
    (hX.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDY : Continuous (fun z : ℝ × ℝ ↦ fderiv ℝ Y z (0,1)) :=
    (hY.continuous_fderiv (by simp)).clm_apply continuous_const
  have hXint : (∫ x in a..b, ∫ y in c..d, fderiv ℝ X (x,y) (1,0)) =
      ∫ y in c..d, X (b,y)-X (a,y) := by
    rw [continuous_interval_integral_swap hDX hab hcd]
    apply intervalIntegral.integral_congr
    intro y _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ ↦ hasDerivAt_coordinate_left (hX.differentiable (by simp)) x y)
      ((hDX.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  have hYint (x : ℝ) : (∫ y in c..d, fderiv ℝ Y (x,y) (0,1)) = Y (x,d)-Y (x,c) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ ↦ hasDerivAt_coordinate_right (hY.differentiable (by simp)) x y)
      ((hDY.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  have hsum (x : ℝ) : (∫ y in c..d, planarCoordinateDivergence X Y (x,y)) =
      (∫ y in c..d, fderiv ℝ X (x,y) (1,0)) + (Y (x,d)-Y (x,c)) := by
    have hcX : Continuous (fun y : ℝ ↦ fderiv ℝ X (x,y) (1,0)) := hDX.comp (continuous_const.prodMk continuous_id)
    have hcY : Continuous (fun y : ℝ ↦ fderiv ℝ Y (x,y) (0,1)) := hDY.comp (continuous_const.prodMk continuous_id)
    rw [show (fun y ↦ planarCoordinateDivergence X Y (x,y)) =
      (fun y ↦ fderiv ℝ X (x,y) (1,0)+fderiv ℝ Y (x,y) (0,1)) from rfl,
      intervalIntegral.integral_add
        (hcX.intervalIntegrable _ _) (hcY.intervalIntegrable _ _),hYint]
  simp_rw [hsum]
  have hintX : IntervalIntegrable (fun x ↦ ∫ y in c..d, fderiv ℝ X (x,y) (1,0)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hi : Integrable (fun z : ℝ × ℝ ↦ fderiv ℝ X z (1,0))
        ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
      rw [Measure.prod_restrict,← Measure.volume_eq_prod]
      exact (hDX.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    simp_rw [intervalIntegral.integral_of_le hcd]
    exact hi.integral_prod_left
  have hc : Continuous (fun x : ℝ ↦ Y (x,d)-Y (x,c)) := by fun_prop
  rw [intervalIntegral.integral_add hintX (hc.intervalIntegrable _ _),hXint]

theorem triangle_coordinate_divergence {X Y : ℝ × ℝ → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ s in (0 : ℝ)..b, ∫ x in (s*l)..(s*u), planarCoordinateDivergence X Y (x,s)) =
      (∫ s in (0 : ℝ)..b, (X (s*u,s)-u*Y (s*u,s))-(X (s*l,s)-l*Y (s*l,s))) +
      (∫ x in (b*l)..(b*u), Y (x,b)) := by
  let G : ℝ × ℝ → ℝ := fun z ↦ z.1*Y (z.1*z.2,z.1)
  let H : ℝ × ℝ → ℝ := fun z ↦ X (z.1*z.2,z.1)-z.2*Y (z.1*z.2,z.1)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by dsimp [G]; fun_prop
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by dsimp [H]; fun_prop
  have hdiv (s t : ℝ) : planarCoordinateDivergence G H (s,t) =
      s*planarCoordinateDivergence X Y (s*t,s) := by
    rw [planarCoordinateDivergence,← (hasDerivAt_coordinate_left (hG.differentiable (by simp)) s t).deriv,
      ← (hasDerivAt_coordinate_right (hH.differentiable (by simp)) s t).deriv]
    dsimp only [G,H]
    rw [add_comm]
    exact triangle_piola_derivatives (hX.differentiable (by simp)) (hY.differentiable (by simp)) s t
  have he := rectangle_coordinate_divergence hG hH hb hlu
  simp_rw [hdiv] at he
  have hscale (s : ℝ) : (∫ t in l..u, s*planarCoordinateDivergence X Y (s*t,s)) =
      ∫ x in (s*l)..(s*u), planarCoordinateDivergence X Y (x,s) := by
    rw [intervalIntegral.integral_const_mul]
    exact intervalIntegral.smul_integral_comp_mul_left (fun x ↦ planarCoordinateDivergence X Y (x,s)) s
  simp_rw [hscale] at he
  have hg : (∫ t in l..u, G (b,t)-G (0,t)) = ∫ x in (b*l)..(b*u), Y (x,b) := by
    simp only [G,zero_mul,sub_zero]
    rw [intervalIntegral.integral_const_mul]
    exact intervalIntegral.smul_integral_comp_mul_left (fun x ↦ Y (x,b)) b
  rw [hg] at he
  simpa only [H,add_comm] using he

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVTriangleRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma measurableSet_coordinateTriangle (b l u : ℝ) : MeasurableSet (coordinateTriangle b l u) := by
  exact (measurable_snd measurableSet_Ioc).inter
    ((measurableSet_lt (measurable_snd.mul_const l) measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_snd.mul_const u)))

lemma integralOn_coordinateTriangle {f : ℝ × ℝ → ℝ} {b l u : ℝ}
    (hf : IntegrableOn f (coordinateTriangle b l u)) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinateTriangle b l u, f z) =
      ∫ s in (0 : ℝ)..b, ∫ x in (s*l)..(s*u), f (x,s) := by
  rw [← integral_indicator (measurableSet_coordinateTriangle b l u),Measure.volume_eq_prod]
  have hi := hf.integrable_indicator (measurableSet_coordinateTriangle b l u)
  rw [Measure.volume_eq_prod] at hi
  rw [integral_prod_symm _ hi]
  have he (s : ℝ) : (∫ x : ℝ, (coordinateTriangle b l u).indicator f (x,s)) =
      (Ioc (0 : ℝ) b).indicator (fun s ↦ ∫ x in (s*l)..(s*u), f (x,s)) s := by
    by_cases hs : s ∈ Ioc (0 : ℝ) b
    · rw [indicator_of_mem hs,intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hlu hs.1.le)]
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change (coordinateTriangle b l u).indicator f (x,s) =
        (Ioc (s*l) (s*u)).indicator (fun x ↦ f (x,s)) x
      by_cases hx : x ∈ Ioc (s*l) (s*u)
      · erw [indicator_of_mem (show (x,s) ∈ coordinateTriangle b l u from ⟨hs,hx⟩),indicator_of_mem hx]
      · erw [indicator_of_notMem (show (x,s) ∉ coordinateTriangle b l u from fun h ↦ hx h.2),indicator_of_notMem hx]
    · rw [indicator_of_notMem hs]
      apply integral_eq_zero_of_ae
      exact ae_of_all _ (fun x ↦ indicator_of_notMem
        (show (x,s) ∉ coordinateTriangle b l u from fun h ↦ hs h.1) _)
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le hb]

lemma integral_coordinateTriangle {f : ℝ × ℝ → ℝ} (hf : Integrable f)
    {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinateTriangle b l u, f z) =
      ∫ s in (0 : ℝ)..b, ∫ x in (s*l)..(s*u), f (x,s) :=
  integralOn_coordinateTriangle hf.integrableOn hb hlu

theorem integral_coordinateTriangle_divergence {X Y : ℝ × ℝ → ℝ}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y)
    {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinateTriangle b l u, planarCoordinateDivergence X Y z) =
      (∫ s in (0 : ℝ)..b, (X (s*u,s)-u*Y (s*u,s))-(X (s*l,s)-l*Y (s*l,s))) +
      (∫ x in (b*l)..(b*u), Y (x,b)) := by
  have hiX : Integrable (fun z : ℝ × ℝ ↦ fderiv ℝ X z (1,0)) :=
    ((hX.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsX.fderiv_apply ℝ (1,0))
  have hiY : Integrable (fun z : ℝ × ℝ ↦ fderiv ℝ Y z (0,1)) :=
    ((hY.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsY.fderiv_apply ℝ (0,1))
  have hi : Integrable (planarCoordinateDivergence X Y) := hiX.add hiY
  rw [integral_coordinateTriangle hi hb hlu]
  exact triangle_coordinate_divergence hX hY hb hlu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma hasDerivAt_prism_axial {T : PrismCoordinates → ℝ}
    (hT : Differentiable ℝ T) (t : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun v : ℝ ↦ T (v,z)) (fderiv ℝ T (t,z) (1,(0,0))) t := by
  have h : HasDerivAt (fun v : ℝ ↦ (v,z)) (1,(0,0)) t := by
    convert (hasDerivAt_id t).prodMk (hasDerivAt_const t z) using 1 <;> rfl
  exact (hT (t,z)).hasFDerivAt.comp_hasDerivAt t h

lemma prism_planar_coordinate_derivatives {X Y : PrismCoordinates → ℝ}
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) (t : ℝ) (z : ℝ × ℝ) :
    planarCoordinateDivergence (fun w ↦ X (t,w)) (fun w ↦ Y (t,w)) z =
      fderiv ℝ X (t,z) (0,(1,0)) + fderiv ℝ Y (t,z) (0,(0,1)) := by
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ (t,w))
      (ContinuousLinearMap.prod (0 : (ℝ × ℝ) →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z := by
    exact (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
  erw [planarCoordinateDivergence,((hX (t,z)).hasFDerivAt.comp z h).fderiv,
    ((hY (t,z)).hasFDerivAt.comp z h).fderiv]
  rfl

lemma compact_support_prism_slice {X : PrismCoordinates → ℝ}
    (hsX : HasCompactSupport X) (t : ℝ) : HasCompactSupport (fun z : ℝ × ℝ ↦ X (t,z)) := by
  apply hsX.comp_isClosedEmbedding
  have hi : Isometry (fun z : ℝ × ℝ ↦ (t,z)) := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp
  exact hi.isClosedEmbedding

theorem integral_coordinatePrism_divergence {T X Y : PrismCoordinates → ℝ}
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hsT : HasCompactSupport T) (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinatePrism a c b l u, prismCoordinateDivergence T X Y z) =
      (∫ z in coordinateTriangle b l u, T (c,z)-T (a,z)) +
      (∫ t in a..c, (∫ s in (0 : ℝ)..b,
        (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))) +
        (∫ x in (b*l)..(b*u), Y (t,(x,b)))) := by
  let DT : PrismCoordinates → ℝ := fun z ↦ fderiv ℝ T z (1,(0,0))
  let DP : PrismCoordinates → ℝ := fun z ↦ fderiv ℝ X z (0,(1,0)) + fderiv ℝ Y z (0,(0,1))
  have iT : Integrable DT :=
    ((hT.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsT.fderiv_apply ℝ (1,(0,0)))
  have iX : Integrable (fun z ↦ fderiv ℝ X z (0,(1,0))) :=
    ((hX.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsX.fderiv_apply ℝ (0,(1,0)))
  have iY : Integrable (fun z ↦ fderiv ℝ Y z (0,(0,1))) :=
    ((hY.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hsY.fderiv_apply ℝ (0,(0,1)))
  have iP : Integrable DP := iX.add iY
  have hid : prismCoordinateDivergence T X Y = fun z ↦ DT z + DP z := by
    funext z; dsimp [prismCoordinateDivergence,DT,DP]; ring
  rw [hid,integral_add iT.integrableOn iP.integrableOn]
  congr 1
  · have hi : IntegrableOn DT ((Ioc a c) ×ˢ coordinateTriangle b l u) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact iT.integrableOn
    change (∫ z in (Ioc a c) ×ˢ coordinateTriangle b l u, DT z) = _
    rw [Measure.volume_eq_prod,setIntegral_prod DT hi]
    have hi' : Integrable DT ((volume.restrict (Ioc a c)).prod (volume.restrict (coordinateTriangle b l u))) := by
      rwa [Measure.prod_restrict]
    rw [integral_integral_swap hi']
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change (∫ t in Ioc a c, DT (t,z)) = T (c,z)-T (a,z)
    rw [← intervalIntegral.integral_of_le hac]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_prism_axial (hT.differentiable (by simp)) t z)
      (((hT.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_id.prodMk continuous_const) |>.intervalIntegrable _ _)
  · have hi : IntegrableOn DP ((Ioc a c) ×ˢ coordinateTriangle b l u) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact iP.integrableOn
    change (∫ z in (Ioc a c) ×ˢ coordinateTriangle b l u, DP z) = _
    rw [Measure.volume_eq_prod,setIntegral_prod DP hi,← intervalIntegral.integral_of_le hac]
    apply intervalIntegral.integral_congr
    intro t _
    have hsX' := compact_support_prism_slice hsX t
    have hsY' := compact_support_prism_slice hsY t
    have hX' : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ ↦ X (t,z)) := by fun_prop
    have hY' : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ ↦ Y (t,z)) := by fun_prop
    have he (z : ℝ × ℝ) : DP (t,z) =
        planarCoordinateDivergence (fun w ↦ X (t,w)) (fun w ↦ Y (t,w)) z :=
      (prism_planar_coordinate_derivatives (hX.differentiable (by simp))
        (hY.differentiable (by simp)) t z).symm
    simp_rw [he]
    exact integral_coordinateTriangle_divergence hX' hY' hsX' hsY' hb hlu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma coordinateTriangle_subset_box {b l u : ℝ} (_hb : 0 ≤ b) :
    coordinateTriangle b l u ⊆
      Icc (-b*max |l| |u|) (b*max |l| |u|) ×ˢ Icc 0 b := by
  intro z hz
  have hs0 : 0 ≤ z.2 := hz.1.1.le
  have hs : z.2 ≤ b := hz.1.2
  have hm : 0 ≤ max |l| |u| := le_trans (abs_nonneg l) (le_max_left _ _)
  have hlo : -max |l| |u| ≤ l := by linarith [neg_abs_le l,le_max_left |l| |u|]
  have hup : u ≤ max |l| |u| := le_trans (le_abs_self u) (le_max_right _ _)
  have hh := mul_le_mul_of_nonneg_right hs hm
  have hl := mul_le_mul_of_nonneg_left hlo hs0
  have hu := mul_le_mul_of_nonneg_left hup hs0
  exact ⟨⟨by nlinarith [hz.2.1],by nlinarith [hz.2.2]⟩,hs0,hs⟩

lemma coordinateTriangle_measure_lt_top {b l u : ℝ} (hb : 0 ≤ b) :
    volume (coordinateTriangle b l u) < ⊤ :=
  (measure_mono (coordinateTriangle_subset_box hb)).trans_lt
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top

theorem volume_real_coordinateTriangle {b l u : ℝ} (hb : 0 ≤ b) (hlu : l ≤ u) :
    volume.real (coordinateTriangle b l u) = b^2*(u-l)/2 := by
  have hi : IntegrableOn (fun _ : ℝ × ℝ ↦ (1 : ℝ)) (coordinateTriangle b l u) :=
    integrableOn_const (coordinateTriangle_measure_lt_top hb).ne
  have he := integralOn_coordinateTriangle hi hb hlu
  simp only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ,
    intervalIntegral.integral_const] at he
  have hf : (fun s : ℝ ↦ s*u-s*l) = fun s ↦ (u-l)*s := by funext s; ring
  rw [hf,intervalIntegral.integral_const_mul,integral_id] at he
  convert he using 1 <;> first | rfl | ring

theorem triangular_chord_margin_pos (l u : ℝ) :
    0 < Real.sqrt (1+l^2)+Real.sqrt (1+u^2)-(u-l) := by
  have hl : |l| < Real.sqrt (1+l^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+l^2 by positivity)
    nlinarith [sq_abs l,abs_nonneg l,Real.sqrt_nonneg (1+l^2)]
  have hu : |u| < Real.sqrt (1+u^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1+u^2 by positivity)
    nlinarith [sq_abs u,abs_nonneg u,Real.sqrt_nonneg (1+u^2)]
  linarith [neg_abs_le l,le_abs_self u]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma integral_coordinatePrism_divergence_split {T X Y : PrismCoordinates → ℝ}
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hsT : HasCompactSupport T) (hsX : HasCompactSupport X) (hsY : HasCompactSupport Y)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ z in coordinatePrism a c b l u, prismCoordinateDivergence T X Y z) =
      prismRadialFlux X Y a c b l u + prismClosingFlux T Y a c b l u := by
  rw [integral_coordinatePrism_divergence hT hX hY hsT hsX hsY hac hb hlu]
  have hr : Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..b,
      (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  have hc : Continuous (fun t : ℝ ↦ ∫ x in (b*l)..(b*u), Y (t,(x,b))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  rw [intervalIntegral.integral_add (hr.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  dsimp [prismRadialFlux,prismClosingFlux]
  ring

theorem abs_prismClosingFlux_le {T Y : PrismCoordinates → ℝ}
    (hT : ∀ z, |T z| ≤ 1) (hY : ∀ z, |Y z| ≤ 1)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    |prismClosingFlux T Y a c b l u| ≤
      (c-a)*b*(u-l)+b^2*(u-l) := by
  have hcap := norm_setIntegral_le_of_norm_le_const
    (coordinateTriangle_measure_lt_top (l := l) (u := u) hb)
    (f := fun z : ℝ × ℝ ↦ T (c,z)-T (a,z)) (C := (2 : ℝ)) (fun z _ ↦ ?_)
  · have hchord (t : ℝ) : |∫ x in (b*l)..(b*u), Y (t,(x,b))| ≤ b*(u-l) := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := b*l) (b := b*u) (fun x _ ↦ show ‖Y (t,(x,b))‖ ≤ (1 : ℝ) by
          simpa only [Real.norm_eq_abs] using hY (t,(x,b)))
      simp only [Real.norm_eq_abs,one_mul,
        abs_of_nonneg (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hlu hb))] at hi
      nlinarith
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := c) (fun t _ ↦ show ‖∫ x in (b*l)..(b*u), Y (t,(x,b))‖ ≤ b*(u-l) by
        simpa only [Real.norm_eq_abs] using hchord t)
    rw [volume_real_coordinateTriangle hb hlu,Real.norm_eq_abs] at hcap
    simp only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hac)] at hi
    dsimp [prismClosingFlux]
    exact (abs_add_le _ _).trans (by nlinarith)
  · rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hT (c,z),hT (a,z)])

theorem exists_strict_prism_replacement_scale {a c l u : ℝ}
    (hac : a < c) (hlu : l < u) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ b < ε ∧
      (c-a)*b*(u-l)+b^2*(u-l) <
        (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)) := by
  let m := Real.sqrt (1+l^2)+Real.sqrt (1+u^2)-(u-l)
  have hm : 0 < m := triangular_chord_margin_pos l u
  let b := min (ε/2) ((c-a)*m/(2*(u-l)))
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hbe : b < ε := (min_le_left _ _).trans_lt (by linarith)
  have hbs : b*(u-l) ≤ (c-a)*m/2 := by
    have hh := min_le_right (ε/2) ((c-a)*m/(2*(u-l)))
    have hd : 0 < 2*(u-l) := by linarith
    have hh' := (le_div_iff₀ hd).mp hh
    dsimp only [b] at *
    nlinarith
  refine ⟨b,hb,hbe,?_⟩
  have hcm : 0 < (c-a)*m := mul_pos (sub_pos.mpr hac) hm
  have hstrict : b*(u-l) < (c-a)*m := by linarith
  have hmul := mul_lt_mul_of_pos_left hstrict hb
  dsimp only [m] at hmul
  nlinarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_lipschitz (n : Cover) :
    LipschitzWith 1 (normalPlaneCoordinates n) := by
  apply (normalPlaneCoordinates n).lipschitz.weaken
  change ‖(normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint‖₊ ≤ 1
  simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_apply (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    normalColumnChart a n (t, y) = a + (normalPlaneEmbedding n y + t • n) := by
  change a + normalProductChart n (t, WithLp.ofLp y) = _
  rw [normalProductChart_decompose hn]
  congr 1
  exact add_comm _ _

lemma normalColumnChart_measurePreserving (a n : Cover) :
    MeasurePreserving (normalColumnChart a n) := by
  apply MeasurePreserving.trans _ (measurePreserving_add_left volume a)
  apply MeasurePreserving.trans _ (normalProductChart_measurePreserving n)
  change MeasurePreserving
    (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
  simpa only [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

lemma integral_normalColumnChart (a n : Cover) {f : Cover → ℝ} (hf : Integrable f) :
    (∫ x : Cover, f x) = ∫ y : Plane, ∫ t : ℝ, f (normalColumnChart a n (t, y)) := by
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f]
  have hi := (normalColumnChart_measurePreserving a n).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf
  exact integral_prod_symm (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z))
    (by simpa only [Measure.volume_eq_prod, Function.comp_def] using hi)

lemma normalColumnChart_height (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) : ⟪n, normalColumnChart a n (t, y) - a⟫ = t := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, inner_add_right,
    normalPlaneEmbedding_inner hn, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, zero_add]

lemma normalColumnChart_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) :
    normalPlaneCoordinates n (normalColumnChart a n (t, y) - a) = y := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, map_add, map_smul,
    normalPlaneCoordinates_embedding, normalPlaneCoordinates_normal hn, smul_zero, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_line_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    Isometry (fun t : ℝ ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + s • n) -
      (a + (normalPlaneEmbedding n y + t • n)) = (s - t) • n := by rw [sub_smul]; abel
  rw [he, norm_smul, Real.norm_eq_abs, hn, mul_one, Real.dist_eq]

lemma normalColumnChart_plane_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) :
    Isometry (fun y : Plane ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + t • n) -
      (a + (normalPlaneEmbedding n z + t • n)) = normalPlaneEmbedding n (y - z) := by
    rw [show normalPlaneEmbedding n (y - z) = normalPlaneEmbedding n y - normalPlaneEmbedding n z from
      (normalPlaneLinearIsometry n).map_sub y z]; abel
  rw [he, normalPlaneEmbedding_norm, dist_eq_norm]

lemma halfspace_directional_integrable {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (a n v : Cover) :
    Integrable (fun x ↦ halfspaceIndicator n (x - a) * fderiv ℝ ψ x v) := by
  exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hs.fderiv_apply ℝ v)).bdd_mul
      ((measurable_halfspaceIndicator n).comp (measurable_id.sub_const a)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n (x-a))

lemma integral_halfspace_normal_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) =
      ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  rw [integral_normalColumnChart a n (halfspace_directional_integrable hψ hs a n n)]
  apply integral_congr_ae
  filter_upwards [] with y
  let f : ℝ → ℝ := fun t ↦ ψ (normalColumnChart a n (t,y))
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ normalColumnChart a n (t,y)) := by
    simp_rw [normalColumnChart_apply a hn]
    fun_prop
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp hc
  have hfs : HasCompactSupport f := hs.comp_isClosedEmbedding
    (normalColumnChart_line_isometry a hn y).isClosedEmbedding
  have hd (t : ℝ) : deriv f t = fderiv ℝ ψ (normalColumnChart a n (t,y)) n := by
    have hh : HasDerivAt (fun s : ℝ ↦ normalColumnChart a n (s,y)) n t := by
      simp_rw [normalColumnChart_apply a hn]
      simpa only [one_smul, add_zero, zero_add, id_eq, add_assoc] using
        ((hasDerivAt_id t).smul_const n).const_add (a + normalPlaneEmbedding n y)
    exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hh).deriv
  have he (t : ℝ) : halfspaceIndicator n (normalColumnChart a n (t,y)-a) *
      fderiv ℝ ψ (normalColumnChart a n (t,y)) n = (Iio (0 : ℝ)).indicator (deriv f) t := by
    by_cases ht : t < 0 <;> simp [halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    hfs.integral_Iic_deriv_eq (hf.of_le (by simp)) 0]
  simp [f, normalColumnChart_apply a hn]

lemma integral_halfspace_tangent_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Plane) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)) = 0 := by
  let f : Cover → ℝ := fun x ↦ halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)
  have hi := halfspace_directional_integrable hψ hs a n (normalPlaneEmbedding n v)
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f, Measure.volume_eq_prod]
  have hic := (normalColumnChart_measurePreserving a n).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  rw [integral_prod (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z)) (by
    simpa only [Measure.volume_eq_prod, Function.comp_def] using hic)]
  have he (t : ℝ) : (∫ y : Plane, f (normalColumnChart a n (t,y))) = 0 := by
    let g : Plane → ℝ := fun y ↦ ψ (normalColumnChart a n (t,y))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ normalColumnChart a n (t,y)) := by
      simp_rw [normalColumnChart_apply a hn]
      exact contDiff_const.add ((normalPlaneLinearIsometry n).contDiff.add contDiff_const)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.comp hc
    have hs' : HasCompactSupport g := hs.comp_isClosedEmbedding
      (normalColumnChart_plane_isometry a hn t).isClosedEmbedding
    have hd (y : Plane) : fderiv ℝ g y v =
        fderiv ℝ ψ (normalColumnChart a n (t,y)) (normalPlaneEmbedding n v) := by
      have hline := ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt (x := y)).add_const (t • n) |>.const_add a
      have hh := ((hψ.differentiable (by simp) _).hasFDerivAt.comp y hline).fderiv
      have he : g = ψ ∘ (fun z : Plane ↦ a + ((normalPlaneLinearIsometry n).toContinuousLinearMap z + t • n)) := by
        funext z
        simp only [g, Function.comp_def, normalColumnChart_apply a hn]
        rfl
      rw [he, hh, normalColumnChart_apply a hn]
      rfl
    have hh : (fun y : Plane ↦ f (normalColumnChart a n (t,y))) =
        fun y ↦ (if t < 0 then (1 : ℝ) else 0) * fderiv ℝ g y v := by
      ext y
      by_cases ht : t < 0 <;> simp [f, halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
    rw [hh, integral_const_mul, integral_compact_fderiv_zero hg hs', mul_zero]
  simp_rw [he]
  simp

lemma integral_halfspace_directional_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Cover) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x v) =
      ⟪n,v⟫ * ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  have he (x : Cover) : halfspaceIndicator n (x-a) * fderiv ℝ ψ x v =
      halfspaceIndicator n (x-a) * fderiv ℝ ψ x
        (normalPlaneEmbedding n (normalPlaneCoordinates n v)) +
      ⟪n,v⟫ * (halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) := by
    conv_lhs => arg 2; arg 2; rw [← normalPlaneCoordinates_reconstruct hn v]
    rw [map_add, map_smul]
    ring
  simp_rw [he]
  rw [integral_add (halfspace_directional_integrable hψ hs a n _)
      ((halfspace_directional_integrable hψ hs a n n).const_mul ⟪n,v⟫),
    integral_const_mul, integral_halfspace_tangent_derivative a hn hψ hs,
    integral_halfspace_normal_derivative a hn hψ hs, zero_add]

theorem integral_halfspace_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * divergence F x) =
      ∫ y : Plane, ⟪n, F (a + normalPlaneEmbedding n y)⟫ := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ halfspace_directional_integrable (hp i) (hps i) a n _)]
  simp_rw [integral_halfspace_directional_derivative a hn (hp _) (hps _)]
  have hg (i : Fin 3) : Integrable (fun y : Plane ↦ ⟪n, EuclideanSpace.single i 1⟫ *
      ψ i (a + normalPlaneEmbedding n y)) := by
    have hc := (hp i).continuous.comp (normalColumnChart_plane_isometry a hn 0).continuous
    have hcc := (hps i).comp_isClosedEmbedding (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
    have hi := (hc.integrable_of_hasCompactSupport (μ := volume) hcc).const_mul ⟪n, EuclideanSpace.single i 1⟫
    simpa only [Function.comp_def, normalColumnChart_apply a hn, zero_smul, add_zero] using hi
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ hg i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [EuclideanSpace.inner_single_right, ψ]
  simp [PiLp.inner_apply, mul_comm]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupNormalMeasure
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverLocalPerimeter_mono (A : Set Cover) {O P : Set Cover} (hOP : O ⊆ P) :
    coverLocalPerimeter A O ≤ coverLocalPerimeter A P := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hs
  apply iSup_le
  intro hO
  apply iSup_le
  intro hb
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
    (le_iSup_of_le (hO.trans hOP) (le_iSup_of_le hb le_rfl))))

theorem coverLocalPerimeter_le_normal {A O : Set Cover}
    {ν : FiniteMeasure BlowupNormalBundle} (hO : MeasurableSet O)
    (hO1 : O ⊆ Metric.closedBall (0 : Cover) 1)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) :
    coverLocalPerimeter A O ≤ (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hs
  apply iSup_le
  intro hFO
  apply iSup_le
  intro hb
  have hm : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} := hO.preimage measurable_fst
  have hc : Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) :=
    (continuous_subtype_val.comp continuous_snd).inner (hF.continuous.comp continuous_fst)
  have hbd (z : BlowupNormalBundle) : ‖⟪(z.2 : Cover),F z.1⟫‖ ≤ 1 := by
    calc
      _ ≤ ‖(z.2 : Cover)‖*‖F z.1‖ := norm_inner_le_norm _ _
      _ ≤ 1 := by rw [z.2.property,one_mul]; exact hb _
  have hi : Integrable (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) ν :=
    Integrable.of_bound hc.aestronglyMeasurable 1 (ae_of_all _ hbd)
  have hri : Integrable ({z : BlowupNormalBundle | z.1 ∈ O}.indicator (fun _ ↦ (1 : ℝ))) ν :=
    (integrable_const 1).indicator hm
  have he : (∫ x in A, divergence F x) ≤ (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ O} := by
    rw [← hflux F hF (hFO.trans hO1)]
    have hh := integral_mono_ae hi hri (ae_of_all _ fun z ↦ ?_)
    · simpa only [integral_indicator hm,integral_const,smul_eq_mul,mul_one,
        measureReal_restrict_apply_univ] using hh
    · by_cases hz : z.1 ∈ O
      · simpa [Set.indicator,hz] using (le_abs_self _).trans (hbd z)
      · have hzero : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hz (hFO hh))
        simp [Set.indicator,hz,hzero]
  exact (ENNReal.ofReal_le_ofReal he).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma coverPrismCoordinates_symm_apply (z : PrismCoordinates) :
    coverPrismCoordinates.symm z = WithLp.toLp 2 ![z.1,z.2.1,z.2.2] := rfl

lemma coverPrismCoordinates_measurePreserving : MeasurePreserving coverPrismCoordinates := by
  have h1 : MeasurePreserving (WithLp.ofLp : Cover → Fin 3 → ℝ) :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp h1
  have h3 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  convert! h3.comp h2 using 1
  all_goals try with_reducible_and_instances rfl

lemma coverPrismCoordinates_symm_measurePreserving :
    MeasurePreserving coverPrismCoordinates.symm :=
  coverPrismCoordinates_measurePreserving.symm coverPrismCoordinates.toHomeomorph.toMeasurableEquiv

lemma prism_component_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : PrismCoordinates ↦ F (coverPrismCoordinates.symm z) i) :=
  (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp (hF.comp coverPrismCoordinates.symm.contDiff)

lemma prism_component_compactSupport {F : Cover → Cover}
    (hF : HasCompactSupport F) (i : Fin 3) :
    HasCompactSupport (fun z : PrismCoordinates ↦ F (coverPrismCoordinates.symm z) i) := by
  have hh := hF.comp_isClosedEmbedding coverPrismCoordinates.symm.toHomeomorph.isClosedEmbedding
  apply hh.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro z hz
  contrapose! hz
  simp only [Function.mem_support,not_not] at hz ⊢
  change F (coverPrismCoordinates.symm z) = 0 at hz
  rw [hz]
  rfl

lemma prism_component_fderiv {F : Cover → Cover} (hF : Differentiable ℝ F)
    (i : Fin 3) (z v : PrismCoordinates) :
    fderiv ℝ (fun w : PrismCoordinates ↦ F (coverPrismCoordinates.symm w) i) z v =
      (fderiv ℝ F (coverPrismCoordinates.symm z) (coverPrismCoordinates.symm v)) i := by
  exact (((EuclideanSpace.proj i).hasFDerivAt.comp _
    ((hF _).hasFDerivAt.comp z coverPrismCoordinates.symm.hasFDerivAt)).fderiv |> congrArg (fun L ↦ L v))

lemma prism_coordinate_divergence {F : Cover → Cover} (hF : Differentiable ℝ F)
    (z : PrismCoordinates) :
    prismCoordinateDivergence (fun w ↦ F (coverPrismCoordinates.symm w) 0)
      (fun w ↦ F (coverPrismCoordinates.symm w) 1)
      (fun w ↦ F (coverPrismCoordinates.symm w) 2) z =
      divergence F (coverPrismCoordinates.symm z) := by
  simp only [prismCoordinateDivergence,prism_component_fderiv hF,divergence,
    Fin.sum_univ_three]
  have he0 : coverPrismCoordinates.symm (1,(0,0)) = EuclideanSpace.single 0 1 := by
    ext i; fin_cases i <;> simp [coverPrismCoordinates_symm_apply]
  have he1 : coverPrismCoordinates.symm (0,(1,0)) = EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp [coverPrismCoordinates_symm_apply]
  have he2 : coverPrismCoordinates.symm (0,(0,1)) = EuclideanSpace.single 2 1 := by
    ext i; fin_cases i <;> simp [coverPrismCoordinates_symm_apply]
  rw [he0,he1,he2]

lemma measurableSet_euclideanPrism (a c b l u : ℝ) : MeasurableSet (euclideanPrism a c b l u) :=
  (measurableSet_Ioc.prod (measurableSet_coordinateTriangle b l u)).preimage
    coverPrismCoordinates.continuous.measurable

theorem integral_euclideanPrism_divergence {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    (∫ x in euclideanPrism a c b l u, divergence F x) =
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u +
      prismClosingFlux (fun w ↦ F (coverPrismCoordinates.symm w) 0)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u := by
  have hmeas : MeasurableSet (coordinatePrism a c b l u) :=
    measurableSet_Ioc.prod (measurableSet_coordinateTriangle b l u)
  have hm := coverPrismCoordinates_symm_measurePreserving.restrict_preimage
    (measurableSet_euclideanPrism a c b l u)
  have he : coverPrismCoordinates.symm ⁻¹' euclideanPrism a c b l u = coordinatePrism a c b l u := by
    ext x; simp [euclideanPrism]
  rw [he] at hm
  rw [← hm.integral_comp coverPrismCoordinates.symm.toHomeomorph.measurableEmbedding]
  simp_rw [← prism_coordinate_divergence (hF.differentiable (by simp))]
  exact integral_coordinatePrism_divergence_split
    (prism_component_contDiff hF 0) (prism_component_contDiff hF 1) (prism_component_contDiff hF 2)
    (prism_component_compactSupport hs 0) (prism_component_compactSupport hs 1)
    (prism_component_compactSupport hs 2) hac hb hlu

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVOneDimensionalHat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma primitive_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ u in (0 : ℝ)..t, b u) := by
  have hd (t : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.continuous.intervalIntegrable 0 t) (hb.continuous.stronglyMeasurableAtFilter volume _)
    hb.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (hd t).differentiableAt,?_⟩
  simpa only [funext (fun t ↦ (hd t).deriv)] using hb

lemma intervalSmoothHat_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (a c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (intervalSmoothHat b a c) :=
  ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const)).sub
    ((primitive_contDiff hb).comp (contDiff_id.sub contDiff_const))

lemma intervalSmoothHat_hasDerivAt {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : HasDerivAt (intervalSmoothHat b a c) (b (t-a)-b (t-c)) t := by
  have hd (x : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hb.intervalIntegrable 0 x) (hb.stronglyMeasurableAtFilter volume _) hb.continuousAt
  change HasDerivAt (fun x : ℝ ↦ (∫ u in (0 : ℝ)..x-a, b u) -
    ∫ u in (0 : ℝ)..x-c, b u) _ _
  simpa only [Function.comp_def,mul_one,id_eq,Pi.sub_def] using
    ((hd (t-a)).comp t ((hasDerivAt_id t).sub_const a)).sub
      ((hd (t-c)).comp t ((hasDerivAt_id t).sub_const c))

lemma intervalSmoothHat_eq_integral {b : ℝ → ℝ} (hb : Continuous b)
    (a c t : ℝ) : intervalSmoothHat b a c t = ∫ u in t-c..t-a, b u := by
  rw [intervalSmoothHat]
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hb.intervalIntegrable 0 (t-c)) (hb.intervalIntegrable (t-c) (t-a))
  linarith

lemma intervalSmoothHat_nonneg {b : ℝ → ℝ} (hb : Continuous b)
    (hb0 : ∀ t, 0 ≤ b t) {a c : ℝ} (hac : a ≤ c) (t : ℝ) :
    0 ≤ intervalSmoothHat b a c t := by
  rw [intervalSmoothHat_eq_integral hb]
  exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ hb0 _)

lemma intervalSmoothHat_le_one {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable b volume) (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    {a c : ℝ} (hac : a ≤ c) (t : ℝ) : intervalSmoothHat b a c t ≤ 1 := by
  rw [intervalSmoothHat_eq_integral hb,intervalIntegral.integral_of_le (by linarith)]
  rw [← hb1]
  exact setIntegral_le_integral hbi (ae_of_all _ hb0)

lemma intervalSmoothHat_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a ≤ c) :
    tsupport (intervalSmoothHat b a c) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  rw [intervalSmoothHat_eq_integral hb]
  apply intervalIntegral.integral_zero_ae
  apply ae_of_all
  intro u hu
  have htc : t-c ≤ t-a := by linarith
  rw [uIoc_of_le htc] at hu
  apply image_eq_zero_of_notMem_tsupport
  intro hub
  have hur := hs hub
  simp only [mem_Icc,not_and_or,not_le] at hh
  rcases hh with hl|hr
  · linarith [hu.2,hur.1]
  · linarith [hu.1,hur.2]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma intervalSmoothHat_sum (b : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range n, intervalSmoothHat b (u i) (u (i+1)) t) =
      intervalSmoothHat b (u 0) (u n) t := by
  induction n with
  | zero => simp [intervalSmoothHat]
  | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [intervalSmoothHat]; ring

lemma partitionSmoothTest_contDiff {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (u σ : ℕ → ℝ) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (partitionSmoothTest b u σ n) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (intervalSmoothHat_contDiff hb _ _)

lemma partitionSmoothTest_deriv {b : ℝ → ℝ} (hb : Continuous b)
    (u σ : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    deriv (partitionSmoothTest b u σ n) t =
      ∑ i ∈ Finset.range n, σ i * (b (t-u i)-b (t-u (i+1))) := by
  have he : partitionSmoothTest b u σ n =
      ∑ i ∈ Finset.range n, (fun y ↦ σ i*intervalSmoothHat b (u i) (u (i+1)) y) := by
    ext y
    simp [partitionSmoothTest]
  rw [he]
  exact (HasDerivAt.sum (u := Finset.range n) (fun i _ ↦
    (intervalSmoothHat_hasDerivAt hb (u i) (u (i+1)) t).const_mul (σ i))).deriv

lemma partitionSmoothTest_bound {b : ℝ → ℝ} (hb : Continuous b)
    (hbi : Integrable b volume) (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    {u σ : ℕ → ℝ} (hu : Monotone u) (hσ : ∀ i, |σ i| ≤ 1) (n : ℕ) (t : ℝ) :
    |partitionSmoothTest b u σ n t| ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |σ i*intervalSmoothHat b (u i) (u (i+1)) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, intervalSmoothHat b (u i) (u (i+1)) t := by
      apply Finset.sum_le_sum
      intro i _
      have hh := intervalSmoothHat_nonneg hb hb0 (hu (Nat.le_succ i)) t
      rw [abs_mul,abs_of_nonneg hh]
      exact mul_le_of_le_one_left hh (hσ i)
    _ = intervalSmoothHat b (u 0) (u n) t := intervalSmoothHat_sum _ _ _ _
    _ ≤ 1 := intervalSmoothHat_le_one hb hbi hb0 hb1 (hu (Nat.zero_le n)) t

lemma partitionSmoothTest_support {b : ℝ → ℝ} (hb : Continuous b)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r)
    {u σ : ℕ → ℝ} (hu : Monotone u) (hus : ∀ i, u i ∈ Icc a c) (n : ℕ) :
    tsupport (partitionSmoothTest b u σ n) ⊆ Icc (a-r) (c+r) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hh
  apply ht
  apply Finset.sum_eq_zero
  intro i _
  have hn : t ∉ tsupport (intervalSmoothHat b (u i) (u (i+1))) := by
    intro h
    have H := intervalSmoothHat_support hb hs (hu (Nat.le_succ i)) h
    exact hh ⟨by linarith [(hus i).1,H.1],by linarith [(hus (i+1)).2,H.2]⟩
  rw [image_eq_zero_of_notMem_tsupport hn,mul_zero]

lemma bounded_mul_shift_integrable {f b : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) (hbi : Integrable b volume) (x : ℝ) :
    Integrable (fun t ↦ f t*b (t-x)) volume := by
  have hi : Integrable (fun t ↦ b (t-x)) volume := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      ((measurePreserving_add_right volume (-x)).integrable_comp hbi.aestronglyMeasurable).mpr hbi
  apply hi.norm.mono' (hf.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  apply ae_of_all
  intro t
  change |f t*b (t-x)| ≤ |b (t-x)|
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hf1 t)

lemma partitionSmoothTest_flux {f b : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) (hb : Continuous b) (hbi : Integrable b volume)
    (u σ : ℕ → ℝ) (n : ℕ) :
    (∫ t : ℝ, f t*deriv (partitionSmoothTest b u σ n) t) =
      ∑ i ∈ Finset.range n, σ i*((∫ t : ℝ, f t*b (t-u i))-
        ∫ t : ℝ, f t*b (t-u (i+1))) := by
  simp_rw [partitionSmoothTest_deriv hb,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    simp_rw [show ∀ t : ℝ, f t*(σ i*(b (t-u i)-b (t-u (i+1)))) =
      σ i*(f t*b (t-u i)-f t*b (t-u (i+1))) by intro t; ring]
    rw [integral_const_mul,integral_sub (bounded_mul_shift_integrable hf hf1 hbi _)
      (bounded_mul_shift_integrable hf hf1 hbi _)]
  · intro i _
    convert ((bounded_mul_shift_integrable hf hf1 hbi (u i)).sub
      (bounded_mul_shift_integrable hf hf1 hbi (u (i+1)))).const_mul (σ i) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simp only [Pi.sub_apply]
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma binary_tendsto_eventually_constant {α : Type*} {f : α → ℝ} {l : Filter α}
    {c : ℝ} (ht : Tendsto f l (𝓝 c)) (hb : ∀ᶠ x in l, f x=0 ∨ f x=1) :
    ∃ d : ℝ, (d=0 ∨ d=1) ∧ ∀ᶠ x in l, f x=d := by
  rcases Filter.eq_or_neBot l with hl|hl
  · exact ⟨0,Or.inl rfl,by simp [hl]⟩
  have hc : c ∈ ({0,1} : Set ℝ) := (Set.toFinite ({0,1} : Set ℝ)).isClosed.mem_of_tendsto ht
    (hb.mono (fun _ hx ↦ by simpa using hx))
  have he := ht.eventually (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ)<1/2))
  refine ⟨c,by simpa using hc,?_⟩
  filter_upwards [he,hb] with x hx hxb
  have hh : |f x-c| < 1/2 := by simpa only [Metric.mem_ball,Real.dist_eq] using hx
  rcases (show c=0 ∨ c=1 by simpa using hc) with rfl|rfl <;>
    rcases hxb with he|he <;> simp_all <;> norm_num at *

lemma binary_bv_side_constants {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hb : ∀ x ∈ s, f x=0 ∨ f x=1) (x : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ a b : ℝ,
      (∀ y ∈ s, y ∈ Metric.ball x δ → y < x → f y=a) ∧
      (∀ y ∈ s, y ∈ Metric.ball x δ → x < y → f y=b) := by
  obtain ⟨a,ha⟩ := hf.exists_tendsto_left x
  obtain ⟨b,hb'⟩ := hf.exists_tendsto_right x
  obtain ⟨a',_,ha'⟩ := binary_tendsto_eventually_constant ha
    (Filter.Eventually.mono self_mem_nhdsWithin (fun y hy ↦ hb y hy.1))
  obtain ⟨b',_,hb''⟩ := binary_tendsto_eventually_constant hb'
    (Filter.Eventually.mono self_mem_nhdsWithin (fun y hy ↦ hb y hy.1))
  obtain ⟨δ,hδ,hleft⟩ := Metric.mem_nhdsWithin_iff.mp ha'
  obtain ⟨ε,hε,hright⟩ := Metric.mem_nhdsWithin_iff.mp hb''
  refine ⟨min δ ε,lt_min hδ hε,a',b',?_,?_⟩
  · exact fun y hy hyd hyx ↦ hleft ⟨(Metric.ball_subset_ball (min_le_left _ _)) hyd,hy,hyx⟩
  · exact fun y hy hyd hxy ↦ hright ⟨(Metric.ball_subset_ball (min_le_right _ _)) hyd,hy,hxy⟩

lemma eVariationOn_le_of_pointwise_tendsto {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {s : Set ℝ} {K : ℝ≥0∞} (hg : ∀ i, eVariationOn (g i) s ≤ K)
    (ht : ∀ x ∈ s, Tendsto (fun i ↦ g i x) atTop (𝓝 (f x))) :
    eVariationOn f s ≤ K := by
  apply iSup_le
  rintro ⟨n,u,hu,hus⟩
  have hlim : Tendsto (fun j ↦ ∑ i ∈ Finset.range n,
      edist (g j (u (i+1))) (g j (u i))) atTop
      (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i)))) :=
    tendsto_finsetSum _ (fun i _ ↦ (ht _ (hus (i+1))).edist (ht _ (hus i)))
  exact le_of_tendsto hlim (Filter.Eventually.of_forall fun j ↦ (eVariationOn.sum_le hu hus).trans (hg j))

lemma locally_constant_not_mixed_closure {f : ℝ → ℝ} {s : Set ℝ}
    {y a ε : ℝ} (hε : 0 < ε)
    (hf : ∀ z ∈ s, z ∈ Metric.ball y ε → f z=a) :
    y ∉ closure {z ∈ s | f z=0} ∩ closure {z ∈ s | f z=1} := by
  rintro ⟨h0,h1⟩
  obtain ⟨z,hz,hz0⟩ := Metric.mem_closure_iff.mp h0 ε hε
  obtain ⟨w,hw,hw1⟩ := Metric.mem_closure_iff.mp h1 ε hε
  have ha0 := hf z hz.1 (by simpa only [Metric.mem_ball,dist_comm] using hz0)
  have ha1 := hf w hw.1 (by simpa only [Metric.mem_ball,dist_comm] using hw1)
  rw [hz.2] at ha0
  rw [hw.2] at ha1
  linarith

theorem binary_bv_finite_mixed_boundary {f : ℝ → ℝ} {s K : Set ℝ}
    (hf : BoundedVariationOn f s) (hb : ∀ x ∈ s, f x=0 ∨ f x=1)
    (hK : IsCompact K) :
    (K ∩ (closure {z ∈ s | f z=0} ∩ closure {z ∈ s | f z=1})).Finite := by
  let D : Set ℝ := closure {z ∈ s | f z=0} ∩ closure {z ∈ s | f z=1}
  have hlocal (x : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Metric.ball x δ, y ≠ x → y ∉ D := by
    obtain ⟨δ,hδ,a,b,ha,hb'⟩ := binary_bv_side_constants hf hb x
    refine ⟨δ,hδ,?_⟩
    intro y hy hyx
    rcases lt_or_gt_of_ne hyx with hlt|hgt
    · have hn : Metric.ball x δ ∩ Iio x ∈ 𝓝 y :=
        inter_mem (Metric.isOpen_ball.mem_nhds hy) (Iio_mem_nhds hlt)
      obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hn
      exact locally_constant_not_mixed_closure hε (fun z hz hze ↦
        ha z hz (hsub hze).1 (hsub hze).2)
    · have hn : Metric.ball x δ ∩ Ioi x ∈ 𝓝 y :=
        inter_mem (Metric.isOpen_ball.mem_nhds hy) (Ioi_mem_nhds hgt)
      obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hn
      exact locally_constant_not_mixed_closure hε (fun z hz hze ↦
        hb' z hz (hsub hze).1 (hsub hze).2)
  by_contra hfin
  obtain ⟨x,_,hx⟩ := (show (K ∩ D).Infinite from hfin).exists_accPt_of_subset_isCompact hK
    inter_subset_left
  obtain ⟨δ,hδ,hd⟩ := hlocal x
  obtain ⟨y,hy,hyx⟩ := accPt_iff_nhds.mp hx (Metric.ball x δ) (Metric.ball_mem_nhds x hδ)
  exact hd y hy.1 hyx hy.2.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

theorem smoothed_variation_of_dual_bound {f b : ℝ → ℝ}
    (hf : Measurable f) (hf1 : ∀ t, |f t| ≤ 1)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t, 0 ≤ b t) (hb1 : ∫ t, b t = 1)
    (hbs : tsupport b ⊆ Icc (-(1/8 : ℝ)) (1/8)) {L : ℝ}
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t : ℝ, f t*deriv ψ t| ≤ L) :
    eVariationOn (fun x : ℝ ↦ ∫ t : ℝ, f t*b (t-x)) (Icc (-(1/2 : ℝ)) (1/2)) ≤
      ENNReal.ofReal L := by
  let F : ℝ → ℝ := fun x ↦ ∫ t : ℝ, f t*b (t-x)
  apply iSup_le
  rintro ⟨n,u,hu,hus⟩
  let σ : ℕ → ℝ := fun i ↦ if 0 ≤ F (u i)-F (u (i+1)) then 1 else -1
  have hσ (i : ℕ) : |σ i| ≤ 1 := by dsimp [σ]; split_ifs <;> norm_num
  have he (i : ℕ) : σ i*(F (u i)-F (u (i+1))) = |F (u (i+1))-F (u i)| := by
    rw [abs_sub_comm]
    dsimp [σ]
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hs : tsupport (partitionSmoothTest b u σ n) ⊆ Ioo (-1 : ℝ) 1 :=
    (partitionSmoothTest_support hb.continuous hbs hu hus n).trans
      (by intro t ht; constructor <;> linarith [ht.1,ht.2])
  have hh := hdual (partitionSmoothTest b u σ n) (partitionSmoothTest_contDiff hb u σ n)
    hs (partitionSmoothTest_bound hb.continuous hbi hb0 hb1 hu hσ n)
  rw [partitionSmoothTest_flux hf hf1 hb.continuous hbi] at hh
  change |∑ i ∈ Finset.range n, σ i*(F (u i)-F (u (i+1)))| ≤ L at hh
  simp_rw [he] at hh
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))] at hh
  calc
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, |F (u (i+1))-F (u i)|) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ abs_nonneg _)]
      simp only [edist_dist,Real.dist_eq,F]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hh

lemma angularMollifier_radius_tendsto :
    Tendsto (fun n ↦ (angularMollifier n).rOut) atTop (𝓝 0) := by
  have he (n : ℕ) : (angularMollifier n).rOut = (1/8 : ℝ)*(1/((n : ℝ)+1)) := by
    dsimp [angularMollifier]; field_simp; ring
  simp_rw [he]
  simpa only [mul_zero] using (tendsto_const_nhds (x := (1/8 : ℝ))).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma angularMollifier_support (n : ℕ) :
    tsupport ((angularMollifier n).normed volume) ⊆ Icc (-(1/8 : ℝ)) (1/8) := by
  rw [(angularMollifier n).tsupport_normed_eq,Real.closedBall_eq_Icc]
  have hr : (angularMollifier n).rOut ≤ (1/8 : ℝ) := by
    change 2/(16*((n : ℝ)+1)) ≤ 1/8
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  intro t ht
  constructor <;> linarith [ht.1,ht.2]

lemma angular_smoothing_ae_tendsto {f : ℝ → ℝ} (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) :
    ∀ᵐ x : ℝ ∂volume, Tendsto
      (fun n ↦ ∫ t : ℝ, f t*(angularMollifier n).normed volume (t-x)) atTop (𝓝 (f x)) := by
  have hli : LocallyIntegrable f volume := by
    apply (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).locallyIntegrable.mono
      hf.aestronglyMeasurable
    exact ae_of_all _ (fun t ↦ by simpa only [Real.norm_eq_abs,abs_one] using hf1 t)
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    angularMollifier_radius_tendsto (K := 2)
    (Eventually.of_forall fun n ↦ by dsimp [angularMollifier]; ring_nf; rfl) hli
  filter_upwards [ht] with x hx
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change f t*(angularMollifier n).normed volume (t-x) =
      (angularMollifier n).normed volume (x-t)*f t
  rw [show x-t = -(t-x) by ring,(angularMollifier n).normed_neg]
  ring

theorem boundedVariationOn_good_set_of_dual_bound {f : ℝ → ℝ}
    (hf : Measurable f) (hf1 : ∀ t, |f t| ≤ 1) {L : ℝ}
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t : ℝ, f t*deriv ψ t| ≤ L) :
    ∃ s : Set ℝ, s ⊆ Icc (-(1/2 : ℝ)) (1/2) ∧
      (∀ᵐ x : ℝ ∂volume, x ∈ Icc (-(1/2 : ℝ)) (1/2) → x ∈ s) ∧
      BoundedVariationOn f s := by
  let s : Set ℝ := {x | x ∈ Icc (-(1/2 : ℝ)) (1/2) ∧ Tendsto
    (fun n ↦ ∫ t : ℝ, f t*(angularMollifier n).normed volume (t-x)) atTop (𝓝 (f x))}
  refine ⟨s,fun _ hx ↦ hx.1,(angular_smoothing_ae_tendsto hf hf1).mono (fun x hx hI ↦ ⟨hI,hx⟩),?_⟩
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply eVariationOn_le_of_pointwise_tendsto (K := ENNReal.ofReal L) _ (fun _ hx ↦ hx.2)
  intro n
  exact (eVariationOn.mono _ (show s ⊆ Icc (-(1/2 : ℝ)) (1/2) from fun _ hx ↦ hx.1)).trans
    (smoothed_variation_of_dual_bound hf hf1 (angularMollifier n).contDiff_normed
      (angularMollifier n).integrable_normed (angularMollifier n).nonneg_normed
      (angularMollifier n).integral_normed (angularMollifier_support n) hdual)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarAngularChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma triangular_mul_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ (z.1,z.1*z.2)) volume volume := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ (z.1,z.1*z.2)) :=
    measurable_fst.prodMk (measurable_fst.mul measurable_snd)
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun S hS hS0 ↦ ?_)⟩
  rw [Measure.map_apply hm hS,Measure.volume_eq_prod,
    Measure.prod_apply (hm hS)]
  have hnull : ∀ᵐ x : ℝ ∂volume, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) = 0 := by
    apply (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)).mp
    simpa only [← Measure.prod_apply hS,← Measure.volume_eq_prod] using hS0
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  change (∫⁻ x : ℝ, (volume : Measure ℝ) ((fun y : ℝ ↦ (x,x*y)) ⁻¹' S)) = 0
  rw [lintegral_congr_ae (show (fun x : ℝ ↦ (volume : Measure ℝ)
      ((fun y : ℝ ↦ (x,x*y)) ⁻¹' S)) =ᵐ[volume] 0 from ?_)]
  · simp
  filter_upwards [hnull,hn] with x hx hx0
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hx0
  exact hq.preimage_null hx

lemma planarWedgeChart_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving planarWedgeChart volume volume :=
  (planeProductCoordinates_measurePreserving.symm
    planeProductCoordinates.toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.comp
      triangular_mul_quasiMeasurePreserving

lemma planarWedgeChart_smul (s t c : ℝ) :
    c • planarWedgeChart (s,t) = planarWedgeChart (c*s,t) := by
  rw [planarWedgeChart,← planeProductCoordinates.symm.map_smul]
  congr 1
  ext <;> simp [mul_assoc]

lemma planar_cone_all_positive_scales {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {c : ℝ} (hc0 : 0 < c) :
    ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) →
      c • y ∈ Metric.ball (0 : Plane) (1/16) → (c • y ∈ C ↔ y ∈ C) := by
  rcases le_total c 1 with hle|hge
  · have h := hc c⁻¹ ((one_le_inv₀ hc0).mpr hle)
    simp only [inv_inv] at h
    exact h.mono (fun y hy hyb _ ↦ hy hyb)
  · have h := (Measure.quasiMeasurePreserving_smul (volume : Measure Plane) hc0.ne').ae
      (hc c hge)
    filter_upwards [h] with y hy _ hcy
    simpa only [inv_smul_smul₀ hc0.ne'] using (hy hcy).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slopeScalarTest_contDiff {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) : ContDiff ℝ (⊤ : ℕ∞) (slopeScalarTest χ ψ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hP : ContDiff ℝ (⊤ : ℕ∞) planeProductCoordinates :=
    planeProductCoordinates.contDiff
  by_cases hx : (planeProductCoordinates x).1 = 0
  · have heχ : χ =ᶠ[𝓝 ((planeProductCoordinates x).1)] 0 := by
      rw [hx]
      exact notMem_tsupport_iff_eventuallyEq.mp hχ0
    have he : slopeScalarTest χ ψ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(hP.continuous.fst.tendsto x).eventually heχ] with y hy
      simp only [slopeScalarTest,hy,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (hχ.contDiffAt.comp x hP.fst.contDiffAt).mul
      (hψ.contDiffAt.comp x (hP.snd.contDiffAt.div hP.fst.contDiffAt hx))

lemma slopeScalarTest_vertical_derivative {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) (x : Plane) :
    fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector =
      χ (planeProductCoordinates x).1 / (planeProductCoordinates x).1 *
        deriv ψ ((planeProductCoordinates x).2 / (planeProductCoordinates x).1) := by
  have hf := slopeScalarTest_contDiff hχ hψ hχ0
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • slopeVerticalVector) slopeVerticalVector 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const slopeVerticalVector).const_add x
  have hd := ((hf.differentiable (by simp)) (x+(0 : ℝ) • slopeVerticalVector)).hasFDerivAt.comp_hasDerivAt 0 hl
  have he (t : ℝ) : slopeScalarTest χ ψ (x+t • slopeVerticalVector) =
      χ (planeProductCoordinates x).1 *
        ψ (((planeProductCoordinates x).2+t)/(planeProductCoordinates x).1) := by
    simp [slopeScalarTest,slopeVerticalVector]
  have hline : HasDerivAt (fun t : ℝ ↦ ((planeProductCoordinates x).2+t) /
      (planeProductCoordinates x).1) ((planeProductCoordinates x).1)⁻¹ 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_add ((planeProductCoordinates x).2)).div_const
      ((planeProductCoordinates x).1) using 1 <;> first | rfl | simp only [one_div]
  have hψd := (((hψ.differentiable (by simp)) _).hasDerivAt.comp 0 hline).const_mul
    (χ (planeProductCoordinates x).1)
  have hd0 : HasDerivAt (fun t : ℝ ↦ slopeScalarTest χ ψ (x+t • slopeVerticalVector))
      (fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero] using hd
  simp_rw [he] at hd0
  have hh := hd0.unique hψd
  simpa only [zero_add,add_zero,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slopeVerticalVector_norm : ‖slopeVerticalVector‖ = 1 := by
  simp [slopeVerticalVector,planeProductCoordinates]
  change ‖(Complex.I : ℂ)‖ = 1
  exact Complex.norm_I

lemma slopeScalarTest_bound {χ ψ : ℝ → ℝ}
    (hχ : ∀ t, |χ t| ≤ 1) (hψ : ∀ t, |ψ t| ≤ 1) (x : Plane) :
    |slopeScalarTest χ ψ x| ≤ 1 := by
  rw [slopeScalarTest,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hχ _)).trans (hψ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma angular_essential_boundary_in_mixed_closure {D s : Set ℝ}
    (hfull : ∀ᵐ x : ℝ ∂volume, x ∈ Icc (-(1/2 : ℝ)) (1/2) → x ∈ s)
    {x : ℝ} (hx : x ∈ Icc (-(1/4 : ℝ)) (1/4)) (hb : x ∈ angularEssentialBoundary D) :
    x ∈ closure {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=0} ∩
      closure {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=1} := by
  have hphase (A : Set ℝ) (hA : ∀ δ : ℝ, 0 < δ → 0 < volume (A ∩ Metric.ball x δ)) :
      x ∈ closure (s ∩ A) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ : ℝ := min (ε/2) (1/4)
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hsub (t : ℝ) (ht : t ∈ Metric.ball x δ) : t ∈ Icc (-(1/2 : ℝ)) (1/2) := by
      have hd : |t-x| < δ := by simpa only [Metric.mem_ball,Real.dist_eq] using ht
      have hbd : δ ≤ 1/4 := min_le_right _ _
      constructor <;> linarith [(abs_lt.mp hd).1,(abs_lt.mp hd).2,hx.1,hx.2]
    obtain ⟨t,ht,hst⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ne_of_gt (hA δ hδ))
      (ae_restrict_of_ae hfull)
    refine ⟨t,⟨hst (hsub t ht.2),ht.1⟩,?_⟩
    have hd : dist x t < δ := by simpa only [Metric.mem_ball,dist_comm] using ht.2
    exact hd.trans_le (le_trans (min_le_left _ _) (by linarith))
  constructor
  · have hh := hphase Dᶜ (fun δ hδ ↦ (hb δ hδ).2)
    apply closure_mono (show s ∩ Dᶜ ⊆ {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=0} from ?_) hh
    exact fun t ht ↦ ⟨ht.1,indicator_of_notMem ht.2 _⟩
  · have hh := hphase D (fun δ hδ ↦ (hb δ hδ).1)
    apply closure_mono (show s ∩ D ⊆ {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=1} from ?_) hh
    exact fun t ht ↦ ⟨ht.1,indicator_of_mem ht.2 _⟩

theorem angular_dual_bv_finite_transitions {D : Set ℝ} (hD : MeasurableSet D) {L : ℝ}
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t in D, deriv ψ t| ≤ L) :
    (Icc (-(1/4 : ℝ)) (1/4) ∩ angularEssentialBoundary D).Finite := by
  let f : ℝ → ℝ := D.indicator (fun _ ↦ (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hD
  have hfb (t : ℝ) : f t=0 ∨ f t=1 := by
    by_cases ht : t ∈ D <;> simp [f,ht]
  have hf1 (t : ℝ) : |f t| ≤ 1 := by rcases hfb t with h|h <;> rw [h] <;> norm_num
  have hfdual (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hsψ : tsupport ψ ⊆ Ioo (-1 : ℝ) 1) (hbψ : ∀ t, |ψ t| ≤ 1) :
      |∫ t : ℝ, f t*deriv ψ t| ≤ L := by
    have he (t : ℝ) : f t*deriv ψ t = D.indicator (deriv ψ) t := by
      by_cases ht : t ∈ D <;> simp [f,ht]
    simp_rw [he]
    rw [integral_indicator hD]
    exact hdual ψ hψ hsψ hbψ
  obtain ⟨s,_,hfull,hbv⟩ := boundedVariationOn_good_set_of_dual_bound hf hf1 hfdual
  have hfin := binary_bv_finite_mixed_boundary hbv (fun t _ ↦ hfb t)
    (isCompact_Icc : IsCompact (Icc (-(1/4 : ℝ)) (1/4)))
  apply hfin.subset
  intro x hx
  exact ⟨hx.1,angular_essential_boundary_in_mixed_closure hfull hx.1 hx.2⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma angularEssentialBoundary_eq_support (D : Set ℝ) :
    angularEssentialBoundary D = (volume.restrict D).support ∩ (volume.restrict Dᶜ).support := by
  ext x
  rw [Set.mem_inter_iff,Metric.nhds_basis_ball.mem_measureSupport,
    Metric.nhds_basis_ball.mem_measureSupport]
  simp only [angularEssentialBoundary,Set.mem_ofPred_eq,Measure.restrict_apply Metric.isOpen_ball.measurableSet,
    inter_comm]
  simp only [forall_and]

theorem connected_angular_phase {D s : Set ℝ} (hD : MeasurableSet D)
    (hs : MeasurableSet s) (hc : IsPreconnected s)
    (hd : Disjoint s (angularEssentialBoundary D)) :
    volume (s ∩ D) = 0 ∨ volume (s ∩ Dᶜ) = 0 := by
  let U := (volume.restrict D).supportᶜ
  let W := (volume.restrict Dᶜ).supportᶜ
  have hUW : Disjoint U W := by
    have hsum : (volume.restrict D).support ∪ (volume.restrict Dᶜ).support = univ := by
      rw [← Measure.support_add,Measure.restrict_add_restrict_compl hD,Measure.support_eq_univ]
    rw [Set.disjoint_iff_inter_eq_empty]
    change (volume.restrict D).supportᶜ ∩ (volume.restrict Dᶜ).supportᶜ = ∅
    rw [← compl_union,hsum,compl_univ]
  have hsub : s ⊆ U ∪ W := by
    intro x hx
    have hx' : x ∉ angularEssentialBoundary D := fun hb ↦ Set.disjoint_left.mp hd hx hb
    rw [angularEssentialBoundary_eq_support] at hx'
    exact not_and_or.mp hx'
  have hnullD (h : s ⊆ U) : volume (s ∩ D) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  have hnullC (h : s ⊆ W) : volume (s ∩ Dᶜ) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  by_cases hU : (s ∩ U).Nonempty
  · exact Or.inl (hnullD (hc.subset_left_of_subset_union Measure.isOpen_compl_support
      Measure.isOpen_compl_support hUW hsub hU))
  · apply Or.inr
    apply hnullC
    intro x hx
    rcases hsub hx with hu|hw
    · exact (hU ⟨x,hx,hu⟩).elim
    · exact hw

lemma measure_inter_ball_zero_of_sides (A : Set ℝ) (x δ : ℝ)
    (hl : volume (Ioo (x-δ) x ∩ A) = 0) (hr : volume (Ioo x (x+δ) ∩ A) = 0) :
    volume (A ∩ Metric.ball x δ) = 0 := by
  have hp : volume ({x} ∩ A) = 0 := measure_mono_null inter_subset_left (measure_singleton x)
  apply measure_mono_null (t := (Ioo (x-δ) x ∩ A) ∪ ({x} ∩ A) ∪ (Ioo x (x+δ) ∩ A)) ?_
    (measure_union_null (measure_union_null hl hp) hr)
  intro y hy
  have hyb : |y-x| < δ := by simpa only [Metric.mem_ball,Real.dist_eq] using hy.2
  rcases lt_trichotomy y x with hh|hh|hh
  · exact Or.inl (Or.inl ⟨⟨by linarith [(abs_lt.mp hyb).1],hh⟩,hy.1⟩)
  · exact Or.inl (Or.inr ⟨hh,hy.1⟩)
  · exact Or.inr ⟨⟨hh,by linarith [(abs_lt.mp hyb).2]⟩,hy.1⟩

theorem finite_angular_transition_is_jump {D : Set ℝ} (hD : MeasurableSet D)
    {a b x : ℝ} (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hx : x ∈ Ioo a b) (hxb : x ∈ angularEssentialBoundary D) :
    ∃ δ : ℝ, 0 < δ ∧
      ((volume (Ioo (x-δ) x ∩ D) = 0 ∧ volume (Ioo x (x+δ) ∩ Dᶜ) = 0) ∨
       (volume (Ioo (x-δ) x ∩ Dᶜ) = 0 ∧ volume (Ioo x (x+δ) ∩ D) = 0)) := by
  let S := Icc a b ∩ angularEssentialBoundary D
  have hcl : IsClosed (S \ {x}) := (hfin.sdiff (t := {x})).isClosed
  have hop : IsOpen (Ioo a b \ (S \ {x})) := isOpen_Ioo.sdiff hcl
  have hxin : x ∈ Ioo a b \ (S \ {x}) := ⟨hx,by simp⟩
  obtain ⟨δ,hδ,hd⟩ := Metric.isOpen_iff.mp hop x hxin
  have hiso (y : ℝ) (hy : y ∈ Metric.ball x δ) (he : y ∈ angularEssentialBoundary D) : y=x := by
    have hh := hd hy
    by_contra hne
    exact hh.2 ⟨⟨⟨hh.1.1.le,hh.1.2.le⟩,he⟩,hne⟩
  have hleft : Disjoint (Ioo (x-δ) x) (angularEssentialBoundary D) := by
    rw [Set.disjoint_left]
    intro y hy he
    have hyb : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hy.1,hy.2]
    exact (ne_of_lt hy.2) (hiso y hyb he)
  have hright : Disjoint (Ioo x (x+δ)) (angularEssentialBoundary D) := by
    rw [Set.disjoint_left]
    intro y hy he
    have hyb : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hy.1,hy.2]
    exact (ne_of_gt hy.1) (hiso y hyb he)
  have hl := connected_angular_phase hD measurableSet_Ioo isPreconnected_Ioo hleft
  have hr := connected_angular_phase hD measurableSet_Ioo isPreconnected_Ioo hright
  refine ⟨δ,hδ,?_⟩
  rcases hl with hl|hl <;> rcases hr with hr|hr
  · exact ((ne_of_gt (hxb δ hδ).1) (measure_inter_ball_zero_of_sides D x δ hl hr)).elim
  · exact Or.inl ⟨hl,hr⟩
  · exact Or.inr ⟨hl,hr⟩
  · exact ((ne_of_gt (hxb δ hδ).2) (measure_inter_ball_zero_of_sides Dᶜ x δ hl hr)).elim

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVPlanarLocalModels
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma planar_cone_rotation {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ R ⁻¹' C ↔ y ∈ R ⁻¹' C) := by
  intro t ht
  filter_upwards [R.measurePreserving.quasiMeasurePreserving.ae (hc t ht)] with y hy hyb
  have hRy : R y ∈ Metric.ball (0 : Plane) (1/16) := by
    simpa only [Metric.mem_ball,dist_zero_right,R.norm_map] using hyb
  simpa only [Set.mem_preimage,R.map_smul] using hy hRy

lemma planar_directional_bv_rotation {C : Set Plane} {K : ℝ}
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in R ⁻¹' C, fderiv ℝ φ y u| ≤ K := by
  intro φ hφ hs hb u hu
  let ψ : Plane → ℝ := φ ∘ R.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp R.symm.toContinuousLinearEquiv.contDiff
  have hsψ : tsupport ψ ⊆ Metric.closedBall (0 : Plane) (1/32) := by
    rw [show ψ = φ ∘ R.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
    intro y hy
    have hh := hs hy
    simp only [Metric.mem_closedBall,dist_zero_right] at hh
    change ‖R.symm y‖ ≤ 1/32 at hh
    simpa only [Metric.mem_closedBall,dist_zero_right,R.symm.norm_map] using hh
  have hd (y : Plane) : fderiv ℝ ψ (R y) (R u) = fderiv ℝ φ y u := by
    have he := ((hφ.differentiable (by simp)) (R.symm (R y))).hasFDerivAt.comp (R y)
      R.symm.toContinuousLinearEquiv.hasFDerivAt
    have h := congrArg (fun A : Plane →L[ℝ] ℝ ↦ A (R u)) he.fderiv
    change fderiv ℝ ψ (R y) (R u) = fderiv ℝ φ (R.symm (R y)) (R.symm (R u)) at h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h
  have he := R.measurePreserving.setIntegral_preimage_emb R.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y ↦ fderiv ℝ ψ y (R u)) C
  simp_rw [hd] at he
  rw [he]
  exact hbv ψ hψ hsψ (fun y ↦ hb _) (R u) (by simpa using hu)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma triangular_inv_mul_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ (z.1,z.1⁻¹*z.2)) volume volume := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ (z.1,z.1⁻¹*z.2)) :=
    measurable_fst.prodMk (measurable_fst.inv.mul measurable_snd)
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun S hS hS0 ↦ ?_)⟩
  rw [Measure.map_apply hm hS,Measure.volume_eq_prod,Measure.prod_apply (hm hS)]
  have hnull : ∀ᵐ x : ℝ ∂volume, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) = 0 := by
    apply (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)).mp
    simpa only [← Measure.prod_apply hS,← Measure.volume_eq_prod] using hS0
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  change (∫⁻ x : ℝ, (volume : Measure ℝ) ((fun y : ℝ ↦ (x,x⁻¹*y)) ⁻¹' S)) = 0
  rw [lintegral_congr_ae (show (fun x : ℝ ↦ (volume : Measure ℝ)
      ((fun y : ℝ ↦ (x,x⁻¹*y)) ⁻¹' S)) =ᵐ[volume] 0 from ?_)]
  · simp
  filter_upwards [hnull,hn] with x hx hx0
  exact (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hx0)).preimage_null hx

lemma planarWedgeCoordinates_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving planarWedgeCoordinates volume volume :=
  triangular_inv_mul_quasiMeasurePreserving.comp
    planeProductCoordinates_measurePreserving.quasiMeasurePreserving

lemma planarWedgeChart_coordinates {y : Plane} (hy : (planeProductCoordinates y).1 ≠ 0) :
    planarWedgeChart (planarWedgeCoordinates y) = y := by
  unfold planarWedgeCoordinates planarWedgeChart
  simp only [mul_inv_cancel_left₀ hy,Prod.mk.eta,ContinuousLinearEquiv.symm_apply_apply]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma swapPrismPlane_apply (x : Cover) :
    swapPrismPlane x = WithLp.toLp 2 ![x 0,x 2,x 1] := by
  ext i
  fin_cases i <;> norm_num [swapPrismPlane,LinearIsometryEquiv.piLpCongrLeft,Equiv.swap_apply_def,Fin.ext_iff]

lemma normalColumnChart_zero_coordinates (n : Cover) (x : Cover) :
    normalColumnChart 0 n (coverPlaneCoordinates x) = normalRotation n x := by
  rw [coverPlaneCoordinates_apply]
  change 0 + normalProductChart n (x 0,WithLp.ofLp (WithLp.toLp 2 ![x 1,x 2])) = _
  rw [zero_add,normalProductChart_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma prismFrame_apply (n : Cover) (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Cover) :
    prismFrame n R x = normalColumnChart 0 n
      (x 0,R (planeProductCoordinates.symm (x 2,x 1))) := by
  change normalRotation n (coverPlaneRotationCLE R (swapPrismPlane x)) = _
  rw [← normalColumnChart_zero_coordinates,coverPlaneRotationCLE_coordinates,
    swapPrismPlane_apply,coverPlaneCoordinates_apply,planeProductCoordinates_symm_apply]
  rfl

lemma prismColumnCoordinates_measurePreserving :
    MeasurePreserving (fun x : Cover ↦ (x 0,planeProductCoordinates.symm (x 2,x 1))) volume volume := by
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod
    ((planeProductCoordinates_measurePreserving.symm
      planeProductCoordinates.toHomeomorph.toMeasurableEquiv).comp
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))))
  have hh := hp.comp coverPrismCoordinates_measurePreserving
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma blowup_test_inner_bound {F : Cover → Cover} (hn : ∀ x, ‖F x‖ ≤ 1)
    (z : BlowupNormalBundle) : |⟪(z.2 : Cover),F z.1⟫| ≤ 1 := by
  have hh : |⟪(z.2 : Cover),F z.1⟫| ≤ ‖F z.1‖ := by
    simpa only [Real.norm_eq_abs,z.2.property,one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (z.2 : Cover) (F z.1)
  exact hh.trans (hn _)

theorem blowupNormal_weighted_saturation {A O : Set Cover}
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {w : BlowupNormalBundle → ℝ}
    (hiw : Integrable w ((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}))
    {C : ℝ} (hC : 0 < C) (hwC : ∀ z, w z ≤ C)
    {L : ℝ}
    (hL : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z*⟪(z.2 : Cover),F z.1⟫
        ∂(ν : Measure BlowupNormalBundle)) ≤ L) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z
      ∂(ν : Measure BlowupNormalBundle)) ≤ L := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let P : ℝ := (coverLocalPerimeter A O).toReal
  let I : ℝ := ∫ z, w z ∂μ
  let B : ℝ := P+(L-I)/C
  have hmass : (∫ _ : BlowupNormalBundle, (1 : ℝ) ∂μ) = P := by
    simp only [integral_const,smul_eq_mul,mul_one,μ,P,heq,Measure.real,Measure.restrict_apply_univ]
  have hbound (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F ⊆ O) (hn : ∀ x, ‖F x‖ ≤ 1) :
      (∫ x in A, divergence F x) ≤ B := by
    let T : BlowupNormalBundle → ℝ := fun z ↦ ⟪(z.2 : Cover),F z.1⟫
    have hTc : Continuous T := (continuous_subtype_val.comp continuous_snd).inner
      (hF.continuous.comp continuous_fst)
    have hTb (z : BlowupNormalBundle) : |T z| ≤ 1 := blowup_test_inner_bound hn z
    have hiT : Integrable T μ := Integrable.of_bound hTc.aestronglyMeasurable 1
      (ae_of_all μ hTb)
    have hiwT : Integrable (fun z ↦ w z*T z) μ := by
      simpa only [mul_comm] using hiw.bdd_mul hTc.aestronglyMeasurable (ae_of_all μ hTb)
    have hh := integral_mono (hiw.sub hiwT)
      (((integrable_const (1 : ℝ)).sub hiT).const_mul C) (fun z ↦ show
        w z-w z*T z ≤ C*(1-T z) from by
          have ht : 0 ≤ 1-T z := by linarith [(le_abs_self (T z)).trans (hTb z)]
          nlinarith [mul_le_mul_of_nonneg_right (hwC z) ht])
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hiw hiwT,integral_const_mul,integral_sub (integrable_const 1) hiT,hmass] at hh
    have hf : (∫ z, T z ∂μ) = ∫ x in A, divergence F x := by
      rw [show (∫ z, T z ∂μ) = ∫ z, T z ∂(ν : Measure BlowupNormalBundle) from ?_]
      · exact hflux F hF hs hO hn
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzF : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hz (hO hh))
      simp only [T,hzF,inner_zero_right]
    rw [hf] at hh
    have hl := hL F hF hs hO hn
    change (∫ z, w z*T z ∂μ) ≤ L at hl
    dsimp only [B]
    apply (mul_le_mul_iff_left₀ hC).mp
    rw [add_mul,div_mul_cancel₀ _ hC.ne']
    dsimp only [I]
    nlinarith
  have hB : 0 ≤ B := by
    have hh := hbound (fun _ ↦ 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa only [divergence_zero,integral_zero] using hh
  have hper : coverLocalPerimeter A O ≤ ENNReal.ofReal B := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hn
    exact ENNReal.ofReal_le_ofReal (hbound F hF hs hO hn)
  have hPB : P ≤ B := by
    simpa only [P,ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hper
  have hnon : 0 ≤ (L-I)/C := by dsimp only [B] at hPB; linarith
  have hh := mul_nonneg hnon hC.le
  rw [div_mul_cancel₀ _ hC.ne'] at hh
  exact sub_nonneg.mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma setIntegral_divergence_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B))
    {F : Cover → Cover} (hs : tsupport F ⊆ O) :
    (∫ x in A, divergence F x) = ∫ x in B, divergence F x := by
  rw [← integral_indicator hA,← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hAB] with x hx
  by_cases ho : x ∈ O
  · have hh := hx ho
    by_cases ha : x ∈ A
    · simp only [indicator_of_mem ha,indicator_of_mem (hh.mp ha)]
    · simp only [indicator_of_notMem ha,indicator_of_notMem (mt hh.mpr ha)]
  · have hz : divergence F x = 0 := divergence_of_notMem_tsupport (fun hh ↦ ho (hs hh))
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha,hb,hz]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurableSet_coverHalfspace (n : Cover) : MeasurableSet (coverHalfspace n) :=
  measurableSet_lt (by fun_prop) measurable_const

lemma halfspace_indicator_eq (n : Cover) :
    (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) = halfspaceIndicator n := rfl

lemma setIntegral_coverHalfspace_divergence {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in coverHalfspace n, divergence F x) =
      ∫ y : Plane, ⟪n,F (normalPlaneEmbedding n y)⟫ := by
  have hh := integral_halfspace_divergence 0 hn hF hs
  simp only [sub_zero,zero_add] at hh
  rw [← hh,← halfspace_indicator_eq]
  simp only [← indicator_mul_left,one_mul,integral_indicator (measurableSet_coverHalfspace n)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_scalar_trace_integrable {n : Cover} (hn : ‖n‖ = 1)
    {φ : Cover → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun y : Plane ↦ φ (normalPlaneEmbedding n y)) := by
  have he : (fun y : Plane ↦ normalColumnChart 0 n (0,y)) = normalPlaneEmbedding n := by
    funext y
    simp only [normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add]
  have hi := (normalColumnChart_plane_isometry 0 hn 0)
  have hc : Continuous (normalPlaneEmbedding n) := he ▸ hi.continuous
  have hh : Topology.IsClosedEmbedding (normalPlaneEmbedding n) := he ▸ hi.isClosedEmbedding
  exact (hφ.comp hc).integrable_of_hasCompactSupport (hs.comp_isClosedEmbedding hh)

theorem blowup_flat_patch_weighted_flux {A O U : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (normalPlaneEmbedding n y)*⟪n,F (normalPlaneEmbedding n y)⟫ := by
  let H : Cover → Cover := fun x ↦ φ x • F x
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hφ.smul hF
  have hsH : HasCompactSupport H := hsφ.smul_right
  have hHU : tsupport H ⊆ U := (tsupport_smul_subset_left _ _).trans hφU
  have hHO : tsupport H ⊆ O := (tsupport_smul_subset_left _ _).trans hφO
  have hnH (x) : ‖H x‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφb x).1]
    exact (mul_le_mul (hφb x).2 (hnF x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),H z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ z, ⟪(z.2 : Cover),H z.1⟫ ∂(ν : Measure BlowupNormalBundle) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hh : H z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hHO h))
    simp only [hh,inner_zero_right]
  have hh := hflux H hH hsH hHO hnH
  rw [setIntegral_divergence_congr_local hA (measurableSet_coverHalfspace n) hflat hHU,
    setIntegral_coverHalfspace_divergence hn hH hsH] at hh
  rw [← he] at hh
  simpa only [H,inner_smul_right] using hh

theorem blowup_flat_patch_weighted_mass {A O U : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (normalPlaneEmbedding n y) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiplane := plane_scalar_trace_integrable hn hφ.continuous hsφ
  have hfield (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) ≤ ∫ y : Plane, φ (normalPlaneEmbedding n y) := by
    rw [show (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) = _ from
      blowup_flat_patch_weighted_flux hA hn hflat hflux hφ hsφ hφU hφO hφb hF hnF]
    have hc : Continuous (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
      have hh := (normalColumnChart_plane_isometry 0 hn 0).continuous
      simp only [normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] at hh
      exact continuous_const.inner (hF.continuous.comp hh)
    have hb (y : Plane) : |⟪n,F (normalPlaneEmbedding n y)⟫| ≤ 1 :=
      by
      have hh : |⟪n,F (normalPlaneEmbedding n y)⟫| ≤ ‖n‖*‖F (normalPlaneEmbedding n y)‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) n (F (normalPlaneEmbedding n y))
      exact hh.trans (by rw [hn,one_mul]; exact hnF _)
    have hi := hiplane.bdd_mul hc.aestronglyMeasurable (ae_of_all volume hb)
    apply integral_mono (by simpa only [mul_comm] using hi) hiplane
    intro y
    exact mul_le_of_le_one_right (hφb _).1 ((le_abs_self _).trans (hb y))
  refine le_antisymm ?_ ?_
  · exact blowupNormal_weighted_saturation heq hflux hiφ (by norm_num : (0 : ℝ)<1)
      (fun z ↦ (hφb z.1).2) (fun F hF _ _ hnF ↦ hfield F hF hnF)
  · have he := blowup_flat_patch_weighted_flux hA hn hflat hflux hφ hsφ hφU hφO hφb
      (F := fun _ ↦ n) contDiff_const (fun _ ↦ hn.le)
    simp only [real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at he
    rw [← he]
    have hiinner : Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),n⟫) μ := by
      simpa only [mul_comm] using hiφ.bdd_mul
        (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) from by fun_prop).aestronglyMeasurable
        (ae_of_all μ fun z ↦ blowup_test_inner_bound (F := fun _ ↦ n) (fun _ ↦ hn.le) z)
    apply integral_mono hiinner hiφ
    intro z
    apply mul_le_of_le_one_right (hφb _).1
    exact (real_inner_le_norm (z.2 : Cover) n).trans_eq (by rw [z.2.property,hn,one_mul])

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlaneAreaCoordinates
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_coordinates_of_inner_zero {n x : Cover} (hn : ‖n‖ = 1)
    (hx : ⟪n,x⟫ = 0) : normalPlaneEmbedding n (normalPlaneCoordinates n x) = x := by
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart 0 n).surjective x
  have ht : t = 0 := by
    have hh := normalColumnChart_height 0 hn t y
    simp only [sub_zero] at hh
    exact hh.symm.trans hx
  rw [ht,normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add,
    normalPlaneCoordinates_embedding]

lemma normalPlaneCoordinates_norm_of_inner_zero {n x : Cover} (hn : ‖n‖ = 1)
    (hx : ⟪n,x⟫ = 0) : ‖normalPlaneCoordinates n x‖ = ‖x‖ := by
  rw [← normalPlaneEmbedding_norm n,normalPlaneEmbedding_coordinates_of_inner_zero hn hx]

theorem integral_normalPlane_eq_isometry {n : Cover} (hn : ‖n‖ = 1)
    (T : Plane →ₗᵢ[ℝ] Cover) (hT : ∀ y, ⟪n,T y⟫ = 0) (f : Cover → ℝ) :
    (∫ y : Plane, f (normalPlaneEmbedding n y)) = ∫ y : Plane, f (T y) := by
  let R : Plane →ₗᵢ[ℝ] Plane :=
    { toLinearMap := (normalPlaneCoordinates n).toLinearMap.comp T.toLinearMap
      norm_map' := fun y ↦ (normalPlaneCoordinates_norm_of_inner_zero hn (hT y)).trans (T.norm_map y) }
  have hR : Function.Surjective R :=
    (LinearMap.injective_iff_surjective (f := R.toLinearMap)).mp R.injective
  let e := LinearIsometryEquiv.ofSurjective R hR
  have he (y : Plane) : normalPlaneEmbedding n (e y) = T y :=
    normalPlaneEmbedding_coordinates_of_inner_zero hn (hT y)
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  simp_rw [he]

lemma radialFaceNormal_norm (u : ℝ) : ‖radialFaceNormal u‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  have hh := radial_face_coefficients u
  simpa [radialFaceNormal,neg_div,neg_sq,add_comm] using hh

lemma radialFaceIsometry_perp (u : ℝ) (y : Plane) :
    ⟪radialFaceNormal u,radialFaceIsometry u y⟫ = 0 := by
  simp [radialFaceNormal,radialFaceIsometry,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,Fin.sum_univ_three]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {ι : Type*} [Fintype ι]

lemma strictPatchCutoff_contDiff {g : ι → Cover → ℝ}
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (strictPatchCutoff g ε) :=
  contDiff_prod (fun i _ ↦ Real.smoothTransition.contDiff.comp
    (((hg i).div_const ε).sub contDiff_const))

lemma strictPatchCutoff_bounds (g : ι → Cover → ℝ) (ε : ℝ) (x : Cover) :
    strictPatchCutoff g ε x ∈ Icc 0 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ ↦ Real.smoothTransition.nonneg _)
  · exact Finset.prod_le_one (fun i _ ↦ Real.smoothTransition.nonneg _)
      (fun i _ ↦ Real.smoothTransition.le_one _)

lemma strictPatchCutoff_support {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i))
    {ε : ℝ} (hε : 0 < ε) : tsupport (strictPatchCutoff g ε) ⊆ {x | ∀ i, ε ≤ g i x} := by
  classical
  apply closure_minimal
  · intro x hx i
    by_contra hh
    have hz : Real.smoothTransition (g i x/ε-1) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      have hh' : g i x ≤ ε := le_of_not_ge hh
      have hd := (div_le_one hε).mpr hh'
      linarith
    apply hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  · have he : {x : Cover | ∀ i, ε ≤ g i x} = ⋂ i, {x | ε ≤ g i x} := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i ↦ isClosed_le continuous_const (hg i))

lemma strictPatchCutoff_tsupport_open {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i))
    {ε : ℝ} (hε : 0 < ε) : tsupport (strictPatchCutoff g ε) ⊆ strictPatchOpen g := by
  intro x hx i
  exact hε.trans_le (strictPatchCutoff_support hg hε hx i)

omit [Fintype ι] in
lemma strictPatchOpen_subset_closed (g : ι → Cover → ℝ) :
    strictPatchOpen g ⊆ strictPatchClosed g := fun _ hx i ↦ (hx i).le

lemma strictPatchCutoff_hasCompactSupport {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i))
    (hK : IsCompact (strictPatchClosed g)) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (strictPatchCutoff g ε) :=
  hK.of_isClosed_subset isClosed_closure
    ((strictPatchCutoff_tsupport_open hg hε).trans (strictPatchOpen_subset_closed g))

lemma measurableSet_strictPatchOpen {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i)) :
    MeasurableSet (strictPatchOpen g) := by
  have he : strictPatchOpen g = ⋂ i, {x | 0 < g i x} := by ext; simp [strictPatchOpen]
  rw [he]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const (hg i).measurable)

lemma strictPatchCutoff_tendsto (g : ι → Cover → ℝ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0)) (x : Cover) :
    Tendsto (fun j ↦ strictPatchCutoff g (ε j) x) atTop
      (𝓝 ((strictPatchOpen g).indicator (fun _ ↦ (1 : ℝ)) x)) := by
  classical
  by_cases hx : x ∈ strictPatchOpen g
  · rw [indicator_of_mem hx]
    have he (i : ι) : ∀ᶠ j in atTop, Real.smoothTransition (g i x/ε j-1) = 1 := by
      filter_upwards [hlim.eventually (gt_mem_nhds (half_pos (hx i)))] with j hj
      apply Real.smoothTransition.one_of_one_le
      have hh := (le_div_iff₀ (hε j)).mpr (show (2 : ℝ)*ε j ≤ g i x by linarith)
      linarith
    have hall : ∀ᶠ j in atTop, ∀ i, Real.smoothTransition (g i x/ε j-1) = 1 :=
      eventually_all.mpr he
    apply tendsto_const_nhds.congr'
    filter_upwards [hall] with j hj
    simp only [strictPatchCutoff,hj,Finset.prod_const_one]
  · rw [indicator_of_notMem hx]
    simp only [strictPatchOpen,mem_ofPred_eq,not_forall,not_lt] at hx
    obtain ⟨i,hi⟩ := hx
    have hz (j : ℕ) : strictPatchCutoff g (ε j) x = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply Real.smoothTransition.zero_of_nonpos
      have hh := div_nonpos_of_nonpos_of_nonneg hi (hε j).le
      linarith
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma blowup_weighted_remainder_le {ν : FiniteMeasure BlowupNormalBundle} {O : Set Cover}
    {w : BlowupNormalBundle → ℝ}
    (hiw : Integrable w ((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}))
    (hwb : ∀ z, w z ∈ Icc 0 1)
    {F : Cover → Cover} (hF : Continuous F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) -
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) ≤
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ O} -
      (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z ∂(ν : Measure BlowupNormalBundle)) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let T : BlowupNormalBundle → ℝ := fun z ↦ ⟪(z.2 : Cover),F z.1⟫
  have hTc : Continuous T := (continuous_subtype_val.comp continuous_snd).inner (hF.comp continuous_fst)
  have hTb (z : BlowupNormalBundle) : |T z| ≤ 1 := blowup_test_inner_bound hnF z
  have hiT : Integrable T μ := Integrable.of_bound hTc.aestronglyMeasurable 1 (ae_of_all μ hTb)
  have hiwT : Integrable (fun z ↦ w z*T z) μ := by
    simpa only [mul_comm] using hiw.bdd_mul hTc.aestronglyMeasurable (ae_of_all μ hTb)
  have hm := integral_mono (hiT.sub hiwT) ((integrable_const (1 : ℝ)).sub hiw) (fun z ↦ show
      T z-w z*T z ≤ 1-w z from by
        have ht := (le_abs_self (T z)).trans (hTb z)
        nlinarith [mul_nonneg (sub_nonneg.mpr (hwb z).2) (sub_nonneg.mpr ht)])
  simp only [Pi.sub_apply] at hm
  rw [integral_sub hiT hiwT,integral_sub (integrable_const 1) hiw,integral_const] at hm
  simpa only [μ,T,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hm

theorem blowup_two_flat_patches_remainder_le {A O U₁ U₂ : Set Cover} (hA : MeasurableSet A)
    {n₁ n₂ : Cover} (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hflat₁ : ∀ᵐ x : Cover ∂volume, x ∈ U₁ → (x ∈ A ↔ x ∈ coverHalfspace n₁))
    (hflat₂ : ∀ᵐ x : Cover ∂volume, x ∈ U₂ → (x ∈ A ↔ x ∈ coverHalfspace n₂))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ₁ φ₂ : Cover → ℝ}
    (hφ₁ : ContDiff ℝ (⊤ : ℕ∞) φ₁) (hs₁ : HasCompactSupport φ₁)
    (hφ₂ : ContDiff ℝ (⊤ : ℕ∞) φ₂) (hs₂ : HasCompactSupport φ₂)
    (hU₁ : tsupport φ₁ ⊆ U₁) (hU₂ : tsupport φ₂ ⊆ U₂)
    (hO₁ : tsupport φ₁ ⊆ O) (hO₂ : tsupport φ₂ ⊆ O)
    (hb₁ : ∀ x, φ₁ x ∈ Icc 0 1) (hb₂ : ∀ x, φ₂ x ∈ Icc 0 1)
    (hsum : ∀ x, φ₁ x+φ₂ x ≤ 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) -
      (∫ y : Plane, φ₁ (normalPlaneEmbedding n₁ y)*⟪n₁,F (normalPlaneEmbedding n₁ y)⟫) -
      (∫ y : Plane, φ₂ (normalPlaneEmbedding n₂ y)*⟪n₂,F (normalPlaneEmbedding n₂ y)⟫) ≤
    (coverLocalPerimeter A O).toReal -
      (∫ y : Plane, φ₁ (normalPlaneEmbedding n₁ y)) -
      (∫ y : Plane, φ₂ (normalPlaneEmbedding n₂ y)) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ {φ : Cover → ℝ} (hc : Continuous φ) (hb : ∀ x, φ x ∈ Icc 0 1) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hc.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb z.1).1]; exact (hb z.1).2)
  have hi₁ := hiφ hφ₁.continuous hb₁
  have hi₂ := hiφ hφ₂.continuous hb₂
  have hiF {φ : Cover → ℝ} (hi : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),F z.1⟫) μ := by
    simpa only [mul_comm,Function.comp_apply] using hi.bdd_mul
      ((continuous_subtype_val.comp continuous_snd).inner
        (hF.continuous.comp continuous_fst)).aestronglyMeasurable
      (ae_of_all μ (blowup_test_inner_bound hnF))
  have hh := blowup_weighted_remainder_le (hi₁.add hi₂)
    (fun z ↦ ⟨add_nonneg (hb₁ z.1).1 (hb₂ z.1).1,hsum z.1⟩) hF.continuous hnF
  simp only [Pi.add_apply,add_mul] at hh
  rw [integral_add (hiF hi₁) (hiF hi₂),integral_add hi₁ hi₂] at hh
  have htot : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hflux F hF hs hO hnF
    intro z hz
    have he : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hO h))
    simp only [he,inner_zero_right]
  rw [htot,blowup_flat_patch_weighted_flux hA hn₁ hflat₁ hflux hφ₁ hs₁ hU₁ hO₁ hb₁ hF hnF,
    blowup_flat_patch_weighted_flux hA hn₂ hflat₂ hflux hφ₂ hs₂ hU₂ hO₂ hb₂ hF hnF,
    blowup_flat_patch_weighted_mass hA hn₁ hflat₁ heq hflux hφ₁ hs₁ hU₁ hO₁ hb₁,
    blowup_flat_patch_weighted_mass hA hn₂ hflat₂ heq hflux hφ₂ hs₂ hU₂ hO₂ hb₂] at hh
  rw [Measure.real,← heq] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {ι : Type*} [Fintype ι]

theorem strictPatchCutoff_integral_tendsto {g : ι → Cover → ℝ}
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) (hK : IsCompact (strictPatchClosed g))
    (T : Plane →ₗᵢ[ℝ] Cover) {f : Cover → ℝ} (hf : Continuous f) (hfb : ∀ x, |f x| ≤ 1)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ y : Plane, strictPatchCutoff g (ε i) (T y)*f (T y)) atTop
      (𝓝 (∫ y in T ⁻¹' strictPatchOpen g, f (T y))) := by
  let K : Set Plane := T ⁻¹' strictPatchClosed g
  have hKc : IsCompact K := T.isometry.isClosedEmbedding.isCompact_preimage hK
  have hi : Integrable (K.indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKc.measurableSet
  have hb (i : ℕ) (y : Plane) :
      ‖strictPatchCutoff g (ε i) (T y)*f (T y)‖ ≤ K.indicator (fun _ ↦ (1 : ℝ)) y := by
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy,norm_mul,Real.norm_eq_abs,
        abs_of_nonneg (strictPatchCutoff_bounds g (ε i) (T y)).1,Real.norm_eq_abs]
      exact (mul_le_mul (strictPatchCutoff_bounds g (ε i) (T y)).2 (hfb (T y))
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · rw [indicator_of_notMem hy]
      have hz : strictPatchCutoff g (ε i) (T y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hh
        exact hy (strictPatchOpen_subset_closed g
          (strictPatchCutoff_tsupport_open (fun j ↦ (hg j).continuous) (hε i) hh))
      simp only [hz,zero_mul,norm_zero,le_refl]
  have ht := tendsto_integral_of_dominated_convergence (K.indicator (fun _ ↦ (1 : ℝ)))
    (fun i ↦ (((strictPatchCutoff_contDiff hg (ε i)).continuous.comp T.continuous).mul
      (hf.comp T.continuous)).aestronglyMeasurable)
    hi (fun i ↦ ae_of_all volume (hb i))
    (ae_of_all volume (fun y ↦ (strictPatchCutoff_tendsto g hε hlim (T y)).mul_const (f (T y))))
  have he : (fun y : Plane ↦ (strictPatchOpen g).indicator (fun _ ↦ (1 : ℝ)) (T y)*f (T y)) =
      (T ⁻¹' strictPatchOpen g).indicator (fun y ↦ f (T y)) := by
    funext y
    by_cases hy : T y ∈ strictPatchOpen g <;> simp [hy]
  rw [he,integral_indicator ((measurableSet_strictPatchOpen (fun i ↦ (hg i).continuous)).preimage T.continuous.measurable)] at ht
  exact ht

lemma strictPatchCutoff_disjoint_sum_le_one {κ : Type*} [Fintype κ]
    {g : ι → Cover → ℝ} {h : κ → Cover → ℝ}
    (hg : ∀ i, Continuous (g i)) (hh : ∀ i, Continuous (h i))
    (hd : Disjoint (strictPatchOpen g) (strictPatchOpen h)) {ε : ℝ} (hε : 0 < ε)
    (x : Cover) : strictPatchCutoff g ε x+strictPatchCutoff h ε x ≤ 1 := by
  by_cases hx : x ∈ strictPatchOpen g
  · have hx' : x ∉ strictPatchOpen h := fun hxh ↦ Set.disjoint_left.mp hd hx hxh
    have hz : strictPatchCutoff h ε x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx' (strictPatchCutoff_tsupport_open hh hε h))
    rw [hz,add_zero]
    exact (strictPatchCutoff_bounds _ _ _).2
  · have hz : strictPatchCutoff g ε x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (strictPatchCutoff_tsupport_open hg hε h))
    rw [hz,zero_add]
    exact (strictPatchCutoff_bounds _ _ _).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem blowup_two_polytope_patches_remainder_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {g : ι → Cover → ℝ} {h : κ → Cover → ℝ}
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i))
    (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i))
    (hKg : IsCompact (strictPatchClosed g)) (hKh : IsCompact (strictPatchClosed h))
    (hdis : Disjoint (strictPatchOpen g) (strictPatchOpen h))
    {A O : Set Cover} (hA : MeasurableSet A)
    {n₁ n₂ : Cover} (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hflat₁ : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen g → (x ∈ A ↔ x ∈ coverHalfspace n₁))
    (hflat₂ : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen h → (x ∈ A ↔ x ∈ coverHalfspace n₂))
    (hgO : strictPatchOpen g ⊆ O) (hhO : strictPatchOpen h ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) -
      (∫ y in normalPlaneEmbedding n₁ ⁻¹' strictPatchOpen g, ⟪n₁,F (normalPlaneEmbedding n₁ y)⟫) -
      (∫ y in normalPlaneEmbedding n₂ ⁻¹' strictPatchOpen h, ⟪n₂,F (normalPlaneEmbedding n₂ y)⟫) ≤
    (coverLocalPerimeter A O).toReal -
      volume.real (normalPlaneEmbedding n₁ ⁻¹' strictPatchOpen g) -
      volume.real (normalPlaneEmbedding n₂ ⁻¹' strictPatchOpen h) := by
  let ε : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ)+1)
  have hε (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht₁ := strictPatchCutoff_integral_tendsto hg hKg (normalPlaneLinearIsometry n₁)
    (continuous_const.inner hF.continuous)
    (fun x ↦ (abs_real_inner_le_norm n₁ (F x)).trans (by rw [hn₁,one_mul]; exact hnF x)) hε hlim
  have ht₂ := strictPatchCutoff_integral_tendsto hh hKh (normalPlaneLinearIsometry n₂)
    (continuous_const.inner hF.continuous)
    (fun x ↦ (abs_real_inner_le_norm n₂ (F x)).trans (by rw [hn₂,one_mul]; exact hnF x)) hε hlim
  have hm₁ := strictPatchCutoff_integral_tendsto hg hKg (normalPlaneLinearIsometry n₁)
    (continuous_const (y := (1 : ℝ))) (fun _ ↦ le_of_eq (abs_one)) hε hlim
  have hm₂ := strictPatchCutoff_integral_tendsto hh hKh (normalPlaneLinearIsometry n₂)
    (continuous_const (y := (1 : ℝ))) (fun _ ↦ le_of_eq (abs_one)) hε hlim
  simp only [mul_one,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] at hm₁ hm₂
  apply le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub ht₁).sub ht₂)
    ((tendsto_const_nhds.sub hm₁).sub hm₂)
  exact Filter.Eventually.of_forall (fun i ↦ blowup_two_flat_patches_remainder_le hA hn₁ hn₂
    hflat₁ hflat₂ heq hflux
    (strictPatchCutoff_contDiff hg (ε i))
    (strictPatchCutoff_hasCompactSupport (fun j ↦ (hg j).continuous) hKg (hε i))
    (strictPatchCutoff_contDiff hh (ε i))
    (strictPatchCutoff_hasCompactSupport (fun j ↦ (hh j).continuous) hKh (hε i))
    (strictPatchCutoff_tsupport_open (fun j ↦ (hg j).continuous) (hε i))
    (strictPatchCutoff_tsupport_open (fun j ↦ (hh j).continuous) (hε i))
    ((strictPatchCutoff_tsupport_open (fun j ↦ (hg j).continuous) (hε i)).trans hgO)
    ((strictPatchCutoff_tsupport_open (fun j ↦ (hh j).continuous) (hε i)).trans hhO)
    (strictPatchCutoff_bounds g (ε i)) (strictPatchCutoff_bounds h (ε i))
    (strictPatchCutoff_disjoint_sum_le_one (fun j ↦ (hg j).continuous)
      (fun j ↦ (hh j).continuous) hdis (hε i)) hF hs hO hnF)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma cover_field_component_bound {v : Cover} (hv : ‖v‖ ≤ 1) (i : Fin 3) : |v i| ≤ 1 := by
  have he : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  exact he.trans hv

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff
namespace CubicTorus

theorem integral_prism_surgery {A : Set Cover}
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in A \ euclideanPrism a c b l u, divergence F x) =
      (∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u -
      prismClosingFlux (fun w ↦ F (coverPrismCoordinates.symm w) 0)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u := by
  have hc : HasCompactSupport (divergence F) :=
    hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  have hi := (continuous_divergence hF).integrable_of_hasCompactSupport (μ := volume) hc
  have he : (A ∩ euclideanPrism a c b l u : Set Cover) =ᵐ[volume] euclideanPrism a c b l u := by
    filter_upwards [hPA] with x hx
    exact propext ⟨fun h ↦ h.2,fun h ↦ ⟨hx h,h⟩⟩
  have hh := integral_inter_add_sdiff (measurableSet_euclideanPrism a c b l u)
    (hi.integrableOn (s := A))
  rw [setIntegral_congr_set he,integral_euclideanPrism_divergence hF hs hac hb hlu] at hh
  linarith

theorem integral_prism_surgery_error {A : Set Cover}
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hnorm : ∀ x, ‖F x‖ ≤ 1) :
    |(∫ x in A \ euclideanPrism a c b l u, divergence F x) -
      ((∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u)| ≤
      (c-a)*b*(u-l)+b^2*(u-l) := by
  rw [integral_prism_surgery hac hb hlu hPA hF hs]
  simp only [sub_sub_cancel_left,abs_neg]
  exact abs_prismClosingFlux_le
    (fun w ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm w)) 0)
    (fun w ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm w)) 2) hac hb hlu

theorem coverLocalPerimeter_prism_surgery_le {A O : Set Cover}
    {a c b l u M : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    (hrem : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u ≤ M) :
    coverLocalPerimeter (A \ euclideanPrism a c b l u) O ≤
      ENNReal.ofReal (M+(c-a)*b*(u-l)+b^2*(u-l)) := by
  apply iSup_le; intro F
  apply iSup_le; intro hF
  apply iSup_le; intro hs
  apply iSup_le; intro hO
  apply iSup_le; intro hn
  apply ENNReal.ofReal_le_ofReal
  have he := integral_prism_surgery_error hac hb hlu hPA hF hs hn
  have hh := hrem F hF hs hO hn
  have he' := (le_abs_self _).trans he
  linarith

lemma prism_surgery_symmDiff_subset (A : Set Cover) (a c b l u : ℝ) :
    A ∆ (A \ euclideanPrism a c b l u) ⊆ euclideanPrism a c b l u := by
  intro x hx
  simp only [mem_symmDiff,Set.mem_sdiff] at hx
  rcases hx with hx | hx
  · exact Classical.byContradiction (fun hh ↦ hx.2 ⟨hx.1,hh⟩)
  · exact False.elim (hx.2 hx.1.1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialPatchInequalities_contDiff (a c b l u : ℝ) (i : Fin 6) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPatchInequalities a c b l u i) := by
  have hc (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ x j) :=
    (EuclideanSpace.proj j : Cover →L[ℝ] ℝ).contDiff
  fin_cases i
  · exact (hc 0).sub contDiff_const
  · exact contDiff_const.sub (hc 0)
  · exact hc 2
  · exact contDiff_const.sub (hc 2)
  · exact (hc 1).sub (contDiff_const.mul (hc 2))
  · exact (contDiff_const.mul (hc 2)).sub (hc 1)

lemma mem_radialPatchOpen (a c b l u : ℝ) (x : Cover) :
    x ∈ strictPatchOpen (radialPatchInequalities a c b l u) ↔
      a < x 0 ∧ x 0 < c ∧ 0 < x 2 ∧ x 2 < b ∧ l*x 2 < x 1 ∧ x 1 < u*x 2 := by
  simp [strictPatchOpen,radialPatchInequalities,Fin.forall_fin_succ,sub_pos]

lemma mem_radialPatchClosed (a c b l u : ℝ) (x : Cover) :
    x ∈ strictPatchClosed (radialPatchInequalities a c b l u) ↔
      a ≤ x 0 ∧ x 0 ≤ c ∧ 0 ≤ x 2 ∧ x 2 ≤ b ∧ l*x 2 ≤ x 1 ∧ x 1 ≤ u*x 2 := by
  simp [strictPatchClosed,radialPatchInequalities,Fin.forall_fin_succ,sub_nonneg]

lemma radialPatchClosed_isCompact (a c b l u : ℝ) :
    IsCompact (strictPatchClosed (radialPatchInequalities a c b l u)) := by
  let M := (|l|+|u|)*|b|
  have hK : IsCompact (coverPrismCoordinates ⁻¹' (Icc a c ×ˢ (Icc (-M) M ×ˢ Icc 0 b))) :=
    coverPrismCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  apply hK.of_isClosed_subset
  · have he : strictPatchClosed (radialPatchInequalities a c b l u) =
        ⋂ i : Fin 6, {x | 0 ≤ radialPatchInequalities a c b l u i x} := by ext; simp [strictPatchClosed]
    rw [he]
    exact isClosed_iInter (fun i ↦ isClosed_le continuous_const
      (radialPatchInequalities_contDiff a c b l u i).continuous)
  intro x hx
  obtain ⟨ha,hc,h0,hb,hl,hu⟩ := (mem_radialPatchClosed a c b l u x).mp hx
  have hbb : x 2 ≤ |b| := hb.trans (le_abs_self b)
  have hlow : -M ≤ x 1 := by
    have hp := mul_le_mul_of_nonneg_left hbb (abs_nonneg l)
    have hq := mul_le_mul_of_nonneg_right (neg_abs_le l) h0
    have hr := mul_nonneg (abs_nonneg u) (abs_nonneg b)
    dsimp [M]; nlinarith
  have hupp : x 1 ≤ M := by
    have hp := mul_le_mul_of_nonneg_left hbb (abs_nonneg u)
    have hq := mul_le_mul_of_nonneg_right (le_abs_self u) h0
    have hr := mul_nonneg (abs_nonneg l) (abs_nonneg b)
    dsimp [M]; nlinarith
  exact ⟨⟨ha,hc⟩,⟨hlow,hupp⟩,h0,hb⟩

lemma radialPatchOpen_disjoint {a c b l u l' u' : ℝ} (hul : u ≤ l') :
    Disjoint (strictPatchOpen (radialPatchInequalities a c b l u))
      (strictPatchOpen (radialPatchInequalities a c b l' u')) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨_,_,h0,_,_,hu⟩ := (mem_radialPatchOpen a c b l u x).mp hx
  obtain ⟨_,_,_,_,hl,_⟩ := (mem_radialPatchOpen a c b l' u' x).mp hy
  have hh := mul_le_mul_of_nonneg_right hul h0.le
  linarith

lemma radialFaceIsometry_preimage_patch {a c b l u v : ℝ} (hl : l < v) (hu : v < u) :
    radialFaceIsometry v ⁻¹' strictPatchOpen (radialPatchInequalities a c b l u) =
      {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < Real.sqrt (1+v^2)*b} := by
  ext y
  rw [Set.mem_preimage,mem_radialPatchOpen]
  change (a < y 0 ∧ y 0 < c ∧ 0 < (1/Real.sqrt (1+v^2))*y 1 ∧
    (1/Real.sqrt (1+v^2))*y 1 < b ∧
    l*((1/Real.sqrt (1+v^2))*y 1) < (v/Real.sqrt (1+v^2))*y 1 ∧
    (v/Real.sqrt (1+v^2))*y 1 < u*((1/Real.sqrt (1+v^2))*y 1)) ↔ _
  have hd : 0 < Real.sqrt (1+v^2) := Real.sqrt_pos.mpr (by positivity)
  have he : (v/Real.sqrt (1+v^2))*y 1 = v*((1/Real.sqrt (1+v^2))*y 1) := by ring
  rw [he]
  have hs : (1/Real.sqrt (1+v^2))*y 1 = y 1/Real.sqrt (1+v^2) := by ring
  rw [hs]
  constructor
  · rintro ⟨ha,hc,h0,hb,_,_⟩
    exact ⟨ha,hc,(div_pos_iff_of_pos_right hd).mp h0,
      by have hh := (div_lt_iff₀ hd).mp hb; simpa only [mul_comm] using hh⟩
  · rintro ⟨ha,hc,h0,hb⟩
    have hp : 0 < y 1/Real.sqrt (1+v^2) := div_pos h0 hd
    exact ⟨ha,hc,hp,(div_lt_iff₀ hd).mpr (by simpa only [mul_comm] using hb),
      mul_lt_mul_of_pos_right hl hp,mul_lt_mul_of_pos_right hu hp⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeFaceCoordinates_measurePreserving : MeasurePreserving planeFaceCoordinates :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

lemma radial_face_patch_area {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u) :
    volume.real (radialFaceIsometry v ⁻¹' strictPatchOpen (radialPatchInequalities a c b l u)) =
      (c-a)*b*Real.sqrt (1+v^2) := by
  rw [radialFaceIsometry_preimage_patch hl hu]
  have he : {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < Real.sqrt (1+v^2)*b} =
      planeFaceCoordinates ⁻¹' (Ioo a c ×ˢ Ioo 0 (Real.sqrt (1+v^2)*b)) := by
    ext y; change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _)); tauto
  rw [he,Measure.real,planeFaceCoordinates_measurePreserving.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
    Measure.volume_eq_prod,Measure.prod_prod,ENNReal.toReal_mul]
  change volume.real (Ioo a c)*volume.real (Ioo 0 (Real.sqrt (1+v^2)*b)) = _
  rw [Real.volume_real_Ioo_of_le hac,Real.volume_real_Ioo_of_le (mul_nonneg (Real.sqrt_nonneg _) hb)]
  ring

lemma integral_plane_coordinate_rectangle {f : Plane → ℝ} (hf : Continuous f)
    {a c d : ℝ} (hac : a ≤ c) (hd : 0 ≤ d) :
    (∫ y in {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < d}, f y) =
      ∫ t in a..c, ∫ s in (0 : ℝ)..d, f (WithLp.toLp 2 ![t,s]) := by
  have he : {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < d} =
      planeFaceCoordinates ⁻¹' (Ioo a c ×ˢ Ioo 0 d) := by
    ext y; change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _)); tauto
  rw [he]
  have hm := planeFaceCoordinates_measurePreserving.restrict_preimage
    (s := Ioo a c ×ˢ Ioo 0 d) (measurableSet_Ioo.prod measurableSet_Ioo)
  have hms := hm.symm planeFaceCoordinates.toHomeomorph.toMeasurableEquiv
  rw [← hms.integral_comp planeFaceCoordinates.symm.toHomeomorph.measurableEmbedding]
  let f' : ℝ × ℝ → ℝ := fun z ↦ f (planeFaceCoordinates.symm z)
  have hc : Continuous f' := hf.comp planeFaceCoordinates.symm.continuous
  have hi : IntegrableOn f' (Ioo a c ×ˢ Ioo 0 d) (volume.prod volume) :=
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  change (∫ z in Ioo a c ×ˢ Ioo 0 d, f' z) = _
  rw [Measure.volume_eq_prod,setIntegral_prod f' hi,
    setIntegral_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le hac]
  apply intervalIntegral.integral_congr
  intro t _
  change (∫ s in Ioo 0 d, f' (t,s)) = _
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le hd]
  rfl

theorem radial_face_patch_integral {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u)
    {f : Cover → ℝ} (hf : Continuous f) :
    (∫ y in radialFaceIsometry v ⁻¹' strictPatchOpen (radialPatchInequalities a c b l u),
      f (radialFaceIsometry v y)) =
      Real.sqrt (1+v^2) *
        ∫ t in a..c, ∫ s in (0 : ℝ)..b, f (WithLp.toLp 2 ![t,v*s,s]) := by
  rw [radialFaceIsometry_preimage_patch hl hu,
    integral_plane_coordinate_rectangle (f := fun y ↦ f (radialFaceIsometry v y))
      (hf.comp (radialFaceIsometry v).continuous) hac
      (mul_nonneg (Real.sqrt_nonneg _) hb),← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have hd : Real.sqrt (1+v^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 1+v^2)).ne'
  have he (s : ℝ) : radialFaceIsometry v (WithLp.toLp 2 ![t,s]) =
      WithLp.toLp 2 ![t,v*(s/Real.sqrt (1+v^2)),s/Real.sqrt (1+v^2)] := by
    ext i; fin_cases i <;> simp [radialFaceIsometry] <;> ring
  simp_rw [he]
  rw [intervalIntegral.integral_comp_div (fun s ↦ f (WithLp.toLp 2 ![t,v*s,s])) hd]
  simp only [zero_div,mul_div_cancel_left₀ _ hd,smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma setIntegral_normalPlane_eq_isometry {n : Cover} (hn : ‖n‖ = 1)
    (T : Plane →ₗᵢ[ℝ] Cover) (hT : ∀ y, ⟪n,T y⟫ = 0)
    {U : Set Cover} (hU : MeasurableSet U) (f : Cover → ℝ) :
    (∫ y in normalPlaneEmbedding n ⁻¹' U, f (normalPlaneEmbedding n y)) =
      ∫ y in T ⁻¹' U, f (T y) := by
  have he := integral_normalPlane_eq_isometry hn T hT (U.indicator f)
  have he' (S : Plane → Cover) : (fun y ↦ U.indicator f (S y)) =
      (S ⁻¹' U).indicator (fun y ↦ f (S y)) := by
    funext y; by_cases hy : S y ∈ U <;> simp [hy]
  have hmn : MeasurableSet (normalPlaneEmbedding n ⁻¹' U) :=
    hU.preimage (normalPlaneLinearIsometry n).continuous.measurable
  rw [he',he',integral_indicator hmn,
    integral_indicator (hU.preimage T.continuous.measurable)] at he
  exact he

lemma real_volume_normalPlane_eq_isometry {n : Cover} (hn : ‖n‖ = 1)
    (T : Plane →ₗᵢ[ℝ] Cover) (hT : ∀ y, ⟪n,T y⟫ = 0)
    {U : Set Cover} (hU : MeasurableSet U) :
    volume.real (normalPlaneEmbedding n ⁻¹' U) = volume.real (T ⁻¹' U) := by
  have hh := setIntegral_normalPlane_eq_isometry hn T hT hU (fun _ ↦ (1 : ℝ))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

lemma inner_radialFaceNormal (v : ℝ) (x : Cover) :
    ⟪radialFaceNormal v,x⟫ = (x 1-v*x 2)/Real.sqrt (1+v^2) := by
  simp [radialFaceNormal,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three]
  ring

theorem radial_face_flux {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u)
    {F : Cover → Cover} (hF : Continuous F) :
    (∫ y in normalPlaneEmbedding (radialFaceNormal v) ⁻¹'
        strictPatchOpen (radialPatchInequalities a c b l u),
      ⟪radialFaceNormal v,F (normalPlaneEmbedding (radialFaceNormal v) y)⟫) =
      ∫ t in a..c, ∫ s in (0 : ℝ)..b,
        F (WithLp.toLp 2 ![t,v*s,s]) 1-v*F (WithLp.toLp 2 ![t,v*s,s]) 2 := by
  rw [setIntegral_normalPlane_eq_isometry (radialFaceNormal_norm v) (radialFaceIsometry v)
    (radialFaceIsometry_perp v) (measurableSet_strictPatchOpen
      (fun i ↦ (radialPatchInequalities_contDiff a c b l u i).continuous))
    (fun x ↦ ⟪radialFaceNormal v,F x⟫)]
  rw [radial_face_patch_integral (f := fun x ↦ ⟪radialFaceNormal v,F x⟫) hac hb hl hu (continuous_const.inner hF)]
  simp_rw [inner_radialFaceNormal]
  simp_rw [div_eq_mul_inv,intervalIntegral.integral_mul_const]
  rw [mul_left_comm,mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity : 0 < 1+v^2)).ne',mul_one]

theorem neg_radial_face_flux {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u)
    {F : Cover → Cover} (hF : Continuous F) :
    (∫ y in normalPlaneEmbedding (-radialFaceNormal v) ⁻¹'
        strictPatchOpen (radialPatchInequalities a c b l u),
      ⟪-radialFaceNormal v,F (normalPlaneEmbedding (-radialFaceNormal v) y)⟫) =
      -(∫ t in a..c, ∫ s in (0 : ℝ)..b,
        F (WithLp.toLp 2 ![t,v*s,s]) 1-v*F (WithLp.toLp 2 ![t,v*s,s]) 2) := by
  have hn : ‖-radialFaceNormal v‖ = 1 := by rw [norm_neg,radialFaceNormal_norm]
  have hperp (y : Plane) : ⟪-radialFaceNormal v,radialFaceIsometry v y⟫ = 0 := by
    rw [inner_neg_left,radialFaceIsometry_perp,neg_zero]
  rw [setIntegral_normalPlane_eq_isometry hn (radialFaceIsometry v) hperp
    (measurableSet_strictPatchOpen (fun i ↦ (radialPatchInequalities_contDiff a c b l u i).continuous))
    (fun x ↦ ⟪-radialFaceNormal v,F x⟫)]
  simp_rw [inner_neg_left]
  rw [integral_neg]
  congr 1
  rw [radial_face_patch_integral (f := fun x ↦ ⟪radialFaceNormal v,F x⟫) hac hb hl hu (continuous_const.inner hF)]
  simp_rw [inner_radialFaceNormal]
  simp_rw [div_eq_mul_inv,intervalIntegral.integral_mul_const]
  rw [mul_left_comm,mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity : 0 < 1+v^2)).ne',mul_one]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupComplement
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma prismRadialFlux_eq_sub {X Y : PrismCoordinates → ℝ}
    (hX : Continuous X) (hY : Continuous Y) (a c b l u : ℝ) :
    prismRadialFlux X Y a c b l u =
      (∫ t in a..c, ∫ s in (0 : ℝ)..b, X (t,(s*u,s))-u*Y (t,(s*u,s))) -
      (∫ t in a..c, ∫ s in (0 : ℝ)..b, X (t,(s*l,s))-l*Y (t,(s*l,s))) := by
  have hc (k : ℝ) : Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..b,
      X (t,(s*k,s))-k*Y (t,(s*k,s))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  have he (t : ℝ) : (∫ s in (0 : ℝ)..b,
      (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))) =
      (∫ s in (0 : ℝ)..b, X (t,(s*u,s))-u*Y (t,(s*u,s))) -
      (∫ s in (0 : ℝ)..b, X (t,(s*l,s))-l*Y (t,(s*l,s))) :=
    intervalIntegral.integral_sub ((by fun_prop : Continuous (fun s : ℝ ↦
      X (t,(s*u,s))-u*Y (t,(s*u,s)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun s : ℝ ↦
      X (t,(s*l,s))-l*Y (t,(s*l,s)))).intervalIntegrable _ _)
  simp only [prismRadialFlux,he]
  exact intervalIntegral.integral_sub ((hc u).intervalIntegrable _ _) ((hc l).intervalIntegrable _ _)

theorem blowup_radial_faces_remainder_le
    {a c b l u l₀ l₁ u₀ u₁ : ℝ} (hac : a ≤ c) (hb : 0 ≤ b)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    {A O : Set Cover} (hA : MeasurableSet A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c b l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c b u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u ≤
    (coverLocalPerimeter A O).toReal -
      (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)) := by
  have hnL : ‖-radialFaceNormal l‖ = 1 := by rw [norm_neg,radialFaceNormal_norm]
  have hpL (y : Plane) : ⟪-radialFaceNormal l,radialFaceIsometry l y⟫ = 0 := by
    rw [inner_neg_left,radialFaceIsometry_perp,neg_zero]
  have hmL := measurableSet_strictPatchOpen
    (fun i ↦ (radialPatchInequalities_contDiff a c b l₀ l₁ i).continuous)
  have hmU := measurableSet_strictPatchOpen
    (fun i ↦ (radialPatchInequalities_contDiff a c b u₀ u₁ i).continuous)
  have h := blowup_two_polytope_patches_remainder_le
    (radialPatchInequalities_contDiff a c b l₀ l₁)
    (radialPatchInequalities_contDiff a c b u₀ u₁)
    (radialPatchClosed_isCompact a c b l₀ l₁) (radialPatchClosed_isCompact a c b u₀ u₁)
    (radialPatchOpen_disjoint hsep) hA hnL (radialFaceNormal_norm u)
    hflatL hflatU hLO hUO heq hflux hF hs hO hnF
  rw [neg_radial_face_flux hac hb hl₀ hl₁ hF.continuous,
    radial_face_flux hac hb hu₀ hu₁ hF.continuous,
    real_volume_normalPlane_eq_isometry hnL (radialFaceIsometry l) hpL hmL,
    real_volume_normalPlane_eq_isometry (radialFaceNormal_norm u)
      (radialFaceIsometry u) (radialFaceIsometry_perp u) hmU,
    radial_face_patch_area hac hb hl₀ hl₁,radial_face_patch_area hac hb hu₀ hu₁] at h
  rw [prismRadialFlux_eq_sub (prism_component_contDiff hF 1).continuous
    (prism_component_contDiff hF 2).continuous]
  simp only [coverPrismCoordinates_symm_apply] at ⊢
  have he (t s k : ℝ) : WithLp.toLp 2 ![t,s*k,s] = WithLp.toLp 2 ![t,k*s,s] := by rw [mul_comm s k]
  simp_rw [he]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem coverLocalPerimeter_prism_surgery_lt
    {a c b l u l₀ l₁ u₀ u₁ : ℝ} (hac : a < c) (hb : 0 < b)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    (hsmall : (c-a)*b*(u-l)+b^2*(u-l) <
      (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)))
    {A O : Set Cover} (hA : MeasurableSet A)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c b l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c b u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) :
    coverLocalPerimeter (A \ euclideanPrism a c b l u) O < coverLocalPerimeter A O := by
  have hlu : l ≤ u := (hl₁.trans_le hsep).trans hu₀ |>.le
  let area := (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2))
  have harea : 0 < area := by
    dsimp [area]
    have hlp : 0 < Real.sqrt (1+l^2) := Real.sqrt_pos.mpr (by positivity)
    have hup : 0 < Real.sqrt (1+u^2) := Real.sqrt_pos.mpr (by positivity)
    exact mul_pos (mul_pos (sub_pos.mpr hac) hb) (add_pos hlp hup)
  have hrem (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F ⊆ O) (hn : ∀ x, ‖F x‖ ≤ 1) :=
    blowup_radial_faces_remainder_le hac.le hb.le hl₀ hl₁ hu₀ hu₁ hsep hA hflatL hflatU
      hLO hUO heq hflux hF hs hO hn
  have hpa : area ≤ (coverLocalPerimeter A O).toReal := by
    have hz := hrem (fun _ ↦ 0) contDiff_const (by simp [HasCompactSupport])
      (by simp) (by simp)
    simp [area,divergence,prismRadialFlux] at hz ⊢
    linarith
  have hp : 0 < (coverLocalPerimeter A O).toReal := harea.trans_le hpa
  have hfin : coverLocalPerimeter A O ≠ ⊤ := by rw [heq]; exact measure_ne_top _ _
  have hbound := coverLocalPerimeter_prism_surgery_le hac.le hb.le hlu hPA hrem
  apply hbound.trans_lt
  apply lt_of_lt_of_eq ?_ (ENNReal.ofReal_toReal hfin)
  apply (ENNReal.ofReal_lt_ofReal_iff hp).mpr
  dsimp [area] at *
  linarith

theorem no_minimizing_strict_prism_sector
    {a c b l u l₀ l₁ u₀ u₁ : ℝ} (hac : a < c) (hb : 0 < b)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    (hsmall : (c-a)*b*(u-l)+b^2*(u-l) <
      (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)))
    {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hPK : euclideanPrism a c b l u ⊆ K)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c b l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c b u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  have hlt := coverLocalPerimeter_prism_surgery_lt hac hb hl₀ hl₁ hu₀ hu₁ hsep hsmall hA
    hPA hflatL hflatU hLO hUO heq hflux
  have hle := hmin (A \ euclideanPrism a c b l u)
    (hA.diff (measurableSet_euclideanPrism a c b l u))
    ((prism_surgery_symmDiff_subset A a c b l u).trans hPK)
  exact not_lt_of_ge hle hlt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma exists_normal_sphere_null_radius (ν : FiniteMeasure BlowupNormalBundle)
    {a b : ℝ} (hab : a < b) :
    ∃ r : ℝ, a < r ∧ r < b ∧ (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0 := by
  have hc := Measure.countable_meas_level_set_pos
    (μ := (ν : Measure BlowupNormalBundle)) (g := fun z : BlowupNormalBundle ↦ ‖z.1‖)
    (by fun_prop)
  obtain ⟨r,hr,hrab⟩ := (hc.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hab)
  refine ⟨r,hrab.1,hrab.2,?_⟩
  exact le_antisymm (not_lt.mp hr) bot_le

lemma normal_closedBall_ae_eq_ball {ν : FiniteMeasure BlowupNormalBundle} {r : ℝ}
    (hr : (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0) :
    {z : BlowupNormalBundle | z.1 ∈ Metric.closedBall (0 : Cover) r} =ᵐ[(ν : Measure BlowupNormalBundle)]
      {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) r} := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hr] with z hz
  apply propext
  simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right]
  exact ⟨fun h ↦ lt_of_le_of_ne h hz,le_of_lt⟩

theorem coverLocalPerimeter_closedBall_eq_ball_of_normal
    {A : Set Cover} {ν : FiniteMeasure BlowupNormalBundle} {r : ℝ} (hr1 : r ≤ 1)
    (hr : (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0)
    (heq : coverLocalPerimeter A (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) :
    coverLocalPerimeter A (Metric.closedBall (0 : Cover) r) =
      coverLocalPerimeter A (Metric.ball (0 : Cover) r) := by
  apply le_antisymm
  · have hh := coverLocalPerimeter_le_normal Metric.isClosed_closedBall.measurableSet
      (Metric.closedBall_subset_closedBall hr1) hflux
    exact hh.trans_eq ((measure_congr (normal_closedBall_ae_eq_ball hr)).trans heq.symm)
  · exact coverLocalPerimeter_mono A Metric.ball_subset_closedBall

theorem normal_radius_local_minimizing {A : Set Cover} {ν : FiniteMeasure BlowupNormalBundle}
    {a r : ℝ} (ha : 0 < a) (har : a < r) (hr1 : r ≤ 1)
    (hr : (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0)
    (heq : coverLocalPerimeter A (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      A ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b)) :
    ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter A (Metric.closedBall (0 : Cover) r) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) r) := by
  intro D hD hAD
  rw [coverLocalPerimeter_closedBall_eq_ball_of_normal hr1 hr heq hflux]
  exact hmin D hD a r ha har hr1 hAD

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma euclideanPrism_mono_height {a c b d l u : ℝ} (hbd : b ≤ d) :
    euclideanPrism a c b l u ⊆ euclideanPrism a c d l u := by
  intro x hx
  exact ⟨hx.1,⟨hx.2.1.1,hx.2.1.2.trans hbd⟩,hx.2.2⟩

lemma radialPatchOpen_mono_height {a c b d l u : ℝ} (hbd : b ≤ d) :
    strictPatchOpen (radialPatchInequalities a c b l u) ⊆
      strictPatchOpen (radialPatchInequalities a c d l u) := by
  intro x hx
  obtain ⟨ha,hc,h0,hb,hl,hu⟩ := (mem_radialPatchOpen a c b l u x).mp hx
  exact (mem_radialPatchOpen a c d l u x).mpr ⟨ha,hc,h0,hb.trans_le hbd,hl,hu⟩

theorem no_minimizing_small_radial_sector
    {a c ε l u l₀ l₁ u₀ u₁ : ℝ} (hac : a < c) (hε : 0 < ε)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hPK : euclideanPrism a c ε l u ⊆ K)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c ε l u → x ∈ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  have hlu : l < u := (hl₁.trans_le hsep).trans hu₀
  obtain ⟨b,hb,hbε,hsmall⟩ := exists_strict_prism_replacement_scale hac hlu hε
  have hPL := radialPatchOpen_mono_height (a := a) (c := c) (l := l₀) (u := l₁) hbε.le
  have hPU := radialPatchOpen_mono_height (a := a) (c := c) (l := u₀) (u := u₁) hbε.le
  have hP := euclideanPrism_mono_height (a := a) (c := c) (l := l) (u := u) hbε.le
  exact no_minimizing_strict_prism_sector hac hb hl₀ hl₁ hu₀ hu₁ hsep hsmall hA hmin
    (hP.trans hPK) (hPA.mono (fun _ hx hy ↦ hx (hP hy)))
    (hflatL.mono (fun _ hx hy ↦ hx (hPL hy)))
    (hflatU.mono (fun _ hx hy ↦ hx (hPU hy))) (hPL.trans hLO) (hPU.trans hUO) heq hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma integral_cover_divergence_zero {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, divergence F x) = 0 := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    exact integral_compact_fderiv_zero (hp i) (hps i) _
  · intro i _
    exact (((hp i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hps i).fderiv_apply ℝ _)

lemma integral_cover_divergence_compl {A : Set Cover} (hA : MeasurableSet A)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in Aᶜ, divergence F x) = -(∫ x in A, divergence F x) := by
  have hi : Integrable (divergence F) (volume : Measure Cover) :=
    (continuous_divergence hF).integrable_of_hasCompactSupport
    (hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F))
  have hh := integral_add_compl hA hi
  rw [integral_cover_divergence_zero hF hs] at hh
  linarith

theorem coverLocalPerimeter_compl {A : Set Cover} (hA : MeasurableSet A) (O : Set Cover) :
    coverLocalPerimeter Aᶜ O = coverLocalPerimeter A O := by
  have hle {A : Set Cover} (hA : MeasurableSet A) :
      coverLocalPerimeter Aᶜ O ≤ coverLocalPerimeter A O := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hnorm
    have hFn : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ -F x) := hF.neg
    have hsFn : HasCompactSupport (fun x ↦ -F x) := hs.neg
    have hOFn : tsupport (fun x ↦ -F x) ⊆ O := by
      change tsupport (-F) ⊆ O
      simpa only [tsupport_neg] using hO
    have hnFn (x) : ‖-F x‖ ≤ 1 := by simpa using hnorm x
    have he : (∫ x in Aᶜ, divergence F x) = ∫ x in A, divergence (fun y ↦ -F y) x := by
      rw [integral_cover_divergence_compl hA hF hs]
      simp only [divergence_neg,integral_neg]
    rw [he]
    exact le_iSup_of_le (fun x ↦ -F x) (le_iSup_of_le hFn (le_iSup_of_le hsFn
      (le_iSup_of_le hOFn (le_iSup_of_le hnFn le_rfl))))
  exact le_antisymm (hle hA) (by simpa only [compl_compl] using hle hA.compl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma continuous_reverseBlowupNormal : Continuous reverseBlowupNormal :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

lemma reverseBlowupNormal_spatial_mass (ν : FiniteMeasure BlowupNormalBundle)
    {O : Set Cover} (hO : MeasurableSet O) :
    (ν.map reverseBlowupNormal : Measure BlowupNormalBundle) {z | z.1 ∈ O} =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [FiniteMeasure.toMeasure_map,Measure.map_apply continuous_reverseBlowupNormal.measurable
    (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} from hO.preimage measurable_fst)]
  rfl

lemma reverseBlowupNormal_flux {A O : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hFO : tsupport F ⊆ O) (hFn : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν.map reverseBlowupNormal : Measure BlowupNormalBundle)) =
      ∫ x in Aᶜ, divergence F x := by
  rw [FiniteMeasure.toMeasure_map,integral_map continuous_reverseBlowupNormal.measurable.aemeasurable
    (continuous_blowupFluxTest hF.continuous).aestronglyMeasurable]
  change (∫ z, ⟪-(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = _
  simp_rw [inner_neg_left,integral_neg]
  rw [integral_cover_divergence_compl hA hF hs,hflux F hF hs hFO hFn]

lemma coverLocalPerimeter_normal_compl {A O : Set Cover} (hA : MeasurableSet A)
    (hO : MeasurableSet O) {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O}) :
    coverLocalPerimeter Aᶜ O =
      (ν.map reverseBlowupNormal : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [coverLocalPerimeter_compl hA,reverseBlowupNormal_spatial_mass ν hO,heq]

lemma coverLocalPerimeter_compl_minimizing {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O) :
    ∀ D : Set Cover, MeasurableSet D → Aᶜ ∆ D ⊆ K →
      coverLocalPerimeter Aᶜ O ≤ coverLocalPerimeter D O := by
  intro D hD hAD
  rw [coverLocalPerimeter_compl hA]
  have hsub : A ∆ Dᶜ ⊆ K := by
    intro x hx
    apply hAD
    simp only [mem_symmDiff,mem_compl_iff] at hx ⊢
    tauto
  simpa only [coverLocalPerimeter_compl hD] using hmin Dᶜ hD.compl hsub

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma prismSlope_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun x : Cover ↦ (x 2)⁻¹*x 1) volume volume := by
  have hp := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp
    prismColumnCoordinates_measurePreserving.quasiMeasurePreserving
  have hw := planarWedgeCoordinates_quasiMeasurePreserving.comp hp
  have hs := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp hw
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [planarWedgeCoordinates]

lemma mem_negative_radial_halfspace {v : ℝ} {x : Cover} (hx : 0 < x 2) :
    x ∈ coverHalfspace (-radialFaceNormal v) ↔ v < (x 2)⁻¹*x 1 := by
  change ⟪-radialFaceNormal v,x⟫ < 0 ↔ _
  rw [inner_neg_left,inner_radialFaceNormal]
  have hd : 0 < Real.sqrt (1+v^2) := Real.sqrt_pos.mpr (by positivity)
  rw [neg_lt_zero,div_pos_iff_of_pos_right hd,sub_pos,← div_eq_inv_mul,lt_div_iff₀ hx]

lemma mem_radial_halfspace {v : ℝ} {x : Cover} (hx : 0 < x 2) :
    x ∈ coverHalfspace (radialFaceNormal v) ↔ (x 2)⁻¹*x 1 < v := by
  change ⟪radialFaceNormal v,x⟫ < 0 ↔ _
  rw [inner_radialFaceNormal]
  have hd : 0 < Real.sqrt (1+v^2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_lt_iff₀ hd,zero_mul,sub_lt_zero,← div_eq_inv_mul,div_lt_iff₀ hx]

theorem slope_interval_radial_models
    {A : Set Cover} {a c ε l u δ : ℝ} (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hmodel : ∀ᵐ x : Cover ∂volume, x 0 ∈ Ioc a c → x 2 ∈ Ioc 0 ε →
      (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u)) :
    (∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c ε l u → x ∈ A) ∧
    (∀ᵐ x : Cover ∂volume,
      x ∈ strictPatchOpen (radialPatchInequalities a c ε (l-δ) (l+δ)) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l))) ∧
    (∀ᵐ x : Cover ∂volume,
      x ∈ strictPatchOpen (radialPatchInequalities a c ε (u-δ) (u+δ)) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u))) := by
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ l ∧ t ≠ u := by
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ l by rw [ae_iff]; simp,
      show ∀ᵐ t : ℝ ∂volume, t ≠ u by rw [ae_iff]; simp] with t hl hu
    exact ⟨hl,hu⟩
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hmodel,prismSlope_quasiMeasurePreserving.ae hne] with x hm hn hx
    change x 0 ∈ Ioc a c ∧ x 2 ∈ Ioc 0 ε ∧ x 1 ∈ Ioc (x 2*l) (x 2*u) at hx
    have ht : (x 2)⁻¹*x 1 ∈ Ioo l u := by
      rw [← div_eq_inv_mul]
      constructor
      · apply lt_of_le_of_ne ((le_div_iff₀ hx.2.1.1).mpr (by nlinarith [hx.2.2.1]))
        simpa only [div_eq_inv_mul] using hn.1.symm
      · apply lt_of_le_of_ne ((div_le_iff₀ hx.2.1.1).mpr (by nlinarith [hx.2.2.2]))
        simpa only [div_eq_inv_mul] using hn.2
    exact (hm hx.1 hx.2.1 ⟨by linarith [ht.1],by linarith [ht.2]⟩).mpr ht
  · filter_upwards [hmodel] with x hm hx
    obtain ⟨ha,hc,h0,hε,hl,hu⟩ := (mem_radialPatchOpen a c ε (l-δ) (l+δ) x).mp hx
    have htL : l-δ < (x 2)⁻¹*x 1 := by rw [← div_eq_inv_mul,lt_div_iff₀ h0]; exact hl
    have htU : (x 2)⁻¹*x 1 < l+δ := by rw [← div_eq_inv_mul,div_lt_iff₀ h0]; exact hu
    rw [hm ⟨ha,hc.le⟩ ⟨h0,hε.le⟩ ⟨htL,by linarith⟩,mem_negative_radial_halfspace h0]
    exact and_iff_left (by linarith)
  · filter_upwards [hmodel] with x hm hx
    obtain ⟨ha,hc,h0,hε,hl,hu⟩ := (mem_radialPatchOpen a c ε (u-δ) (u+δ) x).mp hx
    have htL : u-δ < (x 2)⁻¹*x 1 := by rw [← div_eq_inv_mul,lt_div_iff₀ h0]; exact hl
    have htU : (x 2)⁻¹*x 1 < u+δ := by rw [← div_eq_inv_mul,div_lt_iff₀ h0]; exact hu
    rw [hm ⟨ha,hc.le⟩ ⟨h0,hε.le⟩ ⟨by linarith,htU⟩,mem_radial_halfspace h0]
    exact and_iff_right (by linarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_norm_le_coordinates (x : Cover) : ‖x‖ ≤ |x 0|+|x 1|+|x 2| := by
  have he : x = (EuclideanSpace.single 0 (x 0) : Cover)+(EuclideanSpace.single 1 (x 1) : Cover)+(EuclideanSpace.single 2 (x 2) : Cover) := by
    ext i
    fin_cases i <;> simp
  calc
    ‖x‖ = ‖(EuclideanSpace.single 0 (x 0) : Cover)+(EuclideanSpace.single 1 (x 1) : Cover)+(EuclideanSpace.single 2 (x 2) : Cover)‖ := congrArg norm he
    _ ≤ ‖(EuclideanSpace.single 0 (x 0) : Cover)‖+‖(EuclideanSpace.single 1 (x 1) : Cover)‖+‖(EuclideanSpace.single 2 (x 2) : Cover)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by simp

lemma radialPatchClosed_coordinate_bounds {h b l u : ℝ} (hb : 0 ≤ b) {x : Cover}
    (hx : x ∈ strictPatchClosed (radialPatchInequalities (-h) h b l u)) :
    |x 0| ≤ h ∧ |x 1| ≤ b*(|l|+|u|) ∧ |x 2| ≤ b := by
  obtain ⟨ha,hc,h0,hb',hl,hu⟩ := (mem_radialPatchClosed (-h) h b l u x).mp hx
  refine ⟨abs_le.mpr ⟨ha,hc⟩,abs_le.mpr ⟨?_,?_⟩,by rwa [abs_of_nonneg h0]⟩
  · have hp := mul_le_mul_of_nonneg_left hb' (abs_nonneg l)
    have hq := mul_le_mul_of_nonneg_right (neg_abs_le l) h0
    have hr := mul_nonneg hb (abs_nonneg u)
    nlinarith
  · have hp := mul_le_mul_of_nonneg_left hb' (abs_nonneg u)
    have hq := mul_le_mul_of_nonneg_right (le_abs_self u) h0
    have hr := mul_nonneg hb (abs_nonneg l)
    nlinarith

lemma radialPatchClosed_norm_le {h b l u : ℝ} (hb : 0 ≤ b) {x : Cover}
    (hx : x ∈ strictPatchClosed (radialPatchInequalities (-h) h b l u)) :
    ‖x‖ ≤ h+b*(|l|+|u|+1) := by
  obtain ⟨h0,h1,h2⟩ := radialPatchClosed_coordinate_bounds hb hx
  have hn := cover_norm_le_coordinates x
  nlinarith

lemma euclideanPrism_subset_radialPatchClosed (a c b l u : ℝ) :
    euclideanPrism a c b l u ⊆ strictPatchClosed (radialPatchInequalities a c b l u) := by
  intro x hx
  change x 0 ∈ Ioc a c ∧ x 2 ∈ Ioc 0 b ∧ x 1 ∈ Ioc (x 2*l) (x 2*u) at hx
  apply (mem_radialPatchClosed a c b l u x).mpr
  exact ⟨hx.1.1.le,hx.1.2,hx.2.1.1.le,hx.2.1.2,by nlinarith [hx.2.2.1],by nlinarith [hx.2.2.2]⟩

lemma radialPatchOpen_subset_closed (a c b l u : ℝ) :
    strictPatchOpen (radialPatchInequalities a c b l u) ⊆
      strictPatchClosed (radialPatchInequalities a c b l u) := by
  intro x hx i
  exact (hx i).le

theorem exists_small_sector_geometry {ρ η b l u δ : ℝ}
    (hρ : 0 < ρ) (hη : 0 < η) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ h ε : ℝ, 0 < h ∧ h < η ∧ 0 < ε ∧ ε < b ∧
      (∀ s t : ℝ, |s|+|t| ≤ 2*(|l|+|u|+δ) →
        strictPatchClosed (radialPatchInequalities (-h) h ε s t) ⊆ Metric.ball (0 : Cover) ρ) ∧
      (∀ x : Cover, x 2 ∈ Ioc 0 ε → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
        ‖planeProductCoordinates.symm (x 2,x 1)‖ < η) := by
  let N : ℝ := ‖planeProductCoordinates.symm.toContinuousLinearMap‖
  let M : ℝ := |l|+|u|+δ+1
  let h : ℝ := min (η/2) (ρ/4)
  let ε : ℝ := min (b/2) (min (ρ/(8*M)) (η/(4*(N+1)*M)))
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 0 ≤ N := norm_nonneg _
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have he : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have heρ : ε ≤ ρ/(8*M) := (min_le_right _ _).trans (min_le_left _ _)
  have heη : ε ≤ η/(4*(N+1)*M) := (min_le_right _ _).trans (min_le_right _ _)
  have heρ' := (le_div_iff₀ (show 0 < 8*M by positivity)).mp heρ
  have heη' := (le_div_iff₀ (show 0 < 4*(N+1)*M by positivity)).mp heη
  refine ⟨h,ε,hh,(min_le_left _ _).trans_lt (by linarith),he,
    (min_le_left _ _).trans_lt (by linarith),?_,?_⟩
  · intro s t hst x hx
    have hn := radialPatchClosed_norm_le he.le hx
    have hcoeff : |s|+|t|+1 ≤ 2*M := by dsimp [M]; linarith
    have hecoeff := mul_le_mul_of_nonneg_left hcoeff he.le
    rw [Metric.mem_ball,dist_zero_right]
    have hhr : h ≤ ρ/4 := min_le_right _ _
    nlinarith
  · intro x hx ht
    have hx0 : 0 < x 2 := hx.1
    have hlo : (l-δ)*x 2 < x 1 := by
      have hh := ht.1
      rw [← div_eq_inv_mul,lt_div_iff₀ hx0] at hh
      exact hh
    have hup : x 1 < (u+δ)*x 2 := by
      have hh := ht.2
      rw [← div_eq_inv_mul,div_lt_iff₀ hx0] at hh
      exact hh
    have hx1 : |x 1| ≤ M*ε := by
      apply abs_le.mpr
      constructor
      · have hs : -M ≤ l-δ := by dsimp [M]; linarith [neg_abs_le l,abs_nonneg u]
        have hs' := mul_le_mul_of_nonneg_right hs hx0.le
        have hm := mul_le_mul_of_nonneg_left hx.2 hM.le
        nlinarith
      · have hs : u+δ ≤ M := by dsimp [M]; linarith [le_abs_self u,abs_nonneg l]
        have hs' := mul_le_mul_of_nonneg_right hs hx0.le
        have hm := mul_le_mul_of_nonneg_left hx.2 hM.le
        nlinarith
    have hx2 : |x 2| ≤ M*ε := by
      rw [abs_of_pos hx0]
      have hM1 : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg l,abs_nonneg u]
      exact hx.2.trans (by nlinarith)
    have hpn : ‖((x 2,x 1) : ℝ × ℝ)‖ ≤ M*ε := by
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
      exact max_le hx2 hx1
    have hp := planeProductCoordinates.symm.toContinuousLinearMap.le_opNorm (x 2,x 1)
    have hmult := mul_le_mul_of_nonneg_left hpn hN
    change ‖planeProductCoordinates.symm (x 2,x 1)‖ ≤ N*‖((x 2,x 1) : ℝ × ℝ)‖ at hp
    have hex := mul_pos hM he
    nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma prismRotatedColumn_measurePreserving (R : Plane ≃ₗᵢ[ℝ] Plane) :
    MeasurePreserving (fun x : Cover ↦ (x 0,R (planeProductCoordinates.symm (x 2,x 1)))) volume volume := by
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod R.measurePreserving
  convert! hp.comp prismColumnCoordinates_measurePreserving using 1
  all_goals try with_reducible_and_instances rfl

lemma prismPlanarProjection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun x : Cover ↦ planeProductCoordinates.symm (x 2,x 1)) volume volume := by
  have hh := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp
    prismColumnCoordinates_measurePreserving.quasiMeasurePreserving
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl

theorem prismFrame_product_model {B : Set Cover} {C : Set Plane} {n : Cover} {η : ℝ}
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∀ᵐ x : Cover ∂volume, |x 0| < η → ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      (x ∈ (prismFrame n R) ⁻¹' B ↔ planeProductCoordinates.symm (x 2,x 1) ∈ R ⁻¹' C) := by
  filter_upwards [(prismRotatedColumn_measurePreserving R).quasiMeasurePreserving.ae hprod]
    with x hx ha hp
  change prismFrame n R x ∈ B ↔ R (planeProductCoordinates.symm (x 2,x 1)) ∈ C
  rw [prismFrame_apply]
  exact hx ha (by simpa only [R.norm_map] using hp)

theorem prismFrame_angular_sector_model
    {B : Set Cover} {C : Set Plane} {n : Cover} {η b l u δ : ℝ}
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hangular : ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      (planarWedgeCoordinates y).2 ∈ Ioo (l-δ) (u+δ) →
      (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ Ioo l u)) :
    ∀ᵐ x : Cover ∂volume, |x 0| < η → ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ (prismFrame n R) ⁻¹' B ↔ (x 2)⁻¹*x 1 ∈ Ioo l u) := by
  filter_upwards [prismFrame_product_model hprod R,
    prismPlanarProjection_quasiMeasurePreserving.ae hangular] with x hp ha hax hpn hr hs
  have he : planarWedgeCoordinates (planeProductCoordinates.symm (x 2,x 1)) =
      (x 2,(x 2)⁻¹*x 1) := by simp [planarWedgeCoordinates]
  simp only [he] at ha
  exact (hp hax hpn).trans (ha hr hs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_eq_trace (F : Cover → Cover) (x : Cover) :
    divergence F x = LinearMap.trace ℝ Cover (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [divergence,Matrix.trace,LinearMap.toMatrix_apply]

lemma divergence_isometry_pullback (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : Differentiable ℝ F) (x : Cover) :
    divergence (fun y ↦ R.symm (F (R y))) x = divergence F (R x) := by
  rw [divergence_eq_trace,divergence_eq_trace]
  have hd := R.symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    ((hF (R x)).hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ R.symm (F (R y))) _ x at hd
  rw [hd.fderiv]
  have he : (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((fderiv ℝ F (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap)).toLinearMap =
      R.symm.toLinearEquiv.conj (fderiv ℝ F (R x)).toLinearMap := rfl
  rw [he,LinearMap.trace_conj']

lemma isometry_pullback_contDiff (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ R.symm (F (R x))) :=
  R.symm.toContinuousLinearEquiv.contDiff.comp (hF.comp R.toContinuousLinearEquiv.contDiff)

lemma isometry_pullback_compactSupport (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hs : HasCompactSupport F) : HasCompactSupport (fun x ↦ R.symm (F (R x))) :=
  (hs.comp_isClosedEmbedding R.toHomeomorph.isClosedEmbedding).comp_left (map_zero R.symm)

lemma isometry_pullback_tsupport (R : Cover ≃ₗᵢ[ℝ] Cover) (F : Cover → Cover) :
    tsupport (fun x ↦ R.symm (F (R x))) = R ⁻¹' tsupport F := by
  have h0 : Function.support (fun x ↦ R.symm (F (R x))) = R ⁻¹' Function.support F := by
    ext x
    change (R.symm (F (R x)) ≠ 0) ↔ (F (R x) ≠ 0)
    have he : (R.symm (F (R x)) = 0) ↔ (F (R x) = 0) := by
      constructor
      · intro hh
        simpa only [R.apply_symm_apply,map_zero] using congrArg R hh
      · intro hh
        rw [hh,map_zero]
    exact not_congr he
  change closure (Function.support (fun x ↦ R.symm (F (R x)))) = R ⁻¹' closure (Function.support F)
  rw [h0]
  exact (R.toHomeomorph.preimage_closure _).symm

lemma setIntegral_divergence_isometry_preimage (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A : Set Cover} (hA : MeasurableSet A) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in R ⁻¹' A, divergence (fun y ↦ R.symm (F (R y))) x) =
      ∫ x in A, divergence F x := by
  simp_rw [divergence_isometry_pullback R (hF.differentiable (by simp))]
  exact (R.measurePreserving.restrict_preimage hA).integral_comp R.toHomeomorph.measurableEmbedding _

theorem coverLocalPerimeter_isometry_preimage (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A : Set Cover} (hA : MeasurableSet A) (O : Set Cover) :
    coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) = coverLocalPerimeter A O := by
  have hle (R : Cover ≃ₗᵢ[ℝ] Cover) {A : Set Cover} (hA : MeasurableSet A) (O : Set Cover) :
      coverLocalPerimeter A O ≤ coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hn
    let G : Cover → Cover := fun x ↦ R.symm (F (R x))
    have hG := isometry_pullback_contDiff R hF
    have hsG := isometry_pullback_compactSupport R hs
    have hOG : tsupport G ⊆ R ⁻¹' O := by
      rw [isometry_pullback_tsupport R F]
      exact preimage_mono hO
    have hnG (x) : ‖G x‖ ≤ 1 := by
      rw [R.symm.norm_map]; exact hn _
    have he := setIntegral_divergence_isometry_preimage R hA hF
    rw [← he]
    exact le_iSup_of_le G (le_iSup_of_le hG (le_iSup_of_le hsG
      (le_iSup_of_le hOG (le_iSup_of_le hnG le_rfl))))
  refine le_antisymm ?_ (hle R hA O)
  have hh := hle R.symm (hA.preimage R.continuous.measurable) (R ⁻¹' O)
  simpa only [preimage_preimage,R.apply_symm_apply,preimage_id'] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupRigidCovariance
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma continuous_pullbackBlowupNormal (R : Cover ≃ₗᵢ[ℝ] Cover) :
    Continuous (pullbackBlowupNormal R) :=
  (R.symm.continuous.comp continuous_fst).prodMk
    ((R.symm.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)

lemma pullbackBlowupNormal_spatial_mass (R : Cover ≃ₗᵢ[ℝ] Cover)
    (ν : FiniteMeasure BlowupNormalBundle) {O : Set Cover} (hO : MeasurableSet O) :
    (ν.map (pullbackBlowupNormal R) : Measure BlowupNormalBundle) {z | z.1 ∈ R ⁻¹' O} =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [FiniteMeasure.toMeasure_map,Measure.map_apply (continuous_pullbackBlowupNormal R).measurable
    (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ R ⁻¹' O} from
      (hO.preimage R.continuous.measurable).preimage measurable_fst)]
  congr 1
  ext z
  change R (R.symm z.1) ∈ O ↔ z.1 ∈ O
  rw [R.apply_symm_apply]

lemma pullbackBlowupNormal_flux (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A O : Set Cover} (hA : MeasurableSet A) {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hFO : tsupport F ⊆ R ⁻¹' O) (hFn : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν.map (pullbackBlowupNormal R) : Measure BlowupNormalBundle)) =
      ∫ x in R ⁻¹' A, divergence F x := by
  let G : Cover → Cover := fun x ↦ R (F (R.symm x))
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := isometry_pullback_contDiff R.symm hF
  have hsG : HasCompactSupport G := isometry_pullback_compactSupport R.symm hs
  have hGO : tsupport G ⊆ O := by
    change tsupport (fun x ↦ R.symm.symm (F (R.symm x))) ⊆ O
    rw [isometry_pullback_tsupport R.symm F]
    intro x hx
    simpa only [Set.mem_preimage,R.apply_symm_apply] using hFO hx
  have hGn (x) : ‖G x‖ ≤ 1 := by simpa only [G,R.norm_map] using hFn (R.symm x)
  rw [FiniteMeasure.toMeasure_map,integral_map (continuous_pullbackBlowupNormal R).measurable.aemeasurable
    (continuous_blowupFluxTest hF.continuous).aestronglyMeasurable]
  have hh (z : BlowupNormalBundle) :
      ⟪((pullbackBlowupNormal R z).2 : Cover),F (pullbackBlowupNormal R z).1⟫ =
        ⟪(z.2 : Cover),G z.1⟫ := by
    change ⟪R.symm (z.2 : Cover),F (R.symm z.1)⟫ = ⟪(z.2 : Cover),R (F (R.symm z.1))⟫
    simpa only [R.apply_symm_apply] using
      (R.inner_map_map (R.symm (z.2 : Cover)) (F (R.symm z.1))).symm
  simp_rw [hh]
  rw [hflux G hG hsG hGO hGn]
  have he := setIntegral_divergence_isometry_preimage R hA hG
  have hGF : (fun y ↦ R.symm (G (R y))) = F := by
    ext y
    simp only [G,R.symm_apply_apply]
  rw [hGF] at he
  exact he.symm

lemma coverLocalPerimeter_isometry_normal (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A O : Set Cover} (hA : MeasurableSet A) (hO : MeasurableSet O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O}) :
    coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) =
      (ν.map (pullbackBlowupNormal R) : Measure BlowupNormalBundle) {z | z.1 ∈ R ⁻¹' O} := by
  rw [coverLocalPerimeter_isometry_preimage R hA,pullbackBlowupNormal_spatial_mass R ν hO,heq]

lemma coverLocalPerimeter_isometry_minimizing (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O) :
    ∀ D : Set Cover, MeasurableSet D → (R ⁻¹' A) ∆ D ⊆ R ⁻¹' K →
      coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) ≤ coverLocalPerimeter D (R ⁻¹' O) := by
  intro D hD hAD
  have hD' : MeasurableSet (R.symm ⁻¹' D) := hD.preimage R.symm.continuous.measurable
  have hsub : A ∆ (R.symm ⁻¹' D) ⊆ K := by
    intro x hx
    have hh := hAD (show R.symm x ∈ (R ⁻¹' A) ∆ D from by
      simpa only [mem_symmDiff,Set.mem_preimage,R.apply_symm_apply] using hx)
    simpa only [Set.mem_preimage,R.apply_symm_apply] using hh
  have he : R ⁻¹' (R.symm ⁻¹' D) = D := by ext x; simp only [Set.mem_preimage,R.symm_apply_apply]
  rw [coverLocalPerimeter_isometry_preimage R hA]
  have hc := coverLocalPerimeter_isometry_preimage R hD' O
  rw [he] at hc
  exact (hmin _ hD' hsub).trans_eq hc.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem no_minimizing_angular_sector {A O K : Set Cover} (hA : MeasurableSet A)
    {ρ η b l u δ : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hb : 0 < b)
    (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hKO : Metric.ball (0 : Cover) ρ ⊆ K) (hOO : Metric.ball (0 : Cover) ρ ⊆ O)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hmodel : ∀ᵐ x : Cover ∂volume, |x 0| < η →
      ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  obtain ⟨h,ε,hh,hhη,hε,hεb,hsmall,hplane⟩ := exists_small_sector_geometry hρ hη hb hδ (l := l) (u := u)
  have hmod : ∀ᵐ x : Cover ∂volume, x 0 ∈ Ioc (-h) h → x 2 ∈ Ioc 0 ε →
      (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u) := by
    filter_upwards [hmodel] with x hx hax hr hs
    apply hx (abs_lt.mpr ⟨by linarith [hax.1],hax.2.trans_lt hhη⟩)
      (hplane x hr hs) ⟨hr.1,hr.2.trans_lt hεb⟩ hs
  obtain ⟨hPA,hflatL,hflatU⟩ := slope_interval_radial_models hδ hgap hmod
  have habs {v : ℝ} : |v-δ|+|v+δ| ≤ 2*(|v|+δ) := by
    have h1 := abs_sub v δ
    have h2 := abs_add_le v δ
    rw [abs_of_pos hδ] at h1 h2
    linarith
  apply no_minimizing_small_radial_sector (a := -h) (c := h) (ε := ε)
    (l := l) (u := u) (l₀ := l-δ) (l₁ := l+δ) (u₀ := u-δ) (u₁ := u+δ)
    (by linarith) hε (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hA hmin ?_ hPA hflatL hflatU ?_ ?_ heq hflux
  · exact (euclideanPrism_subset_radialPatchClosed (-h) h ε l u).trans
      ((hsmall l u (by linarith [abs_nonneg l,abs_nonneg u])).trans hKO)
  · exact (radialPatchOpen_subset_closed (-h) h ε (l-δ) (l+δ)).trans
      ((hsmall _ _ (by linarith [habs (v := l),abs_nonneg u])).trans hOO)
  · exact (radialPatchOpen_subset_closed (-h) h ε (u-δ) (u+δ)).trans
      ((hsmall _ _ (by linarith [habs (v := u),abs_nonneg l])).trans hOO)

theorem no_minimizing_angular_phase_sector {A O K : Set Cover} (hA : MeasurableSet A)
    (hO : MeasurableSet O)
    {ρ η b l u δ : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hb : 0 < b)
    (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hKO : Metric.ball (0 : Cover) ρ ⊆ K) (hOO : Metric.ball (0 : Cover) ρ ⊆ O)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hmodel : (∀ᵐ x : Cover ∂volume, |x 0| < η →
      ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u)) ∨
      (∀ᵐ x : Cover ∂volume, |x 0| < η →
      ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ Aᶜ ↔ (x 2)⁻¹*x 1 ∈ Ioo l u)))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  rcases hmodel with hm|hm
  · exact no_minimizing_angular_sector hA hρ hη hb hδ hgap hKO hOO hmin hm heq hflux
  · exact no_minimizing_angular_sector hA.compl hρ hη hb hδ hgap hKO hOO
      (coverLocalPerimeter_compl_minimizing hA hmin) hm
      (coverLocalPerimeter_normal_compl hA hO heq)
      (fun F hF hs hFO hFn ↦ reverseBlowupNormal_flux hA hflux hF hs hFO hFn)

theorem no_moving_product_angular_sector
    {B : Set Cover} {C : Set Plane} {n : Cover} {η b l u δ : ℝ}
    (hB : MeasurableSet B) (hη : 0 < η) (hb : 0 < b) (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hangular : (∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      (planarWedgeCoordinates y).2 ∈ Ioo (l-δ) (u+δ) →
      (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ Ioo l u)) ∨
      (∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      (planarWedgeCoordinates y).2 ∈ Ioo (l-δ) (u+δ) →
      (y ∈ R ⁻¹' Cᶜ ↔ (planarWedgeCoordinates y).2 ∈ Ioo l u)))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x) : False := by
  obtain ⟨r,hρr,hr1,hr⟩ := exists_normal_sphere_null_radius ν (show (1/2 : ℝ) < 1 by norm_num)
  have hr0 : 0 < r := by linarith
  have hpr := heq r hr0 hr1.le
  have hclosed := coverLocalPerimeter_closedBall_eq_ball_of_normal hr1.le hr hpr hflux
  have hmass : coverLocalPerimeter B (Metric.closedBall (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.closedBall (0 : Cover) r} := by
    rw [hclosed,hpr,measure_congr (normal_closedBall_ae_eq_ball hr)]
  let Q := prismFrame n R
  have hQO : Q ⁻¹' Metric.closedBall (0 : Cover) r = Metric.closedBall (0 : Cover) r := by
    rw [Q.preimage_closedBall,map_zero]
  have hQK : Q ⁻¹' Metric.ball (0 : Cover) (1/2) = Metric.ball (0 : Cover) (1/2) := by
    rw [Q.preimage_ball,map_zero]
  have hmin' := coverLocalPerimeter_isometry_minimizing Q hB
    (normal_radius_local_minimizing (by norm_num : (0 : ℝ) < 1/2) hρr hr1.le hr hpr hflux hmin)
  have hmass' := coverLocalPerimeter_isometry_normal Q hB Metric.isClosed_closedBall.measurableSet hmass
  have hflux' : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ Q ⁻¹' Metric.closedBall (0 : Cover) r → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν.map (pullbackBlowupNormal Q) : Measure BlowupNormalBundle)) =
        ∫ x in Q ⁻¹' B, divergence F x := by
    intro F hF hs hFO hFn
    exact pullbackBlowupNormal_flux Q hB
      (fun G hG _ hGO _ ↦ hflux G hG (hGO.trans (Metric.closedBall_subset_closedBall hr1.le)))
      hF hs hFO hFn
  apply no_minimizing_angular_phase_sector (hB.preimage Q.continuous.measurable)
    (Metric.isClosed_closedBall.measurableSet.preimage Q.continuous.measurable)
    (by norm_num : (0 : ℝ) < 1/2) hη hb hδ hgap
    (by rw [hQK]) (by rw [hQO]; exact (Metric.ball_subset_ball hρr.le).trans Metric.ball_subset_closedBall)
    hmin' ?_ hmass' hflux'
  rcases hangular with hm|hm
  · exact Or.inl (prismFrame_angular_sector_model hprod R hm)
  · apply Or.inr
    apply prismFrame_angular_sector_model (B := Bᶜ) (C := Cᶜ) (n := n) (η := η) ?_ R hm
    filter_upwards [hprod] with z hz hza hzp
    exact not_congr (hz hza hzp)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
lemma slopeScalarTest_tsupport_rectangle_wide {χ ψ : ℝ → ℝ} {a b w : ℝ}
    (ha : 0 < a) (hw : 0 ≤ w) (hχ : tsupport χ ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-w) w) :
    tsupport (slopeScalarTest χ ψ) ⊆
      planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-(w*b)) (w*b)) := by
  apply closure_minimal _ ((isClosed_Icc.prod isClosed_Icc).preimage
    planeProductCoordinates.continuous)
  intro x hx
  have hn : χ (planeProductCoordinates x).1 ≠ 0 ∧
      ψ ((planeProductCoordinates x).2/(planeProductCoordinates x).1) ≠ 0 :=
    mul_ne_zero_iff.mp hx
  have hs := hχ (subset_tsupport _ hn.1)
  have ht := hψ (subset_tsupport _ hn.2)
  have hs0 : 0 < (planeProductCoordinates x).1 := ha.trans_le hs.1
  have ht' : |(planeProductCoordinates x).2/(planeProductCoordinates x).1| ≤ w := abs_le.mpr ht
  rw [abs_div,abs_of_pos hs0,div_le_iff₀ hs0] at ht'
  exact ⟨hs,abs_le.mp (ht'.trans (mul_le_mul_of_nonneg_left hs.2 hw))⟩

lemma slopeScalarTest_hasCompactSupport_wide {χ ψ : ℝ → ℝ} {a b w : ℝ}
    (ha : 0 < a) (hw : 0 ≤ w) (hχ : tsupport χ ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-w) w) : HasCompactSupport (slopeScalarTest χ ψ) :=
  (planeProductCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset isClosed_closure
      (slopeScalarTest_tsupport_rectangle_wide ha hw hχ hψ)

theorem planar_slope_flux_wide {C : Set Plane} {D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) {a b w : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (hprod : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D))
    {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsχ : tsupport χ ⊆ Ioo a b) (hsψ : tsupport ψ ⊆ Ioo (-w) w) :
    (∫ x in C, fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector) =
      (∫ s : ℝ, χ s)*(∫ t in D, deriv ψ t) := by
  have hχ0 : 0 ∉ tsupport χ := fun hh ↦ (ha.trans (hsχ hh).1).false
  have hf := slopeScalarTest_contDiff hχ hψ hχ0
  have hfs := slopeScalarTest_hasCompactSupport_wide ha hw
    (hsχ.trans Ioo_subset_Icc_self) (hsψ.trans Ioo_subset_Icc_self)
  let G : Plane → ℝ := C.indicator
    (fun x ↦ fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector)
  have hi : Integrable G volume :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfs.fderiv_apply ℝ slopeVerticalVector)).indicator hC
  have hL : MeasurePreserving planeProductCoordinates.symm :=
    planeProductCoordinates_measurePreserving.symm
      planeProductCoordinates.toHomeomorph.toMeasurableEquiv
  have hLi := (hL.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hsplit := Measure.ae_ae_of_ae_prod hprod
  have he : (fun s : ℝ ↦ ∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =ᵐ[volume]
      (fun s : ℝ ↦ χ s*(∫ t in D, deriv ψ t)) := by
    filter_upwards [hsplit] with s hs
    by_cases hsI : s ∈ Ioo a b
    · have hs0 : 0 < s := ha.trans hsI.1
      have hscale : (∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =
          s*(∫ t : ℝ, G (planarWedgeChart (s,t))) := by
        change (∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =
          s*(∫ t : ℝ, G (planeProductCoordinates.symm (s,s*t)))
        rw [Measure.integral_comp_mul_left (fun y : ℝ ↦ G (planeProductCoordinates.symm (s,y))) s,
          abs_of_pos (inv_pos.mpr hs0),smul_eq_mul]
        rw [mul_inv_cancel_left₀ hs0.ne']
      rw [hscale]
      have hinner : (fun t : ℝ ↦ G (planarWedgeChart (s,t))) =ᵐ[volume]
          (fun t : ℝ ↦ (χ s/s)*D.indicator (deriv ψ) t) := by
        filter_upwards [hs] with t ht
        have hd : fderiv ℝ (slopeScalarTest χ ψ) (planarWedgeChart (s,t))
            slopeVerticalVector = (χ s/s)*deriv ψ t := by
          rw [slopeScalarTest_vertical_derivative hχ hψ hχ0]
          simp [planarWedgeChart,mul_div_cancel_left₀ _ hs0.ne']
        by_cases htI : t ∈ Ioo (-w) w
        · by_cases htD : t ∈ D
          · simp only [G,indicator_of_mem ((ht hsI htI).mpr htD),indicator_of_mem htD,hd]
          · simp only [G,indicator_of_notMem htD,mul_zero,
              indicator_of_notMem (mt (ht hsI htI).mp htD)]
        · have hz : deriv ψ t = 0 := deriv_of_notMem_tsupport (fun hh ↦ htI (hsψ hh))
          simp only [hz,mul_zero] at hd
          by_cases htD : t ∈ D <;> by_cases htC : planarWedgeChart (s,t) ∈ C <;>
            simp [G,htD,htC,hd,hz]
      rw [integral_congr_ae hinner,integral_const_mul,integral_indicator hD]
      field_simp
    · have hz : χ s = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hsI (hsχ hh))
      rw [hz,zero_mul]
      apply integral_eq_zero_of_ae
      apply ae_of_all
      intro y
      have hd : fderiv ℝ (slopeScalarTest χ ψ) (planeProductCoordinates.symm (s,y))
          slopeVerticalVector = 0 := by
        rw [slopeScalarTest_vertical_derivative hχ hψ hχ0]
        simp [hz]
      by_cases hy : planeProductCoordinates.symm (s,y) ∈ C <;> simp [G,hy,hd]
  rw [← integral_indicator hC]
  change (∫ x : Plane, G x) = _
  rw [← hL.integral_comp planeProductCoordinates.symm.toHomeomorph.measurableEmbedding G]
  rw [Measure.volume_eq_prod] at hLi ⊢
  change Integrable (fun z : ℝ × ℝ ↦ G (planeProductCoordinates.symm z)) (volume.prod volume) at hLi
  rw [integral_prod _ hLi,integral_congr_ae he,integral_mul_const]

theorem planar_cone_slope_section_wide {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {a b w : ℝ} (ha : 0 < a) (hab : a < b)
    (hchart : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo (-w) w,
      planarWedgeChart (s,t) ∈ Metric.ball (0 : Plane) (1/16)) :
    ∃ D : Set ℝ, MeasurableSet D ∧ ∀ᵐ z : ℝ × ℝ ∂volume,
      z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D) := by
  have hwm : Measurable planarWedgeChart := planarWedgeChart_quasiMeasurePreserving.measurable
  have hm : MeasurableSet {z : Plane × ℝ | 0 < z.2 →
      z.1 ∈ Metric.ball (0 : Plane) (1/16) →
      z.2 • z.1 ∈ Metric.ball (0 : Plane) (1/16) →
      (z.2 • z.1 ∈ C ↔ z.1 ∈ C)} :=
    (measurableSet_lt measurable_const measurable_snd).imp
      ((Metric.isOpen_ball.measurableSet.preimage measurable_fst).imp
        ((Metric.isOpen_ball.measurableSet.preimage (measurable_snd.smul measurable_fst)).imp
          ((hC.preimage (measurable_snd.smul measurable_fst)).iff
            (hC.preimage measurable_fst))))
  have hx : ∀ᵐ y : Plane ∂volume, ∀ᵐ c : ℝ ∂volume,
      0 < c → y ∈ Metric.ball (0 : Plane) (1/16) →
      c • y ∈ Metric.ball (0 : Plane) (1/16) → (c • y ∈ C ↔ y ∈ C) := by
    apply (Measure.ae_ae_comm hm).mpr
    apply ae_of_all
    intro c
    by_cases hc0 : 0 < c
    · exact (planar_cone_all_positive_scales hc hc0).mono (fun _ h _ ↦ h)
    · exact ae_of_all _ (fun _ h ↦ (hc0 h).elim)
  have hsplit := Measure.ae_ae_of_ae_prod (planarWedgeChart_quasiMeasurePreserving.ae hx)
  have hrel : ∀ᵐ s : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume, ∀ᵐ r : ℝ ∂volume,
      s ∈ Ioo a b → r ∈ Ioo a b → t ∈ Ioo (-w) w →
      (planarWedgeChart (r,t) ∈ C ↔ planarWedgeChart (s,t) ∈ C) := by
    filter_upwards [hsplit] with s hs
    filter_upwards [hs] with t ht
    by_cases hsI : s ∈ Ioo a b
    · have hs0 : 0 < s := ha.trans hsI.1
      have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
        (inv_ne_zero hs0.ne')
      filter_upwards [hq.ae ht] with r hr _ hrI htI
      simp only [smul_eq_mul] at hr
      have hcp : 0 < s⁻¹*r := mul_pos (inv_pos.mpr hs0) (ha.trans hrI.1)
      have he : (s⁻¹*r) • planarWedgeChart (s,t) = planarWedgeChart (r,t) := by
        rw [planarWedgeChart_smul]
        congr 1
        field_simp
      have hh := hr hcp (hchart s hsI t htI)
      rw [he] at hh
      exact hh (hchart r hrI t htI)
    · exact ae_of_all _ (fun _ hs' ↦ (hsI hs').elim)
  have hpos : (volume : Measure ℝ) (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  obtain ⟨s,hsI,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae hrel)
  let D : Set ℝ := {t | planarWedgeChart (s,t) ∈ C}
  have hD : MeasurableSet D := hC.preimage (hwm.comp (measurable_const.prodMk measurable_id))
  refine ⟨D,hD,?_⟩
  have hm' : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Ioo a b → z.1 ∈ Ioo (-w) w →
      (planarWedgeChart (z.2,z.1) ∈ C ↔ z.1 ∈ D)} :=
    (measurableSet_Ioo.preimage measurable_snd).imp
      ((measurableSet_Ioo.preimage measurable_fst).imp
        ((hC.preimage (hwm.comp measurable_swap)).iff (hD.preimage measurable_fst)))
  apply (Measure.ae_prod_iff_ae_ae (hm'.preimage measurable_swap)).mpr
  apply (Measure.ae_ae_comm hm').mp
  filter_upwards [hs] with t ht
  filter_upwards [ht] with r hr hrI htI
  exact hr hsI hrI htI

theorem planar_slope_directional_bound_wide {C : Set Plane} {D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) {a b w : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (hprod : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D))
    (hrect : planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-(w*b)) (w*b)) ⊆
      Metric.closedBall (0 : Plane) (1/32))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hsχ : tsupport χ ⊆ Ioo a b) (hbχ : ∀ t, |χ t| ≤ 1)
    (hJ : 0 < ∫ t : ℝ, χ t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) →
      |∫ t in D, deriv ψ t| ≤ L := by
  refine ⟨K/(∫ t : ℝ, χ t),div_nonneg hK hJ.le,?_⟩
  intro ψ hψ hsψ hbψ
  have hχ0 : 0 ∉ tsupport χ := fun hh ↦ (ha.trans (hsχ hh).1).false
  have hh := hbv (slopeScalarTest χ ψ) (slopeScalarTest_contDiff hχ hψ hχ0)
    ((slopeScalarTest_tsupport_rectangle_wide ha hw (hsχ.trans Ioo_subset_Icc_self)
      (hsψ.trans Ioo_subset_Icc_self)).trans hrect)
    (slopeScalarTest_bound hbχ hbψ) slopeVerticalVector slopeVerticalVector_norm
  rw [planar_slope_flux_wide hC hD ha hw hprod hχ hψ hsχ hsψ,abs_mul,abs_of_pos hJ] at hh
  exact (le_div_iff₀ hJ).mpr (by simpa only [mul_comm] using hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slope_rectangle_ball_wide {a b w : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (hb : ‖planeProductCoordinates.symm.toContinuousLinearMap‖*((w+1)*b) ≤ (1/32 : ℝ)) :
    planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-(w*b)) (w*b)) ⊆
      Metric.closedBall (0 : Plane) (1/32) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  have hb0 : 0 ≤ b := (ha.trans_le hx.1.1).le.trans hx.1.2
  have hnorm : ‖planeProductCoordinates x‖ ≤ (w+1)*b := by
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs,abs_of_pos (ha.trans_le hx.1.1)]
      exact hx.1.2.trans (by nlinarith)
    · rw [Real.norm_eq_abs]
      exact (abs_le.mpr hx.2).trans (by nlinarith)
  calc
    ‖x‖ = ‖planeProductCoordinates.symm (planeProductCoordinates x)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖planeProductCoordinates.symm.toContinuousLinearMap‖*‖planeProductCoordinates x‖ :=
      planeProductCoordinates.symm.toContinuousLinearMap.le_opNorm (planeProductCoordinates x)
    _ ≤ ‖planeProductCoordinates.symm.toContinuousLinearMap‖*((w+1)*b) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ _ := hb

theorem planar_cone_angular_dual_bv_wide {C : Set Plane} (hC : MeasurableSet C)
    {w : ℝ} (hw : 0 ≤ w)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K) :
    ∃ (a b L : ℝ) (D : Set ℝ), 0 < a ∧ a < b ∧
      ‖planeProductCoordinates.symm.toContinuousLinearMap‖*((w+1)*b) ≤ (1/32 : ℝ) ∧ 0 ≤ L ∧ MeasurableSet D ∧
      (∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
        (planarWedgeChart z ∈ C ↔ z.2 ∈ D)) ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) →
        |∫ t in D, deriv ψ t| ≤ L := by
  let N : ℝ := ‖planeProductCoordinates.symm.toContinuousLinearMap‖
  let b : ℝ := 1/(128*(N+1)*(w+1))
  have hN : 0 ≤ N := norm_nonneg _
  have hb : 0 < b := by dsimp [b]; positivity
  have hNb : N*((w+1)*b) ≤ 1/32 := by
    dsimp [b]
    rw [mul_one_div,← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hN hw]
  have ha : 0 < b/4 := div_pos hb (by norm_num)
  have hab : b/4 < b := by linarith
  have hrect := slope_rectangle_ball_wide ha hw hNb
  have hchart (s : ℝ) (hs : s ∈ Ioo (b/4) b) (t : ℝ) (ht : t ∈ Ioo (-w) w) :
      planarWedgeChart (s,t) ∈ Metric.ball (0 : Plane) (1/16) := by
    apply (Metric.closedBall_subset_ball (by norm_num : (1/32 : ℝ)<1/16))
    apply hrect
    change (planeProductCoordinates (planeProductCoordinates.symm (s,s*t))).1 ∈ Icc (b/4) b ∧
      (planeProductCoordinates (planeProductCoordinates.symm (s,s*t))).2 ∈ Icc (-(w*b)) (w*b)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    constructor
    · exact ⟨hs.1.le,hs.2.le⟩
    · have hs0 : 0 < s := ha.trans hs.1
      have hst : |s*t| ≤ w*b := by
        rw [abs_mul,abs_of_pos hs0]
        calc
          s*|t| ≤ s*w := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1.le,ht.2.le⟩) hs0.le
          _ ≤ w*b := by nlinarith [mul_le_mul_of_nonneg_left hs.2.le hw]
      exact abs_le.mp hst
  obtain ⟨D,hD,hprod⟩ := planar_cone_slope_section_wide hC hc ha hab hchart
  let χ : ContDiffBump (b/2) := {
    rIn := b/16
    rOut := b/8
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hsχ : tsupport (χ : ℝ → ℝ) ⊆ Ioo (b/4) b := by
    rw [χ.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    change b/2-b/8 ≤ t ∧ t ≤ b/2+b/8 at ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨L,hL,hdual⟩ := planar_slope_directional_bound_wide hC hD ha hw hprod hrect hK hbv
    χ.contDiff hsχ (fun t ↦ by rw [abs_of_nonneg χ.nonneg]; exact χ.le_one) χ.integral_pos
  exact ⟨b/4,b,L,D,ha,hab,hNb,hL,hD,hprod,hdual⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma scaled_test_deriv {w : ℝ} (hw : 0 < w) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (t : ℝ) :
    deriv (fun s ↦ ψ (w⁻¹*s)) (w*t) = w⁻¹*deriv ψ t := by
  have hd := ((hψ.differentiable (by simp)) (w⁻¹*(w*t))).hasDerivAt.comp (w*t)
    ((hasDerivAt_id (w*t)).const_mul w⁻¹)
  simpa only [Function.comp_def,id_eq,mul_one,inv_mul_cancel_left₀ hw.ne',mul_comm] using hd.deriv

lemma scaled_setIntegral_deriv {D : Set ℝ} (hD : MeasurableSet D)
    {w : ℝ} (hw : 0 < w) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∫ t in (fun s : ℝ ↦ w*s) ⁻¹' D, deriv ψ t) =
      ∫ t in D, deriv (fun s ↦ ψ (w⁻¹*s)) t := by
  let φ : ℝ → ℝ := fun s ↦ ψ (w⁻¹*s)
  let g := D.indicator (deriv φ)
  have he (t : ℝ) : g (w*t) = w⁻¹*((fun s : ℝ ↦ w*s) ⁻¹' D).indicator (deriv ψ) t := by
    by_cases ht : w*t ∈ D
    · simp only [g,indicator_of_mem ht,scaled_test_deriv hw hψ,φ,
        indicator_of_mem (show t ∈ (fun s : ℝ ↦ w*s) ⁻¹' D from ht)]
    · simp only [g,indicator_of_notMem ht,
        indicator_of_notMem (show t ∉ (fun s : ℝ ↦ w*s) ⁻¹' D from ht),mul_zero]
  have hm : Measurable (fun t : ℝ ↦ w*t) := measurable_const.mul measurable_id
  have hi := Measure.integral_comp_mul_left g w
  simp_rw [he] at hi
  rw [integral_const_mul,integral_indicator (hD.preimage hm),
    abs_of_pos (inv_pos.mpr hw),smul_eq_mul] at hi
  have hc := mul_left_cancel₀ (inv_ne_zero hw.ne') hi
  simpa only [g,integral_indicator hD] using hc

lemma angular_dual_bv_rescale {D : Set ℝ} (hD : MeasurableSet D)
    {w L : ℝ} (hw : 0 < w)
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) → |∫ t in D, deriv ψ t| ≤ L) :
    ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t in (fun s : ℝ ↦ w*s) ⁻¹' D, deriv ψ t| ≤ L := by
  intro ψ hψ hsψ hbψ
  rw [scaled_setIntegral_deriv hD hw hψ]
  apply hdual
  · exact hψ.comp (contDiff_const.mul contDiff_id)
  · change tsupport (ψ ∘ (Homeomorph.mulLeft₀ w⁻¹ (inv_ne_zero hw.ne'))) ⊆ Ioo (-w) w
    rw [tsupport_comp_eq_preimage]
    intro t ht
    have hh := hsψ ht
    change -1 < w⁻¹*t ∧ w⁻¹*t < 1 at hh
    rw [← div_eq_inv_mul] at hh
    constructor
    · have h := (lt_div_iff₀ hw).mp hh.1
      nlinarith
    · have h := (div_lt_iff₀ hw).mp hh.2
      nlinarith
  · exact fun t ↦ hbψ _

lemma volume_positive_mul_preimage {w : ℝ} (hw : 0 < w) (D : Set ℝ) :
    0 < volume ((fun t : ℝ ↦ w*t) ⁻¹' D) ↔ 0 < volume D := by
  rw [Real.volume_preimage_mul_left hw.ne']
  have hc : 0 < ENNReal.ofReal |w⁻¹| := ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hw.ne'))
  constructor
  · intro hh
    by_contra h
    rw [le_antisymm (not_lt.mp h) (zero_le),mul_zero] at hh
    exact hh.false
  · intro hh
    exact ENNReal.mul_pos hc.ne' hh.ne'

lemma mul_preimage_phase_ball {w : ℝ} (hw : 0 < w) (D : Set ℝ) (x δ : ℝ) :
    (fun t : ℝ ↦ w*t) ⁻¹' (D ∩ Metric.ball (w*x) (w*δ)) =
      ((fun t : ℝ ↦ w*t) ⁻¹' D) ∩ Metric.ball x δ := by
  ext t
  simp only [Set.mem_preimage,Set.mem_inter_iff,Metric.mem_ball,Real.dist_eq,
    ← mul_sub,abs_mul,abs_of_pos hw,mul_lt_mul_iff_right₀ hw]

lemma angularEssentialBoundary_mul_preimage {w : ℝ} (hw : 0 < w) (D : Set ℝ) :
    angularEssentialBoundary ((fun t : ℝ ↦ w*t) ⁻¹' D) =
      (fun t : ℝ ↦ w*t) ⁻¹' angularEssentialBoundary D := by
  ext x
  constructor
  · intro hx δ hδ
    have h := hx (δ/w) (div_pos hδ hw)
    have he : w*(δ/w) = δ := by field_simp
    have hscale (S : Set ℝ) :
        0 < volume (((fun t : ℝ ↦ w*t) ⁻¹' S) ∩ Metric.ball x (δ/w)) ↔
          0 < volume (S ∩ Metric.ball (w*x) δ) := by
      rw [← mul_preimage_phase_ball hw,he,volume_positive_mul_preimage hw]
    exact ⟨(hscale D).mp h.1,(hscale Dᶜ).mp h.2⟩
  · intro hx δ hδ
    have h := hx (w*δ) (mul_pos hw hδ)
    have hscale (S : Set ℝ) :
        0 < volume (((fun t : ℝ ↦ w*t) ⁻¹' S) ∩ Metric.ball x δ) ↔
          0 < volume (S ∩ Metric.ball (w*x) (w*δ)) := by
      rw [← mul_preimage_phase_ball hw,volume_positive_mul_preimage hw]
    exact ⟨(hscale D).mpr h.1,(hscale Dᶜ).mpr h.2⟩

theorem angular_dual_bv_finite_transitions_wide {D : Set ℝ} (hD : MeasurableSet D)
    {w L : ℝ} (hw : 0 < w)
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) → |∫ t in D, deriv ψ t| ≤ L) :
    (Icc (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Finite := by
  have hm : Measurable (fun t : ℝ ↦ w*t) := measurable_const.mul measurable_id
  have hfin := angular_dual_bv_finite_transitions
    (hD.preimage hm) (angular_dual_bv_rescale hD hw hdual)
  have him := hfin.image (fun t : ℝ ↦ w*t)
  apply him.subset
  intro x hx
  refine ⟨x/w,⟨?_,?_⟩,?_⟩
  · constructor
    · apply (le_div_iff₀ hw).mpr
      nlinarith [hx.1.1]
    · apply (div_le_iff₀ hw).mpr
      nlinarith [hx.1.2]
  · rw [angularEssentialBoundary_mul_preimage hw]
    simpa only [Set.mem_preimage,mul_div_cancel₀ _ hw.ne'] using hx.2
  · field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma planarWedgeCoordinates_smul {r : ℝ} (hr : r ≠ 0) (y : Plane) :
    planarWedgeCoordinates (r • y) =
      (r * (planarWedgeCoordinates y).1, (planarWedgeCoordinates y).2) := by
  simp only [planarWedgeCoordinates, map_smul, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_inv_rev]
  congr 1
  field_simp

theorem planar_cone_annulus_to_vertex {C : Set Plane} {D : Set ℝ}
    {a b δ ρ : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) ρ → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hchart : ∀ y : Plane, (planarWedgeCoordinates y).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ → y ∈ Metric.ball (0 : Plane) ρ)
    (hmodel : ∀ᵐ y : Plane ∂volume,
      (planarWedgeCoordinates y).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D)) :
    ∀ᵐ y : Plane ∂volume,
      (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
  have hq (q : ℚ) : ∀ᵐ y : Plane ∂volume,
      1 ≤ (q : ℝ) → (planarWedgeCoordinates ((q : ℝ) • y)).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
    by_cases hq : 1 ≤ (q : ℝ)
    · have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
      have hqm := Measure.quasiMeasurePreserving_smul (volume : Measure Plane) hq0
      filter_upwards [hqm.ae (hc q hq),hqm.ae hmodel] with y hcy hmy _ hy hd
      have hcoord := planarWedgeCoordinates_smul hq0 y
      have hd' : |(planarWedgeCoordinates ((q : ℝ) • y)).2| < δ := by
        simpa only [hcoord] using hd
      have he := hcy (hchart _ hy hd')
      rw [inv_smul_smul₀ hq0] at he
      exact he.trans (by simpa only [hcoord] using hmy hy hd')
    · exact ae_of_all _ (fun _ h ↦ (hq h).elim)
  have hall : ∀ᵐ y : Plane ∂volume, ∀ q : ℚ,
      1 ≤ (q : ℝ) → (planarWedgeCoordinates ((q : ℝ) • y)).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
    exact ae_all_iff.mpr hq
  filter_upwards [hall] with y hy hs hd
  let s : ℝ := (planarWedgeCoordinates y).1
  have hs0 : 0 < s := hs.1
  have hmax : max 1 (a/s) < b/s := by
    apply max_lt
    · exact (lt_div_iff₀ hs0).mpr (by simpa [s] using hs.2)
    · exact (div_lt_div_iff_of_pos_right hs0).mpr hab
  obtain ⟨q,hql,hqu⟩ := exists_rat_btwn hmax
  have hq1 : 1 ≤ (q : ℝ) := (le_max_left _ _).trans hql.le
  have hq0 : (q : ℝ) ≠ 0 :=
    ne_of_gt ((div_pos ha hs0).trans ((le_max_right _ _).trans_lt hql))
  apply hy q hq1 ?_ hd
  rw [planarWedgeCoordinates_smul hq0]
  constructor
  · exact (div_lt_iff₀ hs0).mp ((le_max_right _ _).trans_lt hql)
  · exact (lt_div_iff₀ hs0).mp hqu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem planar_cone_wide_vertex_section {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    (R : Plane ≃ₗᵢ[ℝ] Plane) {w : ℝ} (hw : 0 < w) :
    ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
      (Icc (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Finite ∧
      ∀ᵐ y : Plane ∂volume,
        (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
        |(planarWedgeCoordinates y).2| < w →
        (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
  let C' := R ⁻¹' C
  have hC' : MeasurableSet C' := hC.preimage R.continuous.measurable
  have hc' := planar_cone_rotation hc R
  obtain ⟨a,b,L,D,ha,hab,hNb,hL,hD,hprod,hdual⟩ :=
    planar_cone_angular_dual_bv_wide hC' hw.le hc' hK (planar_directional_bv_rotation hbv R)
  have hmodel : ∀ᵐ y : Plane ∂volume,
      (planarWedgeCoordinates y).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < w →
      (y ∈ C' ↔ (planarWedgeCoordinates y).2 ∈ D) := by
    filter_upwards [planarWedgeCoordinates_quasiMeasurePreserving.ae hprod] with y hy hy1 hy2
    have hnot : (planeProductCoordinates y).1 ≠ 0 := ne_of_gt (ha.trans hy1.1)
    have hh := hy hy1 (abs_lt.mp hy2)
    rwa [planarWedgeChart_coordinates hnot] at hh
  have hchart (y : Plane) (hy1 : (planarWedgeCoordinates y).1 ∈ Ioo a b)
      (hy2 : |(planarWedgeCoordinates y).2| < w) :
      y ∈ Metric.ball (0 : Plane) (1/16) := by
    apply Metric.closedBall_subset_ball (by norm_num : (1/32 : ℝ) < 1/16)
    apply slope_rectangle_ball_wide ha hw.le hNb
    change (planeProductCoordinates y).1 ∈ Icc a b ∧
      (planeProductCoordinates y).2 ∈ Icc (-(w*b)) (w*b)
    have hs0 : 0 < (planeProductCoordinates y).1 := ha.trans hy1.1
    refine ⟨⟨hy1.1.le,hy1.2.le⟩,abs_le.mp ?_⟩
    have he : (planeProductCoordinates y).2 =
        (planeProductCoordinates y).1 * (planarWedgeCoordinates y).2 := by
      simp [planarWedgeCoordinates,hs0.ne']
    rw [he,abs_mul,abs_of_pos hs0]
    calc
      _ ≤ (planeProductCoordinates y).1*w := mul_le_mul_of_nonneg_left hy2.le hs0.le
      _ ≤ w*b := by
        have hyb : (planeProductCoordinates y).1 ≤ b := hy1.2.le
        nlinarith [mul_le_mul_of_nonneg_left hyb hw.le]
  exact ⟨b,D,ha.trans hab,hD,angular_dual_bv_finite_transitions_wide hD hw hdual,
    planar_cone_annulus_to_vertex ha hab hc' hchart hmodel⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma angularEssentialBoundary_compl (D : Set ℝ) :
    angularEssentialBoundary Dᶜ = angularEssentialBoundary D := by
  ext x
  simp only [angularEssentialBoundary,Set.mem_ofPred_eq,compl_compl]
  exact forall_congr' (fun _ ↦ forall_congr' (fun _ ↦ and_comm))

lemma nonempty_interval_two_phases_not_null (D : Set ℝ) {a b : ℝ} (hab : a < b)
    (hD : volume (Ioo a b ∩ D) = 0) (hC : volume (Ioo a b ∩ Dᶜ) = 0) : False := by
  have he : (Ioo a b ∩ D) ∪ (Ioo a b ∩ Dᶜ) = Ioo a b := by
    ext x
    change ((x ∈ Ioo a b ∧ x ∈ D) ∨ (x ∈ Ioo a b ∧ x ∉ D)) ↔ x ∈ Ioo a b
    tauto
  have hh := measure_union_null hD hC
  rw [he,Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hh
  linarith

lemma finite_angular_next_transition {D : Set ℝ} {a b l v : ℝ}
    (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hl : l ∈ Ioo a b) (hv : v ∈ Ioo a b) (hlv : l < v)
    (hvb : v ∈ angularEssentialBoundary D) :
    ∃ u : ℝ, l < u ∧ u ≤ v ∧ u ∈ angularEssentialBoundary D ∧
      Disjoint (Ioo l u) (angularEssentialBoundary D) := by
  classical
  let S : Set ℝ := Ioc l v ∩ angularEssentialBoundary D
  have hS : S.Finite := hfin.subset (by
    intro x hx
    exact ⟨⟨hl.1.le.trans hx.1.1.le,hx.1.2.trans hv.2.le⟩,hx.2⟩)
  have hn : hS.toFinset.Nonempty := ⟨v,by simp only [Finite.mem_toFinset]; exact ⟨⟨hlv,le_rfl⟩,hvb⟩⟩
  let u := hS.toFinset.min' hn
  have hu : u ∈ S := by
    exact (Finite.mem_toFinset hS).mp (Finset.min'_mem hS.toFinset hn)
  refine ⟨u,hu.1.1,hu.1.2,hu.2,?_⟩
  rw [Set.disjoint_left]
  intro x hx hxb
  have hxS : x ∈ hS.toFinset := by
    rw [Finite.mem_toFinset]
    exact ⟨⟨hx.1,hx.2.le.trans hu.1.2⟩,hxb⟩
  exact (not_le_of_gt hx.2) (Finset.min'_le hS.toFinset x hxS)

theorem occupied_adjacent_angular_model {D : Set ℝ} (hD : MeasurableSet D)
    {a b l u : ℝ} (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hl : l ∈ Ioo a b) (hu : u ∈ Ioo a b) (hlu : l < u)
    (hlb : l ∈ angularEssentialBoundary D) (hub : u ∈ angularEssentialBoundary D)
    (hinside : volume (Ioo l u ∩ Dᶜ) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ 3*δ < u-l ∧
      ∀ᵐ t : ℝ ∂volume, t ∈ Ioo (l-δ) (u+δ) →
        (t ∈ D ↔ t ∈ Ioo l u) := by
  obtain ⟨δL,hδL,hjumpL⟩ := finite_angular_transition_is_jump hD hfin hl hlb
  obtain ⟨δU,hδU,hjumpU⟩ := finite_angular_transition_is_jump hD hfin hu hub
  let δ : ℝ := min (min δL δU) ((u-l)/4)
  have hδ : 0 < δ := lt_min (lt_min hδL hδU) (by linarith)
  have hδl : δ ≤ δL := (min_le_left _ _).trans (min_le_left _ _)
  have hδu : δ ≤ δU := (min_le_left _ _).trans (min_le_right _ _)
  have hδg : δ ≤ (u-l)/4 := min_le_right _ _
  have hgap : 3*δ < u-l := by linarith
  have hleft : volume (Ioo (l-δ) l ∩ D) = 0 := by
    rcases hjumpL with hgood|hbad
    · exact measure_mono_null (by intro t ht; exact ⟨⟨by linarith [ht.1.1],ht.1.2⟩,ht.2⟩) hgood.1
    · exfalso
      apply nonempty_interval_two_phases_not_null D (show l < l+δ by linarith)
      · exact measure_mono_null (by intro t ht; exact ⟨⟨ht.1.1,by linarith [ht.1.2]⟩,ht.2⟩) hbad.2
      · exact measure_mono_null (by intro t ht; exact ⟨⟨ht.1.1,by linarith [ht.1.2]⟩,ht.2⟩) hinside
  have hright : volume (Ioo u (u+δ) ∩ D) = 0 := by
    rcases hjumpU with hbad|hgood
    · exfalso
      apply nonempty_interval_two_phases_not_null D (show u-δ < u by linarith)
      · exact measure_mono_null (by intro t ht; exact ⟨⟨by linarith [ht.1.1],ht.1.2⟩,ht.2⟩) hbad.1
      · exact measure_mono_null (by intro t ht; exact ⟨⟨by linarith [ht.1.1],ht.1.2⟩,ht.2⟩) hinside
    · exact measure_mono_null (by intro t ht; exact ⟨⟨ht.1.1,by linarith [ht.1.2]⟩,ht.2⟩) hgood.2
  have hlne : ∀ᵐ t : ℝ ∂volume, t ≠ l := by rw [ae_iff]; simp
  have hune : ∀ᵐ t : ℝ ∂volume, t ≠ u := by rw [ae_iff]; simp
  refine ⟨δ,hδ,hgap,?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hleft,
    measure_eq_zero_iff_ae_notMem.mp hright,measure_eq_zero_iff_ae_notMem.mp hinside,
    hlne,hune] with t htL htU htI htl htu ht
  constructor
  · intro htD
    constructor
    · by_contra h
      exact htL ⟨⟨ht.1,lt_of_le_of_ne (not_lt.mp h) htl⟩,htD⟩
    · by_contra h
      exact htU ⟨⟨lt_of_le_of_ne (not_lt.mp h) htu.symm,ht.2⟩,htD⟩
  · intro hti
    by_contra h
    exact htI ⟨hti,h⟩

theorem adjacent_angular_sector_model {D : Set ℝ} (hD : MeasurableSet D)
    {a b l u : ℝ} (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hl : l ∈ Ioo a b) (hu : u ∈ Ioo a b) (hlu : l < u)
    (hlb : l ∈ angularEssentialBoundary D) (hub : u ∈ angularEssentialBoundary D)
    (hadj : Disjoint (Ioo l u) (angularEssentialBoundary D)) :
    ∃ δ : ℝ, 0 < δ ∧ 3*δ < u-l ∧
      ((∀ᵐ t : ℝ ∂volume, t ∈ Ioo (l-δ) (u+δ) → (t ∈ D ↔ t ∈ Ioo l u)) ∨
       (∀ᵐ t : ℝ ∂volume, t ∈ Ioo (l-δ) (u+δ) → (t ∈ Dᶜ ↔ t ∈ Ioo l u))) := by
  rcases connected_angular_phase hD measurableSet_Ioo isPreconnected_Ioo hadj with hempty|hfull
  · have hfin' : (Icc a b ∩ angularEssentialBoundary Dᶜ).Finite := by
      rwa [angularEssentialBoundary_compl]
    have hlb' : l ∈ angularEssentialBoundary Dᶜ := by rwa [angularEssentialBoundary_compl]
    have hub' : u ∈ angularEssentialBoundary Dᶜ := by rwa [angularEssentialBoundary_compl]
    obtain ⟨δ,hδ,hgap,hmod⟩ := occupied_adjacent_angular_model hD.compl hfin' hl hu hlu hlb' hub'
      (by simpa only [compl_compl] using hempty)
    exact ⟨δ,hδ,hgap,Or.inr hmod⟩
  · obtain ⟨δ,hδ,hgap,hmod⟩ := occupied_adjacent_angular_model hD hfin hl hu hlu hlb hub hfull
    exact ⟨δ,hδ,hgap,Or.inl hmod⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVPlanarEssentialBoundary
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma planarSlope_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun y : Plane ↦ (planarWedgeCoordinates y).2) volume volume :=
  (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp
    planarWedgeCoordinates_quasiMeasurePreserving

theorem moving_product_angular_boundary_subsingleton
    {B : Set Cover} {C : Set Plane} {n : Cover} {η b w : ℝ}
    (hB : MeasurableSet B) (hη : 0 < η) (hb : 0 < b) (hw : 0 < w)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane)
    {D : Set ℝ} (hD : MeasurableSet D)
    (hfin : (Icc (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Finite)
    (hmodel : ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      |(planarWedgeCoordinates y).2| < w → (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x) :
    (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton := by
  have hno : ∀ l v : ℝ, l ∈ Ioo (-(w/4)) (w/4) → v ∈ Ioo (-(w/4)) (w/4) →
      l ∈ angularEssentialBoundary D → v ∈ angularEssentialBoundary D → l < v → False := by
    intro l v hl hv hlb hvb hlv
    obtain ⟨u,hlu,huv,hub,hadj⟩ := finite_angular_next_transition hfin hl hv hlv hvb
    have hu : u ∈ Ioo (-(w/4)) (w/4) := ⟨hl.1.trans hlu,huv.trans_lt hv.2⟩
    obtain ⟨δ,hδ,hgap,hphase⟩ := adjacent_angular_sector_model hD hfin hl hu hlu hlb hub hadj
    have hwide {t : ℝ} (ht : t ∈ Ioo (l-δ) (u+δ)) : |t| < w := by
      apply lt_trans ?_ (half_lt_self hw)
      apply abs_lt.mpr
      constructor <;> linarith [hl.1,hl.2,hu.1,hu.2,ht.1,ht.2]
    apply no_moving_product_angular_sector hB hη hb hδ hgap hmin hprod R ?_ heq hflux
    rcases hphase with hi|hi
    · apply Or.inl
      filter_upwards [hmodel,planarSlope_quasiMeasurePreserving.ae hi] with y hm hi hr hs
      exact (hm hr (hwide hs)).trans (hi hs)
    · apply Or.inr
      filter_upwards [hmodel,planarSlope_quasiMeasurePreserving.ae hi] with y hm hi hr hs
      exact (not_congr (hm hr (hwide hs))).trans (hi hs)
  intro l hl u hu
  rcases lt_trichotomy l u with hlt|he|hgt
  · exact (hno l u hl.1 hu.1 hl.2 hu.2 hlt).elim
  · exact he
  · exact (hno u l hu.1 hl.1 hu.2 hl.2 hgt).elim

theorem minimizing_planar_chart_single_transition
    {B : Set Cover} {C : Set Plane} {n : Cover} {η : ℝ}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hη : 0 < η)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x)
    (R : Plane ≃ₗᵢ[ℝ] Plane) {w : ℝ} (hw : 0 < w) :
    ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
      (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
      ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
        |(planarWedgeCoordinates y).2| < w →
        (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
  obtain ⟨b,D,hb,hD,hfin,hmodel⟩ := planar_cone_wide_vertex_section hC hc hK hbv R hw
  exact ⟨b,D,hb,hD,moving_product_angular_boundary_subsingleton hB hη hb hw hmin hprod R hD
    hfin hmodel heq hflux,hmodel⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measureSupport_local_ae_mono {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {A B O : Set X} {p : X}
    (hO : O ∈ 𝓝 p) (hae : ∀ᵐ x ∂μ, x ∈ O → x ∈ A → x ∈ B)
    (hp : p ∈ (μ.restrict A).support) : p ∈ (μ.restrict B).support := by
  obtain ⟨W,hWO,hW,hpW⟩ := mem_nhds_iff.mp hO
  rw [(nhds_basis_opens p).mem_measureSupport]
  rintro U ⟨hpU,hU⟩
  have hpos := (Measure.mem_support_iff_forall p).mp hp (U ∩ W)
    (inter_mem (hU.mem_nhds hpU) (hW.mem_nhds hpW))
  rw [Measure.restrict_apply (hU.inter hW).measurableSet] at hpos
  rw [Measure.restrict_apply hU.measurableSet]
  apply hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [hae] with x hx hxx
  exact ⟨hxx.1.1,hx (hWO hxx.1.2) hxx.2⟩

lemma planar_boundary_local_ae {C D O : Set Plane} {p : Plane}
    (hO : O ∈ 𝓝 p) (hae : ∀ᵐ y : Plane ∂volume, y ∈ O → (y ∈ C ↔ y ∈ D))
    (hp : p ∈ planarEssentialBoundary C) : p ∈ planarEssentialBoundary D := by
  exact ⟨measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (h ho).mp)) hp.1,
    measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (not_congr (h ho)).mp)) hp.2⟩

lemma measureSupport_preimage_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {D : Set Y} {p : X}
    (hq : Measure.QuasiMeasurePreserving f μ ν) (hf : ContinuousAt f p)
    (hp : p ∈ (μ.restrict (f ⁻¹' D)).support) : f p ∈ (ν.restrict D).support := by
  rw [(nhds_basis_opens (f p)).mem_measureSupport]
  rintro U ⟨hpU,hU⟩
  rw [Measure.restrict_apply hU.measurableSet]
  by_contra h
  have hzero : ν (U ∩ D) = 0 := (not_lt.mp h).antisymm bot_le
  have hz := hq.preimage_null hzero
  have hpos := (Measure.mem_support_iff_forall p).mp hp (f ⁻¹' U)
    (hf (hU.mem_nhds hpU))
  rw [Measure.restrict_apply (hU.measurableSet.preimage hq.measurable)] at hpos
  exact (ne_of_gt hpos) hz

lemma planar_boundary_preimage_image {C : Set Plane} {f : Plane → Plane} {p : Plane}
    (hq : Measure.QuasiMeasurePreserving f volume volume) (hf : ContinuousAt f p)
    (hp : p ∈ planarEssentialBoundary (f ⁻¹' C)) : f p ∈ planarEssentialBoundary C := by
  exact ⟨measureSupport_preimage_image hq hf hp.1,measureSupport_preimage_image hq hf hp.2⟩

lemma planar_boundary_isometry {C : Set Plane} (R : Plane ≃ₗᵢ[ℝ] Plane) {p : Plane}
    (hp : p ∈ planarEssentialBoundary C) : R.symm p ∈ planarEssentialBoundary (R ⁻¹' C) := by
  apply planar_boundary_preimage_image R.symm.measurePreserving.quasiMeasurePreserving R.symm.continuous.continuousAt
  convert! hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [Set.mem_preimage,R.apply_symm_apply]

lemma continuousAt_planarWedgeCoordinates {p : Plane} (hp : (planeProductCoordinates p).1 ≠ 0) :
    ContinuousAt planarWedgeCoordinates p := by
  exact (planeProductCoordinates.continuous.fst.continuousAt).prodMk
    (((planeProductCoordinates.continuous.fst.continuousAt).inv₀ hp).mul
      planeProductCoordinates.continuous.snd.continuousAt)

lemma planar_boundary_angular_transition {C : Set Plane} {D : Set ℝ} {b w : ℝ}
    (hmodel : ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      |(planarWedgeCoordinates y).2| < w → (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {p : Plane} (hp : p ∈ planarEssentialBoundary C)
    (hpr : (planarWedgeCoordinates p).1 ∈ Ioo 0 b)
    (hps : |(planarWedgeCoordinates p).2| < w) :
    (planarWedgeCoordinates p).2 ∈ angularEssentialBoundary D := by
  let f : Plane → ℝ := fun y ↦ (planarWedgeCoordinates y).2
  have hc := continuousAt_planarWedgeCoordinates (show (planeProductCoordinates p).1 ≠ 0 from hpr.1.ne')
  have hO : {y : Plane | (planarWedgeCoordinates y).1 ∈ Ioo 0 b ∧
      |(planarWedgeCoordinates y).2| < w} ∈ 𝓝 p := by
    exact inter_mem (hc.fst (isOpen_Ioo.mem_nhds hpr))
      ((hc.snd.abs) (Iio_mem_nhds hps))
  have hp' : p ∈ planarEssentialBoundary (f ⁻¹' D) :=
    planar_boundary_local_ae hO (hmodel.mono (fun _ h hy ↦ h hy.1 hy.2)) hp
  rw [angularEssentialBoundary_eq_support]
  exact ⟨measureSupport_preimage_image (f := f) (p := p) planarSlope_quasiMeasurePreserving hc.snd hp'.1,
    measureSupport_preimage_image (f := f) (p := p) planarSlope_quasiMeasurePreserving hc.snd hp'.2⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_cone_boundary_contract {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {p : Plane} (hp : p ∈ planarEssentialBoundary C) (hpball : p ∈ Metric.ball (0 : Plane) (1/16))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) : c • p ∈ planarEssentialBoundary C := by
  have hca := hc c⁻¹ ((one_le_inv₀ hc0).mpr hc1)
  simp only [inv_inv] at hca
  have hp' : p ∈ planarEssentialBoundary ((fun y : Plane ↦ c • y) ⁻¹' C) :=
    planar_boundary_local_ae (Metric.isOpen_ball.mem_nhds hpball)
      (hca.mono (fun _ h hy ↦ (h hy).symm)) hp
  exact planar_boundary_preimage_image (Measure.quasiMeasurePreserving_smul volume hc0.ne')
    (continuous_const_smul c).continuousAt hp'

theorem planar_cone_boundary_chart_unique_slope {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hcharts : ∀ (R : Plane ≃ₗᵢ[ℝ] Plane) (w : ℝ), 0 < w →
      ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
        (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
        ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
          |(planarWedgeCoordinates y).2| < w →
          (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {p q : Plane} (hp : p ∈ planarEssentialBoundary C) (hq : q ∈ planarEssentialBoundary C)
    (hpb : p ∈ Metric.ball (0 : Plane) (1/16)) (hqb : q ∈ Metric.ball (0 : Plane) (1/16))
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hpr : 0 < (planarWedgeCoordinates (R.symm p)).1)
    (hqr : 0 < (planarWedgeCoordinates (R.symm q)).1) :
    (planarWedgeCoordinates (R.symm p)).2 = (planarWedgeCoordinates (R.symm q)).2 := by
  let s := (planarWedgeCoordinates (R.symm p)).2
  let t := (planarWedgeCoordinates (R.symm q)).2
  let a := (planarWedgeCoordinates (R.symm p)).1
  let d := (planarWedgeCoordinates (R.symm q)).1
  let w : ℝ := 4*(|s|+|t|+1)
  have hw : 0 < w := by dsimp [w]; positivity
  obtain ⟨b,D,hb,hD,hsub,hmodel⟩ := hcharts R w hw
  let c : ℝ := min (1/2) (b/(2*(a+d+1)))
  have had : 0 < a+d+1 := by change 0 < (planarWedgeCoordinates (R.symm p)).1 + (planarWedgeCoordinates (R.symm q)).1 + 1; linarith
  have hc0 : 0 < c := lt_min (by norm_num) (div_pos hb (by positivity))
  have hc1 : c ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcb := (le_div_iff₀ (show 0 < 2*(a+d+1) by positivity)).mp (min_le_right (1/2) (b/(2*(a+d+1))))
  have hcpa : c*a < b := by
    have ha0 : 0 < a := hpr
    have hd0 : 0 < d := hqr
    nlinarith [mul_pos hc0 hd0]
  have hcqd : c*d < b := by
    have ha0 : 0 < a := hpr
    have hd0 : 0 < d := hqr
    nlinarith [mul_pos hc0 ha0]
  have hsi : s ∈ Ioo (-(w/4)) (w/4) := by dsimp [w]; constructor <;> linarith [neg_abs_le s,le_abs_self s,abs_nonneg t]
  have hti : t ∈ Ioo (-(w/4)) (w/4) := by dsimp [w]; constructor <;> linarith [neg_abs_le t,le_abs_self t,abs_nonneg s]
  have hsw : |s| < w := by dsimp [w]; linarith [abs_nonneg s,abs_nonneg t]
  have htw : |t| < w := by dsimp [w]; linarith [abs_nonneg s,abs_nonneg t]
  have heP : planarWedgeCoordinates (R.symm (c • p)) = (c*a,s) := by
    rw [map_smul,planarWedgeCoordinates_smul hc0.ne']
  have heQ : planarWedgeCoordinates (R.symm (c • q)) = (c*d,t) := by
    rw [map_smul,planarWedgeCoordinates_smul hc0.ne']
  have hps := planar_boundary_angular_transition hmodel
    (planar_boundary_isometry R (planar_cone_boundary_contract hc hp hpb hc0 hc1))
    (by rw [heP]; exact ⟨mul_pos hc0 hpr,hcpa⟩) (by rwa [heP])
  have hqs := planar_boundary_angular_transition hmodel
    (planar_boundary_isometry R (planar_cone_boundary_contract hc hq hqb hc0 hc1))
    (by rw [heQ]; exact ⟨mul_pos hc0 hqr,hcqd⟩) (by rwa [heQ])
  rw [heP] at hps
  rw [heQ] at hqs
  exact hsub ⟨hsi,hps⟩ ⟨hti,hqs⟩

lemma planar_equal_positive_slopes_collinear {p q : Plane}
    (hp : 0 < (planarWedgeCoordinates p).1) (hq : 0 < (planarWedgeCoordinates q).1)
    (hsl : (planarWedgeCoordinates p).2 = (planarWedgeCoordinates q).2) :
    ∃ t : ℝ, 0 < t ∧ q = t • p := by
  let t : ℝ := (planeProductCoordinates q).1 / (planeProductCoordinates p).1
  refine ⟨t,div_pos hq hp,?_⟩
  apply planeProductCoordinates.injective
  rw [map_smul]
  ext
  · change (planeProductCoordinates q).1 = t*(planeProductCoordinates p).1
    dsimp [t]
    have hp0 : (planeProductCoordinates p).1 ≠ 0 := hp.ne'
    field_simp
  · change (planeProductCoordinates q).2 = t*(planeProductCoordinates p).2
    change (planeProductCoordinates p).1⁻¹*(planeProductCoordinates p).2 =
      (planeProductCoordinates q).1⁻¹*(planeProductCoordinates q).2 at hsl
    have hp0 : (planeProductCoordinates p).1 ≠ 0 := hp.ne'
    have hq0 : (planeProductCoordinates q).1 ≠ 0 := hq.ne'
    dsimp [t]
    field_simp at hsl ⊢
    nlinarith [hsl]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarNormalRotation_axis {n : Plane} (hn : ‖n‖ = 1) :
    planarNormalRotation n (EuclideanSpace.single 0 1) = n := by
  apply Submodule.reflection_sub
  simpa using hn.symm

lemma planarNormalRotation_radial {n : Plane} (hn : ‖n‖ = 1) (p : Plane) :
    (planarWedgeCoordinates ((planarNormalRotation n).symm p)).1 = ⟪n,p⟫ := by
  change (planeProductCoordinates ((planarNormalRotation n).symm p)).1 = _
  rw [planeProductCoordinates_apply]
  conv_rhs => lhs; rw [← planarNormalRotation_axis hn]
  conv_rhs => rhs; rw [← (planarNormalRotation n).apply_symm_apply p]
  rw [(planarNormalRotation n).inner_map_map]
  simp [EuclideanSpace.inner_single_left]

lemma planar_common_hemisphere_or_collinear {p q : Plane} (hp : p ≠ 0) (hq : q ≠ 0) :
    (∃ t : ℝ, q = t • p) ∨ ∃ n : Plane, ‖n‖ = 1 ∧ 0 < ⟪n,p⟫ ∧ 0 < ⟪n,q⟫ := by
  let u : Plane := ‖p‖⁻¹ • p
  let v : Plane := ‖q‖⁻¹ • q
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)), inv_mul_cancel₀ hpn.ne']
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg q)), inv_mul_cancel₀ hqn.ne']
  have hpu : p = ‖p‖ • u := by dsimp [u]; rw [smul_smul,mul_inv_cancel₀ hpn.ne',one_smul]
  have hqv : q = ‖q‖ • v := by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hqn.ne',one_smul]
  by_cases hz : u+v=0
  · left
    refine ⟨-‖q‖*‖p‖⁻¹,?_⟩
    have hvu : v = -u := eq_neg_of_add_eq_zero_right hz
    calc
      q = ‖q‖ • v := hqv
      _ = -‖q‖ • u := by rw [hvu,smul_neg,neg_smul]
      _ = (-‖q‖*‖p‖⁻¹) • p := by dsimp [u]; rw [smul_smul]
  · right
    let n : Plane := ‖u+v‖⁻¹ • (u+v)
    have hw : 0 < ‖u+v‖ := norm_pos_iff.mpr hz
    have hinner : 0 < 1+⟪u,v⟫ := by
      have he := norm_add_sq_real u v
      rw [hu,hv] at he
      nlinarith [sq_pos_of_pos hw]
    refine ⟨n,?_,?_,?_⟩
    · dsimp [n]
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hw.ne']
    · rw [hpu]
      dsimp [n]
      rw [real_inner_smul_left,inner_smul_right,inner_add_left,real_inner_self_eq_norm_sq,real_inner_comm u v,hu]
      exact mul_pos (inv_pos.mpr hw) (mul_pos hpn (by simpa using hinner))
    · rw [hqv]
      dsimp [n]
      rw [real_inner_smul_left,inner_smul_right,inner_add_left,real_inner_self_eq_norm_sq,hv]
      exact mul_pos (inv_pos.mpr hw) (mul_pos hqn (by simpa [add_comm] using hinner))

theorem planar_cone_boundary_collinear {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hcharts : ∀ (R : Plane ≃ₗᵢ[ℝ] Plane) (w : ℝ), 0 < w →
      ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
        (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
        ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
          |(planarWedgeCoordinates y).2| < w →
          (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {p q : Plane} (hp : p ∈ planarEssentialBoundary C) (hq : q ∈ planarEssentialBoundary C)
    (hpb : p ∈ Metric.ball (0 : Plane) (1/16)) (hqb : q ∈ Metric.ball (0 : Plane) (1/16))
    (hp0 : p ≠ 0) : ∃ t : ℝ, q = t • p := by
  by_cases hq0 : q = 0
  · exact ⟨0,by simp [hq0]⟩
  rcases planar_common_hemisphere_or_collinear hp0 hq0 with hh|⟨n,hn,hpn,hqn⟩
  · exact hh
  let R := planarNormalRotation n
  have hpr : 0 < (planarWedgeCoordinates (R.symm p)).1 := by
    rw [planarNormalRotation_radial hn]; exact hpn
  have hqr : 0 < (planarWedgeCoordinates (R.symm q)).1 := by
    rw [planarNormalRotation_radial hn]; exact hqn
  obtain ⟨t,_,he⟩ := planar_equal_positive_slopes_collinear hpr hqr
    (planar_cone_boundary_chart_unique_slope hc hcharts hp hq hpb hqb R hpr hqr)
  refine ⟨t,?_⟩
  have he' := congrArg R he
  simpa only [R.apply_symm_apply,map_smul] using he'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem connected_planar_phase {D s : Set Plane} (hD : MeasurableSet D)
    (hs : MeasurableSet s) (hc : IsPreconnected s)
    (hd : Disjoint s (planarEssentialBoundary D)) :
    volume (s ∩ D) = 0 ∨ volume (s ∩ Dᶜ) = 0 := by
  let U := (volume.restrict D).supportᶜ
  let W := (volume.restrict Dᶜ).supportᶜ
  have hUW : Disjoint U W := by
    have hsum : (volume.restrict D).support ∪ (volume.restrict Dᶜ).support = univ := by
      rw [← Measure.support_add,Measure.restrict_add_restrict_compl hD,Measure.support_eq_univ]
    rw [Set.disjoint_iff_inter_eq_empty]
    change (volume.restrict D).supportᶜ ∩ (volume.restrict Dᶜ).supportᶜ = ∅
    rw [← compl_union,hsum,compl_univ]
  have hsub : s ⊆ U ∪ W := by
    intro x hx
    have hx' : x ∉ planarEssentialBoundary D := fun hb ↦ Set.disjoint_left.mp hd hx hb
    rw [planarEssentialBoundary] at hx'
    exact not_and_or.mp hx'
  have hnullD (h : s ⊆ U) : volume (s ∩ D) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  have hnullC (h : s ⊆ W) : volume (s ∩ Dᶜ) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  by_cases hU : (s ∩ U).Nonempty
  · exact Or.inl (hnullD (hc.subset_left_of_subset_union Measure.isOpen_compl_support
      Measure.isOpen_compl_support hUW hsub hU))
  · apply Or.inr
    apply hnullC
    intro x hx
    rcases hsub hx with hu|hw
    · exact (hU ⟨x,hx,hu⟩).elim
    · exact hw

lemma planar_punctured_ball_preconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball (0 : Plane) r \ {0}) := by
  let f := OpenPartialHomeomorph.univBall (0 : Plane) r
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  have hc := (isConnected_compl_singleton_of_one_lt_rank hrank (0 : Plane)).isPreconnected
  have hi : f '' ({0}ᶜ : Set Plane) = Metric.ball (0 : Plane) r \ {0} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← OpenPartialHomeomorph.univBall_target (0 : Plane) hr]
        exact f.map_source (by simp [f])
      · intro he
        have he0 : f x = 0 := he
        have hh := congrArg f.symm he0
        rw [f.left_inv (by simp [f]),OpenPartialHomeomorph.univBall_symm_apply_center] at hh
        exact hx hh
    · rintro ⟨hy,hy0⟩
      have hyt : y ∈ f.target := by rwa [OpenPartialHomeomorph.univBall_target _ hr]
      refine ⟨f.symm y,?_,f.right_inv hyt⟩
      intro hz
      have hz' : f.symm y = 0 := hz
      have hh := congrArg f hz'
      rw [f.right_inv hyt,OpenPartialHomeomorph.univBall_apply_zero] at hh
      exact hy0 hh
  rw [← hi]
  exact hc.image f (OpenPartialHomeomorph.continuous_univBall (0 : Plane) r).continuousOn

theorem planar_boundary_nonzero {C : Set Plane} (hC : MeasurableSet C)
    {r : ℝ} (hr : 0 < r)
    (hpos : 0 < volume (Metric.ball (0 : Plane) r ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Plane) r ∩ Cᶜ)) :
    ∃ p : Plane, p ∈ Metric.ball (0 : Plane) r ∧ p ≠ 0 ∧ p ∈ planarEssentialBoundary C := by
  by_contra he
  have hd : Disjoint (Metric.ball (0 : Plane) r \ {0}) (planarEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro x hx hb
    exact he ⟨x,hx.1,hx.2,hb⟩
  have hnull (A : Set Plane) (h : volume ((Metric.ball (0 : Plane) r \ {0}) ∩ A) = 0) :
      volume (Metric.ball (0 : Plane) r ∩ A) = 0 := by
    apply measure_mono_null (t := ((Metric.ball (0 : Plane) r \ {0}) ∩ A) ∪ {0}) ?_
      (measure_union_null h (measure_singleton 0))
    intro x hx
    by_cases hx0 : x=0
    · exact Or.inr hx0
    · exact Or.inl ⟨⟨hx.1,hx0⟩,hx.2⟩
  rcases connected_planar_phase hC (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton 0))
    (planar_punctured_ball_preconnected hr) hd with hh|hh
  · exact (ne_of_gt hpos) (hnull C hh)
  · exact (ne_of_gt hneg) (hnull Cᶜ hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_hyperplane_volume_zero {n : Plane} (hn : n ≠ 0) :
    volume {y : Plane | ⟪n,y⟫ = 0} = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker (innerSL ℝ n).toLinearMap)
  intro htop
  have hm : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [htop]; trivial
  change ⟪n,n⟫ = 0 at hm
  exact hn (inner_self_eq_zero.mp hm)

lemma planar_halfballs_null {A : Set Plane} {n : Plane} (hn : n ≠ 0) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) = 0)
    (hr : volume ((Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) = 0) :
    volume (Metric.ball (0 : Plane) r ∩ A) = 0 := by
  apply measure_mono_null (t := ((Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) ∪
    ((Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) ∪ {y | ⟪n,y⟫ = 0}) ?_
    (measure_union_null (measure_union_null hl hr) (planar_hyperplane_volume_zero hn))
  intro y hy
  rcases lt_trichotomy ⟪n,y⟫ 0 with hh|hh|hh
  · exact Or.inl (Or.inl ⟨⟨hy.1,hh⟩,hy.2⟩)
  · exact Or.inr hh
  · exact Or.inl (Or.inr ⟨⟨hy.1,hh⟩,hy.2⟩)

lemma planar_opposite_halfballs_model {C : Set Plane} {n : Plane} (hn : n ≠ 0) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) = 0)
    (hr : volume ((Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) = 0) :
    ∀ᵐ y : Plane ∂volume, y ∈ Metric.ball (0 : Plane) r → (y ∈ C ↔ 0 < ⟪n,y⟫) := by
  have hal : ∀ᵐ y : Plane ∂volume, ¬(y ∈ (Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hl
  have har : ∀ᵐ y : Plane ∂volume, ¬(y ∈ (Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hr
  have han : ∀ᵐ y : Plane ∂volume, ⟪n,y⟫ ≠ 0 := by
    simpa only [ae_iff,not_not] using planar_hyperplane_volume_zero hn
  filter_upwards [hal,har,han] with y hl hr hne hy
  constructor
  · intro hc
    by_contra hpos
    exact hl ⟨⟨hy,lt_of_le_of_ne (not_lt.mp hpos) hne⟩,hc⟩
  · intro hpos
    by_contra hnc
    exact hr ⟨⟨hy,hpos⟩,hnc⟩

theorem planar_boundary_line_halfplane {C : Set Plane} (hC : MeasurableSet C)
    {r : ℝ} {n : Plane} (hn : n ≠ 0)
    (hbd : ∀ y : Plane, y ∈ Metric.ball (0 : Plane) r → y ∈ planarEssentialBoundary C → ⟪n,y⟫ = 0)
    (hpos : 0 < volume (Metric.ball (0 : Plane) r ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Plane) r ∩ Cᶜ)) :
    ∃ m : Plane, m ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) r → (y ∈ C ↔ 0 < ⟪m,y⟫) := by
  let U := Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}
  let W := Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet
  have hW : MeasurableSet W := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt continuous_const (innerSL ℝ n).continuous).measurableSet
  have hcU : IsPreconnected U := ((convex_ball (0 : Plane) r).inter
    ((convex_Iio (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hcW : IsPreconnected W := ((convex_ball (0 : Plane) r).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hdU : Disjoint U (planarEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_lt hy.2) (hbd y hy.1 he)
  have hdW : Disjoint W (planarEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_gt hy.2) (hbd y hy.1 he)
  rcases connected_planar_phase hC hU hcU hdU with hu|hu <;>
    rcases connected_planar_phase hC hW hcW hdW with hw|hw
  · exact ((ne_of_gt hpos) (planar_halfballs_null hn hu hw)).elim
  · exact ⟨n,hn,planar_opposite_halfballs_model hn hu hw⟩
  · refine ⟨-n,neg_ne_zero.mpr hn,?_⟩
    apply planar_opposite_halfballs_model (neg_ne_zero.mpr hn)
    · simpa only [inner_neg_left,neg_lt_zero] using hw
    · simpa only [inner_neg_left,neg_pos] using hu
  · exact ((ne_of_gt hneg) (planar_halfballs_null hn hu hw)).elim

lemma exists_planar_perpendicular {p : Plane} (hp : p ≠ 0) :
    ∃ n : Plane, n ≠ 0 ∧ ⟪n,p⟫ = 0 := by
  let n : Plane := EuclideanSpace.single 0 (-p 1) + EuclideanSpace.single 1 (p 0)
  refine ⟨n,?_,?_⟩
  · intro hn
    have h0 := congrArg (fun y : Plane ↦ y 0) hn
    have h1 := congrArg (fun y : Plane ↦ y 1) hn
    simp [n] at h0 h1
    apply hp
    ext i
    fin_cases i <;> simp_all
  · dsimp [n]
    rw [inner_add_left,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_left]
    simp only [starRingEnd_apply,star_trivial]
    ring

theorem planar_cone_halfplane_of_single_transition {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hcharts : ∀ (R : Plane ≃ₗᵢ[ℝ] Plane) (w : ℝ), 0 < w →
      ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
        (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
        ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
          |(planarWedgeCoordinates y).2| < w →
          (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    (hpos : 0 < volume (Metric.ball (0 : Plane) (1/16) ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Plane) (1/16) ∩ Cᶜ)) :
    ∃ n : Plane, n ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (y ∈ C ↔ 0 < ⟪n,y⟫) := by
  obtain ⟨p,hpb,hp0,hp⟩ := planar_boundary_nonzero hC (by norm_num : (0 : ℝ)<1/16) hpos hneg
  obtain ⟨n,hn,hnp⟩ := exists_planar_perpendicular hp0
  apply planar_boundary_line_halfplane hC hn ?_ hpos hneg
  intro y hy hb
  obtain ⟨t,rfl⟩ := planar_cone_boundary_collinear hc hcharts hp hb hpb hy hp0
  rw [inner_smul_right,hnp,mul_zero]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSecondaryPlanarData
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_product_ball_volume_le {B : Set Cover} {C : Set Plane}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/16) :
    volume.real (B ∩ Metric.ball (0 : Cover) ρ) ≤
      (2*ρ)*volume.real (C ∩ Metric.ball (0 : Plane) ρ) := by
  have hm := (normalColumnChart_measurePreserving 0 n).measure_preimage
    (s := B ∩ Metric.ball (0 : Cover) ρ) (hB.inter measurableSet_ball).nullMeasurableSet
  have hsub : (normalColumnChart 0 n ⁻¹' (B ∩ Metric.ball (0 : Cover) ρ)) ≤ᵐ[volume]
      Ioo (-ρ) ρ ×ˢ (C ∩ Metric.ball (0 : Plane) ρ) := by
    filter_upwards [hprod] with z hz hzb
    have hnorm : ‖normalColumnChart 0 n z‖ < ρ := by
      simpa only [Metric.mem_ball,dist_zero_right] using hzb.2
    have hheight : |z.1| < ρ := by
      have hh := abs_real_inner_le_norm n (normalColumnChart 0 n z)
      rw [hn,one_mul] at hh
      have he := normalColumnChart_height 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    have hplane : ‖z.2‖ < ρ := by
      have hh := (normalPlaneCoordinates_lipschitz n).norm_sub_le (normalColumnChart 0 n z) 0
      simp only [map_zero,sub_zero,NNReal.coe_one,one_mul] at hh
      have he := normalColumnChart_projection 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    exact ⟨abs_lt.mp hheight,(hz (hheight.trans_le hρ1) (hplane.trans_le hρ1)).mp hzb.1,
      by simpa only [Metric.mem_ball,dist_zero_right] using hplane⟩
  have hle := measure_mono_ae hsub
  rw [hm,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo] at hle
  have ht : volume (C ∩ Metric.ball (0 : Plane) ρ) ≠ ⊤ := by
    have hsplit := measure_inter_add_sdiff (μ := (volume : Measure Plane))
      (Metric.ball (0 : Plane) ρ) hC
    rw [inter_comm] at hsplit
    have hbound := (le_self_add : volume (C ∩ Metric.ball (0 : Plane) ρ) ≤
      volume (C ∩ Metric.ball (0 : Plane) ρ) + volume (Metric.ball (0 : Plane) ρ \ C))
    exact (hbound.trans_eq hsplit |>.trans_lt measure_ball_lt_top).ne
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht) hle
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by linarith : 0 ≤ ρ + ρ),
    Measure.real_def,sub_neg_eq_add,two_mul] using hh

theorem planar_product_two_sided_density {B : Set Cover} {C : Set Plane}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {b : ℝ} (hb : 0 < b)
    (hden : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
      b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/16) :
    (b/2)*ρ^2 ≤ volume.real (C ∩ Metric.ball (0 : Plane) ρ) ∧
    (b/2)*ρ^2 ≤ volume.real (Cᶜ ∩ Metric.ball (0 : Plane) ρ) := by
  have hpc : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ Bᶜ ↔ z.2 ∈ Cᶜ) := by
    filter_upwards [hprod] with z hz ht hy
    exact not_congr (hz ht hy)
  have hd := hden ρ hρ (by linarith)
  have h1 := hd.1.trans (planar_product_ball_volume_le hB hC hn hprod hρ hρ1)
  have h2 := hd.2.trans (planar_product_ball_volume_le hB.compl hC.compl hn hpc hρ hρ1)
  have hfactor : 0 < 2*ρ :=
    pos_of_mul_pos_left ((mul_pos hb (pow_pos hρ 3)).trans_le h1) measureReal_nonneg
  constructor
  · apply (mul_le_mul_iff_right₀ hfactor).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hfactor).mp
    nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem minimizing_planar_product_halfplane_oai
    {B : Set Cover} {C : Set Plane} {n : Cover}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hn : ‖n‖ = 1)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x)
    {b : ℝ} (hb : 0 < b)
    (hden : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
      b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ)) :
    ∃ m : Plane, m ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (y ∈ C ↔ 0 < ⟪m,y⟫) := by
  have hd := planar_product_two_sided_density hB hC hn hprod hb hden
    (by norm_num : (0 : ℝ) < 1/16) (le_refl (1/16 : ℝ))
  have hp : 0 < (b/2)*(1/16 : ℝ)^2 := by positivity
  apply planar_cone_halfplane_of_single_transition hC hc
  · intro R w hw
    exact minimizing_planar_chart_single_transition hB hC (by norm_num : (0 : ℝ)<1/16)
      hmin hprod hc hK hbv heq hflux R hw
  · have hh : 0 < (volume (C ∩ Metric.ball (0 : Plane) (1/16))).toReal := hp.trans_le hd.1
    exact inter_comm C _ ▸ ENNReal.toReal_pos_iff.mp hh |>.1
  · have hh : 0 < (volume (Cᶜ ∩ Metric.ball (0 : Plane) (1/16))).toReal := hp.trans_le hd.2
    exact inter_comm Cᶜ _ ▸ ENNReal.toReal_pos_iff.mp hh |>.1

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.minimizing_planar_product_halfplane_oai := @OAI.CubicTorus.minimizing_planar_product_halfplane_oai
