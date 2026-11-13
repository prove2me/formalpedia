-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_crosscap_coordinate_strip
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:49:52.426368+00:00
-- url     : https://prove2.me/submissions/7c050666-2996-4f7c-8243-44f7e56790e9

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI007

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalInjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous map injective on a compact set and locally injective
near it is injective on some open neighborhood of the compact set. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem compact_local_injectivity {f : X → Y} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) (hi : K.InjOn f)
    (hloc : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U.InjOn f) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ V.InjOn f := by
  classical
  let S := {U : Set X // IsOpen U ∧ U.InjOn f}
  let A : Set (X × X) := {z | f z.1 ≠ f z.2} ∪ ⋃ U : S, (U: Set X) ×ˢ (U: Set X)
  have hA : IsOpen A := (isOpen_ne_fun (hf.comp continuous_fst)
    (hf.comp continuous_snd)).union (isOpen_iUnion fun U => U.property.1.prod U.property.1)
  have hKA : K ×ˢ K ⊆ A := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    by_cases hxy : f x = f y
    · have heq := hi hx hy hxy
      change x = y at heq
      subst y
      obtain ⟨U,hU,hxU,hUi⟩ := hloc x hx
      exact Or.inr (mem_iUnion.mpr ⟨⟨U,hU,hUi⟩,hxU,hxU⟩)
    · exact Or.inl hxy
  obtain ⟨U,V,hU,hV,hKU,hKV,hUV⟩ := generalized_tube_lemma hK hK hA hKA
  refine ⟨U ∩ V,hU.inter hV,subset_inter hKU hKV,?_⟩
  intro x hx y hy hxy
  rcases hUV (show (x,y) ∈ U ×ˢ V from ⟨hx.1,hy.2⟩) with hn | hn
  · exact False.elim (hn hxy)
  · obtain ⟨W,hxW,hyW⟩ := mem_iUnion.mp hn
    exact W.property.2 hxW hyW hxy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactLocalChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatible local charts near an injectively parameterized compact
set restrict to one actual open partial homeomorphism. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [Nonempty X]

theorem compact_local_chart_with_property (R : OpenPartialHomeomorph X Y → Prop) {f : X → Y} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) (hi : K.InjOn f)
    (hloc : ∀ x ∈ K, ∃ e : OpenPartialHomeomorph X Y,
      x ∈ e.source ∧ EqOn e f e.source ∧ R e) :
    ∃ e : OpenPartialHomeomorph X Y, K ⊆ e.source ∧ (e : X → Y) = f ∧
      ∀ x ∈ e.source, ∃ d : OpenPartialHomeomorph X Y, x ∈ d.source ∧ EqOn d f d.source ∧ R d := by
  classical
  let S := {e : OpenPartialHomeomorph X Y // EqOn e f e.source ∧ R e}
  let U : Set X := ⋃ e : S, e.val.source
  have hU : IsOpen U := isOpen_iUnion fun e => e.val.open_source
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨e,hxe,he,hR⟩ := hloc x hx
    exact mem_iUnion.mpr ⟨⟨e,he,hR⟩,hxe⟩
  obtain ⟨V,hV,hKV,hVI⟩ := compact_local_injectivity hf hK hi (by
    intro x hx
    obtain ⟨e,hxe,he,hR⟩ := hloc x hx
    refine ⟨e.source,e.open_source,hxe,?_⟩
    intro y hy z hz hyz
    exact e.injOn hy hz ((he hy).trans (hyz.trans (he hz).symm)))
  let W := V ∩ U
  have hW : IsOpen W := hV.inter hU
  have hKW : K ⊆ W := subset_inter hKV hKU
  have hWI : W.InjOn f := hVI.mono inter_subset_left
  have hopen : ∀ A : Set X, IsOpen A → A ⊆ W → IsOpen (f '' A) := by
    intro A hA hAW
    have heq : f '' A = ⋃ e : S, e.val '' (A ∩ e.val.source) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨e,hxe⟩ := mem_iUnion.mp (hAW hx).2
        exact mem_iUnion.mpr ⟨e,x,⟨hx,hxe⟩,e.property.1 hxe⟩
      · intro hy
        obtain ⟨e,x,⟨hx,hxe⟩,hxy⟩ := mem_iUnion.mp hy
        exact ⟨x,hx,(e.property.1 hxe).symm.trans hxy⟩
    rw [heq]
    exact isOpen_iUnion fun e => e.val.isOpen_image_of_subset_source
      (hA.inter e.val.open_source) inter_subset_right
  let p := hWI.toPartialEquiv f W
  have hpOpen : IsOpenMap (p.source.domRestrict p) := by
    change IsOpenMap (W.domRestrict f)
    intro A hA
    have himage := hopen (Subtype.val '' A) (hW.isOpenMap_subtype_val A hA)
      (by rintro x ⟨y,hy,rfl⟩; exact y.property)
    change IsOpen ((fun x : W => f x) '' A)
    simpa only [Set.image_image] using himage
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn hpOpen hW
  refine ⟨e,hKW,rfl,?_⟩
  intro x hx
  obtain ⟨d,hxd⟩ := mem_iUnion.mp hx.2
  exact ⟨d.val,hxd,d.property⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateInverseGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local inverse charts agree with the inverse of the assembled chart
near every common source point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M]

theorem coordinate_inverse_germ (e d : OpenPartialHomeomorph M Base)
    {y : Base} (hy : y ∈ e.target) (hx : e.symm y ∈ d.source)
    (heq : EqOn d e d.source) :
    y ∈ d.target ∧ e.symm =ᶠ[𝓝 y] d.symm := by
  have hvalue : d (e.symm y) = y := (heq hx).trans (e.right_inv hy)
  have hyd : y ∈ d.target := hvalue ▸ d.map_source hx
  refine ⟨hyd,?_⟩
  filter_upwards [e.open_target.mem_nhds hy,
    e.symm.continuousAt hy |>.eventually (d.open_source.mem_nhds hx)] with z hz hzd
  calc
    e.symm z = d.symm (d (e.symm z)) := (d.left_inv hzd).symm
    _ = d.symm (e (e.symm z)) := congrArg d.symm (heq hzd)
    _ = d.symm z := congrArg d.symm (e.right_inv hz)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneCurveFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A transverse linear coordinate for a regular curve in the surface plane. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeCurveLinear_apply (v w x : Base) :
    planeCurveLinear v w x = x 0 • v+x 1 • w := rfl

theorem exists_plane_curve_frame {w : Base} (hw : w ≠ 0) :
    ∃ v : Base, Function.Bijective (planeCurveLinear v w) := by
  obtain ⟨v,hli⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ℝ) (M := Base) (by simp [Base]) hw
  refine ⟨v,?_⟩
  have hz : ∀ x, planeCurveLinear v w x = 0 → x = 0 := by
    intro x hx
    have he : x 1 • w+x 0 • v = 0 := by
      rw [add_comm]
      exact hx
    obtain ⟨h1,h0⟩ := (LinearIndependent.pair_iff.mp hli) (x 1) (x 0) he
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hi : Function.Injective (planeCurveLinear v w) := by
    intro x y he
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,he,sub_self]
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (planeCurveLinear v w).toLinearMap) rfl).mp hi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PlaneCurveCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local coordinates straightening a regular curve in the surface plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeCurveTube_smooth {c : ℝ → Base} (hc : ContDiff ℝ ∞ c) (v : Base) :
    ContDiff ℝ ∞ (planeCurveTube c v) :=
  (hc.comp (contDiff_apply ℝ ℝ 1)).add ((contDiff_apply ℝ ℝ 0).smul contDiff_const)

lemma planeCurveTube_fderiv {c : ℝ → Base} (hc : ContDiff ℝ ∞ c) (v : Base) (t : ℝ) :
    fderiv ℝ (planeCurveTube c v) ![0,t] = planeCurveLinear v (deriv c t) := by
  have hC := ((hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasFDerivAt).comp ![0,t]
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) ![0,t])
  have hV := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) ![0,t]).smul_const v
  have hd := hC.add hV
  change HasFDerivAt (planeCurveTube c v) _ ![0,t] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro x
  simp [planeCurveLinear_apply,fderiv_eq_smul_deriv,add_comm]

theorem plane_curve_coordinates {c : ℝ → Base} (hc : ContDiff ℝ ∞ c)
    (t : ℝ) (ht : deriv c t ≠ 0) :
    ∃ (e : OpenPartialHomeomorph Base Base) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ s ∈ U, (![0,s] : Base) ∈ e.source ∧ e ![0,s] = c s := by
  obtain ⟨v,hbij⟩ := exists_plane_curve_frame ht
  let T := planeCurveTube c v
  have hT : ContDiff ℝ ∞ T := planeCurveTube_smooth hc v
  have hD : Function.Bijective (fderiv ℝ T ![0,t]) := by
    rw [planeCurveTube_fderiv hc]
    exact hbij
  let R : Base ≃L[ℝ] Base := ContinuousLinearEquiv.ofBijective (fderiv ℝ T ![0,t])
    (LinearMap.ker_eq_bot.mpr hD.1) (LinearMap.range_eq_top.mpr hD.2)
  have hd : HasFDerivAt T R.toContinuousLinearMap ![0,t] :=
    (hT.differentiable (by simp) _).hasFDerivAt
  let e₀ := hT.contDiffAt.toOpenPartialHomeomorph T hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W := {x : Base | IsUnit (fderiv ℝ T x)}
  have hW : IsOpen W := Units.isOpen.preimage (hT.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = T := rfl
  have htE : (![0,t] : Base) ∈ e.source :=
    ⟨hT.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
      ContinuousLinearMap.isUnit_iff_bijective.mpr hD⟩
  let U := (fun s => (![0,s] : Base)) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (by fun_prop)
  refine ⟨e,U,hU,htE,by simpa only [he] using hT,?_,?_⟩
  · intro y hy
    obtain ⟨u,hu⟩ := (e.map_target hy).2
    let D := ContinuousLinearEquiv.ofUnit u
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he]
      convert (hT.differentiable (by simp) _).hasFDerivAt using 1
      all_goals try with_reducible_and_instances rfl
      exact hu
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hT.contDiffAt)).contDiffWithinAt
  · intro s hs
    refine ⟨hs,?_⟩
    change planeCurveTube c v ![0,s] = c s
    simp [planeCurveTube]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RegularPlaneChart
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local smooth plane chart at an invertible derivative, retaining
its actual globally defined coordinate map. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem regular_plane_chart {F : Base → Base} (hF : ContDiff ℝ ∞ F)
    (p : Base) (hreg : Function.Bijective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (e : Base → Base) = F ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let R : Base ≃L[ℝ] Base := ContinuousLinearEquiv.ofBijective (fderiv ℝ F p)
    (LinearMap.ker_eq_bot.mpr hreg.1) (LinearMap.range_eq_top.mpr hreg.2)
  have hd : HasFDerivAt F R.toContinuousLinearMap p := (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  let e₀ := hF.contDiffAt.toOpenPartialHomeomorph F hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W : Set Base := {x | IsUnit (fderiv ℝ F x)}
  have hW : IsOpen W := Units.isOpen.preimage (hF.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  let e := e₀.restrOpen W hW
  have he : (e : Base → Base) = F := rfl
  refine ⟨e,⟨hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    ContinuousLinearMap.isUnit_iff_bijective.mpr hreg⟩,he,?_⟩
  intro y hy
  obtain ⟨u,hu⟩ := (e.map_target hy).2
  let D := ContinuousLinearEquiv.ofUnit u
  have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
    rw [he]
    convert (hF.differentiable (by simp) _).hasFDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    exact hu
  exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hF.contDiffAt)).contDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceLocalCoordinateMap
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth surface-to-plane map with invertible derivative is an
actual smooth local coordinate chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_local_coordinate_map {f : M → Base}
    (hf : ContMDiff planeModel 𝓘(ℝ,Base) ∞ f) (p : M)
    (hp : Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) f p)) :
    ∃ d : OpenPartialHomeomorph M Base, p ∈ d.source ∧ EqOn d f d.source ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target := by
  let c := chart p
  let a := c p
  have hpc : p ∈ c.source := by simpa only [c,chart_source] using mem_chart_source Plane p
  have ha : a ∈ c.target := c.map_source hpc
  have hlocal : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  obtain ⟨V,hV,haV,hVc,φ,hφ,hφEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) c.open_target (singleton_subset_iff.mpr ha) hlocal
  have haV' : a ∈ V := haV (mem_singleton _)
  have heφ : φ =ᶠ[𝓝 a] f ∘ c.symm := hφEq.eventuallyEq_of_mem (hV.mem_nhds haV')
  have hcp : c.symm a = p := c.left_inv hpc
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨(chart_symm_smooth p).mdifferentiableOn (by simp),(chart_smooth p).mdifferentiableOn (by simp)⟩
  have hφbij : Function.Bijective (fderiv ℝ φ a) := by
    rw [heφ.fderiv_eq,← mfderiv_eq_fderiv,mfderiv_comp a
      (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt ha)]
    exact (hcp.symm ▸ hp).comp (hcD.mfderiv_bijective ha)
  obtain ⟨e,hae,he,hei⟩ := regular_plane_chart hφ a hφbij
  let d₀ := c.trans e
  let O := c.source ∩ c ⁻¹' V
  have hO : IsOpen O := c.isOpen_inter_preimage hV
  let d := d₀.restrOpen O hO
  have hps : p ∈ d.source := ⟨⟨hpc,hae⟩,hpc,haV'⟩
  have hds₀ : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d₀ d₀.source :=
    (he ▸ hφ.contMDiff).comp_contMDiffOn ((chart_smooth p).mono inter_subset_left)
  have hdi₀ : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d₀.symm d₀.target :=
    (chart_symm_smooth p).comp (hei.contMDiffOn.mono inter_subset_left) (fun _ hx => hx.2)
  refine ⟨d,hps,?_,hds₀.mono (fun _ hx => hx.1),hdi₀.mono (fun _ hx => hx.1)⟩
  intro x hx
  change e (c x) = f x
  rw [he,hφEq hx.2.2]
  change f (c.symm (c x)) = f x
  rw [c.left_inv hx.1.1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceCompactCoordinateMap
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth coordinate map regular and injective on a compact surface
set is one smooth chart on a neighborhood of that set. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [Nonempty M]

theorem surface_compact_coordinate_map {f : M → Base}
    (hf : ContMDiff planeModel 𝓘(ℝ,Base) ∞ f) {K : Set M}
    (hK : IsCompact K) (hi : K.InjOn f)
    (hreg : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) f x)) :
    ∃ e : OpenPartialHomeomorph M Base, K ⊆ e.source ∧ (e : M → Base) = f ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ e.symm e.target := by
  obtain ⟨e,hKe,he,hcover⟩ := compact_local_chart_with_property
    (fun d : OpenPartialHomeomorph M Base => ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target)
    hf.continuous hK hi (by
      intro x hx
      obtain ⟨d,hd,heq,_,hdi⟩ := surface_local_coordinate_map hf x (hreg x hx)
      exact ⟨d,hd,heq,hdi⟩)
  refine ⟨e,hKe,he,?_⟩
  intro y hy
  obtain ⟨d,hd,heq,hdi⟩ := hcover (e.symm y) (e.map_target hy)
  have hde : EqOn d e d.source := by intro x hx; rw [he]; exact heq hx
  obtain ⟨hyd,hgerm⟩ := coordinate_inverse_germ e d hy hd hde
  exact ((hdi.contMDiffAt (d.open_target.mem_nhds hyd)).congr_of_eventuallyEq hgerm).contMDiffWithinAt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceCurveCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular smooth curve in the surface is the second coordinate
in actual smooth local surface coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_curve_coordinates {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ I) {t : ℝ} (ht : t ∈ I)
    (hreg : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ (c : OpenPartialHomeomorph M Base) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ U ⊆ I ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ∀ s ∈ U, γ s ∈ c.source ∧ c (γ s) = ![0,s] := by
  let p := γ t
  have hp : p ∈ (chart p).source := by
    simpa only [chart_source] using mem_chart_source Plane p
  let W := I ∩ γ ⁻¹' (chart p).source
  have hW : IsOpen W := hγ.continuousOn.isOpen_inter_preimage hI (chart p).open_source
  have htW : t ∈ W := ⟨ht,hp⟩
  have hγt := hγ.contMDiffAt (hI.mem_nhds ht)
  let φ : ℝ → Base := chart p ∘ γ
  have hφ : ContDiffOn ℝ ∞ φ W :=
    ((chart_smooth p).comp (hγ.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hφI : Function.Injective (fderiv ℝ φ t) := by
    have hc := ((chart_smooth p).contMDiffAt ((chart p).open_source.mem_nhds hp))
    rw [← mfderiv_eq_fderiv,mfderiv_comp t (hc.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hγt.mdifferentiableAt (by simp))]
    exact ((chart_mdifferentiable p).mfderiv_injective hp).comp hreg
  obtain ⟨V,hV,htV,hVW,F,hF,hFφ⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := t)) hW (singleton_subset_iff.mpr htW) hφ
  have hFe : F =ᶠ[𝓝 t] φ := hFφ.eventuallyEq_of_mem (hV.mem_nhds (htV (by simp)))
  have hFI : Function.Injective (fderiv ℝ F t) := by rw [hFe.fderiv_eq]; exact hφI
  have hFt : deriv F t ≠ 0 := by
    intro hz
    have he : fderiv ℝ F t 1 = fderiv ℝ F t 0 := by
      rw [fderiv_apply_one_eq_deriv,hz,map_zero]
    have hn := hFI he
    norm_num at hn
  obtain ⟨e,J,hJ,htJ,hes,hei,heaxis⟩ := plane_curve_coordinates hF t hFt
  let c := (chart p).trans e.symm
  have hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source := by
    exact hei.contMDiffOn.comp ((chart_smooth p).mono inter_subset_left) (fun _ hx => hx.2)
  have hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target := by
    exact (chart_symm_smooth p).comp hes.contMDiff.contMDiffOn (fun _ hx => hx.2)
  refine ⟨c,V ∩ J,hV.inter hJ,⟨htV (by simp),htJ⟩,
    inter_subset_left.trans (hVW.trans inter_subset_left),hcs,hci,?_⟩
  intro s hs
  have hsW := hVW hs.1
  have hmodel : e ![0,s] = chart p (γ s) := (heaxis s hs.2).2.trans (hFφ hs.1)
  have hsource : γ s ∈ c.source := by
    refine ⟨hsW.2,?_⟩
    change chart p (γ s) ∈ e.target
    rw [← hmodel]
    exact e.map_source (heaxis s hs.2).1
  refine ⟨hsource,?_⟩
  change e.symm (chart p (γ s)) = ![0,s]
  rw [← hmodel]
  exact e.left_inv (heaxis s hs.2).1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactArcLocalNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded compact arc admits source neighborhoods which capture
only parameters in any prescribed open parameter neighborhood. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
namespace SmoothCompactArc

theorem local_neighborhood (P : SmoothCompactArc I N) {t : ℝ}
    (ht : t ∈ Icc P.start P.finish) {U : Set ℝ} (hU : IsOpen U) (htU : t ∈ U)
    {O : Set N} (hO : IsOpen O) (htO : P.curve t ∈ O) :
    ∃ V : Set N, IsOpen V ∧ P.curve t ∈ V ∧ V ⊆ O ∧
      ∀ s ∈ Icc P.start P.finish, P.curve s ∈ V → s ∈ U := by
  let A := Icc P.start P.finish \ U
  have hA : IsCompact A := isCompact_Icc.diff hU
  have hAD : A ⊆ P.domain := fun _ hx => P.interval_subset hx.1
  have hK : IsCompact (P.curve '' A) := hA.image_of_continuousOn (P.smooth.continuousOn.mono hAD)
  have htK : P.curve t ∉ P.curve '' A := by
    rintro ⟨s,hs,he⟩
    have hst := P.injective hs.1 ht he
    exact hs.2 (hst ▸ htU)
  refine ⟨O \ (P.curve '' A),hO.sdiff hK.isClosed,⟨htO,htK⟩,sdiff_subset,?_⟩
  intro s hs hsV
  by_contra hn
  exact hsV.2 ⟨s,⟨hs,hn⟩,rfl⟩

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcParameterExtension
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The parameter of a compact embedded regular source arc extends to
an actual globally smooth real function on the surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem smooth_arc_parameter_extension (P : SmoothCompactArc planeModel M) :
    ∃ F : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ F ∧
      ∀ t ∈ Icc P.start P.finish, F (P.curve t) = t := by
  let K := P.curve '' Icc P.start P.finish
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (P.smooth.continuousOn.mono P.interval_subset)
  let C : M → Set ℝ := fun x => {v | ∀ t ∈ Icc P.start P.finish, P.curve t = x → v = t}
  have hC : ∀ x, Convex ℝ (C x) := by
    intro x a ha b hb α β hα hβ hsum t ht he
    rw [ha t ht he,hb t ht he]
    simp only [smul_eq_mul,← add_mul,hsum,one_mul]
  have hloc : ∀ x : M, ∃ V ∈ 𝓝 x, ∃ g : M → ℝ,
      ContMDiffOn planeModel 𝓘(ℝ) ∞ g V ∧ ∀ y ∈ V, g y ∈ C y := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨t,ht,rfl⟩ := hx
      obtain ⟨c,U,hU,htU,_,hcs,_,hcoords⟩ := surface_curve_coordinates
        P.domain_open P.smooth (P.interval_subset ht) (P.regular t (P.interval_subset ht))
      obtain ⟨V,hV,htV,hVc,hVU⟩ := P.local_neighborhood ht hU htU c.open_source (hcoords t htU).1
      refine ⟨V,hV.mem_nhds htV,fun y => c y 1,?_,?_⟩
      · exact (contDiff_apply ℝ ℝ (1:Fin 2)).contMDiff.comp_contMDiffOn (hcs.mono hVc)
      · intro y hy u hu he
        have huV : P.curve u ∈ V := he ▸ hy
        have hh := (hcoords u (hVU u hu huV)).2
        change c y 1 = u
        rw [← he,hh]
        simp
    · refine ⟨Kᶜ,hK.isClosed.isOpen_compl.mem_nhds hx,fun _ => 0,contMDiffOn_const,?_⟩
      intro y hy t ht he
      exact False.elim (hy ⟨t,ht,he⟩)
  obtain ⟨F,hF⟩ := exists_contMDiffMap_forall_mem_convex_of_local planeModel hC hloc
  exact ⟨F,F.contMDiff,fun t ht => hF (P.curve t) t ht rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactSurfaceSmoothExtension
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a smooth function from an open surface neighborhood of a
compact set, retaining its actual germ on a smaller neighborhood. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_surface_smooth_extension {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : M → E}
    (hf : ContMDiffOn planeModel 𝓘(ℝ,E) ∞ f U) :
    ∃ (g : M → E) (V : Set M), ContMDiff planeModel 𝓘(ℝ,E) ∞ g ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn g f V := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace Plane M
  obtain ⟨V,hV,hKV,hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  let C : M → Set E := fun x => if x ∈ closure V then {f x} else univ
  have hC : ∀ x, Convex ℝ (C x) := by
    intro x
    dsimp only [C]
    split_ifs
    · exact convex_singleton _
    · exact convex_univ
  have hloc : ∀ x : M, ∃ W ∈ 𝓝 x, ∃ q : M → E,
      ContMDiffOn planeModel 𝓘(ℝ,E) ∞ q W ∧ ∀ y ∈ W, q y ∈ C y := by
    intro x
    by_cases hx : x ∈ closure V
    · refine ⟨U,hU.mem_nhds (hVU hx),f,hf,?_⟩
      intro y hy
      dsimp only [C]
      split_ifs <;> simp
    · refine ⟨(closure V)ᶜ,isClosed_closure.isOpen_compl.mem_nhds hx,fun _ => 0,contMDiffOn_const,?_⟩
      intro y hy
      have hy' : y ∉ closure V := hy
      simp [C,hy']
  obtain ⟨g,hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local planeModel hC hloc
  refine ⟨g,V,g.contMDiff,hV,hKV,subset_closure.trans hVU,?_⟩
  intro x hx
  have h := hg x
  simpa [C,subset_closure hx] using h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_StandardCrosscapDerivative
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The standard umbrella has one singular point and a transverse double ray. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleSpace
lemma standardCrosscap_hasFDerivAt (x : Base) :
    HasFDerivAt standardCrosscap (standardCrosscapDerivative x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have h := (((h0.mul h1).smul_const ((![1,0],0) : Base × ℝ)).add
    ((h1.pow 2).smul_const ((![0,1],0) : Base × ℝ))).add
      (h0.smul_const ((0,1) : Base × ℝ))
  have he : (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
      (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) =
      standardCrosscap := by
    funext y
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  change HasFDerivAt (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
    (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) _ x at h
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [standardCrosscapDerivative]
    ring
  · simp [standardCrosscapDerivative]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The kernel axis of an actual crosscap chart gives a smooth regular
source curve through the singular point, even though its image velocity vanishes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscapAxis_apply (t : ℝ) : crosscapAxis t = ![0,t] := by
  ext i
  fin_cases i <;> rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TriangularTimeCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing the longitudinal coordinate by a smooth function with
unit axial derivative is an actual local plane diffeomorphism. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma timeCoordinateMap_smooth {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (timeCoordinateMap φ) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [timeCoordinateMap] using contDiff_apply ℝ ℝ (0:Fin 2)
  · simpa [timeCoordinateMap] using hφ

lemma timeCoordinateMap_regular {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : Base) (hvertical : fderiv ℝ φ p (crosscapAxis 1) = 1) :
    Function.Bijective (fderiv ℝ (timeCoordinateMap φ) p) := by
  let D : Base →L[ℝ] Base := ContinuousLinearMap.pi ![ContinuousLinearMap.proj (0:Fin 2),fderiv ℝ φ p]
  have hD : HasFDerivAt (timeCoordinateMap φ) D p := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasFDerivAt_apply (𝕜 := ℝ) 0 p
    · exact (hφ.differentiable (by simp) p).hasFDerivAt
  rw [hD.fderiv]
  have hi : Function.Injective D := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro v hv
      have hv0 : v 0 = 0 := congrFun hv 0
      have hvφ : fderiv ℝ φ p v = 0 := congrFun hv 1
      have he : v = (v 1) • crosscapAxis 1 := by
        ext i
        fin_cases i <;> simp [crosscapAxis_apply,hv0]
      have hv1 : v 1 = 0 := by
        rw [he,map_smul,hvertical] at hvφ
        simpa only [smul_eq_mul,mul_one] using hvφ
      show v = 0
      ext i
      fin_cases i
      · exact hv0
      · exact hv1
    · exact bot_le
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := D.toLinearMap) rfl).mp hi⟩

theorem triangular_time_coordinates {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (p : Base) (hvertical : fderiv ℝ φ p (crosscapAxis 1) = 1) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (e : Base → Base) = timeCoordinateMap φ ∧ ContDiffOn ℝ ∞ e.symm e.target :=
  regular_plane_chart (timeCoordinateMap_smooth hφ) p (timeCoordinateMap_regular hφ p hvertical)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcTimeDerivative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The extended longitudinal parameter has derivative one on the arc,
including its endpoints, and is a submersion there. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem smooth_arc_time_derivative (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ t ∈ Icc P.start P.finish, F (P.curve t) = t)
    {t : ℝ} (ht : t ∈ Icc P.start P.finish) :
    deriv (F ∘ P.curve) t = 1 ∧
      mfderiv planeModel 𝓘(ℝ) F (P.curve t)
        (mfderiv 𝓘(ℝ) planeModel P.curve t 1) = 1 ∧
      Function.Surjective (mfderiv planeModel 𝓘(ℝ) F (P.curve t)) := by
  have hPt := P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht))
  have hcomp : DifferentiableAt ℝ (F ∘ P.curve) t :=
    ((hF.contMDiffAt.comp t hPt).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hwithin : HasDerivWithinAt (F ∘ P.curve) 1 (Icc P.start P.finish) t :=
    (hasDerivWithinAt_id t (Icc P.start P.finish)).congr_of_mem hFP ht
  have hderiv : deriv (F ∘ P.curve) t = 1 :=
    ((uniqueDiffOn_Icc P.start_lt_finish) t ht).eq_deriv (Icc P.start P.finish)
      hcomp.hasDerivAt.hasDerivWithinAt hwithin
  have heval : mfderiv planeModel 𝓘(ℝ) F (P.curve t)
      (mfderiv 𝓘(ℝ) planeModel P.curve t 1) = 1 := by
    rw [← ContinuousLinearMap.comp_apply,← mfderiv_comp t
      (hF.mdifferentiable (by simp) (P.curve t)) (hPt.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    change fderiv ℝ (F ∘ P.curve) t 1 = 1
    rw [fderiv_apply_one_eq_deriv,hderiv]
  refine ⟨hderiv,heval,?_⟩
  intro y
  change ℝ at y
  refine ⟨y • mfderiv 𝓘(ℝ) planeModel P.curve t 1,?_⟩
  rw [map_smul,heval]
  change y * (1:ℝ) = y
  exact mul_one y

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceArcTimeCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local surface coordinates with the fixed global arc-time function
as the second coordinate and with the arc as the zero transverse axis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_arc_time_coordinates (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ s ∈ Icc P.start P.finish, F (P.curve s) = s)
    {t : ℝ} (ht : t ∈ Icc P.start P.finish) :
    ∃ (d : OpenPartialHomeomorph M Base) (J : Set ℝ),
      IsOpen J ∧ t ∈ J ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target ∧
      (∀ x ∈ d.source, d x 1 = F x) ∧
      ∀ s ∈ J, P.curve s ∈ d.source ∧ d (P.curve s) = ![0,F (P.curve s)] := by
  obtain ⟨c,U,hU,htU,_,hcs,hci,hcoords⟩ := surface_curve_coordinates
    P.domain_open P.smooth (P.interval_subset ht) (P.regular t (P.interval_subset ht))
  have hct : c (P.curve t) = crosscapAxis t := (hcoords t htU).2.trans (crosscapAxis_apply t).symm
  have htc : crosscapAxis t ∈ c.target := hct ▸ c.map_source (hcoords t htU).1
  have hφlocal : ContDiffOn ℝ ∞ (F ∘ c.symm) c.target :=
    (hF.comp_contMDiffOn hci).contDiffOn
  obtain ⟨V,hV,htV,hVc,φ,hφ,hφEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := crosscapAxis t)) c.open_target
    (singleton_subset_iff.mpr htc) hφlocal
  have htV' : crosscapAxis t ∈ V := htV (mem_singleton _)
  have hφaxis : φ ∘ crosscapAxis =ᶠ[𝓝 t] F ∘ P.curve := by
    filter_upwards [hU.mem_nhds htU,crosscapAxis.continuous.continuousAt.eventually (hV.mem_nhds htV')] with s hsU hsV
    change φ (crosscapAxis s) = F (P.curve s)
    rw [hφEq hsV]
    change F (c.symm (crosscapAxis s)) = F (P.curve s)
    rw [crosscapAxis_apply,← (hcoords s hsU).2,c.left_inv (hcoords s hsU).1]
  have hdaxis := (hφ.differentiable (by simp) (crosscapAxis t)).hasFDerivAt.comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt
  have hvertical : fderiv ℝ φ (crosscapAxis t) (crosscapAxis 1) = 1 := by
    rw [← hdaxis.deriv,hφaxis.deriv_eq]
    exact (smooth_arc_time_derivative P hF hFP ht).1
  obtain ⟨e,hte,he,hei⟩ := triangular_time_coordinates hφ (crosscapAxis t) hvertical
  have hes : ContDiff ℝ ∞ e := he ▸ timeCoordinateMap_smooth hφ
  let d₀ := c.trans e
  let O := c.source ∩ c ⁻¹' V
  have hO : IsOpen O := c.isOpen_inter_preimage hV
  let d := d₀.restrOpen O hO
  have hds : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source :=
    (hes.contMDiff.comp_contMDiffOn (hcs.mono inter_subset_left)).mono (fun _ hx => hx.1)
  have hdi₀ : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d₀.symm d₀.target := by
    apply hci.comp (hei.contMDiffOn.mono inter_subset_left)
    intro x hx
    exact hx.2
  have hdi : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target :=
    hdi₀.mono (fun _ hx => hx.1)
  have htd : P.curve t ∈ d.source := by
    refine ⟨⟨(hcoords t htU).1,?_⟩,(hcoords t htU).1,?_⟩
    · change c (P.curve t) ∈ e.source
      rwa [hct]
    · change c (P.curve t) ∈ V
      rwa [hct]
  have hsecond : ∀ x ∈ d.source, d x 1 = F x := by
    intro x hx
    change e (c x) 1 = F x
    rw [he]
    change φ (c x) = F x
    rw [hφEq hx.2.2]
    change F (c.symm (c x)) = F x
    rw [c.left_inv hx.1.1]
  let J := U ∩ (P.domain ∩ P.curve ⁻¹' d.source)
  have hJ : IsOpen J := hU.inter
    (P.smooth.continuousOn.isOpen_inter_preimage P.domain_open d.open_source)
  refine ⟨d,J,hJ,⟨htU,P.interval_subset ht,htd⟩,hds,hdi,hsecond,?_⟩
  intro s hs
  refine ⟨hs.2.2,?_⟩
  ext i
  fin_cases i
  · change e (c (P.curve s)) 0 = 0
    rw [he]
    change c (P.curve s) 0 = 0
    rw [(hcoords s hs.1).2]
    rfl
  · simpa using hsecond (P.curve s) hs.2.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactTimeChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular coordinate map on a compact set gives a time chart,
retaining its prescribed longitudinal coordinate on the whole source. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] [Nonempty M]

theorem compact_time_chart {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : M → Base} {F : M → ℝ}
    (hf : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ f U)
    (htime : ∀ x ∈ U, f x 1 = F x) (hi : K.InjOn f)
    (hreg : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) f x)) :
    ∃ c : SurfaceTimeChart F, K ⊆ c.coord.source ∧ EqOn c.coord f c.coord.source := by
  obtain ⟨g,V,hg,hV,hKV,hVU,heq⟩ := compact_surface_smooth_extension hK hU hKU hf
  have hgi : K.InjOn g := by
    intro x hx y hy hxy
    apply hi hx hy
    simpa only [← heq (hKV hx),← heq (hKV hy)] using hxy
  have hgr : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) g x) := by
    intro x hx
    rw [(heq.eventuallyEq_of_mem (hV.mem_nhds (hKV hx))).mfderiv_eq]
    exact hreg x hx
  obtain ⟨d,hKd,hd,hdi⟩ := surface_compact_coordinate_map hg hK hgi hgr
  let e := d.restrOpen V hV
  have hes : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ e e.source := by
    change ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d (d.source ∩ V)
    rw [hd]
    exact hg.contMDiffOn
  refine ⟨⟨e,hes,hdi.mono (fun _ hx => hx.1),?_⟩,?_,?_⟩
  · intro x hx
    change d x 1 = F x
    rw [hd,heq hx.2]
    exact htime x (hVU hx.2)
  · intro x hx
    exact ⟨hKd hx,hKV hx⟩
  · intro x hx
    change d x = f x
    rw [hd]
    exact heq hx.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TimeCoordinateTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two actual charts using the same longitudinal function have a
nonzero transverse transition derivative and preserve the time differential. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem time_coordinate_transition (c d : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (hds : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target)
    {F : M → ℝ} (hcF : ∀ x ∈ c.source, c x 1 = F x)
    (hdF : ∀ x ∈ d.source, d x 1 = F x)
    {x : M} (hxc : x ∈ c.source) (hxd : x ∈ d.source) :
    let L := fderiv ℝ (d ∘ c.symm) (c x)
    Function.Bijective L ∧ (∀ v : Base, L v 1 = v 1) ∧ L ![1,0] 0 ≠ 0 := by
  let L := fderiv ℝ (d ∘ c.symm) (c x)
  have hct := c.map_source hxc
  have hcx := c.left_inv hxc
  have hc' := hci.contMDiffAt (c.open_target.mem_nhds hct)
  have hd' : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d (c.symm (c x)) :=
    hcx.symm ▸ hds.contMDiffAt (d.open_source.mem_nhds hxd)
  have hcomp : ContDiffAt ℝ ∞ (d ∘ c.symm) (c x) := (hd'.comp (c x) hc').contDiffAt
  have hcDiff : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hcs.mdifferentiableOn (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)⟩
  have hdDiff : d.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨hds.mdifferentiableOn (by simp),hdi.mdifferentiableOn (by simp)⟩
  have hL : Function.Bijective L := by
    dsimp [L]
    rw [← mfderiv_eq_fderiv,mfderiv_comp (c x) (hd'.mdifferentiableAt (by simp))
      (hc'.mdifferentiableAt (by simp))]
    exact (hdDiff.mfderiv_bijective (hcx.symm ▸ hxd)).comp (hcDiff.mfderiv_bijective hct)
  have hnear : ∀ᶠ y in 𝓝 (c x), y ∈ c.target ∧ c.symm y ∈ d.source := by
    filter_upwards [c.open_target.mem_nhds hct,
      c.symm.continuousAt hct |>.eventually (d.open_source.mem_nhds (hcx.symm ▸ hxd))] with y hy hz
    exact ⟨hy,hz⟩
  have he : (fun y : Base => d (c.symm y) 1) =ᶠ[𝓝 (c x)] fun y => y 1 := by
    filter_upwards [hnear] with y hy
    rw [hdF _ hy.2,← hcF _ (c.map_target hy.1),c.right_inv hy.1]
  have hproj := (ContinuousLinearMap.proj (1:Fin 2) : Base →L[ℝ] ℝ).hasFDerivAt.comp
    (c x) (hcomp.differentiableAt (by simp)).hasFDerivAt
  have hsecond : ∀ v : Base, L v 1 = v 1 := by
    intro v
    have heq := congrArg (fun A : Base →L[ℝ] ℝ => A v) (hproj.fderiv.symm.trans he.fderiv_eq)
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (1:Fin 2) (c x)).fderiv] at heq
    exact heq
  refine ⟨hL,hsecond,?_⟩
  intro hz
  have hz' : L (![1,0] : Base) = 0 := by
    ext i
    fin_cases i
    · exact hz
    · simpa using hsecond ![1,0]
  have hv := hL.1 (hz'.trans (map_zero L).symm)
  have hv0 := congrFun hv 0
  norm_num at hv0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseReflection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing only the transverse coordinate keeps the global arc time
and all axis points unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma transverseReflection_apply (x : Base) : transverseReflection x = ![-x 0,x 1] := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] {F : M → ℝ}
namespace SurfaceTimeChart

omit [IsManifold planeModel ∞ M] in
lemma reflect_axis (c : SurfaceTimeChart F) {x : M} {t : ℝ}
    (hx : c.coord x = ![0,t]) : c.reflect.coord x = ![0,t] := by
  change transverseReflection (c.coord x) = ![0,t]
  rw [hx,transverseReflection_apply]
  simp

omit [IsManifold planeModel ∞ M] in
lemma reflect_transition (c d : SurfaceTimeChart F) (x : M)
    (h : DifferentiableAt ℝ (d.coord ∘ c.coord.symm) (c.coord x)) :
    fderiv ℝ (d.reflect.coord ∘ c.coord.symm) (c.coord x) =
      transverseReflection.toContinuousLinearMap.comp
        (fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x)) := by
  change fderiv ℝ (transverseReflection ∘ (d.coord ∘ c.coord.symm)) (c.coord x) = _
  exact (transverseReflection.hasFDerivAt.comp (c.coord x) h.hasFDerivAt).fderiv

end SurfaceTimeChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OrientedTimeTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transverse orientation of the next time chart can always be
chosen to give a positive derivative at the attachment point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

namespace SurfaceTimeChart

theorem positive_transition (c d : SurfaceTimeChart F) (x : M)
    (hxc : x ∈ c.coord.source) (hxd : x ∈ d.coord.source) :
    ∃ e : SurfaceTimeChart F, e.coord.source = d.coord.source ∧
      (∀ y t, d.coord y = ![0,t] → e.coord y = ![0,t]) ∧
      0 < fderiv ℝ (e.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0 := by
  have hn := (time_coordinate_transition c.coord d.coord c.smooth c.inverse_smooth
    d.smooth d.inverse_smooth c.time d.time hxc hxd).2.2
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hci := c.inverse_smooth.contMDiffAt
      (c.coord.open_target.mem_nhds (c.coord.map_source hxc))
    have hds : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d.coord (c.coord.symm (c.coord x)) :=
      (c.coord.left_inv hxc).symm ▸ d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hxd)
    have hd : DifferentiableAt ℝ (d.coord ∘ c.coord.symm) (c.coord x) :=
      (hds.comp (c.coord x) hci).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    refine ⟨d.reflect,rfl,fun y t h => d.reflect_axis h,?_⟩
    rw [reflect_transition c d x hd]
    change 0 < -(fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0)
    exact neg_pos.mpr hneg
  · exact ⟨d,rfl,fun _ _ h => h,hpos⟩

end SurfaceTimeChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveTimeOverlap
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the actual transverse transition persists on an open
surface neighborhood of the chosen attachment point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}
namespace SurfaceTimeChart

theorem positive_overlap (c d : SurfaceTimeChart F) (x : M)
    (hxc : x ∈ c.coord.source) (hxd : x ∈ d.coord.source)
    (hpos : 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ c.coord.source ∩ d.coord.source ∧
      ∀ y ∈ U, 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord y) ![1,0] 0 := by
  have hc := c.inverse_smooth.contMDiffAt
    (c.coord.open_target.mem_nhds (c.coord.map_source hxc))
  have hd : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d.coord (c.coord.symm (c.coord x)) :=
    (c.coord.left_inv hxc).symm ▸ d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hxd)
  have hD := (hd.comp (c.coord x) hc).contDiffAt.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hv : ContinuousAt (fun z : Base => fderiv ℝ (d.coord ∘ c.coord.symm) z (![1,0] : Base) 0)
      (c.coord x) := (continuous_apply (0:Fin 2)).continuousAt.comp
        (hD.clm_apply continuousAt_const)
  have hvalue : ∀ᶠ y in 𝓝 x, 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord y) ![1,0] 0 :=
    (hv.comp (c.coord.continuousAt hxc)).eventually (isOpen_Ioi.mem_nhds hpos)
  have hall : ∀ᶠ y in 𝓝 x, y ∈ c.coord.source ∧ y ∈ d.coord.source ∧
      0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord y) ![1,0] 0 := by
    filter_upwards [c.coord.open_source.mem_nhds hxc,d.coord.open_source.mem_nhds hxd,hvalue] with y hyc hyd hy
    exact ⟨hyc,hyd,hy⟩
  obtain ⟨U,hU,hUopen,hxU⟩ := eventually_nhds_iff.mp hall
  exact ⟨U,hUopen,hxU,fun y hy => ⟨(hU y hy).1,(hU y hy).2.1⟩,
    fun y hy => (hU y hy).2.2⟩

end SurfaceTimeChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveTimeLinearBlend
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive transverse coordinate changes can be blended while keeping
the common time differential and an invertible derivative. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma time_linear_bijective (L : Base →L[ℝ] Base)
    (hsecond : ∀ v, L v 1 = v 1) (hfirst : L ![1,0] 0 ≠ 0) : Function.Bijective L := by
  have hi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro v hv
      have hv1 : v 1 = 0 := (hsecond v).symm.trans (congrFun hv 1)
      have he : v = (v 0) • (![1,0] : Base) := by
        ext i
        fin_cases i <;> simp [hv1]
      have hv0 : v 0 = 0 := by
        have hh := congrFun hv 0
        rw [he,map_smul] at hh
        change v 0 * L ![1,0] 0 = 0 at hh
        exact (mul_eq_zero.mp hh).resolve_right hfirst
      show v = 0
      ext i
      fin_cases i
      · exact hv0
      · exact hv1
    · exact bot_le
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) rfl).mp hi⟩

theorem positive_time_linear_blend (L : Base →L[ℝ] Base)
    (hsecond : ∀ v, L v 1 = v 1) (hfirst : 0 < L ![1,0] 0)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    Function.Bijective ((1-θ) • ContinuousLinearMap.id ℝ Base + θ • L) := by
  let D := (1-θ) • ContinuousLinearMap.id ℝ Base + θ • L
  apply time_linear_bijective D
  · intro v
    change (1-θ)*v 1+θ*(L v 1) = v 1
    rw [hsecond]
    ring
  · have ha : 0 < 1-θ+θ*(L ![1,0] 0) := by
      by_cases hzero : θ = 0
      · rw [hzero]; norm_num
      · have hpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hzero)
        have hprod := mul_pos hpos hfirst
        linarith [hθ.2]
    have he : D ![1,0] 0 = 1-θ+θ*(L ![1,0] 0) := by
      change (1-θ)*1+θ*(L ![1,0] 0) = _
      ring
    rw [he]
    exact ne_of_gt ha

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TimeCoordinateBlend
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonlinear blend of two agreeing time coordinates has
an invertible derivative when their transverse transition is positive. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma timeCoordinateBlend_fderiv {g : Base → Base} {χ : Base → ℝ} {p : Base}
    (hg : DifferentiableAt ℝ g p) (hχ : DifferentiableAt ℝ χ p) (hpoint : g p = p) :
    fderiv ℝ (timeCoordinateBlend g χ) p =
      (1-χ p) • ContinuousLinearMap.id ℝ Base + χ p • fderiv ℝ g p := by
  have hD := (((hasFDerivAt_const (1:ℝ) p).sub hχ.hasFDerivAt).smul (hasFDerivAt_id p)).add
    (hχ.hasFDerivAt.smul hg.hasFDerivAt)
  change HasFDerivAt (timeCoordinateBlend g χ) _ p at hD
  rw [hD.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  ext i
  simp [hpoint,smul_eq_mul]
  ring

theorem timeCoordinateBlend_regular {g : Base → Base} {χ : Base → ℝ} {p : Base}
    (hg : DifferentiableAt ℝ g p) (hχ : DifferentiableAt ℝ χ p) (hpoint : g p = p)
    (hsecond : ∀ v, fderiv ℝ g p v 1 = v 1)
    (hfirst : 0 < fderiv ℝ g p ![1,0] 0) (hweight : χ p ∈ Icc (0:ℝ) 1) :
    Function.Bijective (fderiv ℝ (timeCoordinateBlend g χ) p) := by
  rw [timeCoordinateBlend_fderiv hg hχ hpoint]
  exact positive_time_linear_blend _ hsecond hfirst hweight

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceTimeBlend
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual blend of surface time charts is regular at every common
axis point where their transverse transition is positive. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

lemma surfaceTimeBlend_smooth (c d : SurfaceTimeChart F) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F) :
    ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ (surfaceTimeBlend c d χ)
      (c.coord.source ∩ d.coord.source) := by
  have hw := hχ.contMDiff.comp hF
  exact ((contMDiff_const.sub hw).contMDiffOn.smul (c.smooth.mono inter_subset_left)).add
    (hw.contMDiffOn.smul (d.smooth.mono inter_subset_right))

theorem surfaceTimeBlend_regular (c d : SurfaceTimeChart F) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (x : M) (hxc : x ∈ c.coord.source) (hxd : x ∈ d.coord.source)
    (hagree : d.coord x = c.coord x)
    (hpos : 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0)
    (hw : χ (F x) ∈ Icc (0:ℝ) 1) :
    Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) (surfaceTimeBlend c d χ) x) := by
  let H := surfaceTimeBlend c d χ
  let g : Base → Base := d.coord ∘ c.coord.symm
  let η : Base → ℝ := fun z => χ (z 1)
  have hci := c.inverse_smooth.contMDiffAt (c.coord.open_target.mem_nhds (c.coord.map_source hxc))
  have hds : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d.coord (c.coord.symm (c.coord x)) :=
    (c.coord.left_inv hxc).symm ▸ d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hxd)
  have hgd : DifferentiableAt ℝ g (c.coord x) := (hds.comp (c.coord x) hci).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hη : ContDiff ℝ ∞ η := hχ.comp (contDiff_apply ℝ ℝ (1:Fin 2))
  have hpoint : g (c.coord x) = c.coord x := by dsimp [g]; rw [c.coord.left_inv hxc,hagree]
  have hηweight : η (c.coord x) ∈ Icc (0:ℝ) 1 := by
    change χ (c.coord x 1) ∈ _
    rwa [c.time x hxc]
  have hB := timeCoordinateBlend_regular hgd (hη.differentiable (by simp) _)
    hpoint (time_coordinate_transition c.coord d.coord c.smooth c.inverse_smooth
      d.smooth d.inverse_smooth c.time d.time hxc hxd).2.1 hpos hηweight
  have heq : H ∘ c.coord.symm =ᶠ[𝓝 (c.coord x)] timeCoordinateBlend g η := by
    filter_upwards [c.coord.open_target.mem_nhds (c.coord.map_source hxc)] with z hz
    change (1-χ (F (c.coord.symm z))) • c.coord (c.coord.symm z) +
      χ (F (c.coord.symm z)) • d.coord (c.coord.symm z) = _
    rw [← c.time _ (c.coord.map_target hz),c.coord.right_inv hz]
    rfl
  have hHcx : Function.Bijective (fderiv ℝ (H ∘ c.coord.symm) (c.coord x)) := by
    rw [heq.fderiv_eq]
    exact hB
  have hH : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ H x :=
    (surfaceTimeBlend_smooth c d hχ hF).contMDiffAt
      ((c.coord.open_source.inter d.coord.open_source).mem_nhds ⟨hxc,hxd⟩)
  have hHc : ContMDiffAt 𝓘(ℝ,Base) 𝓘(ℝ,Base) ∞ (H ∘ c.coord.symm) (c.coord x) :=
    ((c.coord.left_inv hxc).symm ▸ hH).comp (c.coord x) hci
  have hrestore : H =ᶠ[𝓝 x] (H ∘ c.coord.symm) ∘ c.coord := by
    filter_upwards [c.coord.open_source.mem_nhds hxc] with y hy
    change H y = H (c.coord.symm (c.coord y))
    rw [c.coord.left_inv hy]
  have hcD : c.coord.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  change Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) H x)
  rw [hrestore.mfderiv_eq,mfderiv_comp x (hHc.mdifferentiableAt (by simp))
    (hcD.mdifferentiableAt hxc),mfderiv_eq_fderiv]
  exact hHcx.comp (hcD.mfderiv_bijective hxc)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceBlendGerms
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior germs of the actual chart blend and an explicit time cutoff. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

lemma surfaceTimeBlend_zero (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M}
    (hx : χ (F x) = 0) : surfaceTimeBlend c d χ x = c.coord x := by
  simp [surfaceTimeBlend,hx]

lemma surfaceTimeBlend_one (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M}
    (hx : χ (F x) = 1) : surfaceTimeBlend c d χ x = d.coord x := by
  simp [surfaceTimeBlend,hx]

lemma surfaceTimeBlend_axis (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M} {t : ℝ}
    (hc : c.coord x = ![0,t]) (hd : d.coord x = ![0,t]) :
    surfaceTimeBlend c d χ x = ![0,t] := by
  simp only [surfaceTimeBlend,hc,hd]
  rw [← add_smul]
  simp

lemma surfaceTimeBlend_time (c d : SurfaceTimeChart F) {χ : ℝ → ℝ} {x : M}
    (hc : x ∈ c.coord.source) (hd : x ∈ d.coord.source) :
    surfaceTimeBlend c d χ x 1 = F x := by
  change (1-χ (F x)) * c.coord x 1 + χ (F x) * d.coord x 1 = F x
  rw [c.time x hc,d.time x hd]
  ring

lemma timeCutoff_smooth (l r : ℝ) : ContDiff ℝ ∞ (timeCutoff l r) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma timeCutoff_mem (l r t : ℝ) : timeCutoff l r t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma timeCutoff_zero {l r t : ℝ} (hlr : l < r) (ht : t ≤ l) :
    timeCutoff l r t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hlr).le

lemma timeCutoff_one {l r t : ℝ} (hlr : l < r) (ht : r ≤ t) :
    timeCutoff l r t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hlr)).mpr
  linarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceBlendExterior
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar cutoff gives exact smooth chart germs outside the transition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

lemma surfaceTimeBlend_left_germ (c d : SurfaceTimeChart F)
    (hF : Continuous F) {l r : ℝ} (hlr : l < r) {x : M} (hx : F x < l) :
    surfaceTimeBlend c d (timeCutoff l r) =ᶠ[𝓝 x] c.coord := by
  filter_upwards [hF.continuousAt.eventually (isOpen_Iio.mem_nhds hx)] with y hy
  exact surfaceTimeBlend_zero c d (timeCutoff_zero hlr hy.le)

lemma surfaceTimeBlend_right_germ (c d : SurfaceTimeChart F)
    (hF : Continuous F) {l r : ℝ} (hlr : l < r) {x : M} (hx : r < F x) :
    surfaceTimeBlend c d (timeCutoff l r) =ᶠ[𝓝 x] d.coord := by
  filter_upwards [hF.continuousAt.eventually (isOpen_Ioi.mem_nhds hx)] with y hy
  exact surfaceTimeBlend_one c d (timeCutoff_one hlr hy.le)

lemma SurfaceTimeChart.regular (c : SurfaceTimeChart F) {x : M}
    (hx : x ∈ c.coord.source) :
    Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) c.coord x) := by
  have hD : c.coord.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  exact hD.mfderiv_bijective hx

lemma straddling_compact_interval {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {V : Set ℝ} (hV : V ∈ 𝓝 b) :
    ∃ l r, a < l ∧ l < b ∧ b < r ∧ r < c ∧ Icc l r ⊆ V := by
  obtain ⟨s,t,hbst,hst⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem hV (Ioo_mem_nhds hab hbc))
  have hs : a < b := hab
  have hsa : a < t := (hst ⟨hbst.1,hbst.2⟩).2.1.trans hbst.2
  let l := (max a s + b)/2
  let r := (b + min c t)/2
  have hmax : max a s < b := max_lt hab hbst.1
  have hmin : b < min c t := lt_min hbc hbst.2
  refine ⟨l,r,?_,?_,?_,?_,?_⟩
  · dsimp [l]; have := le_max_left a s; linarith
  · dsimp [l] <;> linarith
  · dsimp [r] <;> linarith
  · dsimp [r]; have := min_le_left c t; linarith
  · intro x hx
    apply (hst ?_).1
    constructor
    · have := le_max_right a s; dsimp [l] at hx <;> linarith [hx.1]
    · have := min_le_right c t; dsimp [r] at hx <;> linarith [hx.2]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TimeBlendDomain
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An open domain for joining time charts using an exact scalar cutoff. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

lemma timeBlendDomain_open (c d : SurfaceTimeChart F) (l r : ℝ)
    (hF : Continuous F) : IsOpen (timeBlendDomain c d l r) :=
  ((c.coord.open_source.inter (isOpen_Iio.preimage hF)).union
    (c.coord.open_source.inter d.coord.open_source)).union
      (d.coord.open_source.inter (isOpen_Ioi.preimage hF))

lemma timeBlendDomain_smooth (c d : SurfaceTimeChart F) {l r : ℝ} (hlr : l < r)
    (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F) :
    ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ (surfaceTimeBlend c d (timeCutoff l r))
      (timeBlendDomain c d l r) := by
  intro x hx
  rcases hx with (⟨hc,ht⟩ | ⟨hc,hd⟩) | ⟨hd,ht⟩
  · exact ((c.smooth.contMDiffAt (c.coord.open_source.mem_nhds hc)).congr_of_eventuallyEq
      (surfaceTimeBlend_left_germ c d hF.continuous hlr ht)).contMDiffWithinAt
  · exact ((surfaceTimeBlend_smooth c d (timeCutoff_smooth l r) hF).contMDiffAt
      ((c.coord.open_source.inter d.coord.open_source).mem_nhds ⟨hc,hd⟩)).contMDiffWithinAt
  · exact ((d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hd)).congr_of_eventuallyEq
      (surfaceTimeBlend_right_germ c d hF.continuous hlr ht)).contMDiffWithinAt

lemma timeBlendDomain_time (c d : SurfaceTimeChart F) {l r : ℝ} (hlr : l < r)
    {x : M} (hx : x ∈ timeBlendDomain c d l r) :
    surfaceTimeBlend c d (timeCutoff l r) x 1 = F x := by
  rcases hx with (⟨hc,ht⟩ | ⟨hc,hd⟩) | ⟨hd,ht⟩
  · rw [surfaceTimeBlend_zero c d (timeCutoff_zero hlr ht.le)]
    exact c.time x hc
  · exact surfaceTimeBlend_time c d hc hd
  · rw [surfaceTimeBlend_one c d (timeCutoff_one hlr ht.le)]
    exact d.time x hd

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_JoinTimeCharts
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adjacent charts straightening the same regular arc can be joined,
retaining the longitudinal coordinate and both exterior axis germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] [Nonempty M]

theorem join_time_charts {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    {γ : ℝ → M} {a b e : ℝ} (hab : a < b) (hbe : b < e)
    (hγ : ∀ t ∈ Icc a e, ContinuousAt γ t)
    {W : Set ℝ} (hW : W ∈ 𝓝 b) (hIW : Icc a e ⊆ W)
    (c d : SurfaceTimeChart F)
    (hc : ∀ t ∈ Icc a b, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ c.coord.source ∧ c.coord (γ s) = ![0,s])
    (hd : ∀ t ∈ Icc b e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ d.coord.source ∧ d.coord (γ s) = ![0,s]) :
    ∃ k : SurfaceTimeChart F, ∀ t ∈ Icc a e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ k.coord.source ∧ k.coord (γ s) = ![0,s] := by
  have hcb : ∀ᶠ s in 𝓝 b, γ s ∈ c.coord.source ∧ c.coord (γ s) = ![0,s] := by
    simpa only [nhdsWithin_eq_nhds.mpr hW] using hc b ⟨hab.le,le_rfl⟩
  have hdb : ∀ᶠ s in 𝓝 b, γ s ∈ d.coord.source ∧ d.coord (γ s) = ![0,s] := by
    simpa only [nhdsWithin_eq_nhds.mpr hW] using hd b ⟨le_rfl,hbe.le⟩
  obtain ⟨d',hsource,haxis,hpos⟩ := c.positive_transition d (γ b)
    (Filter.Eventually.self_of_nhds hcb).1 (Filter.Eventually.self_of_nhds hdb).1
  have hd' : ∀ t ∈ Icc b e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ d'.coord.source ∧ d'.coord (γ s) = ![0,s] := by
    intro t ht
    filter_upwards [hd t ht] with s hs
    exact ⟨hsource.symm ▸ hs.1,haxis _ _ hs.2⟩
  have hdb' : ∀ᶠ s in 𝓝 b, γ s ∈ d'.coord.source ∧ d'.coord (γ s) = ![0,s] := by
    simpa only [nhdsWithin_eq_nhds.mpr hW] using hd' b ⟨le_rfl,hbe.le⟩
  obtain ⟨V,hV,hbV,hVsub,hVpos⟩ := c.positive_overlap d' (γ b)
    (Filter.Eventually.self_of_nhds hcb).1 (Filter.Eventually.self_of_nhds hdb').1 hpos
  have hcommon : ∀ᶠ s in 𝓝 b, γ s ∈ V ∧
      (γ s ∈ c.coord.source ∧ c.coord (γ s) = ![0,s]) ∧
      (γ s ∈ d'.coord.source ∧ d'.coord (γ s) = ![0,s]) := by
    filter_upwards [(hγ b ⟨hab.le,hbe.le⟩).eventually (hV.mem_nhds hbV),hcb,hdb'] with s hs hcs hds
    exact ⟨hs,hcs,hds⟩
  obtain ⟨O,hOsub,hO,hbO⟩ := eventually_nhds_iff.mp hcommon
  obtain ⟨l,r,hal,hlb,hbr,hre,hlrsub⟩ :=
    straddling_compact_interval hab hbe (hO.mem_nhds hbO)
  have hlr : l < r := hlb.trans hbr
  let H := surfaceTimeBlend c d' (timeCutoff l r)
  let U := timeBlendDomain c d' l r
  have hU : IsOpen U := timeBlendDomain_open c d' l r hF.continuous
  have hHgerm : ∀ t ∈ Icc a e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ U ∧ H (γ s) = ![0,s] := by
    intro t ht
    by_cases htl : t < l
    · have hct := hc t ⟨ht.1,htl.le.trans hlb.le⟩
      filter_upwards [hct,nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htl)] with s hs hsl
      refine ⟨Or.inl (Or.inl ⟨hs.1,?_⟩),?_⟩
      · change F (γ s) < l
        rw [← c.time _ hs.1,hs.2]
        exact hsl
      · change surfaceTimeBlend c d' (timeCutoff l r) (γ s) = _
        rw [surfaceTimeBlend_zero c d' (timeCutoff_zero hlr ?_)]
        · exact hs.2
        · rw [← c.time _ hs.1,hs.2]; exact hsl.le
    · by_cases hrt : r < t
      · have hdt := hd' t ⟨hbr.le.trans hrt.le,ht.2⟩
        filter_upwards [hdt,nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hrt)] with s hs hrs
        refine ⟨Or.inr ⟨hs.1,?_⟩,?_⟩
        · change r < F (γ s)
          rw [← d'.time _ hs.1,hs.2]; exact hrs
        · change surfaceTimeBlend c d' (timeCutoff l r) (γ s) = _
          rw [surfaceTimeBlend_one c d' (timeCutoff_one hlr ?_)]
          · exact hs.2
          · rw [← d'.time _ hs.1,hs.2]; exact hrs.le
      · have htO := hlrsub ⟨le_of_not_gt htl,le_of_not_gt hrt⟩
        filter_upwards [nhdsWithin_le_nhds (hO.mem_nhds htO)] with s hs
        have hsc := hOsub s hs
        exact ⟨Or.inl (Or.inr ⟨hsc.2.1.1,hsc.2.2.1⟩),
          surfaceTimeBlend_axis c d' hsc.2.1.2 hsc.2.2.2⟩
  let K := γ '' Icc a e
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (fun t ht => (hγ t ht).continuousWithinAt)
  have hKU : K ⊆ U := by
    rintro x ⟨t,ht,rfl⟩
    exact (mem_of_mem_nhdsWithin (hIW ht) (hHgerm t ht)).1
  have hHi : K.InjOn H := by
    rintro x ⟨t,ht,rfl⟩ y ⟨s,hs,rfl⟩ heq
    have hta := (mem_of_mem_nhdsWithin (hIW ht) (hHgerm t ht)).2
    have hsa := (mem_of_mem_nhdsWithin (hIW hs) (hHgerm s hs)).2
    have hts : t = s := by
      have hh := congrFun (hta.symm.trans (heq.trans hsa)) (1:Fin 2)
      exact hh
    rw [hts]
  have hHr : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) H x) := by
    rintro x ⟨t,ht,rfl⟩
    by_cases htl : t < l
    · have hct := mem_of_mem_nhdsWithin (hIW ht) (hc t ⟨ht.1,htl.le.trans hlb.le⟩)
      have hFt : F (γ t) = t := by rw [← c.time _ hct.1,hct.2]; rfl
      have heq := surfaceTimeBlend_left_germ c d' hF.continuous hlr (hFt ▸ htl)
      change Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base)
        (surfaceTimeBlend c d' (timeCutoff l r)) (γ t))
      rw [heq.mfderiv_eq]
      exact c.regular hct.1
    · by_cases hrt : r < t
      · have hdt := mem_of_mem_nhdsWithin (hIW ht) (hd' t ⟨hbr.le.trans hrt.le,ht.2⟩)
        have hFt : F (γ t) = t := by rw [← d'.time _ hdt.1,hdt.2]; rfl
        have heq := surfaceTimeBlend_right_germ c d' hF.continuous hlr (hFt ▸ hrt)
        change Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base)
          (surfaceTimeBlend c d' (timeCutoff l r)) (γ t))
        rw [heq.mfderiv_eq]
        exact d'.regular hdt.1
      · have htcommon := hOsub t (hlrsub ⟨le_of_not_gt htl,le_of_not_gt hrt⟩)
        exact surfaceTimeBlend_regular c d' (timeCutoff_smooth l r) hF (γ t)
          htcommon.2.1.1 htcommon.2.2.1 (htcommon.2.2.2.trans htcommon.2.1.2.symm)
          (hVpos _ htcommon.1) (timeCutoff_mem l r _)
  obtain ⟨k,hKk,hkf⟩ := compact_time_chart hK hU hKU
    (timeBlendDomain_smooth c d' hlr hF) (fun x hx => timeBlendDomain_time c d' hlr hx) hHi hHr
  refine ⟨k,?_⟩
  intro t ht
  have htk : γ t ∈ k.coord.source := hKk ⟨t,ht,rfl⟩
  filter_upwards [((hγ t ht).eventually (k.coord.open_source.mem_nhds htk)).filter_mono nhdsWithin_le_nhds,hHgerm t ht] with s hs hsg
  exact ⟨hs,(hkf hs).trans hsg.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ArcTimeGermPartition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite time-chart subdivision retains axis germs relative to the
entire compact arc, including at subdivision points. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem arc_time_chart_germ_partition (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ s ∈ Icc P.start P.finish, F (P.curve s) = s) :
    ∃ (τ : ℕ → ℝ) (N : ℕ), τ 0 = P.start ∧ Monotone τ ∧
      (∀ n, τ n ∈ Icc P.start P.finish) ∧ (∀ n ≥ N, τ n = P.finish) ∧
      ∀ n, ∃ c : SurfaceTimeChart F,
        ∀ s ∈ Icc (τ n) (τ (n+1)), ∀ᶠ u in 𝓝[Icc P.start P.finish] s,
          P.curve u ∈ c.coord.source ∧ c.coord (P.curve u) = ![0,u] := by
  classical
  choose d J hJ htJ hds hdi hdF haxis using
    fun t : Icc P.start P.finish => surface_arc_time_coordinates P hF hFP t.property
  let C : Icc P.start P.finish → Set (Icc P.start P.finish) :=
    fun t => (fun s : Icc P.start P.finish => (s:ℝ)) ⁻¹' J t
  have hC : ∀ t, IsOpen (C t) := fun t => (hJ t).preimage continuous_subtype_val
  have hcover : univ ⊆ ⋃ t, C t := by
    intro t _
    exact mem_iUnion.mpr ⟨t,htJ t⟩
  obtain ⟨τ,hzero,hmono,⟨N,hend⟩,hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc P.start_lt_finish.le hC hcover
  refine ⟨fun n => (τ n:ℝ),N,hzero,fun _ _ h => hmono h,fun n => (τ n).property,hend,?_⟩
  intro n
  obtain ⟨t,ht⟩ := hsub n
  refine ⟨⟨d t,hds t,hdi t,hdF t⟩,?_⟩
  intro s hs
  have hsP : s ∈ Icc P.start P.finish :=
    ⟨(τ n).property.1.trans hs.1,hs.2.trans (τ (n+1)).property.2⟩
  have hsJ : s ∈ J t := ht (show (⟨s,hsP⟩ : Icc P.start P.finish) ∈ Icc (τ n) (τ (n+1)) from hs)
  filter_upwards [nhdsWithin_le_nhds ((hJ t).mem_nhds hsJ),
    self_mem_nhdsWithin] with u huJ huW
  exact ⟨(haxis t u huJ).1,(haxis t u huJ).2.trans (by rw [hFP u huW])⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactArcTimeChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual smooth source chart around the entire compact embedded arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] [Nonempty M]

theorem compact_arc_time_chart (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ t ∈ Icc P.start P.finish, F (P.curve t) = t) :
    ∃ c : SurfaceTimeChart F, ∀ t ∈ Icc P.start P.finish,
      ∀ᶠ s in 𝓝[Icc P.start P.finish] t,
        P.curve s ∈ c.coord.source ∧ c.coord (P.curve s) = ![0,s] := by
  obtain ⟨τ,N,hzero,hmono,hbounds,hend,hcharts⟩ := arc_time_chart_germ_partition P hF hFP
  have hγ : ∀ t ∈ Icc P.start P.finish, ContinuousAt P.curve t := by
    intro t ht
    exact (P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht))).continuousAt
  have hstep : ∀ n : ℕ, ∃ c : SurfaceTimeChart F,
      ∀ t ∈ Icc P.start (τ n), ∀ᶠ s in 𝓝[Icc P.start P.finish] t,
        P.curve s ∈ c.coord.source ∧ c.coord (P.curve s) = ![0,s] := by
    intro n
    induction n with
    | zero =>
      obtain ⟨c,hc⟩ := hcharts 0
      refine ⟨c,?_⟩
      intro t ht
      have ht0 : t = P.start := le_antisymm (ht.2.trans_eq hzero) ht.1
      apply hc t
      constructor
      · rw [ht0,hzero]
      · rw [ht0]
        exact (hbounds 1).1
    | succ n ih =>
      obtain ⟨c,hc⟩ := ih
      obtain ⟨d,hd⟩ := hcharts n
      by_cases hn : τ n = P.start
      · refine ⟨d,?_⟩
        intro t ht
        exact hd t ⟨hn.symm ▸ ht.1,ht.2⟩
      · by_cases heq : τ (n+1) = τ n
        · refine ⟨c,?_⟩
          intro t ht
          exact hc t ⟨ht.1,heq ▸ ht.2⟩
        · have hsn : P.start < τ n := lt_of_le_of_ne (hbounds n).1 (Ne.symm hn)
          have hns : τ n < τ (n+1) := lt_of_le_of_ne (hmono (Nat.le_succ n)) (Ne.symm heq)
          apply join_time_charts hF hsn hns
            (fun t ht => hγ t ⟨ht.1,ht.2.trans (hbounds (n+1)).2⟩)
            (Icc_mem_nhds hsn (hns.trans_le (hbounds (n+1)).2))
            (fun t ht => ⟨ht.1,ht.2.trans (hbounds (n+1)).2⟩) c d hc hd
  obtain ⟨c,hc⟩ := hstep N
  refine ⟨c,?_⟩
  intro t ht
  apply hc t
  rwa [hend N le_rfl]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAxisRectangle
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact axis segment in an open plane set has a uniform rectangular collar. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma open_interval_collar {a b : ℝ} (hab : a ≤ b) {U : Set ℝ}
    (hU : IsOpen U) (hI : Icc a b ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (a-δ) (b+δ) ⊆ U := by
  obtain ⟨δ,hδ,hsub⟩ := isCompact_Icc.exists_cthickening_subset_open hU hI
  refine ⟨δ,hδ,?_⟩
  intro x hx
  apply hsub
  by_cases hxa : x < a
  · apply mem_cthickening_of_dist_le x a δ (Icc a b) ⟨le_rfl,hab⟩
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxa.le)]
    linarith [hx.1]
  · by_cases hbx : b < x
    · apply mem_cthickening_of_dist_le x b δ (Icc a b) ⟨hab,le_rfl⟩
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hbx.le)]
      linarith [hx.2]
    · exact mem_cthickening_of_dist_le x x δ (Icc a b)
        ⟨le_of_not_gt hxa,le_of_not_gt hbx⟩ (by simpa using hδ.le)

theorem compact_axis_rectangle {a b : ℝ} (hab : a ≤ b) {U : Set Base}
    (hU : IsOpen U) (haxis : ∀ t ∈ Icc a b, (![0,t] : Base) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (a-δ) (b+δ),
      (![x,t] : Base) ∈ U := by
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hTU : ({0} : Set ℝ) ×ˢ Icc a b ⊆ T ⁻¹' U := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    obtain rfl : x = 0 := hx
    exact haxis t ht
  obtain ⟨V,W,hV,hW,h0V,hIW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc (hU.preimage hT) hTU
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (by simp))
  obtain ⟨η,hη,hηW⟩ := open_interval_collar hab hW hIW
  let δ := min (r/2) η
  have hδ : 0 < δ := lt_min (half_pos hr) hη
  refine ⟨δ,hδ,?_⟩
  intro x hx t ht
  change (x,t) ∈ T ⁻¹' U
  apply hVW
  constructor
  · apply hrV
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
    constructor <;> linarith [hx.1,hx.2]
  · apply hηW
    have hδη : δ ≤ η := min_le_right _ _
    constructor <;> linarith [ht.1,ht.2]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SourceArcChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rectangular source coordinates along the whole embedded crosscap arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem source_arc_chart (P : SmoothCompactArc planeModel M) :
    ∃ (c : OpenPartialHomeomorph M Base) (δ : ℝ), 0 < δ ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ c.source ∧ c (P.curve t) = ![0,t]) ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (P.start-δ) (P.finish+δ), (![x,t] : Base) ∈ c.target) := by
  let : Nonempty M := ⟨P.curve P.start⟩
  obtain ⟨F,hF,hFP⟩ := smooth_arc_parameter_extension P
  obtain ⟨c,hc⟩ := compact_arc_time_chart P hF hFP
  have haxis : ∀ t ∈ Icc P.start P.finish,
      P.curve t ∈ c.coord.source ∧ c.coord (P.curve t) = ![0,t] := by
    intro t ht
    change t ∈ {s : ℝ | P.curve s ∈ c.coord.source ∧ c.coord (P.curve s) = ![0,s]}
    exact mem_of_mem_nhdsWithin ht (hc t ht)
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_rectangle P.start_lt_finish.le c.coord.open_target (by
    intro t ht
    rw [← (haxis t ht).2]
    exact c.coord.map_source (haxis t ht).1)
  exact ⟨c.coord,δ,hδ,c.smooth,c.inverse_smooth,haxis,hrect⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SourceMapRepresentative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original surface map in the constructed full-arc coordinates,
with an actual globally smooth representative near the entire rectangle. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem source_map_representative (P : SmoothCompactArc planeModel M)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f) :
    ∃ (c : OpenPartialHomeomorph M Base) (δ : ℝ) (φ : Base → V) (U : Set Base),
      0 < δ ∧ ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ContDiff ℝ ∞ φ ∧ IsOpen U ∧ U ⊆ c.target ∧ EqOn φ (f ∘ c.symm) U ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ c.source ∧ c (P.curve t) = ![0,t]) ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (P.start-δ) (P.finish+δ), (![x,t] : Base) ∈ U) := by
  obtain ⟨c,δ,hδ,hcs,hci,haxis,hrect⟩ := source_arc_chart P
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  let K := T '' (Icc (-δ) δ ×ˢ Icc (P.start-δ) (P.finish+δ))
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hT
  have hKt : K ⊆ c.target := by
    rintro x ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩
    exact hrect s hs t ht
  have hlocal : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target :=
    (hf.comp_contMDiffOn hci).contDiffOn
  obtain ⟨U,hU,hKU,hUt,φ,hφ,hEq⟩ :=
    CollarVelocity.compact_smooth_extension hK c.open_target hKt hlocal
  refine ⟨c,δ,φ,U,hδ,hcs,hci,hφ,hU,hUt,hEq,haxis,?_⟩
  intro x hx t ht
  exact hKU ⟨(x,t),⟨hx,ht⟩,rfl⟩

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem coordinate_representative_immersion_iff (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {φ : Base → V} {U : Set Base} (hU : IsOpen U) (hUt : U ⊆ c.target)
    (hEq : EqOn φ (f ∘ c.symm) U) {x : Base} (hx : x ∈ U) :
    Function.Injective (fderiv ℝ φ x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) := by
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hbij := hcD.mfderiv_bijective (hUt hx)
  rw [(hEq.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq,← mfderiv_eq_fderiv,
    mfderiv_comp x (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt (hUt hx))]
  change Function.Injective ((mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) ∘
    (mfderiv 𝓘(ℝ,Base) planeModel c.symm x)) ↔ _
  constructor
  · intro h v w hvw
    obtain ⟨v',rfl⟩ := hbij.2 v
    obtain ⟨w',rfl⟩ := hbij.2 w
    exact congrArg (mfderiv 𝓘(ℝ,Base) planeModel c.symm x) (h hvw)
  · intro h
    exact h.comp hbij.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateAxisDerivative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate representative has exactly the original map's axis velocity,
including both endpoints of the compact arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma coordinate_axis_derivative (P : SmoothCompactArc planeModel M)
    (c : OpenPartialHomeomorph M Base) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f) {φ : Base → V}
    (hφ : ContDiff ℝ ∞ φ) {U : Set Base} (hEq : EqOn φ (f ∘ c.symm) U)
    (haxis : ∀ t ∈ Icc P.start P.finish,
      P.curve t ∈ c.source ∧ c (P.curve t) = ![0,t])
    (hUaxis : ∀ t ∈ Icc P.start P.finish, (![0,t] : Base) ∈ U)
    {t : ℝ} (ht : t ∈ Icc P.start P.finish) :
    fderiv ℝ φ (![0,t] : Base) (![0,1] : Base) = deriv (f ∘ P.curve) t := by
  have heq : EqOn (φ ∘ crosscapAxis) (f ∘ P.curve) (Icc P.start P.finish) := by
    intro s hs
    rw [Function.comp_apply,crosscapAxis_apply,hEq (hUaxis s hs)]
    change f (c.symm (![0,s] : Base)) = f (P.curve s)
    rw [← (haxis s hs).2,c.left_inv (haxis s hs).1]
  have hD := ((hφ.differentiable (by simp) (crosscapAxis t)).hasFDerivAt).comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt
  have hD' := hD.hasDerivWithinAt.congr_of_mem (fun s hs => (heq hs).symm) ht
  have hfD := ((hf.contMDiffAt.comp t
    (P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht)))).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hd := ((uniqueDiffOn_Icc P.start_lt_finish) t ht).eq_deriv (Icc P.start P.finish)
    hfD.hasDerivWithinAt hD'
  simpa only [crosscapAxis_apply] using hd.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisImageVelocity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact endpoint axis germs force zero image velocity at each crosscap. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {f : M → ProjectionTarget 3} {p : M}

lemma crosscap_axis_image_velocity (c : SurfaceCrosscapCoordinates f p)
    {γ : ℝ → M} {a : ℝ} (e : ℝ → ℝ) (he : ContDiff ℝ ∞ e) (he0 : e a = 0)
    (hγ : γ =ᶠ[𝓝 a] c.axisCurve ∘ e) : deriv (f ∘ γ) a = 0 := by
  have heD := (he.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) a).hasDerivAt
  have haD := crosscapAxis.hasFDerivAt.comp_hasDerivAt a heD
  have hstd := (standardCrosscap_hasFDerivAt (crosscapAxis (e a))).comp_hasDerivAt a haD
  have hz : standardCrosscapDerivative (crosscapAxis (e a))
      (crosscapAxis (deriv e a)) = 0 := by
    rw [he0,map_zero]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscapDerivative,crosscapAxis_apply]
    · simp [standardCrosscapDerivative,crosscapAxis_apply]
  rw [hz] at hstd
  have htar := (c.target_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt a hstd
  have h0 : (0:Base) ∈ c.source.target := by
    rw [← c.source_center]
    exact c.source.map_source c.source_mem
  have hnear : ∀ᶠ t in 𝓝 a, crosscapAxis (e t) ∈ c.source.target := by
    apply (c.source.open_target.preimage (crosscapAxis.continuous.comp he.continuous)).mem_nhds
    change crosscapAxis (e a) ∈ c.source.target
    rw [he0,map_zero]
    exact h0
  have hEq : f ∘ γ =ᶠ[𝓝 a] c.target ∘ (standardCrosscap ∘ (crosscapAxis ∘ e)) := by
    filter_upwards [hγ,hnear] with t ht htS
    have hm := c.model_eq (c.source.symm (crosscapAxis (e t))) (c.source.map_target htS)
    rw [c.source.right_inv htS] at hm
    simpa only [Function.comp_apply,ht,SurfaceCrosscapCoordinates.axisCurve] using hm
  rw [hEq.deriv_eq]
  exact htar.deriv.trans (map_zero _)

lemma CrosscapConnectingArc.endpoint_image_velocity [T2Space M]
    {q : M} (A : CrosscapConnectingArc f p q) :
    deriv (f ∘ A.arc.curve) A.arc.start = 0 ∧
      deriv (f ∘ A.arc.curve) A.arc.finish = 0 :=
  ⟨crosscap_axis_image_velocity A.left A.leftParameter A.left_smooth A.left_zero A.left_germ,
    crosscap_axis_image_velocity A.right A.rightParameter A.right_smooth A.right_zero A.right_germ⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapDerivativeNonzero
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative at an actual crosscap has rank at least one. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {f : M → ProjectionTarget 3} {p : M}

lemma SurfaceCrosscapCoordinates.derivative_ne_zero (c : SurfaceCrosscapCoordinates f p)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p ≠ 0 := by
  intro hzero
  have h0 : (0:Base) ∈ c.source.target := by
    rw [← c.source_center]
    exact c.source.map_source c.source_mem
  have hinv : c.source.symm 0 = p := by
    rw [← c.source_center,c.source.left_inv c.source_mem]
  have hstd0 : standardCrosscap (0:Base) = 0 := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  have heq : f ∘ c.source.symm =ᶠ[𝓝 (0:Base)] c.target ∘ standardCrosscap := by
    filter_upwards [c.source.open_target.mem_nhds h0] with x hx
    have h := c.model_eq (c.source.symm x) (c.source.map_target hx)
    rwa [c.source.right_inv hx] at h
  have hcomp0 : fderiv ℝ (f ∘ c.source.symm) 0 = 0 := by
    rw [← mfderiv_eq_fderiv,mfderiv_comp 0 (hf.mdifferentiable (by simp) _)
      ((c.source_inverse_smooth.contMDiffAt (c.source.open_target.mem_nhds h0)).mdifferentiableAt (by simp)),
      ]
    have hz : mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (c.source.symm 0) = 0 :=
      hinv.symm ▸ hzero
    rw [hz]
    exact ContinuousLinearMap.zero_comp _
  have htD : c.target.MDifferentiable 𝓘(ℝ,Base × ℝ) 𝓘(ℝ,ProjectionTarget 3) :=
    ⟨c.target_smooth.contMDiff.contMDiffOn.mdifferentiableOn (by simp),
      c.target_inverse_smooth.contMDiffOn.mdifferentiableOn (by simp)⟩
  have htI : Function.Injective (fderiv ℝ c.target 0) := by
    rw [← mfderiv_eq_fderiv]
    exact htD.mfderiv_injective c.target_mem
  have hv := congrArg (fun L : Base →L[ℝ] ProjectionTarget 3 => L (![1,0] : Base))
    (heq.fderiv_eq.symm.trans hcomp0)
  rw [fderiv_comp 0 (c.target_smooth.differentiable (by simp) _)
    (standardCrosscap_hasFDerivAt 0).differentiableAt,
    (standardCrosscap_hasFDerivAt 0).fderiv,hstd0] at hv
  have hval : standardCrosscapDerivative 0 (![1,0] : Base) = (0,1) := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscapDerivative]
    · simp [standardCrosscapDerivative]
  change fderiv ℝ c.target 0 (standardCrosscapDerivative 0 (![1,0] : Base)) = 0 at hv
  rw [hval] at hv
  have hh := htI (hv.trans (map_zero _).symm)
  have hs := congrArg Prod.snd hh
  norm_num at hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTransverseDerivative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transverse coordinate derivative never vanishes at a rank-one
crosscap whose longitudinal coordinate is the kernel. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma horizontal_ne_zero_of_vertical_zero (L : Base →L[ℝ] V)
    (hL : L ≠ 0) (hv : L (![0,1] : Base) = 0) : L (![1,0] : Base) ≠ 0 := by
  intro hh
  apply hL
  ext x
  have hx : x = (x 0) • (![1,0] : Base) + (x 1) • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  rw [hx,map_add,map_smul,map_smul,hh,hv]
  simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinate_representative_derivative_ne_zero (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {φ : Base → V} {U : Set Base} (hU : IsOpen U) (hUt : U ⊆ c.target)
    (hEq : EqOn φ (f ∘ c.symm) U) {x : Base} (hx : x ∈ U)
    (hn : mfderiv planeModel 𝓘(ℝ,V) f (c.symm x) ≠ 0) : fderiv ℝ φ x ≠ 0 := by
  intro hz
  apply hn
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hsur := (hcD.mfderiv_bijective (hUt hx)).2
  rw [(hEq.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq,← mfderiv_eq_fderiv,
    mfderiv_comp x (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt (hUt hx))] at hz
  ext v
  obtain ⟨w,rfl⟩ := hsur v
  exact congrArg (fun L => L w) hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapCoordinateStrip
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual map on a rectangular source strip through two crosscaps,
with a nonzero transverse derivative along the entire central arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem exists_crosscap_coordinate_strip_oai
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (A : CrosscapConnectingArc f p q) : Nonempty (CrosscapCoordinateStrip A) := by
  obtain ⟨c,δ,φ,U,hδ,hcs,hci,hφ,hU,hUt,hEq,haxis,hrect⟩ := source_map_representative A.arc hf
  have hUaxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U := by
    intro t ht
    apply hrect 0 ⟨by linarith,by linarith⟩ t
    constructor <;> linarith [ht.1,ht.2]
  have hrecover : ∀ t ∈ Icc A.arc.start A.arc.finish, c.symm (![0,t] : Base) = A.arc.curve t := by
    intro t ht
    rw [← (haxis t ht).2,c.left_inv (haxis t ht).1]
  have hleft : fderiv ℝ φ (![0,A.arc.start] : Base) (![0,1] : Base) = 0 :=
    (coordinate_axis_derivative A.arc c hf hφ hEq haxis hUaxis
      (left_mem_Icc.mpr A.arc.start_lt_finish.le)).trans A.endpoint_image_velocity.1
  have hright : fderiv ℝ φ (![0,A.arc.finish] : Base) (![0,1] : Base) = 0 :=
    (coordinate_axis_derivative A.arc c hf hφ hEq haxis hUaxis
      (right_mem_Icc.mpr A.arc.start_lt_finish.le)).trans A.endpoint_image_velocity.2
  have hregular : ∀ t ∈ Ioo A.arc.start A.arc.finish,
      Function.Injective (fderiv ℝ φ (![0,t] : Base)) := by
    intro t ht
    apply (coordinate_representative_immersion_iff c hcs hci hf hU hUt hEq (hUaxis t ⟨ht.1.le,ht.2.le⟩)).mpr
    rw [hrecover t ⟨ht.1.le,ht.2.le⟩]
    exact A.regular t ht
  refine ⟨⟨c,δ,hδ,hcs,hci,φ,hφ,U,hU,hUt,hEq,haxis,hrect,?_,hregular,hleft,hright⟩⟩
  intro t ht
  by_cases hl : t = A.arc.start
  · subst t
    apply horizontal_ne_zero_of_vertical_zero _ ?_ hleft
    apply coordinate_representative_derivative_ne_zero c hcs hci hf hU hUt hEq (hUaxis _ ht)
    rw [hrecover _ ht,A.source]
    exact A.left.derivative_ne_zero hf
  · by_cases hr : t = A.arc.finish
    · subst t
      apply horizontal_ne_zero_of_vertical_zero _ ?_ hright
      apply coordinate_representative_derivative_ne_zero c hcs hci hf hU hUt hEq (hUaxis _ ht)
      rw [hrecover _ ht,A.target]
      exact A.right.derivative_ne_zero hf
    · have hreg := hregular t ⟨lt_of_le_of_ne ht.1 (Ne.symm hl),lt_of_le_of_ne ht.2 hr⟩
      intro hz
      have hh := hreg (hz.trans (map_zero _).symm)
      have h0 := congrFun hh 0
      norm_num at h0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_crosscap_coordinate_strip_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_crosscap_coordinate_strip_oai.{u_1}
