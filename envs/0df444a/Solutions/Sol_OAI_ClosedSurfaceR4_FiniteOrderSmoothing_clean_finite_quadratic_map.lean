-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.clean_finite_quadratic_map
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:41:44.874433+00:00
-- url     : https://prove2.me/submissions/8db0de47-5013-4e18-86ed-126ff9949004

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI004
import Definitions.Def_OAIQ249SI005
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SurfacePairTranslationPatch_regularize_avoiding_points
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_clean_crosscap_neighborhoods

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_injective_stability {K : Set (Base →L[ℝ] V)}
    (hK : IsCompact K) (hI : ∀ L ∈ K, Function.Injective L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ L ∈ K, ∀ H : Base →L[ℝ] V,
      ‖H-L‖ < ε → Function.Injective H := by
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open
    ContinuousLinearMap.isOpen_injective hI
  exact ⟨ε,hε,fun L hL H hH => he
    (Metric.mem_thickening_iff.mpr ⟨L,hL,by simpa only [dist_eq_norm] using hH⟩)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

omit [CompactSpace M] in
lemma fderiv_comp_chart_symm {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {x : Base}
    (hx : x ∈ (chart p).target) :
    fderiv ℝ (f ∘ (chart p).symm) x =
      (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x (hf.mdifferentiable one_ne_zero).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt_symm hx)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartGermImmersion
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Immersion of a smooth coordinate representative is equivalent to
immersion of the represented surface map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma chart_germ_immersion_iff (p : M) {q : M} (hq : q ∈ (chart p).source)
    {g : M → ProjectionTarget 3} {G : Base → ProjectionTarget 3}
    (hG : ContDiff ℝ ∞ G) (he : g =ᶠ[𝓝 q] G ∘ chart p) :
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g q) ↔
      Function.Injective (fderiv ℝ G (chart p q)) := by
  have hGc : ContMDiff 𝓘(ℝ,Base) 𝓘(ℝ,ProjectionTarget 3) ∞ G := hG.contMDiff
  rw [he.mfderiv_eq,mfderiv_comp q (hGc.mdifferentiable (by simp)).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt hq),mfderiv_eq_fderiv]
  change Function.Injective (fderiv ℝ G (chart p q) ∘
    mfderiv planeModel 𝓘(ℝ,Base) (chart p) q) ↔ _
  constructor
  · intro hi
    exact hi.of_comp_right ((chart_mdifferentiable p).mfderiv_surjective hq)
  · intro hi
    exact hi.comp ((chart_mdifferentiable p).mfderiv_injective hq)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceGermTranslation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth supported translation families and their unchanged first jets
at points where the scalar separator is locally constant. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
theorem surfaceTranslation_smooth {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ) (a : ProjectionTarget 3) :
    ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (surfaceTranslation f χ a) :=
  hf.add (hχ.smul contMDiff_const)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceScalarRepresentative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every smooth scalar surface function has a globally smooth Euclidean
representative on an actual smaller neighborhood of any chosen point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem scalar_surface_chart_representative {f : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ℝ) ∞ f) (p : M) :
    ∃ (U : Set M) (F : Base → ℝ), IsOpen U ∧ p ∈ U ∧
      U ⊆ (chart p).source ∧ ContDiff ℝ ∞ F ∧ EqOn f (F ∘ chart p) U := by
  have hp : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have hlocal : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  obtain ⟨W,hW,hpW,hWT,F,hF,hFF⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := chart p p)) (chart p).open_target
    (singleton_subset_iff.mpr ((chart p).map_source hp)) hlocal
  let U := (chart p).source ∩ (chart p) ⁻¹' W
  refine ⟨U,F,(chart p).isOpen_inter_preimage hW,⟨hp,hpW (mem_singleton _)⟩,
    inter_subset_left,hF,?_⟩
  intro x hx
  change f x = F (chart p x)
  rw [hFF hx.2]
  change f x = f ((chart p).symm (chart p x))
  rw [(chart p).left_inv hx.1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceCoordinateTranslation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate representatives of scalar-weighted surface translations. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surface_translation_chart_germ (p : M) {x : M}
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F : Base → ProjectionTarget 3} {ρ : Base → ℝ}
    (hF : f =ᶠ[𝓝 x] F ∘ chart p) (hρ : χ =ᶠ[𝓝 x] ρ ∘ chart p)
    (a : ProjectionTarget 3) :
    surfaceTranslation f χ a =ᶠ[𝓝 x] (fun z => F z+ρ z • a) ∘ chart p := by
  filter_upwards [hF,hρ] with y hy hρy
  change f y+χ y • a = F (chart p y)+ρ (chart p y) • a
  rw [hy,hρy]
  rfl

theorem surface_pair_translation_coordinate_iff (p q : M) {x y : M}
    (hx : x ∈ (chart p).source) (hy : y ∈ (chart q).source)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F G : Base → ProjectionTarget 3} {ρ σ : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hρ : ContDiff ℝ ∞ ρ) (hσ : ContDiff ℝ ∞ σ)
    (heF : f =ᶠ[𝓝 x] F ∘ chart p) (heG : f =ᶠ[𝓝 y] G ∘ chart q)
    (heρ : χ =ᶠ[𝓝 x] ρ ∘ chart p) (heσ : χ =ᶠ[𝓝 y] σ ∘ chart q)
    (a : ProjectionTarget 3) :
    Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) x y) ↔
      Function.Surjective (fderiv ℝ
        (fun z : Base × Base => (F z.1-G z.2)+(ρ z.1-σ z.2) • a)
        (chart p x,chart q y)) := by
  have h := surface_pair_coordinate_regular_iff p q hx hy
    (hF.add (hρ.smul contDiff_const)) (hG.add (hσ.smul contDiff_const))
    (surface_translation_chart_germ p heF heρ a) (surface_translation_chart_germ q heG heσ a)
  have heq : (fun z : Base × Base => (F z.1+ρ z.1 • a)-(G z.2+σ z.2 • a)) =
      (fun z : Base × Base => (F z.1-G z.2)+(ρ z.1-σ z.2) • a) := by
    funext z
    rw [sub_smul]
    abel
  change Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) x y) ↔
    Function.Surjective (fderiv ℝ (fun z : Base × Base =>
      (F z.1+ρ z.1 • a)-(G z.2+σ z.2 • a)) (chart p x,chart q y)) at h
  rwa [heq] at h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceChartTranslationBound
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform chart derivative bounds for a fixed scalar translation family. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance chartScalarDerivNormed_rfec734_1 : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance chartScalarDerivSpace_rfec734_1 : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
lemma surface_chart_translation_derivative (p : M)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (a : ProjectionTarget 3) {x : Base} (hx : x ∈ (chart p).target) :
    fderiv ℝ (surfaceTranslation f χ a ∘ (chart p).symm) x =
      fderiv ℝ (f ∘ (chart p).symm) x+
        (fderiv ℝ (χ ∘ (chart p).symm) x).smulRight a := by
  have hF : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hC : ContDiffOn ℝ ∞ (χ ∘ (chart p).symm) (chart p).target :=
    (hχ.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  exact (((hF.contDiffAt ((chart p).open_target.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.add
    (((hC.contDiffAt ((chart p).open_target.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.smul_const a)).fderiv

theorem compact_chart_translation_bound (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    {S : Set Base} (hS : IsCompact S) (hST : S ⊆ (chart p).target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {f : M → ProjectionTarget 3},
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f →
      ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ S,
        ‖fderiv ℝ (surfaceTranslation f χ a ∘ (chart p).symm) x-
          fderiv ℝ (f ∘ (chart p).symm) x‖ < ε := by
  have hC : ContDiffOn ℝ ∞ (χ ∘ (chart p).symm) (chart p).target :=
    (hχ.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hD : ContinuousOn (fderiv ℝ (χ ∘ (chart p).symm)) S :=
    (hC.continuousOn_fderiv_of_isOpen (chart p).open_target (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mono hST
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn hD
  let B := max C 0+1
  have hB : 0 < B := by dsimp [B] <;> linarith [le_max_right C 0]
  refine ⟨ε/B,div_pos hε hB,?_⟩
  intro f hf a ha x hx
  rw [surface_chart_translation_derivative p hf hχ a (hST hx),add_sub_cancel_left,
    ContinuousLinearMap.norm_smulRight_apply]
  have hb : ‖fderiv ℝ (χ ∘ (chart p).symm) x‖ ≤ B :=
    (hC x hx).trans (by dsimp [B] <;> linarith [le_max_left C 0])
  calc
    _ ≤ B*‖a‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg a)
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hB).mp ha

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FiniteChartTranslationBound
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smallness simultaneously in any fixed finite collection of compact
chart regions. The bound is independent of the translated map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [Fintype ι]

theorem finite_chart_translation_bound
    (p : ι → M) (S : ι → Set Base) (hS : ∀ i, IsCompact (S i))
    (hST : ∀ i, S i ⊆ (chart (p i)).target) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {f : M → ProjectionTarget 3},
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f →
      ∀ a : ProjectionTarget 3, ‖a‖ < δ →
      ChartDerivativeClose p S f (surfaceTranslation f χ a) ε := by
  classical
  choose δ hδ hb using fun i => compact_chart_translation_bound (p i) hχ (hS i) (hST i) hε
  have hsmall (s : Finset ι) : ∃ η > 0, ∀ i ∈ s, η ≤ δ i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨η,hη,he⟩ := ih
      refine ⟨min η (δ i),lt_min hη (hδ i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (he j hj)
  obtain ⟨η,hη,he⟩ := hsmall Finset.univ
  exact ⟨η,hη,fun hf a ha i x hx => hb i hf a (ha.trans_le (he i (Finset.mem_univ i))) x hx⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CriticalSetClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional critical loci are closed. This supplies compact
exhaustions for the fiberwise critical-value argument. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem surjective_clm_open : IsOpen {K : E →L[ℝ] F | Function.Surjective K} := by
  rw [isOpen_iff_mem_nhds]
  intro K hK
  obtain ⟨R,hR⟩ := K.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hK)
  let R' : F →L[ℝ] E := R.toContinuousLinearMap
  have hKR : K.comp R' = ContinuousLinearMap.id ℝ F := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun L : F →ₗ[ℝ] F => L x) hR
  have hc : Continuous (fun L : E →L[ℝ] F => L.comp R') := continuous_id.clm_comp continuous_const
  have hn : ∀ᶠ L in 𝓝 K, IsUnit (L.comp R') := by
    change (fun L : E →L[ℝ] F => L.comp R') ⁻¹' {A | IsUnit A} ∈ 𝓝 K
    apply hc.continuousAt.preimage_mem_nhds
    apply Units.isOpen.mem_nhds
    rw [hKR]
    exact isUnit_one
  filter_upwards [hn] with L hL
  obtain ⟨u,hu⟩ := hL
  intro y
  refine ⟨R' ((↑u⁻¹ : F →L[ℝ] F) y),?_⟩
  have hval : L (R' ((↑u⁻¹ : F →L[ℝ] F) y)) =
      (↑u : F →L[ℝ] F) ((↑u⁻¹ : F →L[ℝ] F) y) := by rw [hu]; rfl
  rw [hval]
  change ((u : F →L[ℝ] F) * (↑u⁻¹ : F →L[ℝ] F)) y = y
  simp

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularZeroStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform first-jet stability of regular zero sets on compact domains.
This allows the finite pair-patch construction to preserve earlier patches. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

lemma regularZeroJets_open : IsOpen (regularZeroJets (E := E) (F := F)) :=
  (isOpen_compl_singleton.preimage continuous_fst).union
    (surjective_clm_open.preimage continuous_snd)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.zeroJetNormed
local instance zeroJetSpace_rfec734_1 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
theorem compact_regular_zero_stability {f : E → F} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, f x = 0 → Function.Surjective (fderiv ℝ f x)) :
    ∃ ε > 0, ∀ g : E → F,
      (∀ x ∈ K, ‖g x-f x‖ < ε) →
      (∀ x ∈ K, ‖fderiv ℝ g x-fderiv ℝ f x‖ < ε) →
      ∀ x ∈ K, g x = 0 → Function.Surjective (fderiv ℝ g x) := by
  let J : E → F × (E →L[ℝ] F) := fun x => (f x,fderiv ℝ f x)
  have hJ : Continuous J := hf.continuous.prodMk (hf.continuous_fderiv (by simp))
  have hsub : J '' K ⊆ regularZeroJets := by
    rintro z ⟨x,hx,rfl⟩
    by_cases h : f x = 0
    · exact Or.inr (hreg x hx h)
    · exact Or.inl h
  obtain ⟨ε,hε,hεsub⟩ := (hK.image hJ).exists_thickening_subset_open regularZeroJets_open hsub
  refine ⟨ε,hε,?_⟩
  intro g hv hd x hx hgx
  have hdist : dist (g x,fderiv ℝ g x) (J x) < ε := by
    rw [Prod.dist_eq]
    exact max_lt (by simpa only [J,dist_eq_norm] using hv x hx)
      (by simpa only [J,dist_eq_norm] using hd x hx)
  have hm : (g x,fderiv ℝ g x) ∈ thickening ε (J '' K) :=
    mem_thickening_iff.mpr ⟨J x,⟨x,hx,rfl⟩,hdist⟩
  rcases hεsub hm with h | h
  · exact False.elim (h hgx)
  · exact h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactTranslationStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small scalar-weighted translations preserve compact regular zero sets. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem compact_translation_stability {f : E → F} {χ : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ)
    {K : Set E} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, f x = 0 → Function.Surjective (fderiv ℝ f x)) :
    ∃ δ > 0, ∀ a : F, ‖a‖ < δ → ∀ x ∈ K, f x+χ x • a = 0 →
      Function.Surjective (fderiv ℝ (fun y => f y+χ y • a) x) := by
  obtain ⟨ε,hε,hεreg⟩ := compact_regular_zero_stability hf hK hreg
  obtain ⟨M₀,hM₀⟩ := hK.exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨M₁,hM₁⟩ := hK.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let B := max M₀ (max M₁ 0)+1
  have hB : 0 < B := by dsimp [B]; have := le_max_right M₀ (max M₁ 0); have := le_max_right M₁ 0; linarith
  refine ⟨ε/B,div_pos hε hB,?_⟩
  intro a ha
  have hab : B*‖a‖ < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp ha
  apply hεreg (fun y => f y+χ y • a)
  · intro x hx
    rw [add_sub_cancel_left,norm_smul]
    have hχB : ‖χ x‖ ≤ B := (hM₀ x hx).trans (by dsimp [B] <;> linarith [le_max_left M₀ (max M₁ 0)])
    exact (mul_le_mul_of_nonneg_right hχB (norm_nonneg a)).trans_lt hab
  · intro x hx
    have hd := ((hf.differentiable (by simp) x).hasFDerivAt.add
      ((hχ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv
    change ‖fderiv ℝ (f + fun y => χ y • a) x-fderiv ℝ f x‖ < ε
    rw [hd,add_sub_cancel_left,ContinuousLinearMap.norm_smulRight_apply]
    have hχB : ‖fderiv ℝ χ x‖ ≤ B := (hM₁ x hx).trans (by
      dsimp [B] <;> linarith [le_max_right M₀ (max M₁ 0),le_max_left M₁ 0])
    exact (mul_le_mul_of_nonneg_right hχB (norm_nonneg a)).trans_lt hab

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceChartPairStability
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact set of regular surface double pairs stays regular under a
small scalar-weighted translation, inside fixed coordinate patches. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_chart_pair_stability (p q : M)
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    {F G : Base → ProjectionTarget 3} {ρ σ : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hρ : ContDiff ℝ ∞ ρ) (hσ : ContDiff ℝ ∞ σ)
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hUp : U ⊆ (chart p).source) (hVq : V ⊆ (chart q).source)
    (heF : EqOn f (F ∘ chart p) U) (heG : EqOn f (G ∘ chart q) V)
    (heρ : EqOn χ (ρ ∘ chart p) U) (heσ : EqOn χ (σ ∘ chart q) V)
    {K : Set (M × M)} (hK : IsCompact K) (hKU : K ⊆ U ×ˢ V)
    (hreg : ∀ z ∈ K, f z.1 = f z.2 → Function.Surjective (surfacePairDerivative f z.1 z.2)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      surfaceTranslation f χ a z.1 = surfaceTranslation f χ a z.2 →
      Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) z.1 z.2) := by
  let κ : M × M → Base × Base := fun z => (chart p z.1,chart q z.2)
  let D : Base × Base → ProjectionTarget 3 := fun z => F z.1-G z.2
  let c : Base × Base → ℝ := fun z => ρ z.1-σ z.2
  have hDc : ContDiff ℝ ∞ D := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
  have hcc : ContDiff ℝ ∞ c := (hρ.comp contDiff_fst).sub (hσ.comp contDiff_snd)
  have hκ : ContinuousOn κ K := by
    intro z hz
    exact (((chart p).continuousAt (hUp (hKU hz).1)).comp continuous_fst.continuousAt).prodMk
      (((chart q).continuousAt (hVq (hKU hz).2)).comp continuous_snd.continuousAt) |>.continuousWithinAt
  have hKc : IsCompact (κ '' K) := hK.image_of_continuousOn hκ
  have hregc : ∀ w ∈ κ '' K, D w = 0 → Function.Surjective (fderiv ℝ D w) := by
    rintro w ⟨z,hz,rfl⟩ hw
    have hzU := (hKU hz).1
    have hzV := (hKU hz).2
    have hv : f z.1 = f z.2 := by
      rw [heF hzU,heG hzV]
      exact sub_eq_zero.mp hw
    exact (surface_pair_coordinate_regular_iff p q (hUp hzU) (hVq hzV) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hzU))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hzV))).mp (hreg z hz hv)
  obtain ⟨δ,hδ,hstable⟩ := compact_translation_stability hDc hcc hKc hregc
  refine ⟨δ,hδ,?_⟩
  intro a ha z hz hval
  have hzU := (hKU hz).1
  have hzV := (hKU hz).2
  apply (surface_pair_translation_coordinate_iff p q (hUp hzU) (hVq hzV) hF hG hρ hσ
    (heF.eventuallyEq_of_mem (hU.mem_nhds hzU))
    (heG.eventuallyEq_of_mem (hV.mem_nhds hzV))
    (heρ.eventuallyEq_of_mem (hU.mem_nhds hzU))
    (heσ.eventuallyEq_of_mem (hV.mem_nhds hzV)) a).mpr
  apply hstable a ha (κ z) ⟨z,hz,rfl⟩
  change (F (chart p z.1)-G (chart q z.2))+(ρ (chart p z.1)-σ (chart q z.2)) • a = 0
  have hf1 := heF hzU
  have hf2 := heG hzV
  have hχ1 := heρ hzU
  have hχ2 := heσ hzV
  change f z.1+χ z.1 • a = f z.2+χ z.2 • a at hval
  rw [hf1,hf2,hχ1,hχ2] at hval
  rw [sub_smul]
  calc
    _ = (F (chart p z.1)+ρ (chart p z.1) • a)-
      (G (chart q z.2)+σ (chart q z.2) • a) := by abel
    _ = 0 := sub_eq_zero.mpr hval

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ClosedFamilySeparator
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth separators constant near each member of a finite disjoint
closed family. This freezes whole quadratic crosscap neighborhoods while
regularizing double pairs outside the corresponding diagonal squares. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem closed_family_separator {ι : Type*} [Fintype ι]
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (p q : M) (hpq : p ≠ q) (hpair : ∀ i, ¬ (p ∈ A i ∧ q ∈ A i)) :
    ∃ χ : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ χ =ᶠ[𝓝 p] (fun _ => 1) ∧
      χ =ᶠ[𝓝 q] (fun _ => 0) ∧ ∀ i,
      (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
  classical
  let B₀ : Set M := {q} ∪ ⋃ i, if p ∈ A i then ∅ else A i
  let B₁ : Set M := {p} ∪ ⋃ i, if p ∈ A i then A i else ∅
  have hB₀ : IsClosed B₀ := isClosed_singleton.union (isClosed_iUnion_of_finite fun i => by
    split_ifs <;> first | exact isClosed_empty | exact hA i)
  have hB₁ : IsClosed B₁ := isClosed_singleton.union (isClosed_iUnion_of_finite fun i => by
    split_ifs <;> first | exact isClosed_empty | exact hA i)
  have hBdis : Disjoint B₀ B₁ := by
    apply Set.disjoint_left.mpr
    intro x hx₀ hx₁
    rcases hx₀ with hxq | hx₀
    · have hx : x = q := mem_singleton_iff.mp hxq
      subst x
      rcases hx₁ with hqp | hx₁
      · exact hpq (mem_singleton_iff.mp hqp).symm
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx₁
        split_ifs at hi with hp
        · exact hpair i ⟨hp,hi⟩
        · exact hi
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx₀
      split_ifs at hi with hpi
      · exact hi
      rcases hx₁ with hxp | hx₁
      · exact hpi ((mem_singleton_iff.mp hxp) ▸ hi)
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hx₁
        split_ifs at hj with hpj
        · by_cases hij : i = j
          · subst j; exact hpi hpj
          · exact Set.disjoint_left.mp (hdis hij) hi hj
        · exact hj
  obtain ⟨χ,hχ0,hχ1,hχr⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    planeModel hB₀ hB₁ hBdis (n := (⊤ : ℕ∞))
  have hpB : p ∈ B₁ := Or.inl (mem_singleton p)
  have hqB : q ∈ B₀ := Or.inl (mem_singleton q)
  refine ⟨χ,χ.contMDiff,hχr,
    hχ1.filter_mono (nhds_le_nhdsSet hpB),
    hχ0.filter_mono (nhds_le_nhdsSet hqB),?_⟩
  intro i
  by_cases hp : p ∈ A i
  · apply Or.inr
    apply hχ1.filter_mono
    apply nhdsSet_mono
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨i,by simpa [hp] using hx⟩)
  · apply Or.inl
    apply hχ0.filter_mono
    apply nhdsSet_mono
    intro x hx
    exact Or.inr (mem_iUnion.mpr ⟨i,by simpa [hp] using hx⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactPairAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absence of coincidences on a compact pair set persists under small
translations with a bounded scalar cutoff. -/
noncomputable section
open Set Filter Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M]

theorem compact_pair_avoidance_stability {f : M → ProjectionTarget 3} (hf : Continuous f)
    (χ : M → ℝ) (hχ : ∀ x, χ x ∈ Icc 0 1)
    {K : Set (M × M)} (hK : IsCompact K) (havoid : ∀ z ∈ K, f z.1 ≠ f z.2) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      surfaceTranslation f χ a z.1 ≠ surfaceTranslation f χ a z.2 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1,by norm_num,by simp⟩
  have hc : Continuous (fun z : M × M => ‖f z.1-f z.2‖) :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  have hpos : 0 < ‖f z.1-f z.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (havoid z hz))
  refine ⟨_,hpos,?_⟩
  intro a ha w hw heq
  change f w.1+χ w.1 • a = f w.2+χ w.2 • a at heq
  have hd : f w.1-f w.2 = (χ w.2-χ w.1) • a := by
    calc
      f w.1-f w.2 = (f w.1+χ w.1 • a)-(f w.2+χ w.1 • a) := by abel
      _ = (f w.2+χ w.2 • a)-(f w.2+χ w.1 • a) := by rw [heq]
      _ = (χ w.2-χ w.1) • a := by module
  have hb : |χ w.2-χ w.1| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ w.1).2,(hχ w.2).1],
    by linarith [(hχ w.1).1,(hχ w.2).2]⟩
  have hnorm : ‖f w.1-f w.2‖ ≤ ‖a‖ := by
    rw [hd,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg a)).trans_eq (one_mul _)
  exact (not_lt_of_ge (hmin hw)) (hnorm.trans_lt ha)

variable [T2Space M]
theorem compact_finite_pair_avoidance_stability {f : M → ProjectionTarget 3} (hf : Continuous f)
    (χ : M → ℝ) (hχ : ∀ x, χ x ∈ Icc 0 1)
    {K : Set (M × M)} (hK : IsCompact K) {S : Set M} (hS : S.Finite)
    (havoid : ∀ z ∈ K, z.1 ∈ S ∨ z.2 ∈ S → f z.1 ≠ f z.2) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      z.1 ∈ S ∨ z.2 ∈ S → surfaceTranslation f χ a z.1 ≠ surfaceTranslation f χ a z.2 := by
  have hclosed : IsClosed {z : M × M | z.1 ∈ S ∨ z.2 ∈ S} :=
    (hS.isClosed.preimage continuous_fst).union (hS.isClosed.preimage continuous_snd)
  obtain ⟨δ,hδ,hstable⟩ := compact_pair_avoidance_stability hf χ hχ
    (hK.inter_right hclosed) (fun z hz => havoid z hz.1 hz.2)
  exact ⟨δ,hδ,fun a ha z hz hS => hstable a ha z ⟨hz,hS⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactTranslationImmersion
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small scalar-weighted translations preserve immersion on compact
coordinate domains. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

local instance injectiveScalarNormed_rfec734_1 : NormedAddCommGroup (Base →L[ℝ] ℝ) := inferInstance
local instance injectiveScalarSpace_rfec734_1 : NormedSpace ℝ (Base →L[ℝ] ℝ) := inferInstance
theorem compact_translation_immersion {f : Base → ProjectionTarget 3} {χ : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ)
    {K : Set Base} (hK : IsCompact K)
    (hI : ∀ x ∈ K, Function.Injective (fderiv ℝ f x)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ K,
      Function.Injective (fderiv ℝ (fun y => f y+χ y • a) x) := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨ε,hε,hstable⟩ := compact_injective_stability (hK.image hD)
    (by rintro L ⟨x,hx,rfl⟩; exact hI x hx)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let B := max M 0+1
  have hB : 0 < B := by dsimp [B] <;> linarith [le_max_right M 0]
  refine ⟨ε/B,div_pos hε hB,?_⟩
  intro a ha x hx
  apply hstable (fderiv ℝ f x) ⟨x,hx,rfl⟩
  have hd := ((hf.differentiable (by simp) x).hasFDerivAt.add
    ((hχ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv
  change ‖fderiv ℝ (f + fun y => χ y • a) x-fderiv ℝ f x‖ < ε
  rw [hd,add_sub_cancel_left,ContinuousLinearMap.norm_smulRight_apply]
  have hbound : ‖fderiv ℝ χ x‖ ≤ B := (hM x hx).trans (by dsimp [B] <;> linarith [le_max_left M 0])
  calc
    _ ≤ B*‖a‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg a)
    _ < ε := by simpa only [mul_comm] using (lt_div_iff₀ hB).mp ha

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactSurfacePairStability
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact stability of actual surface double-point transversality
under a fixed smooth scalar-weighted translation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem compact_surface_pair_stability
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    {K : Set (M × M)} (hK : IsCompact K)
    (hreg : ∀ z ∈ K, f z.1 = f z.2 → Function.Surjective (surfacePairDerivative f z.1 z.2)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ z ∈ K,
      surfaceTranslation f χ a z.1 = surfaceTranslation f χ a z.2 →
      Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) z.1 z.2) := by
  classical
  have hlocal (z : K) : ∃ (W : Set (M × M)) (δ : ℝ), IsOpen W ∧ (z : M × M) ∈ W ∧
      0 < δ ∧ ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ w ∈ K ∩ W,
      surfaceTranslation f χ a w.1 = surfaceTranslation f χ a w.2 →
      Function.Surjective (surfacePairDerivative (surfaceTranslation f χ a) w.1 w.2) := by
    obtain ⟨U₁,F,hU₁,hxU₁,hU₁s,hF,heF⟩ := surface_chart_representative hf z.val.1
    obtain ⟨U₂,ρ,hU₂,hxU₂,hU₂s,hρ,heρ⟩ := scalar_surface_chart_representative hχ z.val.1
    obtain ⟨V₁,G,hV₁,hyV₁,hV₁s,hG,heG⟩ := surface_chart_representative hf z.val.2
    obtain ⟨V₂,σ,hV₂,hyV₂,hV₂s,hσ,heσ⟩ := scalar_surface_chart_representative hχ z.val.2
    let U := U₁ ∩ U₂
    let V := V₁ ∩ V₂
    have hU : IsOpen U := hU₁.inter hU₂
    have hV : IsOpen V := hV₁.inter hV₂
    obtain ⟨T,hT,hzT,hTUV⟩ := exists_compact_subset (hU.prod hV) ⟨⟨hxU₁,hxU₂⟩,hyV₁,hyV₂⟩
    have hKT : IsCompact (K ∩ T) := hK.inter hT
    obtain ⟨δ,hδ,hδreg⟩ := surface_chart_pair_stability z.val.1 z.val.2 hF hG hρ hσ hU hV
      (fun x hx => hU₁s hx.1) (fun x hx => hV₁s hx.1)
      (heF.mono inter_subset_left) (heG.mono inter_subset_left)
      (heρ.mono inter_subset_right) (heσ.mono inter_subset_right)
      hKT (fun _ hx => hTUV hx.2) (fun w hw => hreg w hw.1)
    refine ⟨interior T,δ,isOpen_interior,hzT,hδ,?_⟩
    intro a ha w hw
    exact hδreg a ha w ⟨hw.1,interior_subset hw.2⟩
  choose W δ hW hzW hδ hδreg using hlocal
  have hcover : K ⊆ ⋃ z : K, W z := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzW ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover W hW hcover
  have hsmall : ∃ ε > 0, ∀ i ∈ s, ε ≤ δ i := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε,hε,hεs⟩ := ih
      refine ⟨min ε (δ i),lt_min hε (hδ i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεs j hj)
  obtain ⟨ε,hε,hεs⟩ := hsmall
  refine ⟨ε,hε,?_⟩
  intro a ha z hz
  obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hs hz)
  exact hδreg i a (ha.trans_le (hεs i hi)) z ⟨hz,hzi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactSurfaceImmersionStability
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Immersion on a compact part of the surface is preserved by small
parameters in a fixed smooth scalar translation family. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem compact_surface_immersion_stability
    {f : M → ProjectionTarget 3} {χ : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    {K : Set M} (hK : IsCompact K)
    (hI : ∀ x ∈ K, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ K,
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (surfaceTranslation f χ a) x) := by
  classical
  have hlocal (z : K) : ∃ (V : Set M) (δ : ℝ), IsOpen V ∧ (z : M) ∈ V ∧
      0 < δ ∧ ∀ a : ProjectionTarget 3, ‖a‖ < δ → ∀ x ∈ K ∩ V,
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (surfaceTranslation f χ a) x) := by
    obtain ⟨U₁,F,hU₁,hzU₁,hU₁s,hF,heF⟩ := surface_chart_representative hf z.val
    obtain ⟨U₂,ρ,hU₂,hzU₂,hU₂s,hρ,heρ⟩ := scalar_surface_chart_representative hχ z.val
    let U := U₁ ∩ U₂
    have hU : IsOpen U := hU₁.inter hU₂
    obtain ⟨T,hT,hzT,hTU⟩ := exists_compact_subset hU ⟨hzU₁,hzU₂⟩
    have hKT : IsCompact (K ∩ T) := hK.inter hT
    have hs : K ∩ T ⊆ (chart z.val).source := fun x hx => hU₁s (hTU hx.2).1
    have hKc : IsCompact ((chart z.val) '' (K ∩ T)) :=
      hKT.image_of_continuousOn ((chart z.val).continuousOn.mono hs)
    have hIc : ∀ y ∈ (chart z.val) '' (K ∩ T), Function.Injective (fderiv ℝ F y) := by
      rintro y ⟨x,hx,rfl⟩
      exact (chart_germ_immersion_iff z.val (hs hx) hF
        (heF.eventuallyEq_of_mem (hU₁.mem_nhds (hTU hx.2).1))).mp (hI x hx.1)
    obtain ⟨δ,hδ,hstable⟩ := compact_translation_immersion hF hρ hKc hIc
    refine ⟨interior T,δ,isOpen_interior,hzT,hδ,?_⟩
    intro a ha x hx
    have hxT := interior_subset hx.2
    have hxU := hTU hxT
    apply (chart_germ_immersion_iff z.val (hU₁s hxU.1) (hF.add (hρ.smul contDiff_const))
      (surface_translation_chart_germ z.val
        (heF.eventuallyEq_of_mem (hU₁.mem_nhds hxU.1))
        (heρ.eventuallyEq_of_mem (hU₂.mem_nhds hxU.2)) a)).mpr
    exact hstable a ha (chart z.val x) ⟨x,⟨hx.1,hxT⟩,rfl⟩
  choose V δ hV hzV hδ hδI using hlocal
  have hcover : K ⊆ ⋃ z : K, V z := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzV ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV hcover
  have hsmall : ∃ ε > 0, ∀ i ∈ s, ε ≤ δ i := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε,hε,hεs⟩ := ih
      refine ⟨min ε (δ i),lt_min hε (hδ i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεs j hj)
  obtain ⟨ε,hε,hεs⟩ := hsmall
  refine ⟨ε,hε,?_⟩
  intro a ha x hx
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
  exact hδI i a (ha.trans_le (hεs i hi)) x ⟨hx,hxi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConvexDerivativeInjectivity
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed strict derivative bound excludes distinct coincidences on a
convex coordinate neighborhood. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem convex_injective_of_derivative_close
    {f : Base → ProjectionTarget 3} {L : Base →L[ℝ] ProjectionTarget 3}
    {K : NNReal} (hK : 0 < K) (hL : AntilipschitzWith K L)
    {S : Set Base} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hclose : ∀ x ∈ S, ‖fderiv ℝ f x-L‖ ≤ 1/(2*(K:ℝ))) :
    Set.InjOn f S := by
  intro x hx y hy he
  have hb := hS.norm_image_sub_le_of_norm_fderiv_le' hf hclose hx hy
  have hl := ZeroHomClass.bound_of_antilipschitz L hL (y-x)
  rw [he,sub_self,zero_sub,norm_neg] at hb
  have hKr : 0 < (K:ℝ) := hK
  have hnum : (K:ℝ)*(1/(2*(K:ℝ))) = 1/2 := by field_simp [ne_of_gt hKr]
  have hnorm : ‖y-x‖ ≤ (1/2)*‖y-x‖ := by
    calc
      ‖y-x‖ ≤ (K:ℝ)*‖L (y-x)‖ := hl
      _ ≤ (K:ℝ)*((1/(2*(K:ℝ)))*‖y-x‖) := mul_le_mul_of_nonneg_left hb hKr.le
      _ = (1/2)*‖y-x‖ := by rw [← mul_assoc,hnum]
  have hz : y-x = 0 := norm_eq_zero.mp (by linarith [norm_nonneg (y-x)])
  exact (sub_eq_zero.mp hz).symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceInjectivityPatch
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed coordinate balls with quantitative local injectivity margins. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma SurfaceInjectivityPatch.region_open {f : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p) : IsOpen P.region :=
  (chart p).isOpen_inter_preimage isOpen_ball

omit [IsManifold planeModel ∞ M] in
lemma SurfaceInjectivityPatch.mem_region {f : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p) : p ∈ P.region := by
  exact ⟨by simpa only [chart_source] using mem_chart_source Plane p,
    mem_ball_self P.radius_pos⟩

theorem exists_surface_injectivity_patch {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (p : M) (hi : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    Nonempty (SurfaceInjectivityPatch f p) := by
  have hp : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have hxp := (chart p).map_source hp
  have hI : Function.Injective (fderiv ℝ (f ∘ (chart p).symm) (chart p p)) := by
    rw [fderiv_comp_chart_symm (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p hxp,(chart p).left_inv hp]
    exact hi.comp ((chart_mdifferentiable p).symm.mfderiv_injective hxp)
  obtain ⟨K,hK,hL⟩ := (fderiv ℝ (f ∘ (chart p).symm) (chart p p)).toLinearMap.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hI)
  have hF : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hD := (hF.continuousOn_fderiv_of_isOpen (chart p).open_target (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
    ((chart p).open_target.mem_nhds hxp)
  have hc : ∀ᶠ y in 𝓝 (chart p p),
      ‖fderiv ℝ (f ∘ (chart p).symm) y-fderiv ℝ (f ∘ (chart p).symm) (chart p p)‖ < 1/(4*(K:ℝ)) := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hD) (1/(4*(K:ℝ))) (by positivity)
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((chart p).open_target.mem_nhds hxp) hc)
  refine ⟨⟨r/2,half_pos hr,?_,K,hK,hL,?_⟩⟩
  · intro y hy
    exact (hrb (closedBall_subset_ball (by linarith : r/2 < r) hy)).1
  · intro y hy
    exact (hrb (closedBall_subset_ball (by linarith : r/2 < r) hy)).2

theorem SurfaceInjectivityPatch.injective_of_close {f g : M → ProjectionTarget 3} {p : M}
    (P : SurfaceInjectivityPatch f p)
    (hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g)
    (hclose : ∀ y ∈ closedBall (chart p p) P.radius,
      ‖fderiv ℝ (g ∘ (chart p).symm) y-fderiv ℝ (f ∘ (chart p).symm) y‖ < 1/(4*(P.K:ℝ))) :
    InjOn g P.region := by
  have hG : ContDiffOn ℝ ∞ (g ∘ (chart p).symm) (chart p).target :=
    (hg.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hi : InjOn (g ∘ (chart p).symm) (closedBall (chart p p) P.radius) := by
    apply convex_injective_of_derivative_close P.K_pos P.anti (convex_closedBall _ _)
    · intro x hx
      exact (hG.contDiffAt ((chart p).open_target.mem_nhds (P.target hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · intro x hx
      calc
        _ ≤ ‖fderiv ℝ (g ∘ (chart p).symm) x-fderiv ℝ (f ∘ (chart p).symm) x‖+
            ‖fderiv ℝ (f ∘ (chart p).symm) x-fderiv ℝ (f ∘ (chart p).symm) (chart p p)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1/(2*(P.K:ℝ)) := by
          have h1 := hclose x hx
          have h2 := P.bound x hx
          have hK : 0 < (P.K:ℝ) := P.K_pos
          have he : 1/(4*(P.K:ℝ))+1/(4*(P.K:ℝ)) = 1/(2*(P.K:ℝ)) := by ring
          linarith
  intro x hx y hy he
  apply (chart p).injOn hx.1 hy.1
  apply hi (ball_subset_closedBall hx.2) (ball_subset_closedBall hy.2)
  simpa only [Function.comp_apply,(chart p).left_inv hx.1,(chart p).left_inv hy.1] using he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteInjectivityCover
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite quantitative injectivity cover of a compact immersed region. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem finite_injectivity_cover {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {B : Set M} (hB : IsCompact B)
    (hI : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
    ∃ (P : ∀ x : B, SurfaceInjectivityPatch f x.val) (s : Finset B),
      B ⊆ ⋃ x ∈ s, (P x).region := by
  classical
  let P : ∀ x : B, SurfaceInjectivityPatch f x.val := fun x =>
    Classical.choice (exists_surface_injectivity_patch hf x.val (hI x x.property))
  have hcover : B ⊆ ⋃ x : B, (P x).region :=
    fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,(P ⟨x,hx⟩).mem_region⟩
  obtain ⟨s,hs⟩ := hB.elim_finite_subcover (fun x => (P x).region)
    (fun x => (P x).region_open) hcover
  exact ⟨P,s,hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FixedSurfacePairPatch
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair patches and their cutoffs are fixed before the surface map or
perturbation size. Whole closed crosscap neighborhoods may be frozen. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem exists_fixed_surface_pair_patch {ι : Type*} [Fintype ι]
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i)) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (p q : M) (hpq : p ≠ q) (hpair : ∀ i, ¬ (p ∈ A i ∧ q ∈ A i)) :
    ∃ P : SurfacePairTranslationPatch p q, ∀ i,
      (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
  obtain ⟨χ,hχ,hχbounds,hpχ,hqχ,hAχ⟩ := closed_family_separator A hA hdis p q hpq hpair
  obtain ⟨Wp,hχWp,hWp,hpWp⟩ := _root_.mem_nhds_iff.mp hpχ
  obtain ⟨Wq,hχWq,hWq,hqWq⟩ := _root_.mem_nhds_iff.mp hqχ
  have hpS : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have hqS : q ∈ (chart q).source := by simpa only [chart_source] using mem_chart_source Plane q
  have hpO : ({p} : Set M) ⊆ Wp ∩ (chart p).source := singleton_subset_iff.mpr ⟨hpWp,hpS⟩
  have hqO : ({q} : Set M) ⊆ Wq ∩ (chart q).source := singleton_subset_iff.mpr ⟨hqWq,hqS⟩
  obtain ⟨U,hU,hpU,hclU⟩ := (isCompact_singleton (x := p)).exists_isOpen_closure_subset
    ((hWp.inter (chart p).open_source).mem_nhdsSet.mpr hpO)
  obtain ⟨V,hV,hqV,hclV⟩ := (isCompact_singleton (x := q)).exists_isOpen_closure_subset
    ((hWq.inter (chart q).open_source).mem_nhdsSet.mpr hqO)
  refine ⟨{
    χ := χ
    smooth := hχ
    bounds := hχbounds
    U := U
    V := V
    openU := hU
    openV := hV
    memU := hpU (mem_singleton p)
    memV := hqV (mem_singleton q)
    sourceU := fun x hx => (hclU hx).2
    sourceV := fun x hx => (hclV hx).2
    oneOn := fun x hx => hχWp ((hclU (subset_closure hx)).1)
    zeroOn := fun x hx => hχWq ((hclV (subset_closure hx)).1)
  },hAχ⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenTranslationGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation germs on frozen closed neighborhoods are retained by
finite compositions of the constructed scalar translation families. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M]

lemma frozenTranslationGerms_refl (A : ι → Set M) (f : M → ProjectionTarget 3) :
    FrozenTranslationGerms A f f := by
  intro i
  exact ⟨0,Filter.Eventually.of_forall fun _ => (add_zero _).symm⟩

lemma FrozenTranslationGerms.trans {A : ι → Set M} {f g h : M → ProjectionTarget 3}
    (hfg : FrozenTranslationGerms A f g) (hgh : FrozenTranslationGerms A g h) :
    FrozenTranslationGerms A f h := by
  intro i
  obtain ⟨a,ha⟩ := hfg i
  obtain ⟨b,hb⟩ := hgh i
  refine ⟨a+b,?_⟩
  filter_upwards [ha,hb] with x hax hbx
  rw [hbx,hax,add_assoc]

lemma frozenTranslationGerms_translate {A : ι → Set M} {χ : M → ℝ}
    (hχ : ∀ i, (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)))
    (f : M → ProjectionTarget 3) (a : ProjectionTarget 3) :
    FrozenTranslationGerms A f (surfaceTranslation f χ a) := by
  intro i
  rcases hχ i with h0 | h1
  · refine ⟨0,?_⟩
    filter_upwards [h0] with x hx
    simp only [surfaceTranslation,hx,zero_smul]
  · refine ⟨a,?_⟩
    filter_upwards [h1] with x hx
    simp only [surfaceTranslation,hx,one_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenGermDerivative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation germs preserve the full first derivative, and hence
preserve the prepared singularities on the frozen neighborhoods. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma mfderiv_eq_of_translation_germ {f g : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {x : M} {a : ProjectionTarget 3} (he : g =ᶠ[𝓝 x] (fun y => f y+a)) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x =
      mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x := by
  rw [he.mfderiv_eq]
  apply ContinuousLinearMap.ext
  intro v
  change (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (f + fun _ => a) x) v = _
  rw [mfderiv_add ((hf x).mdifferentiableAt (by simp)) mdifferentiableAt_const,mfderiv_const]
  change (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) v+0 = _
  exact add_zero _

lemma FrozenTranslationGerms.mfderiv_eq {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (i : ι) {x : M} (hx : x ∈ A i) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x =
      mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x := by
  obtain ⟨a,ha⟩ := h i
  exact mfderiv_eq_of_translation_germ hf (ha.filter_mono (nhds_le_nhdsSet hx))

theorem frozen_immersion_equivalence {A : ι → Set M} {B : Set M}
    (hcover : B ∪ ⋃ i, A i = univ) {f g : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (h : FrozenTranslationGerms A f g)
    (hIf : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hIg : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)) :
    ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
  intro x
  have hx : x ∈ B ∪ ⋃ i, A i := by rw [hcover]; trivial
  rcases hx with hx | hx
  · exact iff_of_true (hIg x hx) (hIf x hx)
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    rw [h.mfderiv_eq hf i hi]
    exact Iff.rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceRegularPairLocus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularity of a surface coincidence is an open first-jet condition. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem regularSurfacePairs_open {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    IsOpen (regularSurfacePairs f) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases hz with hz | hz
  · have ho : IsOpen {w : M × M | f w.1 ≠ f w.2} :=
      (isClosed_eq (hf.continuous.comp continuous_fst) (hf.continuous.comp continuous_snd)).isOpen_compl
    exact mem_of_superset (ho.mem_nhds hz) fun w hw => Or.inl hw
  · obtain ⟨U,F,hU,hzU,hUs,hF,heF⟩ := surface_chart_representative hf z.1
    obtain ⟨V,G,hV,hzV,hVs,hG,heG⟩ := surface_chart_representative hf z.2
    let H : Base × Base → ProjectionTarget 3 := fun w => F w.1-G w.2
    have hH : ContDiff ℝ ∞ H := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
    have hsurj : Function.Surjective (fderiv ℝ H (chart z.1 z.1,chart z.2 z.2)) :=
      (surface_pair_coordinate_regular_iff z.1 z.2 (hUs hzU) (hVs hzV) hF hG
        (heF.eventuallyEq_of_mem (hU.mem_nhds hzU))
        (heG.eventuallyEq_of_mem (hV.mem_nhds hzV))).mp hz
    have hc : ContinuousAt (fun w : M × M => (chart z.1 w.1,chart z.2 w.2)) z :=
      ((chart z.1).continuousAt (hUs hzU)).comp continuousAt_fst |>.prodMk
        (((chart z.2).continuousAt (hVs hzV)).comp continuousAt_snd)
    have hn : ∀ᶠ w : M × M in 𝓝 z,
        Function.Surjective (fderiv ℝ H (chart z.1 w.1,chart z.2 w.2)) :=
      hc.eventually (((surjective_clm_open).preimage
        (hH.continuous_fderiv (by simp))).mem_nhds hsurj)
    filter_upwards [(hU.prod hV).mem_nhds ⟨hzU,hzV⟩,hn] with w hw hs
    right
    exact (surface_pair_coordinate_regular_iff z.1 z.2 (hUs hw.1) (hVs hw.2) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hw.1))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hw.2))).mpr hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenPairGeometry
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translations on an entire frozen neighborhood preserve its internal
coincidences and their transverse tangent-plane geometry. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] [ChartedSpace Plane M] in
lemma FrozenTranslationGerms.coincidence_iff {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g) (i : ι) {x y : M} (hx : x ∈ A i) (hy : y ∈ A i) :
    g x = g y ↔ f x = f y := by
  obtain ⟨a,ha⟩ := h i
  have hxg := (ha.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
  have hyg := (ha.filter_mono (nhds_le_nhdsSet hy)).self_of_nhds
  change g x = f x+a at hxg
  change g y = f y+a at hyg
  rw [hxg,hyg,add_left_inj]

omit [IsManifold planeModel ∞ M] in
lemma FrozenTranslationGerms.pairDerivative_eq {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (i : ι) {x y : M} (hx : x ∈ A i) (hy : y ∈ A i) :
    surfacePairDerivative g x y = surfacePairDerivative f x y := by
  unfold surfacePairDerivative
  rw [h.mfderiv_eq hf i hx,h.mfderiv_eq hf i hy]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CleanSurfacePairs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular pairs which additionally have no coincidence involving the
prescribed finite singular set form an open, stable condition. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma mem_cleanSurfacePairs {f : M → ProjectionTarget 3} {S : Set M} {z : M × M} :
    z ∈ cleanSurfacePairs f S ↔
      (f z.1 = f z.2 → z.1 ∉ S ∧ z.2 ∉ S ∧ Function.Surjective (surfacePairDerivative f z.1 z.2)) := by
  constructor
  · rintro ⟨hr,ha⟩ he
    exact ⟨(ha.resolve_left (not_not.mpr he)).1,(ha.resolve_left (not_not.mpr he)).2,
      hr.resolve_left (not_not.mpr he)⟩
  · intro h
    by_cases he : f z.1 = f z.2
    · have hh := h he
      exact ⟨Or.inr hh.2.2,Or.inr ⟨hh.1,hh.2.1⟩⟩
    · exact ⟨Or.inl he,Or.inl he⟩

variable [IsManifold planeModel ∞ M] [T2Space M]
theorem cleanSurfacePairs_open {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {S : Set M} (hS : S.Finite) :
    IsOpen (cleanSurfacePairs f S) := by
  have he : IsOpen {z : M × M | f z.1 ≠ f z.2} :=
    (isClosed_eq (hf.continuous.comp continuous_fst) (hf.continuous.comp continuous_snd)).isOpen_compl
  have hs : IsOpen {z : M × M | z.1 ∉ S ∧ z.2 ∉ S} :=
    (hS.isClosed.isOpen_compl.preimage continuous_fst).inter
      (hS.isClosed.isOpen_compl.preimage continuous_snd)
  exact (regularSurfacePairs_open hf).inter (he.union hs)

variable [CompactSpace M]
theorem compact_clean_pair_stability {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {χ : M → ℝ} (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ) (hb : ∀ x, χ x ∈ Icc 0 1)
    {K : Set (M × M)} (hK : IsCompact K) {S : Set M} (hS : S.Finite)
    (hclean : K ⊆ cleanSurfacePairs f S) :
    ∃ δ > 0, ∀ a : ProjectionTarget 3, ‖a‖ < δ → K ⊆ cleanSurfacePairs (surfaceTranslation f χ a) S := by
  have hr : ∀ z ∈ K, f z.1 = f z.2 → Function.Surjective (surfacePairDerivative f z.1 z.2) :=
    fun z hz he => ((mem_cleanSurfacePairs.mp (hclean hz)) he).2.2
  have ha : ∀ z ∈ K, z.1 ∈ S ∨ z.2 ∈ S → f z.1 ≠ f z.2 := by
    intro z hz hS he
    have hh := (mem_cleanSurfacePairs.mp (hclean hz)) he
    rcases hS with h | h
    · exact hh.1 h
    · exact hh.2.1 h
  obtain ⟨δ,hδ,hδr⟩ := compact_surface_pair_stability hf hχ hK hr
  obtain ⟨η,hη,hηa⟩ := compact_finite_pair_avoidance_stability hf.continuous χ hb hK hS ha
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro a ha z hz
  apply mem_cleanSurfacePairs.mpr
  intro he
  have hn : ¬ (z.1 ∈ S ∨ z.2 ∈ S) :=
    fun h => hηa a (ha.trans_le (min_le_right _ _)) z hz h he
  exact ⟨(not_or.mp hn).1,(not_or.mp hn).2,hδr a (ha.trans_le (min_le_left _ _)) z hz he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenCleanPairs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen translation germs preserve both clean coincidences and their regularity. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma FrozenTranslationGerms.clean_pair {A : ι → Set M} {f g : M → ProjectionTarget 3}
    (h : FrozenTranslationGerms A f g)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (S : Set M) (i : ι) {x y : M} (hx : x ∈ A i) (hy : y ∈ A i)
    (hclean : (x,y) ∈ cleanSurfacePairs f S) : (x,y) ∈ cleanSurfacePairs g S := by
  apply mem_cleanSurfacePairs.mpr
  intro heq
  have hh := (mem_cleanSurfacePairs.mp hclean) ((h.coincidence_iff i hx hy).mp heq)
  refine ⟨hh.1,hh.2.1,?_⟩
  rw [h.pairDerivative_eq hf i hx hy]
  exact hh.2.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UncleanPairPatchCover
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cover only pairs that fail transversality or finite-point avoidance;
the compact remainder already satisfies both properties. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι]

theorem unclean_pair_patch_cover
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    {K : Set (M × M)} (hK : IsCompact K) (hne : ∀ z ∈ K, z.1 ≠ z.2)
    (S : Set M) (hS : S.Finite)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hAreg : ∀ z ∈ K, (∃ i, z.1 ∈ A i ∧ z.2 ∈ A i) → z ∈ cleanSurfacePairs f S) :
    let D := K \ cleanSurfacePairs f S
    ∃ (P : ∀ z : D, SurfacePairTranslationPatch z.val.1 z.val.2)
      (T : D → Set (M × M)) (s : Finset D) (J : Set (M × M)),
      (∀ z, IsCompact (T z) ∧ T z ⊆ (P z).U ×ˢ (P z).V) ∧
      (∀ z i, ((P z).χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨
        ((P z).χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1))) ∧
      IsCompact J ∧ J ⊆ cleanSurfacePairs f S ∧ K ⊆ J ∪ ⋃ z ∈ s, T z := by
  classical
  dsimp only
  let D := K \ cleanSurfacePairs f S
  have hD : IsCompact D := hK.diff (cleanSurfacePairs_open hf hS)
  have hex (z : D) : ∃ (P : SurfacePairTranslationPatch z.val.1 z.val.2)
      (T : Set (M × M)), IsCompact T ∧ z.val ∈ interior T ∧
      T ⊆ P.U ×ˢ P.V ∧ ∀ i,
      (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 0)) ∨ (P.χ =ᶠ[𝓝ˢ (A i)] (fun _ => 1)) := by
    have hout : ∀ i, ¬ (z.val.1 ∈ A i ∧ z.val.2 ∈ A i) := by
      intro i hi
      exact z.property.2 (hAreg z z.property.1 ⟨i,hi⟩)
    obtain ⟨P,hP⟩ := exists_fixed_surface_pair_patch A hA hdis z.val.1 z.val.2
      (hne z z.property.1) hout
    obtain ⟨T,hT,hzT,hTP⟩ := exists_compact_subset (P.openU.prod P.openV) ⟨P.memU,P.memV⟩
    exact ⟨P,T,hT,hzT,hTP,hP⟩
  choose P T hT hzT hTP hP using hex
  have hcover : D ⊆ ⋃ z : D, interior (T z) :=
    fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzT ⟨z,hz⟩⟩
  obtain ⟨s,hs⟩ := hD.elim_finite_subcover (fun z => interior (T z)) (fun _ => isOpen_interior) hcover
  let J := K \ ⋃ z ∈ s, interior (T z)
  have hJ : IsCompact J := hK.diff (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_interior)
  have hJgood : J ⊆ cleanSurfacePairs f S := by
    intro z hz
    by_contra hbad
    exact hz.2 (hs ⟨hz.1,hbad⟩)
  refine ⟨P,T,s,J,fun z => ⟨hT z,hTP z⟩,hP,hJ,hJgood,?_⟩
  intro z hz
  by_cases hu : z ∈ ⋃ i ∈ s, interior (T i)
  · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hu
    exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,interior_subset hzi⟩)
  · exact Or.inl ⟨hz,hu⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteCleanPairRegularization
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite regularization with both transversality and finite-point avoidance,
including preservation on an initially good compact set and C1 control. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι κ ν : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem finite_surface_pair_clean_relative
    (p q : ι → M) (P : ∀ i, SurfacePairTranslationPatch (p i) (q i))
    (T : ι → Set (M × M)) (hT : ∀ i, IsCompact (T i))
    (hTP : ∀ i, T i ⊆ (P i).U ×ˢ (P i).V)
    (A : κ → Set M)
    (hPA : ∀ i j, ((P i).χ =ᶠ[𝓝ˢ (A j)] (fun _ => 0)) ∨
      ((P i).χ =ᶠ[𝓝ˢ (A j)] (fun _ => 1)))
    (S : Set M) (hS : S.Finite) (J : Set (M × M)) (hJ : IsCompact J)
    [Fintype ν] (c : ν → M) (Q : ν → Set JetPolynomial.Base)
    (hQ : ∀ j, IsCompact (Q j)) (hQT : ∀ j, Q j ⊆ (chart (c j)).target)
    (s : Finset ι) (B : Set M) (hB : IsCompact B) {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hIf : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hJreg : J ⊆ cleanSurfacePairs f S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      ChartDerivativeClose c Q f g ε ∧
      (∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)) ∧
      (J ⊆ cleanSurfacePairs g S) ∧
      ∀ i ∈ s, T i ⊆ cleanSurfacePairs g S := by
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty =>
    exact ⟨f,hf,frozenTranslationGerms_refl A f,by simpa using fun _ : M => hε,by intro j x hx; simpa using hε,hIf,hJreg,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨g,hg,hfg,hclose,hDc,hIg,hJg,hgood⟩ := ih (half_pos hε)
    let K := J ∪ ⋃ j ∈ s, T j
    have hK : IsCompact K := hJ.union (s.isCompact_biUnion (fun j _ => hT j))
    have hKreg : K ⊆ cleanSurfacePairs g S := by
      intro z hz
      rcases hz with hz | hz
      · exact hJg hz
      · obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hz
        exact hgood j hj hzj
    obtain ⟨δ,hδ,hstable⟩ := compact_clean_pair_stability hg (P i).smooth (P i).bounds hK hS hKreg
    obtain ⟨η,hη,hηI⟩ := compact_surface_immersion_stability hg (P i).smooth hB hIg
    obtain ⟨ζ,hζ,hζD⟩ := finite_chart_translation_bound c Q hQ hQT (P i).smooth (half_pos hε)
    obtain ⟨a,ha,hnew⟩ := (P i).regularize_avoiding_points hg S S hS hS (lt_min hδ (lt_min hη (lt_min hζ (half_pos hε))))
    let G := surfaceTranslation g (P i).χ a
    have haδ : ‖a‖ < δ := ha.trans_le (min_le_left _ _)
    have haη : ‖a‖ < η := ha.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have haζ : ‖a‖ < ζ := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have haε : ‖a‖ < ε/2 := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨G,surfaceTranslation_smooth hg (P i).smooth a,
      hfg.trans (frozenTranslationGerms_translate (hPA i) g a),?_,?_,hηI a haη,?_,?_⟩
    · intro x
      have hx : ‖G x-g x‖ < ε/2 := by
        change ‖g x+(P i).χ x • a-g x‖ < ε/2
        rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ((P i).bounds x).1]
        exact (mul_le_mul_of_nonneg_right ((P i).bounds x).2 (norm_nonneg a)).trans_lt (by simpa using haε)
      calc
        ‖G x-f x‖ ≤ ‖G x-g x‖+‖g x-f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε/2+ε/2 := add_lt_add hx (hclose x)
        _ = ε := by ring
    · intro j x hx
      have hd := hζD hg a haζ j x hx
      calc
        _ ≤ ‖fderiv ℝ (G ∘ (chart (c j)).symm) x-fderiv ℝ (g ∘ (chart (c j)).symm) x‖+
            ‖fderiv ℝ (g ∘ (chart (c j)).symm) x-fderiv ℝ (f ∘ (chart (c j)).symm) x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε/2+ε/2 := add_lt_add hd (hDc j x hx)
        _ = ε := by ring
    · intro z hz
      exact hstable a haδ (Or.inl hz)
    · intro j hj z hz
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact mem_cleanSurfacePairs.mpr (hnew z.1 (hTP j hz).1 z.2 (hTP j hz).2)
      · exact hstable a haδ (Or.inr (mem_iUnion₂.mpr ⟨j,hj,hz⟩))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactCleanPairRegularization
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative transversality on compact pair sets, including sets that
meet the frozen crosscap neighborhoods. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M ι ν : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι] [Fintype ν]

theorem compact_relative_clean_pair_regularization
    (A : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    {K : Set (M × M)} (hK : IsCompact K) (hne : ∀ z ∈ K, z.1 ≠ z.2)
    (S : Set M) (hS : S.Finite)
    (c : ν → M) (Q : ν → Set Base) (hQ : ∀ j, IsCompact (Q j))
    (hQT : ∀ j, Q j ⊆ (chart (c j)).target)
    (B : Set M) (hB : IsCompact B)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hIf : ∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hAreg : ∀ z ∈ K, (∃ i, z.1 ∈ A i ∧ z.2 ∈ A i) → z ∈ cleanSurfacePairs f S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      ChartDerivativeClose c Q f g ε ∧
      (∀ x ∈ B, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)) ∧
      K ⊆ cleanSurfacePairs g S := by
  obtain ⟨P,T,s,J,hT,hPA,hJ,hJreg,hcover⟩ := unclean_pair_patch_cover A hA hdis hK hne S hS hf hAreg
  obtain ⟨g,hg,hfg,hclose,hD,hI,hJg,hgood⟩ := finite_surface_pair_clean_relative
    (fun z : {z : M × M // z ∈ K ∧ z ∉ cleanSurfacePairs f S} => z.val.1)
    (fun z : {z : M × M // z ∈ K ∧ z ∉ cleanSurfacePairs f S} => z.val.2) P T
    (fun z => (hT z).1) (fun z => (hT z).2) A hPA S hS J hJ c Q hQ hQT s B hB hf hIf
    hJreg hε
  refine ⟨g,hg,hfg,hclose,hD,hI,?_⟩
  intro z hz
  rcases hcover hz with hz | hz
  · exact hJg hz
  · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hz
    exact hgood i hi hzi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_GlobalCleanPairRegularization
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global regularization with a fixed injectivity cover and frozen
crosscap neighborhoods. No distinct double pair is left uncontrolled. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M ι ν : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι] [Fintype ν]

theorem global_clean_pair_regularization_with_cover
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (A U : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hU : ∀ i, IsOpen (U i)) (hUA : ∀ i, U i ⊆ A i)
    (hIf : ∀ x, x ∉ ⋃ i, U i → Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (S : Set M) (hS : S.Finite)
    (hAclean : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ cleanSurfacePairs f S)
    (c : ν → M) (P : ∀ j, SurfaceInjectivityPatch f (c j))
    (hcover : (⋃ i, U i) ∪ (⋃ j, (P j).region) = univ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      ∀ x y, x ≠ y → (x,y) ∈ cleanSurfacePairs g S := by
  classical
  let B : Set M := (⋃ i, U i)ᶜ
  have hB : IsCompact B := (isOpen_iUnion hU).isClosed_compl.isCompact
  let W : Set (M × M) := (⋃ i, U i ×ˢ U i) ∪ (⋃ j, (P j).region ×ˢ (P j).region)
  let K : Set (M × M) := Wᶜ
  have hW : IsOpen W := (isOpen_iUnion fun i => (hU i).prod (hU i)).union
    (isOpen_iUnion fun j => (P j).region_open.prod (P j).region_open)
  have hK : IsCompact K := hW.isClosed_compl.isCompact
  have hne : ∀ z ∈ K, z.1 ≠ z.2 := by
    rintro ⟨x,y⟩ hz hxy
    have hx : x ∈ (⋃ i, U i) ∪ ⋃ j, (P j).region := by rw [hcover]; trivial
    apply hz
    rcases hx with hx | hx
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact Or.inl (mem_iUnion.mpr ⟨i,hi,hxy ▸ hi⟩)
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨j,hj,hxy ▸ hj⟩)
  let Q : ν → Set Base := fun j => Metric.closedBall (chart (c j) (c j)) (P j).radius
  have hsmall (s : Finset ν) : ∃ η > 0, η ≤ ε ∧ ∀ j ∈ s, η ≤ 1/(4*((P j).K:ℝ)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨ε,hε,le_rfl,by simp⟩
    | @insert j s hj ih =>
      obtain ⟨η,hη,hηε,hηs⟩ := ih
      have hp : 0 < 1/(4*((P j).K:ℝ)) := by have := (P j).K_pos; positivity
      refine ⟨min η (1/(4*((P j).K:ℝ))),lt_min hη hp,(min_le_left _ _).trans hηε,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hηs k hk)
  obtain ⟨η,hη,hηε,hηP⟩ := hsmall Finset.univ
  obtain ⟨g,hg,hfg,hclose,hD,hIg,hgood⟩ := compact_relative_clean_pair_regularization A hA hdis hK hne S hS
    c Q (fun j => isCompact_closedBall _ _) (fun j => (P j).target)
    B hB hf hIf
    (by rintro z hz ⟨i,hix,hiy⟩; exact hAclean i z.1 hix z.2 hiy (hne z hz)) hη
  have hIpatch (j : ν) : InjOn g (P j).region := (P j).injective_of_close hg
    (fun y hy => (hD j y hy).trans_le (hηP j (Finset.mem_univ j)))
  have hBA : B ∪ ⋃ i, A i = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ ⋃ i, U i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,hUA i hi⟩)
    · exact Or.inl hx
  refine ⟨g,hg,hfg,fun x => (hclose x).trans_le hηε,
    frozen_immersion_equivalence hBA hf hfg hIf hIg,?_⟩
  intro x y hxy
  by_cases hxyK : (x,y) ∈ K
  · exact hgood hxyK
  have hxyW : (x,y) ∈ W := by simpa only [K,mem_compl_iff,not_not] using hxyK
  rcases hxyW with hu | hp
  · obtain ⟨i,hxi,hyi⟩ := mem_iUnion.mp hu
    exact hfg.clean_pair hf S i (hUA i hxi) (hUA i hyi)
      (hAclean i x (hUA i hxi) y (hUA i hyi) hxy)
  · obtain ⟨j,hxj,hyj⟩ := mem_iUnion.mp hp
    apply mem_cleanSurfacePairs.mpr
    intro hgeq
    exact False.elim (hxy (hIpatch j hxj hyj hgeq))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RelativeGlobalCleanPairs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the quantitative injectivity cover before regularizing
all double pairs on the surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype ι]

theorem relative_global_clean_pairs
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (A U : ι → Set M) (hA : ∀ i, IsClosed (A i))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hU : ∀ i, IsOpen (U i)) (hUA : ∀ i, U i ⊆ A i)
    (hIf : ∀ x, x ∉ ⋃ i, U i → Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (S : Set M) (hS : S.Finite)
    (hAclean : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ cleanSurfacePairs f S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      FrozenTranslationGerms A f g ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      ∀ x y, x ≠ y → (x,y) ∈ cleanSurfacePairs g S := by
  classical
  let B : Set M := (⋃ i, U i)ᶜ
  have hB : IsCompact B := (isOpen_iUnion hU).isClosed_compl.isCompact
  obtain ⟨P,s,hs⟩ := finite_injectivity_cover hf hB hIf
  let c : s → M := fun j => j.val.val
  let Q : ∀ j : s, SurfaceInjectivityPatch f (c j) := fun j => P j.val
  have hcover : (⋃ i, U i) ∪ (⋃ j : s, (Q j).region) = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ ⋃ i, U i
    · exact Or.inl hx
    · obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (hs hx)
      exact Or.inr (mem_iUnion.mpr ⟨⟨j,hj⟩,hxj⟩)
  exact global_clean_pair_regularization_with_cover hf A U hA hdis hU hUA hIf S hS hAclean c Q hcover hε

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TaylorTargetTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Target translations preserve the prepared Taylor polynomial and its
crosscap direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceTaylorTwo_add_const (f : Base → ProjectionTarget 3) (c : ProjectionTarget 3) :
    surfaceTaylorTwo (fun x => f x+c) = fun x => surfaceTaylorTwo f x+c := by
  have hd : fderiv ℝ (fun x => f x+c) = fderiv ℝ f := funext fun x => fderiv_add_const c
  funext x
  simp only [surfaceTaylorTwo,hd]
  abel

lemma centeredSurfaceTaylor_add_const (f : Base → ProjectionTarget 3) (a : Base)
    (c : ProjectionTarget 3) :
    centeredSurfaceTaylor (fun x => f x+c) a = fun x => centeredSurfaceTaylor f a x+c := by
  have ht : translatedSurface (fun x => f x+c) a = fun x => translatedSurface f a x+c := rfl
  funext x
  simp only [centeredSurfaceTaylor,ht,surfaceTaylorTwo_add_const]

lemma surfaceDirection_add_const (f : Base → ProjectionTarget 3) (b : Bool)
    (c : ProjectionTarget 3) : surfaceDirection (fun x => f x+c) b = surfaceDirection f b := by
  funext z
  simp only [surfaceDirection,fderiv_add_const]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteCrosscapCleanup
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prepared finite-crosscap map with global self-transversality and no
additional preimage of any singular point image, preserving every quadratic germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem clean_finite_quadratic_map_oai {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : QuadraticCrosscapGerms f) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) ↔
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) ∧
      (∀ x y, x ≠ y → g x = g y → Function.Surjective (surfacePairDerivative g x y)) ∧
      (∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) →
        ∀ q, g q = g p → q = p) ∧ QuadraticCrosscapGerms g := by
  classical
  let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  let : Fintype S := hfin.fintype
  obtain ⟨A,hA,hdis,hAreg⟩ := prepared_clean_crosscap_neighborhoods hfin hrep
  let U : S → Set M := fun i => interior (A i)
  have hIf : ∀ x, x ∉ ⋃ i : S, U i →
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
    intro x hx
    by_contra hbad
    exact hx (mem_iUnion.mpr ⟨⟨x,hbad⟩,(hA ⟨x,hbad⟩).2⟩)
  obtain ⟨g,hg,hfg,_,hI,hreg⟩ := relative_global_clean_pairs hf A U
    (fun i => (hA i).1.isClosed) hdis (fun _ => isOpen_interior)
    (fun _ => interior_subset) hIf S hfin hAreg zero_lt_one
  refine ⟨g,hg,hI,?_,?_,?_⟩
  · intro x y hxy heq
    exact ((mem_cleanSurfacePairs.mp (hreg x y hxy)) heq).2.2
  · intro p hp q heq
    by_contra hqp
    have hpf : p ∈ S := (hI p).not.mp hp
    exact ((mem_cleanSurfacePairs.mp (hreg q p hqp)) heq).2.1 hpf
  · intro p hp
    have hpf : p ∈ S := by exact (hI p).not.mp hp
    obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hr⟩ := hrep p hpf
    obtain ⟨a,ha⟩ := hfg ⟨p,hpf⟩
    have hpa : p ∈ A ⟨p,hpf⟩ := interior_subset (hA ⟨p,hpf⟩).2
    have htrans : g =ᶠ[𝓝 p] (fun x => f x+a) := ha.filter_mono (nhds_le_nhdsSet hpa)
    refine ⟨q,(fun x => φ x+a),b,t,hpq,hφ.add contDiff_const,?_,?_,?_⟩
    · rw [centeredSurfaceTaylor_add_const]
      filter_upwards [htrans,he] with x hx hex
      change g x = centeredSurfaceTaylor φ (chart q p) (chart q x)+a
      rw [hx,hex]
      rfl
    · rwa [surfaceDirection_add_const]
    · rwa [surfaceDirection_add_const]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.clean_finite_quadratic_map_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.clean_finite_quadratic_map_oai.{u_1}
