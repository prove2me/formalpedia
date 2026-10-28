-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.boundary_jets_global
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:51:39.559476+00:00
-- url     : https://prove2.me/submissions/e89bbf83-93c8-4a73-9de8-5d1373fe7f53

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_boundary_normal_step
import Theorems.Thm_OAI_ElasticityBoundaryPacket_boundary_values_global

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

end ElasticityBoundary

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCharts
attribute [-instance] _root_.OAI.Elasticity.instCompleteSpaceSubtypeJetHMemSubmoduleRealH10Hilbert _root_.OAI.Elasticity.temperate_restrict_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Orthogonal normalization of an honest physical boundary chart. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

lemma coordinateNormal_inner (B : X ≃L[ℝ] X) (z : X) :
    inner ℝ (coordinateNormal B) z = B z 0 := by
  exact InnerProductSpace.toDual_symm_apply

lemma coordinateNormal_ne_zero (B : X ≃L[ℝ] X) : coordinateNormal B ≠ 0 := by
  intro h
  have hi := coordinateNormal_inner B (B.symm (EuclideanSpace.single 0 1))
  rw [h, inner_zero_left, B.apply_symm_apply] at hi
  simp at hi

lemma coordinateFrame_first (B : X ≃L[ℝ] X) :
    coordinateFrame B (EuclideanSpace.single 2 1) =
      ‖coordinateNormal B‖⁻¹ • coordinateNormal B := by
  apply Submodule.reflection_sub
  rw [PiLp.norm_single, norm_one, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (coordinateNormal_ne_zero B)

/-- This normalization preserves the physical half-space without changing its
positive side. It also keeps the physical metric Euclidean at the base point. -/
theorem coordinateFrame_normal (B : X ≃L[ℝ] X) (z : X) :
    B (coordinateFrame B z) 0 = ‖coordinateNormal B‖ * z 2 := by
  have hn : ‖coordinateNormal B‖ ≠ 0 := norm_ne_zero_iff.mpr (coordinateNormal_ne_zero B)
  have h : ‖coordinateNormal B‖ • coordinateFrame B (EuclideanSpace.single 2 1) =
      coordinateNormal B := by
    rw [coordinateFrame_first, smul_smul, mul_inv_cancel₀ hn, one_smul]
  calc
    B (coordinateFrame B z) 0 = inner ℝ (coordinateNormal B) (coordinateFrame B z) :=
      (coordinateNormal_inner B _).symm
    _ = inner ℝ (‖coordinateNormal B‖ • coordinateFrame B (EuclideanSpace.single 2 1))
        (coordinateFrame B z) := congrArg (fun v => inner ℝ v (coordinateFrame B z)) h.symm
    _ = ‖coordinateNormal B‖ * z 2 := by
      rw [inner_smul_left, (coordinateFrame B).inner_map_map, EuclideanSpace.inner_single_left]
      simp

lemma coordinateFrame_positive (B : X ≃L[ℝ] X) (z : X) :
    0 < B (coordinateFrame B z) 0 ↔ 0 < z 2 := by
  rw [coordinateFrame_normal]
  exact mul_pos_iff_of_pos_left (norm_pos_iff.mpr (coordinateNormal_ne_zero B))

end Elasticity

end
end
section
/-! Honest boundary coordinates with orthogonal physical derivative at the
base point. The inward normal is coordinate 2, matching the frozen physical
half-space ODE. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x ∈ e.source)

lemma normalizedParam_source :
    (normalizedParam e he hi hx).source =
      {z | normalizedLinear e he hi hx z + e x ∈ e.target} := by
  ext z
  simp [normalizedParam]

lemma normalizedParam_zero_source : (0 : X) ∈ (normalizedParam e he hi hx).source := by
  rw [normalizedParam_source]
  simpa using e.map_source hx

lemma normalizedParam_contDiff :
    ContDiffOn ℝ (⊤ : ℕ∞) (normalizedParam e he hi hx)
      (normalizedParam e he hi hx).source := by
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z => normalizedLinear e he hi hx z + e x) :=
    (normalizedLinear e he hi hx).contDiff.add contDiff_const
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => e.symm (normalizedLinear e he hi hx z + e x)) _
  apply hi.comp ha.contDiffOn
  intro z hz
  simpa only [normalizedParam_source, Set.mem_ofPred_eq] using hz

lemma normalizedParam_symm_contDiff :
    ContDiffOn ℝ (⊤ : ℕ∞) (normalizedParam e he hi hx).symm
      (normalizedParam e he hi hx).target := by
  rw [normalizedParam_target]
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => e y - e x) e.source :=
    he.sub contDiffOn_const
  exact ((normalizedLinear e he hi hx).symm.contDiff.comp_contDiffOn hs)

lemma normalizedParam_fderiv :
    HasFDerivAt (normalizedParam e he hi hx)
      (coordinateFrame (chartDerivativeEquiv e he hi hx)).toContinuousLinearEquiv.toContinuousLinearMap 0 := by
  let B := chartDerivativeEquiv e he hi hx
  let Q := coordinateFrame B
  have hb : HasFDerivAt e.symm B.symm.toContinuousLinearMap (e x) :=
    ((hi.differentiableOn (by simp)).differentiableAt
      (e.open_target.mem_nhds (e.map_source hx))).hasFDerivAt
  have ha := ((normalizedLinear e he hi hx).hasFDerivAt (x := (0 : X))).add_const (e x)
  have hcomp := (by simpa using hb : HasFDerivAt e.symm B.symm.toContinuousLinearMap
    (normalizedLinear e he hi hx 0 + e x)).comp 0 ha
  have hQ : B.symm.toContinuousLinearMap.comp
      (normalizedLinear e he hi hx).toContinuousLinearMap =
      Q.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    exact B.symm_apply_apply (Q z)
  rw [hQ] at hcomp
  exact hcomp

lemma normalizedParam_halfspace {Ω : Set X} (h0 : e x 0 = 0)
    (hΩ : ∀ y ∈ e.source, y ∈ Ω ↔ 0 < e y 0)
    {z : X} (hz : z ∈ (normalizedParam e he hi hx).source) :
    normalizedParam e he hi hx z ∈ Ω ↔ 0 < z 2 := by
  have ht : normalizedLinear e he hi hx z + e x ∈ e.target :=
    by simpa only [normalizedParam_source, Set.mem_ofPred_eq] using hz
  rw [normalizedParam_apply, hΩ _ (e.map_target ht), e.right_inv ht]
  change 0 < (chartDerivativeEquiv e he hi hx)
    (coordinateFrame (chartDerivativeEquiv e he hi hx) z) 0 + e x 0 ↔ _
  rw [h0, add_zero]
  exact coordinateFrame_positive _ z

/-- Normalized local physical parametrizations exist at every boundary point
of a domain with smooth open boundary charts. No regularity is imposed on the
Lamé moduli here. -/
theorem SourceSmoothBoundary.normalized {Ω : Set X} (h : SourceSmoothBoundary Ω)
    {x : X} (hx : x ∈ frontier Ω) :
    ∃ (φ : OpenPartialHomeomorph X X) (Q : X ≃ₗᵢ[ℝ] X),
      (0 : X) ∈ φ.source ∧ φ 0 = x ∧
      ContDiffOn ℝ (⊤ : ℕ∞) φ φ.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) φ.symm φ.target ∧
      HasFDerivAt φ Q.toContinuousLinearEquiv.toContinuousLinearMap 0 ∧
      ∀ z ∈ φ.source, φ z ∈ Ω ↔ 0 < z 2 := by
  obtain ⟨e, hxs, he, hi, h0, hΩ⟩ := h x hx
  exact ⟨normalizedParam e he hi hxs, coordinateFrame (chartDerivativeEquiv e he hi hxs),
    normalizedParam_zero_source e he hi hxs, normalizedParam_zero e he hi hxs,
    normalizedParam_contDiff e he hi hxs, normalizedParam_symm_contDiff e he hi hxs,
    normalizedParam_fderiv e he hi hxs,
    fun _ hz => normalizedParam_halfspace e he hi hxs h0 hΩ hz⟩

end Elasticity

end
end
section
/-! Smooth compact extensions of genuine local maps, in arbitrary finite
 dimensional physical and coordinate spaces. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The output may itself be an actual chart or vector displacement. -/
theorem smooth_vector_extension {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K⊆U) (f : E → F) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ g =ᶠ[𝓝ˢ K] f := by
  obtain ⟨χ,hχ,hc,hs,h1,_⟩ := compact_smooth_cutoff hK hU hKU
  refine ⟨fun x => χ x • f x,contDiff_cutoff_smul hU f χ hf hχ hs,?_,?_⟩
  · exact hc.smul_right
  · filter_upwards [h1] with x hx
    simp [hx]

end ElasticityBoundary

end
end
section
/-! Transferring a trial supported in an honest chart produces an actual
 globally smooth compact physical field, without imposing artificial boundary
 data. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cutoffs and both globally smooth chart extensions exist from honest source
 hypotheses. The extensions agree near the whole compact supports used in the
 physical change of variables. -/
theorem compact_chart_data (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hs : K⊆e.source) :
    ∃ (η : E → ℝ) (Φ Ψ : E → E),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η⊆e.target ∧
      η =ᶠ[𝓝ˢ (e '' K)] (fun _ => 1) ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ Φ =ᶠ[𝓝ˢ K] e ∧
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ Ψ =ᶠ[𝓝ˢ (tsupport η)] e.symm := by
  have hKe : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hs)
  have hst : e '' K⊆e.target := by
    rintro x ⟨y,hy,rfl⟩
    exact e.map_source (hs hy)
  obtain ⟨η,hη,hc,hηs,hη1,_⟩ := compact_smooth_cutoff hKe e.open_target hst
  obtain ⟨Φ,hΦ,_,hΦe⟩ := smooth_vector_extension hK e.open_source hs e he
  obtain ⟨Ψ,hΨ,_,hΨe⟩ := smooth_vector_extension hc e.open_target hηs e.symm hi
  exact ⟨η,Φ,Ψ,hη,hc,hηs,hη1,hΦ,hΦe,hΨ,hΨe⟩

end ElasticityBoundary

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer
  ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryLayerOperator ElasticityBoundaryPhysicalTransfer

lemma Setup.zero_mem {Ω : Set X} {x : X} (s : Setup Ω x) : (0:X)∈s.K := by
  apply s.cutoff_support
  change s.cutoff 0≠0
  rw [s.cutoff_one.eq_of_nhds]
  exact one_ne_zero

end ElasticityBoundaryPacket

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Projection-stable packet supports are constructed inside honest open charts. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary ElasticityBoundaryNormalTaylor
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer
lemma setup_ball_exists {Ω : Set X} (h : SourceSmoothBoundary Ω) {x : X} (hx : x∈frontier Ω) :
    ∃ s : Setup Ω x, ∃ r : ℝ, 0 < r ∧ s.K=Metric.closedBall 0 r := by
  obtain ⟨e,Q,he0,hec,he,hi,hQ,hhalf⟩ := h.normalized hx
  obtain ⟨r,hr,hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_source.mem_nhds he0)
  obtain ⟨χ,hχ,hχc,hχs,hχ0,_⟩ := compact_smooth_cutoff (isCompact_singleton (x := (0:X)))
    Metric.isOpen_ball (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  let K := Metric.closedBall (0:X) r
  have hK : IsCompact K := isCompact_closedBall 0 r
  have hχK : tsupport χ⊆K := fun z hz => Metric.ball_subset_closedBall (hχs hz)
  obtain ⟨η,Φ,Ψ,hη,hηc,hηs,hη1,hΦ,hΦe,hΨ,hΨe⟩ := compact_chart_data e he hi hK hrs
  have hηK : ∀ z∈e '' K, η z=1 := fun z hz => hη1.self_of_nhdsSet hz
  have hKη : e '' K⊆tsupport η := by
    intro z hz
    exact subset_tsupport η (show η z≠0 from by rw [hηK z hz]; exact one_ne_zero)
  let χc : Y → ℂ := fun y => (χ (WithLp.toLp 2 y):ℂ)
  have hχcs : ContDiff ℝ (⊤ : ℕ∞) χc :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp PiLp.contDiff_toLp)
  have hχcc : HasCompactSupport χc :=
    (hχc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  have hχc0 : χc =ᶠ[𝓝 (0:Y)] fun _ => 1 := by
    have hh : χ =ᶠ[𝓝 (0:X)] fun _ => 1 := by
      change ∀ᶠ z in 𝓝 (0:X), χ z=1
      simpa only [nhdsSet_singleton] using hχ0
    have ht : Tendsto (WithLp.toLp 2 : Y → X) (𝓝 (0:Y)) (𝓝 (0:X)) :=
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).continuousAt
    filter_upwards [hh.comp_tendsto ht] with y hy
    change χ (WithLp.toLp 2 y)=1 at hy
    simp only [χc,hy,Complex.ofReal_one]
  refine ⟨{
    e := e, Q := Q, at_zero := he0, center := hec, smooth := he,
    inverse_smooth := hi, deriv := hQ, inside := hhalf, K := K, compact := hK,
    source := hrs, cutoff := χc, cutoff_smooth := hχcs, cutoff_compact := hχcc,
    cutoff_one := hχc0, cutoff_support := ?_, η := η, η_smooth := hη,
    η_compact := hηc, η_support := hηs, η_one := hηK, Φ := Φ, Ψ := Ψ,
    Φ_smooth := hΦ, Ψ_smooth := hΨ, Φ_germ := ?_, Ψ_germ := ?_ },r,hr,rfl⟩
  · intro z hz
    apply hχK
    apply subset_tsupport χ
    intro hc
    exact hz (by simp [χc,hc])
  · intro y hy
    exact hΦe.filter_mono (nhds_le_nhdsSet hy)
  · intro z hz
    exact hΨe.filter_mono (nhds_le_nhdsSet (hKη hz))

end ElasticityBoundaryPacket

end
end
section
/-! Flat finite jets remain flat under arbitrary honest smooth coordinates.
This is a consequence of the actual Faà di Bruno formula. -/
noncomputable section
namespace ElasticityBoundaryFlatComposition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma comp_flat {f : F → G} {g : E → F} {x : E} (n : ℕ)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (g x)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hz : ∀ k≤n, iteratedFDeriv ℝ k f (g x)=0) :
    iteratedFDeriv ℝ n (f ∘ g) x=0 := by
  rw [iteratedFDeriv_comp hf hg (by exact_mod_cast le_top)]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext v
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    ftaylorSeries, hz c.length c.length_le,zero_apply]

end ElasticityBoundaryFlatComposition

end
end
section
/-! The flattened zero plane consists of actual boundary points; lower
physical jets give actual normal Taylor remainders on a ball packet support. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryNormalTaylor ElasticityBoundaryFlatComposition
variable {Ω : Set X} {x : X}

lemma Setup.plane_frontier (s : Setup Ω x) (hO : IsOpen Ω)
    {y : X} (hy : y∈s.e.source) (hz : y 2=0) : s.e y∈frontier Ω := by
  have hn : s.e y∉Ω := by
    rw [s.inside y hy,hz]
    exact lt_irrefl 0
  have hct : Continuous (fun t : ℝ => y+t • EuclideanSpace.single 2 (1:ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => y+t • EuclideanSpace.single 2 (1:ℝ)) (𝓝[>] 0) (𝓝 y) := by
    simpa only [zero_smul,add_zero] using hct.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hm : ∀ᶠ t : ℝ in 𝓝[>] 0, s.e (y+t • EuclideanSpace.single 2 (1:ℝ))∈Ω := by
    filter_upwards [ht (s.e.open_source.mem_nhds hy),self_mem_nhdsWithin] with t hty htp
    rw [s.inside _ hty]
    simpa [hz,PiLp.single_apply] using htp
  have hc : s.e y∈closure Ω := mem_closure_of_tendsto
    (((s.smooth.continuousOn y hy).continuousAt (s.e.open_source.mem_nhds hy)).tendsto.comp ht) hm
  rw [hO.frontier_eq]
  exact ⟨hc,hn⟩

lemma Setup.chartFunction_smooth (s : Setup Ω x) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (s.chartFunction f) :=
  hf.comp (s.Φ_smooth.comp PiLp.contDiff_toLp)

lemma Setup.chart_flat (s : Setup Ω x) (hO : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k f z=0)
    {y : Y} (hy : WithLp.toLp 2 y∈s.K) (hy0 : y 2=0) :
    iteratedFDeriv ℝ n (s.chartFunction f) y=0 := by
  apply comp_flat n hf.contDiffAt (s.Φ_smooth.comp PiLp.contDiff_toLp).contDiffAt
  intro k hk
  change iteratedFDeriv ℝ k f (s.Φ (WithLp.toLp 2 y))=0
  rw [(s.Φ_germ _ hy).eq_of_nhds]
  exact hz k hk _ (s.plane_frontier hO (s.source hy) hy0)

end ElasticityBoundaryPacket

end
end
section
/-! Schwarz symmetry at every finite order for real C-infinity functions.
The analytic-only generic-field theorem is not used. -/
noncomputable section
namespace ElasticityBoundaryJetSymmetry
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma dir_smooth {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (dir v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma word_smooth {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (vs : List E) :
    ContDiff ℝ (⊤ : ℕ∞) (word vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact dir_smooth ih v

lemma dir_comm {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w : E) :
    dir v (dir w f)=dir w (dir v f) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)).differentiableAt
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top)))
  have he (z : E) : fderiv ℝ (dir z f) x=(fderiv ℝ (fderiv ℝ f) x).flip z := by
    unfold dir
    rw [fderiv_clm_apply hd (differentiableAt_const z)]
    simp
  change fderiv ℝ (dir w f) x v=fderiv ℝ (dir v f) x w
  rw [he,he]
  exact hs v w

lemma word_perm {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {vs ws : List E}
    (h : vs.Perm ws) : word vs f=word ws f := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [word,ih]
  | swap v w vs => exact dir_comm (word_smooth hf vs) w v
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma word_ofFn {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (v : Fin n → E) (x : E) :
    word (List.ofFn v) f x=iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => simp [word]
  | succ n ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (word (List.ofFn (fun i => v i.succ)) f) x (v 0)=_
    have he : word (List.ofFn (fun i => v i.succ)) f=
        (fun y => iteratedFDeriv ℝ n f y (fun i => v i.succ)) := by
      funext y
      exact ih _ y
    rw [he,fderiv_continuousMultilinear_apply_const
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast (WithTop.coe_lt_top n))).differentiableAt]
    rfl

lemma iterated_perm {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) (x : E) :
    iteratedFDeriv ℝ n f x (fun i => v (σ i))=iteratedFDeriv ℝ n f x v := by
  rw [← word_ofFn hf,← word_ofFn hf]
  exact congrFun (word_perm hf (σ.ofFn_comp_perm v)) x

end ElasticityBoundaryJetSymmetry

end
end
section
/-! Lower full jets vanish on a hypersurface, and the next pure-normal jet
then determines the entire next tensor. No analyticity is used. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryFlatHyperplane
open ElasticityBoundaryJetSymmetry ElasticityBoundaryNormalTaylor
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tangent_deriv_zero {g : Y → F} (hg : DifferentiableAt ℝ g 0)
    {r : ℝ} (hr : 0 < r) (hz : ∀ y∈Metric.ball (0:Y) r, y 2=0 → g y=0)
    {v : Y} (hv : v 2=0) : fderiv ℝ g 0 v=0 := by
  have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0:Y)) := by
    simpa only [zero_smul] using hc.continuousAt.tendsto (x := (0:ℝ))
  have he : (fun t : ℝ => g (t • v)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ht (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with t ht
    exact hz _ ht (by simp [hv])
  have hd := (show DifferentiableAt ℝ g ((0:Y)+(0:ℝ) • v) by simpa using hg).deriv_comp_add_smul
  simp only [zero_add,zero_smul] at hd
  rw [← hd,he.deriv_eq,deriv_const]

lemma flat_step {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    {r : ℝ} (hr : 0 < r)
    (hz : ∀ y∈Metric.ball (0:Y) r, y 2=0 → iteratedFDeriv ℝ n f y=0)
    (hn : normalJet (n+1) f 0=0) : iteratedFDeriv ℝ (n+1) f 0=0 := by
  classical
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) 0 :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast (WithTop.coe_lt_top n))).differentiableAt
  have hfirst (u : Fin (n+1) → Y) (hu : u 0 2=0) : iteratedFDeriv ℝ (n+1) f 0 u=0 := by
    rw [iteratedFDeriv_succ_apply_left, tangent_deriv_zero hd hr hz hu]
    rfl
  have hany (u : Fin (n+1) → Y) (i : Fin (n+1)) (hu : u i 2=0) :
      iteratedFDeriv ℝ (n+1) f 0 u=0 := by
    rw [← iterated_perm hf (n+1) (Equiv.swap 0 i) u 0]
    exact hfirst _ (by simpa using hu)
  ext u
  have he : u=(fun k => ∑ i : Fin 3, u k i • Pi.single i (1:ℝ)) := by
    funext k i
    simp [Pi.single_apply]
  rw [he]
  change (iteratedFDeriv ℝ (n+1) f 0).toMultilinearMap (fun k => ∑ i : Fin 3, u k i • Pi.single i (1:ℝ))=0
  rw [MultilinearMap.map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [MultilinearMap.map_smul_univ]
  suffices (iteratedFDeriv ℝ (n+1) f 0) (fun k => Pi.single (j k) (1:ℝ))=0 by
    change (∏ i, u i (j i)) • (iteratedFDeriv ℝ (n+1) f 0) (fun i => Pi.single (j i) (1:ℝ))=0
    rw [this,smul_zero]
  by_cases h : ∀ k, j k=2
  · simpa only [h,en,normalJet] using hn
  · push Not at h
    obtain ⟨k,hk⟩ := h
    exact hany _ k (by simp [Ne.symm hk])

end ElasticityBoundaryFlatHyperplane

end
end
section
/-! Full jet flatness in honest boundary coordinates and back in the fixed
physical Euclidean coordinates. No jet transformation is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryNormalTaylor ElasticityBoundaryFlatComposition
  ElasticityBoundaryFlatHyperplane
variable {Ω : Set X} {x : X}

lemma Setup.chart_full_step (s : Setup Ω x) (hO : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k f z=0)
    {r : ℝ} (hr : 0 < r) (hK : s.K=Metric.closedBall 0 r)
    (hn : normalJet (n+1) (s.chartFunction f) 0=0) :
    iteratedFDeriv ℝ (n+1) (s.chartFunction f) 0=0 := by
  have ht : Tendsto (WithLp.toLp 2 : Y → X) (𝓝 (0:Y)) (𝓝 (0:X)) :=
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).continuousAt
  obtain ⟨ε,hε,hE⟩ := Metric.mem_nhds_iff.mp
    (ht (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)))
  apply flat_step (s.chartFunction_smooth hf) n hε _ hn
  intro y hy hy0
  exact s.chart_flat hO hf n hz (by rw [hK]; exact Metric.ball_subset_closedBall (hE hy)) hy0

lemma Setup.Ψ_zero (s : Setup Ω x) : s.Ψ x=0 := by
  have hx : x∈s.e '' s.K := ⟨0,s.zero_mem,s.center⟩
  exact (s.Ψ_germ x hx).eq_of_nhds.trans
    ((congrArg s.e.symm s.center).symm.trans (s.e.left_inv s.at_zero))

lemma Setup.inverse_germ (s : Setup Ω x) :
    (fun z => s.Φ (s.Ψ z)) =ᶠ[𝓝 x] fun z => z := by
  have hx : x∈s.e '' s.K := ⟨0,s.zero_mem,s.center⟩
  have ht : Tendsto s.Ψ (𝓝 x) (𝓝 (0:X)) := by
    simpa only [s.Ψ_zero] using s.Ψ_smooth.continuous.continuousAt.tendsto (x := x)
  have hxt : x∈s.e.target := by simpa only [s.center] using s.e.map_source s.at_zero
  filter_upwards [(s.Φ_germ 0 s.zero_mem).comp_tendsto ht,s.Ψ_germ x hx,
    s.e.open_target.mem_nhds hxt] with z hΦ hΨ hz
  change s.Φ (s.Ψ z)=s.e (s.Ψ z) at hΦ
  rw [hΦ,hΨ,s.e.right_inv hz]

lemma Setup.physical_flat_of_chart (s : Setup Ω x) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, iteratedFDeriv ℝ k (s.chartFunction f) 0=0) :
    iteratedFDeriv ℝ n f x=0 := by
  let g : X → Y := fun z => (s.Ψ z).ofLp
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := PiLp.contDiff_ofLp.comp s.Ψ_smooth
  have hg0 : g x=0 := by simp only [g,s.Ψ_zero,WithLp.ofLp_zero]
  have hcomp : iteratedFDeriv ℝ n (s.chartFunction f ∘ g) x=0 := by
    apply comp_flat n (s.chartFunction_smooth hf).contDiffAt hg.contDiffAt
    intro k hk
    rw [hg0]
    exact hz k hk
  have he : (s.chartFunction f ∘ g) =ᶠ[𝓝 x] f := by
    filter_upwards [s.inverse_germ] with z hz
    change f (s.Φ (s.Ψ z))=f z
    rw [hz]
  rw [← (he.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hcomp

end ElasticityBoundaryPacket

end
end
section
/-! All actual Frechet boundary jets from the physical DN map. Induction is
global along the boundary, so tangential derivatives of lower jets are zero;
only the pure normal step uses oscillatory solutions. -/
noncomputable section
open Set
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity
variable {Ω : Set X}

lemma boundary_flat_difference_global {l₁ m₁ l₂ m₂ : X → ℝ}
    (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    ∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n (l₁-l₂) x=0 ∧
      iteratedFDeriv ℝ n (m₁-m₂) x=0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      intro x hx
      have hv := boundary_values_global hS hO hB hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hDN hx
      constructor
      · ext v
        simp only [iteratedFDeriv_zero_apply,Pi.sub_apply,hv.1,sub_self,zero_apply]
      · ext v
        simp only [iteratedFDeriv_zero_apply,Pi.sub_apply,hv.2,sub_self,zero_apply]
    | succ n =>
      intro x hx
      obtain ⟨s,r,hr,hK⟩ := setup_ball_exists hS hx
      have hzl : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (l₁-l₂) z=0 :=
        fun k hk z hz => (ih k (Nat.lt_succ_of_le hk) z hz).1
      have hzm : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (m₁-m₂) z=0 :=
        fun k hk z hz => (ih k (Nat.lt_succ_of_le hk) z hz).2
      have hn := s.boundary_normal_step hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB
        (frontier_subset_closure hx) hDN n hzl hzm hK
      have hlf := s.chart_full_step hO (hl₁.sub hl₂) n hzl hr hK hn.1
      have hmf := s.chart_full_step hO (hm₁.sub hm₂) n hzm hr hK hn.2
      constructor
      · apply s.physical_flat_of_chart (hl₁.sub hl₂) (n+1)
        intro k hk
        obtain hk|hk := lt_or_eq_of_le hk
        · exact s.chart_flat hO (hl₁.sub hl₂) k
            (fun j hj => hzl j (hj.trans (Nat.le_of_lt_succ hk)))
            (by simpa using s.zero_mem) rfl
        · subst k
          exact hlf
      · apply s.physical_flat_of_chart (hm₁.sub hm₂) (n+1)
        intro k hk
        obtain hk|hk := lt_or_eq_of_le hk
        · exact s.chart_flat hO (hm₁.sub hm₂) k
            (fun j hj => hzm j (hj.trans (Nat.le_of_lt_succ hk)))
            (by simpa using s.zero_mem) rfl
        · subst k
          exact hmf

lemma boundary_jets_global_oai {l₁ m₁ l₂ m₂ : X → ℝ}
    (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x) ∧
      (∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x) := by
  have h := boundary_flat_difference_global hS hO hB hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hDN
  constructor
  · intro n x hx
    have hz := (h n x hx).1
    rw [iteratedFDeriv_sub (hl₁.of_le (by exact_mod_cast le_top))
      (hl₂.of_le (by exact_mod_cast le_top))] at hz
    exact (sub_eq_zero.mp hz).symm
  · intro n x hx
    have hz := (h n x hx).2
    rw [iteratedFDeriv_sub (hm₁.of_le (by exact_mod_cast le_top))
      (hm₂.of_le (by exact_mod_cast le_top))] at hz
    exact (sub_eq_zero.mp hz).symm

end ElasticityBoundaryPacket

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.boundary_jets_global_oai := @OAI.ElasticityBoundaryPacket.boundary_jets_global_oai
