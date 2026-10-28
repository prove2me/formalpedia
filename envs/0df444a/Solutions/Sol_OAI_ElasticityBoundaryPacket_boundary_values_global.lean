-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.boundary_values_global
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:52:03.760193+00:00
-- url     : https://prove2.me/submissions/1b6cff5b-f9e8-4da2-9b32-22decf532a56

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_extract_normal
import Theorems.Thm_OAI_ElasticityBoundaryPacket_pair_separates

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Orthogonal covariance of the literal isotropic tensor in physical
coordinates. The frame is an actual Euclidean isometry, not a gauge freedom. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryRotation
open ElasticityBoundaryLayerOperator

lemma frameMatrix_orthogonal (Q : X ≃ₗᵢ[ℝ] X) (j k : I) :
    (∑ i, frameMatrix Q i j*frameMatrix Q i k)=if j=k then 1 else 0 := by
  have hreal : (∑ i, Q (EuclideanSpace.single j 1) i*Q (EuclideanSpace.single k 1) i)=
      if j=k then 1 else 0 := by
    calc
      _ = inner ℝ (Q (EuclideanSpace.single k 1)) (Q (EuclideanSpace.single j 1)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        rfl
      _ = inner ℝ (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) := Q.inner_map_map _ _
      _ = _ := by simp [EuclideanSpace.inner_single_left, PiLp.single_apply, eq_comm]
  simpa only [frameMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero] using congrArg Complex.ofReal hreal

lemma rotate_isotropic_formula (Q : I → I → ℂ) (l m : ℂ) (s α r β : I) :
    rotateTensor Q (elasticityTensor l m) s α r β =
      l*columnDot Q s α*columnDot Q r β+
      m*(columnDot Q s r*columnDot Q α β+columnDot Q s β*columnDot Q α r) := by
  unfold rotateTensor elasticityTensor
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Fintype.sum_ite_eq, Finset.sum_const_zero]
  unfold columnDot
  simp only [Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Simultaneously transporting displacement and spatial coordinates by the
same actual orthogonal frame leaves the frozen physical tensor unchanged. -/
theorem rotate_isotropic (Q : X ≃ₗᵢ[ℝ] X) (l m : ℂ) (s α r β : I) :
    rotateTensor (frameMatrix Q) (elasticityTensor l m) s α r β=elasticityTensor l m s α r β := by
  rw [rotate_isotropic_formula]
  simp only [columnDot, frameMatrix_orthogonal, elasticityTensor]

end ElasticityBoundaryRotation

end
end

end OAI
end

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
/-! The boundary-coordinate differential operator is obtained from literal
physical elasticity by the chain rule and a fixed Euclidean rotation. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChartOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
  ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundarySmoothOperator ElasticityBoundaryLayerOperator ElasticityBoundaryStrongLayer

lemma smooth_jac {ψ : X → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : X) (α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (jac ψ v α) := by
  exact contDiff_apply ℝ ℝ α |>.comp ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)

lemma smooth_chartPrincipal (Q : X ≃ₗᵢ[ℝ] X) {Φ : Y → X} {ψ : X → Y}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (s α r β : I) : ContDiff ℝ (⊤ : ℕ∞) (chartPrincipal Q Φ ψ l m s α r β) := by
  apply ContDiff.comp _ hΦ
  apply ContDiff.sum; intro k _
  apply ContDiff.sum; intro v _
  apply ContDiff.mul
  · apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold coeff elasticityTensor
      exact (hl.mul contDiff_const |>.mul contDiff_const).add (hm.mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis k) α)
  · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis v) β)

lemma chartPrincipal_frozen (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) (ψ : X → Y)
    (l m : X → ℂ) (hj : ∀ k α, (jac ψ (basis k) α (Φ 0):ℂ)=frameMatrix Q k α)
    (s α r β : I) :
    chartPrincipal Q Φ ψ l m s α r β 0=elasticityTensor (l (Φ 0)) (m (Φ 0)) s α r β := by
  have he : chartPrincipal Q Φ ψ l m s α r β 0=
      rotateTensor (frameMatrix Q) (elasticityTensor (l (Φ 0)) (m (Φ 0))) s α r β := by
    unfold chartPrincipal principalPull mixedTensor coeff rotateTensor
    simp only [hj, Finset.sum_mul]
    calc
      _ = ∑ k, ∑ i, ∑ v, ∑ j, frameMatrix Q i s *
          elasticityTensor (l (Φ 0)) (m (Φ 0)) i k j v * frameMatrix Q j r *
          frameMatrix Q k α * frameMatrix Q v β := by
        apply Finset.sum_congr rfl; intro k _
        exact Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ v, ∑ j, frameMatrix Q i s *
          elasticityTensor (l (Φ 0)) (m (Φ 0)) i k j v * frameMatrix Q j r *
          frameMatrix Q k α * frameMatrix Q v β := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro v _
        ring
  rw [he,rotate_isotropic]

end ElasticityBoundaryChartOperator

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
/-! The exact inverse derivative at normalized physical boundary charts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryInverseGeometry
open Elasticity ElasticityBoundaryChainRule ElasticityBoundaryRotation

lemma inverse_derivative (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x∈e.source) (Q : X ≃ₗᵢ[ℝ] X)
    (hQ : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap x) :
    HasFDerivAt e.symm Q.symm.toContinuousLinearEquiv.toContinuousLinearMap (e x) := by
  have hd := (hi.differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hinv := chart_fderiv_left_inverse e he hi hx
  rw [hQ.fderiv] at hinv
  have hf : fderiv ℝ e.symm (e x)=Q.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : X →L[ℝ] X => A (Q.symm v)) hinv
    change fderiv ℝ e.symm (e x) (Q (Q.symm v))=Q.symm v at h
    change fderiv ℝ e.symm (e x) v=Q.symm v
    simpa only [Q.apply_symm_apply] using h
  rw [← hf]
  exact hd.hasFDerivAt

lemma inverse_frame_entry (Q : X ≃ₗᵢ[ℝ] X) (k α : I) :
    Q.symm (EuclideanSpace.single k 1) α=Q (EuclideanSpace.single α 1) k := by
  have h := Q.inner_map_eq_flip (EuclideanSpace.single α 1) (EuclideanSpace.single k 1)
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    map_one, one_mul, mul_one, starRingEnd_apply, star_trivial] using h.symm

lemma coordinate_inverse_jac (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x∈e.source) (Q : X ≃ₗᵢ[ℝ] X)
    (hQ : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap x)
    {Ψ : X → X} (hΨ : Ψ =ᶠ[𝓝 (e x)] e.symm) (k α : I) :
    (jac (fun z => (Ψ z).ofLp) (EuclideanSpace.single k 1) α (e x):ℂ)=frameMatrix Q k α := by
  have hder := (inverse_derivative e he hi hx Q hQ).congr_of_eventuallyEq hΨ
  have hcoords := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).hasFDerivAt.comp (e x) hder
  change ((fderiv ℝ (fun z => (Ψ z).ofLp) (e x) (EuclideanSpace.single k 1)) α:ℂ)=_
  change HasFDerivAt (fun z => (Ψ z).ofLp) _ (e x) at hcoords
  rw [hcoords.fderiv]
  change (Q.symm (EuclideanSpace.single k 1) α:ℂ)=_
  rw [inverse_frame_entry]
  rfl

end ElasticityBoundaryInverseGeometry

end
end
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer
  ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryLayerOperator ElasticityBoundaryPhysicalTransfer

lemma setup_exists {Ω : Set X} (h : SourceSmoothBoundary Ω) {x : X} (hx : x∈frontier Ω) :
    Nonempty (Setup Ω x) := by
  obtain ⟨e,Q,he0,hec,he,hi,hQ,hhalf⟩ := h.normalized hx
  obtain ⟨χ,hχ,hχc,hχs,hχ0,_⟩ := compact_smooth_cutoff (isCompact_singleton (x := (0:X)))
    e.open_source (singleton_subset_iff.mpr he0)
  let K := tsupport χ
  obtain ⟨η,Φ,Ψ,hη,hηc,hηs,hη1,hΦ,hΦe,hΨ,hΨe⟩ := compact_chart_data e he hi hχc hχs
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
    inverse_smooth := hi, deriv := hQ, inside := hhalf, K := K, compact := hχc,
    source := hχs, cutoff := χc, cutoff_smooth := hχcs, cutoff_compact := hχcc,
    cutoff_one := hχc0, cutoff_support := ?_, η := η, η_smooth := hη,
    η_compact := hηc, η_support := hηs, η_one := hηK, Φ := Φ, Ψ := Ψ,
    Φ_smooth := hΦ, Ψ_smooth := hΨ, Φ_germ := ?_, Ψ_germ := ?_ }⟩
  · intro z hz
    apply subset_tsupport χ
    intro hc
    exact hz (by simp [χc,hc])
  · intro y hy
    exact hΦe.filter_mono (nhds_le_nhdsSet hy)
  · intro z hz
    exact hΨe.filter_mono (nhds_le_nhdsSet (hKη hz))

lemma Setup.zero_mem {Ω : Set X} {x : X} (s : Setup Ω x) : (0:X)∈s.K := by
  apply s.cutoff_support
  change s.cutoff 0≠0
  rw [s.cutoff_one.eq_of_nhds]
  exact one_ne_zero

lemma Setup.Φ_zero {Ω : Set X} {x : X} (s : Setup Ω x) : s.Φ 0=x :=
  (s.Φ_germ 0 s.zero_mem).eq_of_nhds.trans s.center

lemma Setup.frozen {Ω : Set X} {x : X} (s : Setup Ω x) (l m : X → ℂ)
    (i α j β : I) : principal s.Q s.Φ s.Ψ l m i α j β 0=elasticityTensor (l x) (m x) i α j β := by
  unfold ElasticityBoundaryPhysicalMass.principal
  rw [chartPrincipal_frozen]
  · simp only [WithLp.toLp_zero,s.Φ_zero]
  · intro k a
    simp only [WithLp.toLp_zero]
    rw [(s.Φ_germ 0 s.zero_mem).eq_of_nhds]
    exact coordinate_inverse_jac s.e s.smooth s.inverse_smooth s.at_zero s.Q s.deriv
      (s.Ψ_germ _ (mem_image_of_mem s.e s.zero_mem)) k a

end ElasticityBoundaryPacket

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryPacket
/-! Smooth compact localization of the literal pulled physical energy tensor.
The true chart Jacobian is retained, including its nonzero value at the center. -/
open Set Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundary ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChartOperator ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

lemma Setup.jacobian_continuous (s : Setup Ω x) : Continuous s.jacobian :=
  ((ContinuousLinearMap.continuous_det.comp (s.Φ_smooth.continuous_fderiv (by simp))).abs).comp
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ))

lemma Setup.jacobian_pos (s : Setup Ω x) : 0 < s.jacobian 0 := by
  have hf : fderiv ℝ s.Φ 0=s.Q.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [(s.Φ_germ 0 s.zero_mem).fderiv_eq]
    exact s.deriv.fderiv
  simp only [Setup.jacobian,WithLp.toLp_zero,hf]
  exact abs_pos.mpr s.Q.toLinearEquiv.isUnit_det'.ne_zero

lemma Setup.rawCoeff_continuous (s : Setup Ω x) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (i α j β : I) :
    Continuous (s.rawCoeff l m i α j β) := by
  exact (Complex.continuous_ofReal.comp s.jacobian_continuous).mul
    (smooth_chartPrincipal s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
      (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm i α j β).continuous

lemma Setup.rawCoeff_zero (s : Setup Ω x) (l m : X → ℂ) (i α j β : I) :
    s.rawCoeff l m i α j β 0=(s.jacobian 0:ℂ)*elasticityTensor (l x) (m x) i α j β := by
  rw [Setup.rawCoeff,s.frozen]

/-- All modifications of this coefficient are outside the support of the
actual trial gradients. Its leading coefficient is the actual isotropic tensor. -/
lemma Setup.compact_energy_coefficients (s : Setup Ω x) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    ∃ H : I → I → I → I → Y → ℂ,
      (∀ i α j β, Continuous (H i α j β)) ∧
      (∀ i α j β, HasCompactSupport (H i α j β)) ∧
      (∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=s.rawCoeff l m i α j β y) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := compact_smooth_cutoff s.compact isOpen_univ (subset_univ s.K)
  let ρc : Y → ℂ := fun y => (ρ (WithLp.toLp 2 y):ℂ)
  have hρcc : HasCompactSupport ρc :=
    (hρc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  refine ⟨fun i α j β y => ρc y*s.rawCoeff l m i α j β y,?_,?_,?_⟩
  · intro i α j β
    exact (Complex.continuous_ofReal.comp (hρ.continuous.comp
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)))).mul (s.rawCoeff_continuous hl hm i α j β)
  · intro i α j β
    exact hρcc.mul_right
  · intro i α j β y hy
    simp only [ρc,hρ1.self_of_nhdsSet _ hy,Complex.ofReal_one,one_mul]

end ElasticityBoundaryPacket

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Boundary values of BOTH Lamé parameters from the literal physical DN map
on an arbitrary honest smooth domain. This is not a near-boundary assumption. -/
noncomputable section
open Set
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryLayerOperator
variable {Ω : Set X} {x : X}

lemma elasticityTensor_sub (l₁ m₁ l₂ m₂ : ℂ) (i α j β : I) :
    elasticityTensor l₁ m₁ i α j β-elasticityTensor l₂ m₂ i α j β=
      elasticityTensor (l₁-l₂) (m₁-m₂) i α j β := by
  unfold elasticityTensor
  ring

lemma admissible_frozen_ne {l m : X → ℝ} (ha : Admissible Ω l m) (hx : x∈closure Ω) :
    (m x:ℂ)≠0 ∧ (l x:ℂ)+3*(m x:ℂ)≠0 := by
  obtain ⟨hm,he⟩ := ha.2.2 x hx
  constructor
  · exact Complex.ofReal_ne_zero.mpr hm.ne'
  · have hp : 0<l x+3*m x := by linarith
    exact_mod_cast hp.ne'

lemma Setup.boundary_values (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) : l₁ x=l₂ x ∧ m₁ x=m₂ x := by
  obtain ⟨H₁,hH₁c,hH₁s,hH₁⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₁) (Complex.ofRealCLM.contDiff.comp hm₁)
  obtain ⟨H₂,hH₂c,hH₂s,hH₂⟩ := s.compact_energy_coefficients
    (Complex.ofRealCLM.contDiff.comp hl₂) (Complex.ofRealCLM.contDiff.comp hm₂)
  let H := fun i α j β y => H₁ i α j β y-H₂ i α j β y
  have hHc : ∀ i α j β, Continuous (H i α j β) := fun i α j β =>
    (hH₁c i α j β).sub (hH₂c i α j β)
  have hHs : ∀ i α j β, HasCompactSupport (H i α j β) := fun i α j β =>
    (hH₁s i α j β).sub (hH₂s i α j β)
  have hH (i α j β : I) (y : Y) (hy : WithLp.toLp 2 y∈s.K) :
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^0*H i α j β y := by
    simp only [pow_zero,one_mul,H,hH₁ i α j β y hy,hH₂ i α j β y hy]
    rfl
  have hH0 : (fun i α j β => H i α j β 0)=
      (fun i α j β => (s.jacobian 0:ℂ)*elasticityTensor
        ((l₁ x:ℂ)-(l₂ x:ℂ)) ((m₁ x:ℂ)-(m₂ x:ℂ)) i α j β) := by
    funext i α j β
    have h0 := hH i α j β 0 (by simpa using s.zero_mem)
    simp only [pow_zero,one_mul] at h0
    rw [← h0]
    rw [s.rawCoeff_zero,s.rawCoeff_zero,← mul_sub,elasticityTensor_sub]
  have hpair := pair_separates 0 (l₁ x) (m₁ x) (l₂ x) (m₂ x) (s.jacobian 0)
    ((l₁ x:ℂ)-(l₂ x:ℂ)) ((m₁ x:ℂ)-(m₂ x:ℂ))
    (admissible_frozen_ne ha₁ hx).1 (admissible_frozen_ne ha₂ hx).1
    (admissible_frozen_ne ha₁ hx).2 (admissible_frozen_ne ha₂ hx).2
    (Complex.ofReal_ne_zero.mpr s.jacobian_pos.ne') (by
      intro p q hp hq
      rw [← hH0]
      exact s.extract_normal hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB hx hDN 0 H hHc hHs hH p q hp hq)
  exact ⟨Complex.ofReal_injective (sub_eq_zero.mp hpair.1),
    Complex.ofReal_injective (sub_eq_zero.mp hpair.2)⟩

lemma boundary_values_global_oai {l₁ m₁ l₂ m₂ : X → ℝ}
    (hS : SourceSmoothBoundary Ω) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) (hx : x∈frontier Ω) : l₁ x=l₂ x ∧ m₁ x=m₂ x := by
  obtain ⟨s⟩ := setup_exists hS hx
  exact s.boundary_values hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB (frontier_subset_closure hx) hDN

end ElasticityBoundaryPacket

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.boundary_values_global_oai := @OAI.ElasticityBoundaryPacket.boundary_values_global_oai
