-- Prove2me | solution 1 for OAI.ThreeManifold.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:29:38.8624+00:00
-- url     : https://prove2.me/submissions/995e1daa-490e-43e1-91de-7ae311b4f10a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/ThreeManifold.lean:L260-L266
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ThreeManifold.main_theorem.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ThreeManifold_main_theorem) verbatim and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_ThreeManifold
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_realCompactMetric_nonnegative_index
import Theorems.Thm_OAI_ThreeManifold_GluedConstruction_gluing_transition_positive
import Theorems.Thm_OAI_ThreeManifold_HyperbolicCore_action_orientation
import Theorems.Thm_OAI_ThreeManifold_LoopTopology_fiber_null_transfer
import Theorems.Thm_OAI_ThreeManifold_NonpositiveMetric_CNMidpoint_cyclic_shear_obstruction
import Theorems.Thm_OAI_ThreeManifold_QuotientConstruction_manifold_quotient_positive
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_uniform_turning_parameters
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_LocalMetricIsometry_covariantDerivative_map
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_closedGeodesic_essential
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_geodesic_of_acceleration_zero
import Theorems.Thm_OAI_ThreeManifold_WarpedCurvature_warpedModel_matrix

-- ---- from OAI.Geometry.ConjugatePoints.Gluing ----
namespace OAI

noncomputable section

/-!
# Two-piece gluing, smooth charts, compactness, and orientation.
-/

open Set Manifold Bundle
open scoped ContDiff
open Set Filter Topology Manifold
open scoped ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Set Pointwise
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups

open Set Topology TopologicalSpace CategoryTheory
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]

end ThreeManifold.TwoGluing

open Set Topology TopologicalSpace
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

end ThreeManifold.GluedConstruction
open Set Topology Filter Manifold
open scoped ContDiff
namespace ThreeManifold.CircleConstruction
open QuotientConstruction
end ThreeManifold.CircleConstruction
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore
open QuotientConstruction

end ThreeManifold.HyperbolicCore

open Set Topology Filter TopologicalSpace Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
variable (O : Opens X) (e : O ≃ₜ O)

end ThreeManifold.TwoGluing
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff
namespace ThreeManifold.GluedConstruction
open HyperbolicCore
end ThreeManifold.GluedConstruction

open Set Topology Filter Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.AtlasOrientation

section
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]

lemma transition_contDiffAt [IsManifold 𝓘(ℝ,E) ∞ M]
    {c d : OpenPartialHomeomorph M E} (hc : c ∈ atlas E M) (hd : d ∈ atlas E M)
    {x : E} (hx : x ∈ c.target) (hy : c.symm x ∈ d.source) :
    ContDiffAt ℝ ∞ (d ∘ c.symm) x :=
  ((contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,E)) (subset_maximalAtlas (n := ∞) hd) hy).comp x
    (contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,E)) (subset_maximalAtlas (n := ∞) hc) hx)).contDiffAt

lemma product [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N]
    (hM : Positive (E := E) (M := M)) (hN : Positive (E := F) (M := N)) :
    @Positive (E × F) (M × N) _ _ _ (prodChartedSpace E M F N) := by
  intro a b ha hb x hx hy
  obtain ⟨c,hc,d,hd,rfl⟩ := ha
  obtain ⟨c',hc',d',hd',rfl⟩ := hb
  have h1 := (transition_contDiffAt hc hc' hx.1 hy.1).differentiableAt (by simp)
  have h2 := (transition_contDiffAt hd hd' hx.2 hy.2).differentiableAt (by simp)
  change 0 < LinearMap.det (fderiv ℝ (Prod.map (c' ∘ c.symm) (d' ∘ d.symm)) x).toLinearMap
  rw [(HasFDerivAt.prodMap x h1.hasFDerivAt h2.hasFDerivAt).fderiv]
  change (0 : ℝ) < LinearMap.det ((fderiv ℝ (c' ∘ c.symm) x.1).toLinearMap.prodMap
    (fderiv ℝ (d' ∘ d.symm) x.2).toLinearMap)
  rw [LinearMap.det_prodMap]
  exact mul_pos (hM c c' hc hc' x.1 hx.1 hy.1) (hN d d' hd hd' x.2 hx.2 hy.2)

lemma open_subset (U : TopologicalSpace.Opens M) (hM : Positive (E := E) (M := M)) :
    Positive (E := E) (M := U) := by
  classical
  by_cases hU : Nonempty U
  swap
  · intro c d hc hd x hx hy
    exact (hU ⟨c.symm x⟩).elim
  intro c d hc hd x hx hy
  obtain ⟨a,rfl⟩ := TopologicalSpace.Opens.chart_eq hU hc
  obtain ⟨b,rfl⟩ := TopologicalSpace.Opens.chart_eq hU hd
  have hy' : (chartAt E a.1).symm x ∈ (chartAt E b.1).source := by
    rw [← (chartAt E a.1).subtypeRestr_symm_apply hU hx]
    exact hy.2
  have hg : ((chartAt E b.1).subtypeRestr hU ∘ ((chartAt E a.1).subtypeRestr hU).symm)
      =ᶠ[nhds x] (chartAt E b.1 ∘ (chartAt E a.1).symm) := by
    filter_upwards [((chartAt E a.1).subtypeRestr hU).open_target.mem_nhds hx] with y hy
    change chartAt E b.1 ((((chartAt E a.1).subtypeRestr hU).symm y).1) = _
    rw [← Function.comp_apply (f := Subtype.val),
      (chartAt E a.1).subtypeRestr_symm_apply hU hy]
    rfl
  rw [hg.fderiv_eq]
  exact hM _ _ (chart_mem_atlas E a.1) (chart_mem_atlas E b.1) x hx.1 hy'

end

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma transition_det_mul {c d : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hd : d ∈ atlas E M) {x : E}
    (hx : x ∈ c.target) (hy : c.symm x ∈ d.source) :
    LinearMap.det (fderiv ℝ (c ∘ d.symm) (d (c.symm x))).toLinearMap *
      LinearMap.det (fderiv ℝ (d ∘ c.symm) x).toLinearMap = 1 := by
  have h1 := (transition_contDiffAt hc hd hx hy).differentiableAt (by simp)
  have hyt : d (c.symm x) ∈ d.target := d.map_source hy
  have hys : d.symm (d (c.symm x)) ∈ c.source := by
    rw [d.left_inv hy]
    exact c.map_target hx
  have h2 := (transition_contDiffAt hd hc hyt hys).differentiableAt (by simp)
  have he : ((c ∘ d.symm) ∘ (d ∘ c.symm)) =ᶠ[nhds x] id := by
    filter_upwards [c.open_target.mem_nhds hx,
      c.symm.continuousAt hx (d.open_source.mem_nhds hy)] with y hy1 hy2
    simp only [Function.comp_apply,id_eq,d.left_inv hy2,c.right_inv hy1]
  have hh := h2.hasFDerivAt.comp x h1.hasFDerivAt
  have hid : (fderiv ℝ (c ∘ d.symm) (d (c.symm x))).comp
      (fderiv ℝ (d ∘ c.symm) x) = ContinuousLinearMap.id ℝ E := by
    exact (hh.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id x)
  rw [← LinearMap.det_comp]
  change LinearMap.det ((fderiv ℝ (c ∘ d.symm) (d (c.symm x))).comp
    (fderiv ℝ (d ∘ c.symm) x)).toLinearMap = 1
  rw [hid]
  exact LinearMap.det_id

lemma reverse_positive {c d : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hd : d ∈ atlas E M) {x : E}
    (hx : x ∈ c.target) (hy : c.symm x ∈ d.source)
    (h : 0 < LinearMap.det (fderiv ℝ (d ∘ c.symm) x).toLinearMap) :
    0 < LinearMap.det (fderiv ℝ (c ∘ d.symm) (d (c.symm x))).toLinearMap := by
  have hm := transition_det_mul hc hd hx hy
  exact pos_of_mul_pos_left (by rw [hm]; norm_num) h.le
end ThreeManifold.AtlasOrientation

open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.QuotientConstruction
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
  [Group G] [MulAction G M] {p : M → Q} (hp : IsQuotientCoveringMap p G)

end ThreeManifold.QuotientConstruction
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore
lemma surface_positive : AtlasOrientation.Positive (E := ℂ) (M := Surface) := by
  apply QuotientConstruction.manifold_quotient_positive projection_cover sectionMap_rightInverse
    (fun k => (effective_smooth k).continuous)
  intro k a b x hx hy
  obtain ⟨g,rfl⟩ := effect_surjective k
  exact action_orientation g.val a b x hx
end ThreeManifold.HyperbolicCore
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CircleConstruction
lemma positive (b : ℝ) : AtlasOrientation.Positive (E := ℝ) (M := AddCircle b) := by
  apply QuotientConstruction.manifold_quotient_positive (projection_cover b) (section_spec b)
    (fun k => (action_smooth b k).continuous)
  intro k a c x hx hy
  change 0 < LinearMap.det (fderiv ℝ ((fun _ : ℝ => (Multiplicative.toAdd k).val) + id) x).toLinearMap
  rw [(hasFDerivAt_const (𝕜 := ℝ) (Multiplicative.toAdd k).val x |>.add (hasFDerivAt_id x)).fderiv]
  simp
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
lemma piece_positive : AtlasOrientation.Positive (E := ℂ × ℝ) (M := Piece) := by
  exact AtlasOrientation.product (AtlasOrientation.open_subset (HyperbolicCore.coreOpens 8)
    HyperbolicCore.surface_positive) (CircleConstruction.positive 6)
end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.HyperbolicCore
end ThreeManifold.HyperbolicCore
namespace ThreeManifold.CircleConstruction
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

end ThreeManifold.GluedConstruction

open Set Filter Topology
namespace ThreeManifold.Coordinates3

end ThreeManifold.Coordinates3

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore Coordinates3 TwoGluing

end ThreeManifold.GluedConstruction

open Set Topology Filter Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart

section
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M]
variable (e : E ≃L[ℝ] F)

variable [IsManifold 𝓘(ℝ,E) ∞ M]

end

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma positive (e : E ≃L[ℝ] F) (h : AtlasOrientation.Positive (E := E) (M := M)) :
    let := charts (M := M) e
    AtlasOrientation.Positive (E := F) (M := M) := by
  let := charts (M := M) e
  change AtlasOrientation.Positive (E := F) (M := M)
  rintro _ _ ⟨c,hc,rfl⟩ ⟨d,hd,rfl⟩ x hx hy
  have hcx : e.symm x ∈ c.target := hx.2
  have hdx : c.symm (e.symm x) ∈ d.source := hy.1
  have ht := (AtlasOrientation.transition_contDiffAt hc hd hcx hdx).differentiableAt (by simp)
  have hg := e.hasFDerivAt.comp x (ht.hasFDerivAt.comp x e.symm.hasFDerivAt)
  change 0 < LinearMap.det (fderiv ℝ (e ∘ (d ∘ c.symm) ∘ e.symm) x).toLinearMap
  rw [hg.fderiv]
  change 0 < LinearMap.det ((e.toLinearEquiv : E →ₗ[ℝ] F) ∘ₗ
    (fderiv ℝ (d ∘ c.symm) (e.symm x)).toLinearMap ∘ₗ (e.toLinearEquiv.symm : F →ₗ[ℝ] E))
  rw [LinearMap.det_conj]
  exact h c d hc hd (e.symm x) hcx hdx
end ThreeManifold.Rechart

open Set Filter Topology TopologicalSpace Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
variable (O : Opens X) (e : O ≃ₜ O)
omit [IsManifold 𝓘(ℝ,E) ∞ X] in
lemma mixed_chart_positive
    (hpos : ∀ (a b : X) (x : E), x ∈ (chartAt E a).target →
      (chartAt E a).symm x ∈ O →
      extendedTransition O e ((chartAt E a).symm x) ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (extendedTransition O e ((chartAt E a).symm y))) x).toLinearMap)
    (a b : X) {x : E} (hx : x ∈ (chartAt E a).target)
    (hy : (pieceChart (E := E) O e false a).symm x ∈ (pieceChart (E := E) O e true b).source) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => pieceChart (E := E) O e true b ((pieceChart (E := E) O e false a).symm y)) x).toLinearMap := by
  obtain ⟨y,hy,hey⟩ := hy
  obtain ⟨hxO,hxe⟩ := (inclusion_mixed_eq O e _ _).mp hey.symm
  have hb : extendedTransition O e ((chartAt E a).symm x) ∈ (chartAt E b).source := by
    change extendedTransition O e ((chartAt E a).invFun x) ∈ (chartAt E b).source
    rw [extendedTransition_apply O e ⟨_,hxO⟩,hxe]
    exact hy
  rw [(pieceChart_mixed_germ O e a b hx hxO).fderiv_eq]
  exact hpos a b x hx hxO hb

lemma glued_positive (he : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e)
    (hei : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm)
    (hX : AtlasOrientation.Positive (E := E) (M := X))
    (hpos : ∀ (a b : X) (x : E), x ∈ (chartAt E a).target →
      (chartAt E a).symm x ∈ O →
      extendedTransition O e ((chartAt E a).symm x) ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (extendedTransition O e ((chartAt E a).symm y))) x).toLinearMap) :
    let := gluedCharts (E := E) O e
    AtlasOrientation.Positive (E := E) (M := Space O e) := by
  let := gluedCharts (E := E) O e
  let := glued_isManifold O e he hei
  change AtlasOrientation.Positive (E := E) (M := Space O e)
  rintro c d ⟨i,a,rfl⟩ ⟨j,b,rfl⟩ x hx hy
  have ha : x ∈ (chartAt E a).target := hx
  have same (k : Bool)
      (hk : (pieceChart (E := E) O e k a).symm x ∈ (pieceChart (E := E) O e k b).source) :
      0 < LinearMap.det (fderiv ℝ
        (pieceChart (E := E) O e k b ∘ (pieceChart (E := E) O e k a).symm) x).toLinearMap := by
    obtain ⟨y,hys,hye⟩ := hk
    have hey : y = (chartAt E a).symm x := (inclusion_openEmbedding O e k).injective hye
    have hb : (chartAt E a).symm x ∈ (chartAt E b).source := hey ▸ hys
    have hg : (pieceChart (E := E) O e k b ∘ (pieceChart (E := E) O e k a).symm) =
        (chartAt E b ∘ (chartAt E a).symm) := by
      funext y
      exact pieceChart_apply O e k b _
    rw [hg]
    exact hX _ _ (chart_mem_atlas E a) (chart_mem_atlas E b) x ha hb
  cases i <;> cases j
  · exact same false hy
  · exact mixed_chart_positive O e hpos a b ha hy
  · let c := pieceChart (E := E) O e true a
    let d := pieceChart (E := E) O e false b
    have hc : c ∈ atlas E (Space O e) := ⟨true,a,rfl⟩
    have hd : d ∈ atlas E (Space O e) := ⟨false,b,rfl⟩
    have hyt : d (c.symm x) ∈ d.target := d.map_source hy
    have hys : d.symm (d (c.symm x)) ∈ c.source := by
      rw [d.left_inv hy]
      exact c.map_target hx
    have hp := mixed_chart_positive O e hpos b a hyt hys
    have hh := AtlasOrientation.reverse_positive hd hc hyt hys hp
    rw [d.left_inv hy,c.right_inv hx] at hh
    exact hh
  · exact same true hy
end ThreeManifold.TwoGluing
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.GluedConstruction
lemma manifold_positive : AtlasOrientation.Positive (E := ℂ × ℝ) (M := Manifold) := by
  exact TwoGluing.glued_positive (E := ℂ × ℝ) collar gluingMap
    (by simpa only [modelWithCornersSelf_prod] using gluingMap_smooth)
    (by simpa only [modelWithCornersSelf_prod] using gluingMap_symm_smooth)
    piece_positive gluing_transition_positive

lemma manifold_oriented : OrientedAtlas (M := Manifold) :=
  Rechart.positive Coordinates3.coordinates manifold_positive

end ThreeManifold.GluedConstruction

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Neck ----
namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

lemma blockMatrix_mul (P Q : TMat) :
    blockMatrix P * blockMatrix Q = blockMatrix (P * Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
lemma blockMatrix_one : blockMatrix (1 : TMat) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
lemma blockMatrix_inverse {P Q : TMat} (hQP : Q * P = 1) :
    (blockMatrix Q)⁻¹ = blockMatrix P := by
  apply Matrix.inv_eq_right_inv
  rw [blockMatrix_mul, hQP, blockMatrix_one]

lemma block_entry_hasDerivAt {Q : ℝ → TMat} {A : TMat} {s : ℝ}
    (hQ : HasDerivAt Q A s) (i j : Fin 3) :
    HasDerivAt (fun r => blockMatrix (Q r) i j) (blockJet A i j) s := by
  have h (k l : Fin 2) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ k) l
  fin_cases i <;> fin_cases j <;>
    simp only [blockMatrix, blockJet] <;>
    first | exact hasDerivAt_const _ _ | exact h _ _

lemma coordPartial_block {Q : ℝ → TMat} {A : TMat} {x : E3}
    (hQ : HasDerivAt Q A (x 0)) (i j k : Fin 3) :
    coordPartial (fun y => blockMatrix (Q (y 0)) i j) x k =
      (if k = 0 then 1 else 0) * blockJet A i j := by
  have h := (block_entry_hasDerivAt hQ i j).hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) 0 x)
  change HasFDerivAt (fun y : E3 => blockMatrix (Q (y 0)) i j) _ x at h
  change (fderiv ℝ (fun y : E3 => blockMatrix (Q (y 0)) i j) x) (basisVector k) = _
  rw [h.fderiv]
  fin_cases k <;> simp [basisVector, ContinuousLinearMap.comp_apply]

lemma coordPartial_congr_germ {f h : E3 → ℝ} {x : E3}
    (heq : f =ᶠ[nhds x] h) (i : Fin 3) :
    coordPartial f x i = coordPartial h x i := by
  rw [coordPartial, coordPartial, heq.fderiv_eq]

lemma christoffel_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (i j k : Fin 3) :
    christoffel g c x i j k = (1 / 2 : ℝ) * ∑ l : Fin 3,
      blockMatrix P i l *
        ((if j = 0 then 1 else 0) * blockJet A l k +
         (if k = 0 then 1 else 0) * blockJet A l j -
         (if l = 0 then 1 else 0) * blockJet A j k) := by
  have hentry (a b d : Fin 3) :
      coordPartial (fun y => metricMatrix g c y a b) x d =
        (if d = 0 then 1 else 0) * blockJet A a b := by
    rw [coordPartial_congr_germ
      (Filter.Eventually.mono hg (fun _ h => congrFun (congrFun h a) b))]
    exact coordPartial_block hQ a b d
  rw [christoffel, hg.eq_of_nhds, blockMatrix_inverse hQP]
  simp only [hentry]

lemma connectionTerm_product {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold I3 ∞ M] (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {Q : ℝ → TMat} {P A : TMat} {x : E3}
    (hg : metricMatrix g c =ᶠ[nhds x] fun y => blockMatrix (Q (y 0)))
    (hQ : HasDerivAt Q A (x 0)) (hQP : Q (x 0) * P = 1)
    (hA : Aᵀ = A) (u v : E3) :
    connectionTerm g c x u v =
      joinVector (gamma P A (splitVector u) (splitVector v)) := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  ext i
  fin_cases i <;>
    simp [connectionTerm, christoffel_product g c hg hQ hQP,
      blockMatrix, blockJet, joinVector, gamma, splitVector, pairing,
      dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h10] <;> ring

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

open Cometric Neck

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

open Cometric Neck
end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.TorusNeck

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Curvature ----
namespace OAI

noncomputable section

/-!
# Local isometries, warped curvature, and compact curvature estimates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

lemma comp_smooth {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain) :
    ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ (f ∘ γ) U := by
  intro s hs
  exact ((P.smoothAt (hγP hs)).comp s (hγ.contMDiffAt (hU.mem_nhds hs))).contMDiffWithinAt

lemma velocity_map {γ : ℝ → M} {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hp : γ s ∈ P.domain) :
    velocity (f ∘ γ) s = mfderiv I3 I3 f (γ s) (velocity γ s) := by
  have he := mfderiv_comp s ((P.smoothAt hp).mdifferentiableAt (by simp))
    (hγ.mdifferentiableAt (by simp))
  exact congrArg (fun L => L 1) he

end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
lemma covariantDerivative_germ (g : SmoothMetric M) {γ : ℝ → M}
    {J K : ∀ s, TangentSpace I3 (γ s)} {s : ℝ} (he : J =ᶠ[𝓝 s] K) :
    covariantDerivative g γ J s = covariantDerivative g γ K s := by
  simp only [covariantDerivative]
  congr 1
  apply along_congr g _ Filter.EventuallyEq.rfl
  filter_upwards [he] with r hr
  unfold fieldCoordinates
  rw [hr]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
lemma geodesic_map {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn g γ U) (hγP : MapsTo γ U P.domain) :
    IsGeodesicOn h (f ∘ γ) U := by
  apply geodesic_of_acceleration_zero h hU (P.comp_smooth hU hγ.1 hγP)
  intro s hs
  have he : velocity (f ∘ γ) =ᶠ[𝓝 s] P.mapField γ (velocity γ) := by
    filter_upwards [hU.mem_nhds hs] with r hr
    exact P.velocity_map (hγ.1.contMDiffAt (hU.mem_nhds hr)) (hγP hr)
  rw [covariantDerivative_germ h he,
    P.covariantDerivative_map hU hγ.1 hγP (velocity_smooth hU hγ.1) hs,
    geodesic_acceleration_zero g hU hγ hs,map_zero]
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.WarpedCurvature
open Neck RiemannianCoordinates

lemma diag_transpose (a b : ℝ) : (diag a b)ᵀ = diag a b := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
lemma diag_mul (a b c d : ℝ) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,Matrix.mul_apply,Fin.sum_univ_two]
lemma diag_deriv {a b : ℝ → ℝ} {a' b' s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun t => diag (a t) (b t)) (diag a' b') s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hb

lemma QP (r : ℝ → ℝ) {c t : ℝ} (hr : r t ≠ 0) (hc : c ≠ 0) :
    Q r c t * P r c t = 1 := by
  rw [Q,P,diag_mul]
  simp only [mul_inv_cancel₀ (pow_ne_zero 2 hr),mul_inv_cancel₀ (pow_ne_zero 2 hc)]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [diag]
lemma Q_deriv {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (c t : ℝ) : HasDerivAt (Q r c) (A r t) t := by
  change HasDerivAt (fun s => diag ((r s)^2) (c^2)) (diag (2*r t*deriv r t) 0) t
  simpa only [Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat,pow_one] using diag_deriv (((hs.differentiable (by simp)) t).hasDerivAt.pow 2) (hasDerivAt_const t (c^2))
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.WarpedCurvature
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
end ThreeManifold.Rechart

namespace ThreeManifold.CylinderConstruction
open MetricConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instChartedSpaceE3Cylinder
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instIsManifoldRealE3I3SomeENatTopCylinder
variable {r s c : ℝ → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ t, r t ≠ 0) (hs : ∀ t, s t ≠ 0)
end ThreeManifold.CylinderConstruction

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.WarpedCurvature
open MetricConstruction CylinderConstruction RiemannianCoordinates
variable {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0)
end ThreeManifold.WarpedCurvature

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
end ThreeManifold.Rechart
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff UpperHalfPlane RealInnerProductSpace
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
lemma deriv_injective {p : M} (hp : p ∈ P.domain) : Function.Injective (mfderiv I3 I3 f p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  by_contra hn
  have he := P.metric p hp v v
  have hpos := g.pos p v hn
  rw [hv,map_zero] at he
  change g.inner p v v = 0 at he
  linarith
lemma geodesic_reflect {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hg : IsGeodesicOn h (f ∘ γ) U) : IsGeodesicOn g γ U := by
  apply geodesic_of_acceleration_zero g hU hγ
  intro s hs
  apply P.deriv_injective (hγP hs)
  rw [map_zero]
  have he : velocity (f ∘ γ) =ᶠ[𝓝 s] P.mapField γ (velocity γ) := by
    filter_upwards [hU.mem_nhds hs] with r hr
    exact P.velocity_map (hγ.contMDiffAt (hU.mem_nhds hr)) (hγP hr)
  rw [← P.covariantDerivative_map hU hγ hγP (velocity_smooth hU hγ) hs,
    ← covariantDerivative_germ h he,geodesic_acceleration_zero h hU hg hs]
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise UpperHalfPlane
namespace ThreeManifold.WarpedCurvature
open RiemannianCoordinates Neck
lemma warped_fiber_geodesic {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ}
    (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0) (a x k : ℝ) :
    IsGeodesicOn (warpedModel hs hb hr) (fun t => ![a,x,k*t]) univ := by
  have hsmooth : ContDiff ℝ ∞ (fun t : ℝ => (![a,x,k*t] : E3)) := by
    apply contDiff_pi.mpr; intro i; fin_cases i <;> simp <;> fun_prop
  refine ⟨hsmooth.contMDiff.contMDiffOn,?_⟩
  intro c hc t ht hct
  rw [chartedSpaceSelf_atlas] at hc
  subst c
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (![a,x,k*t] : E3)) (![0,0,k] : E3) t := by
    apply hasDerivAt_pi.mpr; intro i; fin_cases i
    · exact hasDerivAt_const t a
    · exact hasDerivAt_const t x
    · simpa using (hasDerivAt_id t).const_mul k
  have hd' : deriv (fun t : ℝ => (![a,x,k*t] : E3)) = fun _ => (![0,0,k] : E3) :=
    funext (fun t => (hd t).deriv)
  change deriv (deriv (fun t : ℝ => (![a,x,k*t] : E3))) t +
    connectionTerm (warpedModel hs hb hr) (OpenPartialHomeomorph.refl E3)
      (![a,x,k*t] : E3) (deriv (fun t : ℝ => (![a,x,k*t] : E3)) t)
      (deriv (fun t : ℝ => (![a,x,k*t] : E3)) t) = 0
  rw [hd',deriv_const,zero_add,connectionTerm_product _ _
    (Filter.Eventually.of_forall (warpedModel_matrix hs hb hr))
    (Q_deriv hs b a) (QP r (hr a) hb) (diag_transpose _ _)]
  ext i; fin_cases i <;>
    simp [gamma,joinVector,splitVector,P,diag,pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
end ThreeManifold.WarpedCurvature
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_1
lemma universal_fiber_smooth (z : ℍ) (k : ℝ) :
    ContMDiff 𝓘(ℝ,ℝ) I3 ∞ (fun t : ℝ => (z,k*t) : ℝ → UniversalPiece) := by
  have hf : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,EP) ∞ (fun t : ℝ => (z,k*t) : ℝ → UniversalPiece) := by
    simpa only [EP,← modelWithCornersSelf_prod] using
      (contMDiff_const.prodMk (contMDiff_const.mul contMDiff_id) :
        ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℝ)) ∞ (fun t : ℝ => (z,k*t)))
  exact (Rechart.identity_smooth_forward Coordinates3.coordinates).comp hf
lemma universal_fiber_geodesic (c : ℝ) (hc : c ≠ 0) (z : ℍ) (k : ℝ) :
    IsGeodesicOn (realUniversalMetric c hc) (fun t => (z,k*t)) univ := by
  apply (universalLogIsometry c hc).geodesic_reflect isOpen_univ
    (universal_fiber_smooth z k).contMDiffOn (fun _ _ => mem_univ _)
  change IsGeodesicOn (hyperbolicWarped c hc) (fun t => ![Real.log z.im,z.re,k*t]) univ
  exact WarpedCurvature.warped_fiber_geodesic exponentialRadius_smooth hc
    (fun t => (Real.exp_pos (-t)).ne') _ _ _
lemma core_fiber_geodesic (c : ℝ) (hc : c ≠ 0) (z : ℍ) (k : ℝ) :
    IsGeodesicOn (realCoreMetric c hc)
      (fun t => (HyperbolicCore.projection z,((k*t : ℝ) : GluedConstruction.Circle))) univ := by
  exact (coreProjectionIsometry c hc).geodesic_map isOpen_univ
    (universal_fiber_geodesic c hc z k) (fun _ _ => mem_univ _)
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece
end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
variable {M N X : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {k : SmoothMetric X}
  {f : M → N} {w : N → X}
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder
end

open MetricConstruction CylinderConstruction RiemannianCoordinates

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_1
variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece_1
end ThreeManifold.CompactMetric

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Continuation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Geodesic continuation and the covering exponential map.
-/

section
open Set Filter Topology
namespace ThreeManifold.FlowContinuation.Equation
variable {X : Type*} (P : Equation X)

end ThreeManifold.FlowContinuation.Equation

namespace ThreeManifold.PathContinuation
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Y]
variable (f : E → Y) (γ : ℝ → Y)
end ThreeManifold.PathContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}
open RiemannianCoordinates

end ThreeManifold.PathContinuation
end

section
open Set Filter Topology
namespace ThreeManifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]

end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}

variable [CompactSpace M] [T2Space M]

end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M] {γ : ℝ → M}

end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology unitInterval
namespace ThreeManifold
variable {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
variable {p : E → X}

end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
local notation "𝕀" => unitInterval
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
lemma velocity_map_ne_zero (P : LocalMetricIsometry g h f) {γ : ℝ → M} {s : ℝ}
    (hs : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hp : γ s ∈ P.domain)
    (hv : (velocity γ s : E3) ≠ 0) : (velocity (f ∘ γ) s : E3) ≠ 0 := by
  rw [P.velocity_map hs hp]
  exact fun he => hv (P.deriv_injective hp (he.trans (map_zero _).symm))
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction HyperbolicCore
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece_2
lemma universal_fiber_velocity (c : ℝ) (hc : c ≠ 0) (z : ℍ) :
    (velocity (fun t : ℝ => (z,6*t) : ℝ → UniversalPiece) 0 : E3) ≠ 0 := by
  intro he
  have hm := (universalLogIsometry c hc).velocity_map
    ((universal_fiber_smooth z 6) 0) (mem_univ (z,6*(0:ℝ)))
  have hd : HasDerivAt (fun t : ℝ => (![Real.log z.im,z.re,6*t] : E3)) (![0,0,6] : E3) 0 := by
    apply hasDerivAt_pi.mpr; intro i; fin_cases i
    · exact hasDerivAt_const 0 _
    · exact hasDerivAt_const 0 _
    · simpa using (hasDerivAt_id (0:ℝ)).const_mul 6
  have hv : (velocity (fun t : ℝ => (![Real.log z.im,z.re,6*t] : E3)) 0 : E3) = ![0,0,6] := by
    unfold velocity
    change (mfderiv 𝓘(ℝ,ℝ) I3 (fun t : ℝ => (![Real.log z.im,z.re,6*t] : E3)) 0 : ℝ →L[ℝ] E3) 1 = _
    rw [mfderiv_eq_fderiv]
    change deriv (fun t : ℝ => (![Real.log z.im,z.re,6*t] : E3)) 0 = _
    exact hd.deriv
  change velocity (fun t : ℝ => (![Real.log z.im,z.re,6*t] : E3)) 0 = _ at hm
  rw [hv] at hm
  change (![0,0,6] : E3) = mfderiv I3 I3 universalLog (z,6*(0:ℝ))
    (velocity (fun t : ℝ => (z,6*t) : ℝ → UniversalPiece) 0) at hm
  rw [he,map_zero] at hm
  have := congrFun hm 2
  change (6:ℝ) = 0 at this
  norm_num at this
lemma core_fiber_velocity (c : ℝ) (hc : c ≠ 0) (z : ℍ) :
    (velocity (fun t : ℝ => (projection z,((6*t : ℝ) : GluedConstruction.Circle))) 0 : E3) ≠ 0 :=
  (coreProjectionIsometry c hc).velocity_map_ne_zero ((universal_fiber_smooth z 6) 0)
    (mem_univ _) (universal_fiber_velocity c hc z)

lemma lowPoint_height : height (projection lowPoint) < 1/4 := by
  rw [height_projection_high (by norm_num [lowPoint])]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9/8)
  norm_num [lowPoint] at *
  linarith
lemma pieceFiber_smooth (z : ℍ) (hz : height (projection z) < Real.log 8) :
    ContMDiff 𝓘(ℝ,ℝ) I3 ∞ (pieceFiber z hz) := by
  apply (Rechart.identity_smooth_forward Coordinates3.coordinates).comp
  change ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,EP) ∞ (pieceFiber z hz)
  have hc : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => ((6*t : ℝ) : GluedConstruction.Circle)) :=
    (CircleConstruction.projection_smooth 6).comp (contMDiff_const.mul contMDiff_id)
  change ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ × ℝ) ∞ (fun t : ℝ => (⟨projection z,hz⟩,((6*t:ℝ):GluedConstruction.Circle)) : ℝ → Piece)
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_const.prodMk hc : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℝ)) ∞
    (fun t : ℝ => (⟨projection z,hz⟩,((6*t:ℝ):GluedConstruction.Circle)) : ℝ → Piece))
lemma whole_fiber_geodesic (g : Metric (E := CylinderConstruction.P) Cylinder) (c : ℝ) (hc : c ≠ 0)
    (low : ∀ x : CylinderConstruction.P, x.1 < 1/4 → ∀ u v : CylinderConstruction.P,
      pullInner (E := CylinderConstruction.P) g CylinderConstruction.projection x u v =
        u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2) :
    IsGeodesicOn (Rechart.realMetric Coordinates3.coordinates (wholeMetric g c hc low))
      (fun t : ℝ => (projection lowPoint,((6*t : ℝ) : GluedConstruction.Circle))) univ := by
  have hg := core_fiber_geodesic c hc lowPoint 6
  exact (wholeCoreIsometry g c hc low).geodesic_reflect isOpen_univ hg.1
    (fun _ _ => lowPoint_height) hg
lemma piece_fiber_geodesic {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) :
    IsGeodesicOn (realPieceMetric hδ i) (pieceFiber lowPoint lowPoint_core) univ := by
  cases i
  · exact (pieceMapIsometry (leftWhole hδ)).geodesic_reflect isOpen_univ
      (pieceFiber_smooth lowPoint lowPoint_core).contMDiffOn (fun _ _ => mem_univ _)
      (whole_fiber_geodesic _ _ _ (leftCylinder_low hδ))
  · exact (pieceMapIsometry (rightWhole hδ)).geodesic_reflect isOpen_univ
      (pieceFiber_smooth lowPoint lowPoint_core).contMDiffOn (fun _ _ => mem_univ _)
      (whole_fiber_geodesic _ _ _ (rightCylinder_low hδ))
lemma piece_fiber_velocity {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) :
    (velocity (pieceFiber lowPoint lowPoint_core) 0 : E3) ≠ 0 := by
  intro he
  have hv := core_fiber_velocity 1 one_ne_zero lowPoint
  apply hv
  have hs := (pieceFiber_smooth lowPoint lowPoint_core) 0
  cases i
  · have hm := (pieceMapIsometry (leftWhole hδ)).velocity_map hs (mem_univ _)
    rw [he] at hm
    exact hm.trans (map_zero _)
  · have hm := (pieceMapIsometry (rightWhole hδ)).velocity_map hs (mem_univ _)
    rw [he] at hm
    exact hm.trans (map_zero _)
lemma compact_fiber_geodesic {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) :
    IsGeodesicOn (realCompactMetric hδ) (inclusion i ∘ pieceFiber lowPoint lowPoint_core) univ :=
  (pieceInclusionIsometry hδ i).geodesic_map isOpen_univ (piece_fiber_geodesic hδ i) (fun _ _ => mem_univ _)
lemma compact_fiber_velocity {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) :
    (velocity (inclusion i ∘ pieceFiber lowPoint lowPoint_core) 0 : E3) ≠ 0 :=
  (pieceInclusionIsometry hδ i).velocity_map_ne_zero ((pieceFiber_smooth lowPoint lowPoint_core) 0)
    (mem_univ _) (piece_fiber_velocity hδ i)
end ThreeManifold.CompactMetric

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Distance ----
namespace OAI

noncomputable section

/-!
# Riemannian distance and the nonpositively curved universal-cover metric.
-/

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "I" => 𝓘(ℝ,E)

variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

lemma norm_sub_le_pathELength (R : ℝ≥0)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v))
    {γ : ℝ → E} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ‖γ b - γ a‖ₑ ≤ (R : ℝ≥0∞) * pathELength I γ a b := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hγ hab).trans
  rw [pathELength_eq_lintegral_mfderiv_Icc,← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono
  intro t
  have h := ENNReal.ofReal_le_ofReal (hR (γ t) (deriv γ t))
  rw [ENNReal.ofReal_mul R.coe_nonneg] at h
  have hv : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1 : E) = deriv γ t := by
    rw [mfderiv_eq_fderiv]
    rfl
  have hx := congrArg (fun v : E => g.inner (γ t) v v) hv
  dsimp only
  rw [tangent_enorm g]
  rw [hx]
  simpa only [ofReal_norm,ENNReal.ofReal_coe_nnreal] using h

lemma norm_sub_le_riemannianEDist (R : ℝ≥0) (hRp : 0 < R)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v)) (x y : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ‖y-x‖ₑ ≤ (R : ℝ≥0∞) * riemannianEDist I x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  rw [mul_comm]
  apply (ENNReal.div_le_iff (by exact_mod_cast hRp.ne') ENNReal.coe_ne_top).mp
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ,h0,h1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hb := norm_sub_le_pathELength g R hR (contMDiffOn_iff_contDiffOn.mp hγ) (by norm_num : (0:ℝ) ≤ 1)
  rw [h0,h1,mul_comm] at hb
  exact ((ENNReal.div_le_iff (by exact_mod_cast hRp.ne') ENNReal.coe_ne_top).mpr hb).trans_lt hlen

lemma norm_sub_le_dist (R : ℝ≥0) (hRp : 0 < R)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v)) (x y : E) :
    ‖y-x‖ ≤ R * @dist E (metricSpace g).toPseudoMetricSpace.toDist x y := by
  have h := norm_sub_le_riemannianEDist g R hRp hR x y
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : MetricSpace E := metricSpace g
  have hh : ‖y-x‖ₑ ≤ (R : ℝ≥0∞) * edist x y := h
  have hh' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (@edist_ne_top E (metricSpace g).toPseudoMetricSpace x y)) hh
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,toReal_enorm] at hh'
  rw [@edist_dist E (metricSpace g).toPseudoMetricSpace,
    ENNReal.toReal_ofReal (@dist_nonneg E (metricSpace g).toPseudoMetricSpace x y)] at hh'
  exact hh'

theorem properSpace [ProperSpace E] (R : ℝ≥0) (hRp : 0 < R)
    (hR : ∀ (x : E) (v : E), ‖v‖ ≤ R * Real.sqrt (g.inner x v v)) :
    @ProperSpace E (metricSpace g).toPseudoMetricSpace := by
  have hc (x : E) (r : ℝ) : IsCompact {y : E | ‖y-x‖ ≤ R*r} := by
    simpa only [Metric.closedBall,dist_eq_norm] using isCompact_closedBall x ((R:ℝ)*r)
  let : PseudoMetricSpace E := (metricSpace g).toPseudoMetricSpace
  constructor
  intro x r
  apply (hc x r).of_isClosed_subset Metric.isClosed_closedBall
  intro y hy
  exact (norm_sub_le_dist g R hRp hR x y).trans
    (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_comm] using hy) R.coe_nonneg)
end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
end ThreeManifold.MetricConstruction

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.UniversalDeck
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

variable [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]

end ThreeManifold.UniversalDeck
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.QuotientCoverGeometry
variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
variable {p : E → X} (hp : IsQuotientCoveringMap p G)
include hp

lemma locallyFinite_graphs [T2Space X] :
    LocallyFinite (fun g : G => {q : E × E | q.2 = g • q.1}) := by
  let := hp.toContinuousConstSMul
  intro q
  by_cases hq : p q.2 = p q.1
  · obtain ⟨d,hd⟩ := hp.apply_eq_iff_mem_orbit.mp hq
    obtain ⟨U,hU,hdis⟩ := hp.disjoint q.1
    have hV : (fun z : E => d • z) '' U ∈ 𝓝 q.2 := by
      rw [← hd]
      exact (Homeomorph.smul d).isOpenEmbedding.image_mem_nhds.mpr hU
    refine ⟨U ×ˢ ((fun z : E => d • z) '' U),prod_mem_nhds hU hV,?_⟩
    apply (finite_singleton d).subset
    rintro g ⟨⟨a,b⟩,hgraph,ha,⟨c,hc,hcb⟩⟩
    have hmove : (d⁻¹*g) • a = c := by
      rw [mul_smul,← hgraph,← hcb,inv_smul_smul]
    have he := hdis (d⁻¹*g) ⟨c,⟨a,ha,hmove⟩,hc⟩
    exact (inv_mul_eq_one.mp he).symm
  · let V := {q : E × E | p q.2 ≠ p q.1}
    have hV : IsOpen V := isClosed_eq (hp.continuous.comp continuous_snd)
      (hp.continuous.comp continuous_fst) |>.isOpen_compl
    refine ⟨V,hV.mem_nhds hq,?_⟩
    apply finite_empty.subset
    rintro g ⟨⟨a,b⟩,hgraph,hne⟩
    exact False.elim (hne (hgraph ▸ hp.map_smul g))

theorem properlyDiscontinuous [T2Space X] : ProperlyDiscontinuousSMul G E := by
  constructor
  intro K L hK hL
  apply ((locallyFinite_graphs hp).finite_nonempty_inter_compact (hK.prod hL)).subset
  rintro g ⟨b,⟨a,ha,rfl⟩,hb⟩
  exact ⟨(a,g•a),rfl,ha,hb⟩

theorem compact_fundamental_set [LocallyCompactSpace E] [CompactSpace X] :
    ∃ K : Set E, IsCompact K ∧ ∀ z : E, ∃ g : G, g • z ∈ K := by
  choose e he using hp.surjective
  choose K hK hKn using fun x : X => exists_compact_mem_nhds (e x)
  have hn : ∀ x : X, p '' K x ∈ 𝓝 x := by
    intro x
    have h := hp.isCoveringMap.isOpenMap.image_mem_nhds (hKn x)
    simpa only [he x] using h
  obtain ⟨s,hs,hcover⟩ := isCompact_univ.elim_nhds_subcover (fun x => p '' K x) (fun x _ => hn x)
  refine ⟨⋃ x ∈ s, K x,s.finite_toSet.isCompact_biUnion (fun x _ => hK x),?_⟩
  intro z
  obtain ⟨x,hxs,y,hy,hpy⟩ := mem_iUnion₂.mp (hcover (mem_univ (p z)))
  obtain ⟨g,hg⟩ := hp.apply_eq_iff_mem_orbit.mp hpy
  refine ⟨g,mem_iUnion₂.mpr ⟨x,hxs,?_⟩⟩
  have hz : g • z = y := hg
  rw [hz]
  exact hy
end ThreeManifold.QuotientCoverGeometry
end

section

open Set Metric

namespace ThreeManifold.NoNPC

section Attainment
variable {G X : Type*} [Group G] [MetricSpace X] [ProperSpace X]
  [MulAction G X] [IsIsometricSMul G X] [ProperlyDiscontinuousSMul G X]

omit [ProperSpace X] [ProperlyDiscontinuousSMul G X] in
lemma conjugate_displacement (g k : G) (x : X) :
    dist (k • x) ((k * g * k⁻¹) • (k • x)) = dist x (g • x) := by
  simp only [mul_smul, inv_smul_smul, dist_smul]

theorem displacement_attains_minimum [Nonempty X] (g : G)
    {K : Set X} (hK : IsCompact K) (hcover : ∀ x : X, ∃ k : G, k • x ∈ K) :
    ∃ x : X, ∀ y : X, dist x (g • x) ≤ dist y (g • y) := by
  let x₀ : X := Classical.choice inferInstance
  let R : ℝ := dist x₀ (g • x₀)
  let S : Set G := {h | (∃ k : G, h = k * g * k⁻¹) ∧
    ∃ y ∈ K, dist y (h • y) ≤ R}
  have hS : S.Finite := by
    apply (finite_disjoint_inter_image (Γ := G) hK (hK.cthickening (r := R))).subset
    rintro h ⟨_, y, hy, hd⟩
    exact ⟨h • y, ⟨y, hy, rfl⟩,
      mem_cthickening_of_dist_le (h • y) y R K hy (by rwa [dist_comm])⟩
  let A : Set ℝ := ⋃ h ∈ S, (fun y : X => dist y (h • y)) '' K
  have hA : IsCompact A := hS.isCompact_biUnion fun h _ =>
    hK.image (continuous_id.dist (isometry_smul X h).continuous)
  have hmem (x : X) (hx : dist x (g • x) ≤ R) : dist x (g • x) ∈ A := by
    obtain ⟨k, hk⟩ := hcover x
    have hd := conjugate_displacement g k x
    apply mem_iUnion.mpr ⟨k * g * k⁻¹, ?_⟩
    apply mem_iUnion.mpr ⟨⟨⟨k, rfl⟩, k • x, hk, hd.trans_le hx⟩, ?_⟩
    exact ⟨k • x, hk, hd⟩
  have hR : R ∈ A := hmem x₀ le_rfl
  obtain ⟨r, hrA, hr⟩ := hA.exists_isLeast ⟨R, hR⟩
  rcases mem_iUnion.mp hrA with ⟨h, hrA⟩
  rcases mem_iUnion.mp hrA with ⟨hh, y, hy, hyr⟩
  obtain ⟨k, rfl⟩ := hh.1
  refine ⟨k⁻¹ • y, fun z => ?_⟩
  have hdisp : dist (k⁻¹ • y) (g • (k⁻¹ • y)) = r := by
    have he := conjugate_displacement g k (k⁻¹ • y)
    simpa only [smul_inv_smul, hyr] using he.symm
  rw [hdisp]
  by_cases hz : dist z (g • z) ≤ R
  · exact hr (hmem z hz)
  · exact (hr hR).trans (le_of_not_ge hz)

end Attainment

section ProductShift

end ProductShift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end ThreeManifold.NoNPC
end

section
open Set Filter Topology Bundle Manifold
open scoped ContDiff NNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma exponentialMetric_coercive (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) : ∃ R : ℝ≥0, 0 < R ∧ ∀ (x v : E3),
      ‖v‖ ≤ R * Real.sqrt ((exponentialMetric g hn p).inner x v v) := by
  obtain ⟨C,hC,hb⟩ := positive_bilinear_norm_bound (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner p)
    (fun v hv => g.pos p v hv)
  refine ⟨⟨Real.sqrt C,Real.sqrt_nonneg C⟩,Real.sqrt_pos.mpr hC,fun x v => ?_⟩
  have hx := exponentialMetric_expanding g hn p x v
  have hy : 0 ≤ (exponentialMetric g hn p).inner x v v :=
    (inner_self_nonneg g p v).trans hx
  have hs := Real.sq_sqrt hC.le
  have ht := Real.sq_sqrt hy
  have hh := (hb v).trans (mul_le_mul_of_nonneg_left hx hC.le)
  change ‖v‖ ≤ Real.sqrt C * Real.sqrt ((exponentialMetric g hn p).inner x v v)
  nlinarith [norm_nonneg v,Real.sqrt_nonneg C,
    Real.sqrt_nonneg ((exponentialMetric g hn p).inner x v v),
    mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg ((exponentialMetric g hn p).inner x v v)),
    sq_nonneg (‖v‖-Real.sqrt C*Real.sqrt ((exponentialMetric g hn p).inner x v v))]

lemma universalMetric_proper (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    @ProperSpace E3 (universalMetric g hn p).toPseudoMetricSpace := by
  obtain ⟨R,hR,hb⟩ := exponentialMetric_coercive g hn p
  exact RiemannianDistance.properSpace _ R hR hb

theorem npc_deck_displacement_minimum [PathConnectedSpace M]
    (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M)
    (d : UniversalDeck.group (exponential g p)) :
    ∃ x : E3, ∀ y : E3,
      @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist x (d • x) ≤
      @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist y (d • y) := by
  let : MetricSpace E3 := universalMetric g hn p
  let : PseudoMetricSpace E3 := (universalMetric g hn p).toPseudoMetricSpace
  let : PseudoEMetricSpace E3 := (universalMetric g hn p).toPseudoEMetricSpace
  let : ProperSpace E3 := universalMetric_proper g hn p
  let : IsIsometricSMul (UniversalDeck.group (exponential g p)) E3 :=
    ⟨fun d => universalMetric_deck_isometry g hn p d⟩
  have hq := UniversalDeck.quotient_cover (npc_exponential_isCoveringMap g hn p)
  let := QuotientCoverGeometry.properlyDiscontinuous hq
  obtain ⟨K,hK,hcover⟩ := QuotientCoverGeometry.compact_fundamental_set hq
  exact NoNPC.displacement_attains_minimum d hK hcover
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (h : ContinuousRiemannianMetric F (TangentSpace 𝓘(ℝ,F) : F → Type _))
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology
namespace ThreeManifold.UniversalCover
variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
  [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
  {p : E → X} {q : F → X}

end ThreeManifold.UniversalCover
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace ThreeManifold.RiemannianDistance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (g : ContinuousRiemannianMetric E (TangentSpace 𝓘(ℝ,E) : E → Type _))

end ThreeManifold.RiemannianDistance
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff ENNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.FundamentalGroup ----
namespace OAI

noncomputable section

/-!
# Fundamental-group relations and nontrivial fiber classes.
-/

section

open Matrix Set Pointwise
open scoped MatrixGroups UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

lemma effect_neg_one : effect ⟨-1,neg_one_mem⟩ = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  change ((-1:SL(2,ℤ)) • z) = z
  simp

end ThreeManifold.HyperbolicCore
end

section
open Set Filter Topology ModularGroup
open scoped UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

lemma boundaryClass_effect (a : ℝ) (ha : 0 < a) :
    surfaceFundamentalGroupEquiv (horoline a 0 ha) (boundaryClass a ha) =
      MulOpposite.op (effect ⟨T^6,T_six_mem⟩) := by
  change projection_cover.fundamentalGroupToMulOpposite ⟨horoline a 0 ha,rfl⟩
    (boundaryClass a ha) = MulOpposite.op (effect ⟨T^6,T_six_mem⟩)
  apply (projection_cover.fundamentalGroupToMulOpposite_apply_eq_Iff).2
  let hp := projection_cover.isCoveringMap
  have hl : (fun t : unitInterval => horoline a t ha) = hp.liftPath (boundaryPath a ha)
      (horoline a 0 ha) rfl := by
    apply (hp.eq_liftPath_iff rfl).2
    exact ⟨(horoline_continuous a ha).comp continuous_subtype_val,rfl,rfl⟩
  change T^6 • horoline a 0 ha = hp.liftPath (boundaryPath a ha) (horoline a 0 ha) rfl 1
  rw [← hl]; exact (horoline_one a ha).symm

lemma peripheral_effect : effect ⟨T^6,T_six_mem⟩ =
    (effectiveGenerator true)⁻¹*(effectiveGenerator false)⁻¹*
      effectiveGenerator true*effectiveGenerator false := by
  have hm : (⟨T^6,T_six_mem⟩ : Γ) = ⟨-1,neg_one_mem⟩ *
      ((⟨psi,psi_mem⟩ : Γ)⁻¹ * (⟨phi,phi_mem⟩ : Γ)⁻¹ * ⟨psi,psi_mem⟩ * ⟨phi,phi_mem⟩) := by
    apply Subtype.ext
    change T^6 = (-1)*(psi⁻¹*phi⁻¹*psi*phi)
    rw [peripheral_matrix]
    simp
  rw [hm,map_mul,effect_neg_one,one_mul]
  simp only [map_mul,map_inv,effectiveGenerator,pairingGenerator]

theorem boundaryClass_commutator (a : ℝ) (ha : 0 < a) :
    ∃ A B : FundamentalGroup Surface (projection (horoline a 0 ha)),
      boundaryClass a ha = A*B*A⁻¹*B⁻¹ := by
  let e := surfaceFundamentalGroupEquiv (horoline a 0 ha)
  refine ⟨e.symm (MulOpposite.op (effectiveGenerator false)),
    e.symm (MulOpposite.op (effectiveGenerator true)),?_⟩
  apply e.injective
  simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
  rw [boundaryClass_effect,peripheral_effect]
  simp only [MulOpposite.op_mul,MulOpposite.op_inv]
  group
end ThreeManifold.HyperbolicCore
end

section
open Set Topology
namespace ThreeManifold.LoopTopology
open Path.Homotopic
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y}
lemma pair_commute (a : FundamentalGroup X x) (b : FundamentalGroup Y y) :
    Commute (pair a 1) (pair 1 b) := by
  change pair a 1 * pair 1 b = pair 1 b * pair a 1
  rw [← pair_mul,← pair_mul]; simp
lemma pair_split (a : FundamentalGroup X x) (b : FundamentalGroup Y y) :
    pair a b = pair a 1 * pair 1 b := by rw [← pair_mul]; simp

lemma loop_cast_eq_one_iff {x y : X} (h : y = x) (q : FundamentalGroup X x) :
    Path.Homotopic.Quotient.cast q h h = (1 : FundamentalGroup X y) ↔ q = (1 : FundamentalGroup X x) := by
  subst y
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
lemma mapOfEq_eq_one_iff (F : C(X,Y)) {x : X} {y : Y} (h : F x = y)
    (q : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq F h q = 1 ↔ FundamentalGroup.map F x q = 1 := by
  rw [FundamentalGroup.mapOfEq_apply]
  exact loop_cast_eq_one_iff h.symm _
end ThreeManifold.LoopTopology
end

section
open Set Filter Topology
open scoped UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology

lemma fiber_commutes_surface (i : Bool) (a : FundamentalGroup Surface baseSurface) :
    Commute (fiberClass i) (surfaceHom i a) :=
  ((pair_commute a circleClass).symm).map (blockHom i)
lemma boundaryImage_commutator (i : Bool) :
    ∃ a b : FundamentalGroup Manifold basePoint, boundaryImage i = a*b*a⁻¹*b⁻¹ ∧
      Commute (fiberClass i) a ∧ Commute (fiberClass i) b := by
  obtain ⟨a,b,h⟩ := boundaryClass_commutator 4 (by norm_num)
  refine ⟨surfaceHom i a,surfaceHom i b,?_,fiber_commutes_surface i a,fiber_commutes_surface i b⟩
  change surfaceHom i (boundaryClass 4 _) = _
  rw [h]; simp only [map_mul,map_inv]
end ThreeManifold.GluedConstruction
end

open Set Filter Topology
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology
lemma blockHom_mk (i : Bool) (p : Path wholeBase wholeBase) :
    blockHom i (Path.Homotopic.Quotient.mk p) = Path.Homotopic.Quotient.mk
      ((p.map (blockMap i).continuous).cast (blockMap_base i).symm (blockMap_base i).symm) := by
  exact FundamentalGroup.mapOfEq_apply _ _ _
lemma shear_fiber : fiberClass true = boundaryImage false := by
  change blockHom true (Path.Homotopic.Quotient.mk ((Path.refl baseSurface).prod circlePath)) =
    blockHom false (Path.Homotopic.Quotient.mk ((boundaryPath 4 (by norm_num)).prod (Path.refl 0)))
  rw [blockHom_mk,blockHom_mk]
  congr 1
  apply Path.ext
  funext t
  change blockMap true (baseSurface,((6*(t:ℝ):ℝ):Circle)) =
    blockMap false (projection (horoline 4 t (by norm_num)),0)
  rw [← boundarySurface_zero,← boundarySurface_horoline]
  simpa only [zero_add] using blockMap_torus_shear (0,((6*(t:ℝ):ℝ):Circle))
lemma shear_boundary : boundaryImage true = boundaryImage false * fiberClass false := by
  change blockHom true (pair (boundaryClass 4 (by norm_num)) 1) =
    blockHom false (pair (boundaryClass 4 (by norm_num)) 1) * blockHom false (pair 1 circleClass)
  rw [← map_mul,← pair_split]
  change blockHom true (Path.Homotopic.Quotient.mk ((boundaryPath 4 (by norm_num)).prod (Path.refl 0))) =
    blockHom false (Path.Homotopic.Quotient.mk ((boundaryPath 4 (by norm_num)).prod circlePath))
  rw [blockHom_mk,blockHom_mk]
  congr 1
  apply Path.ext
  funext t
  change blockMap true (projection (horoline 4 t (by norm_num)),0) =
    blockMap false (projection (horoline 4 t (by norm_num)),((6*(t:ℝ):ℝ):Circle))
  rw [← boundarySurface_horoline]
  simpa only [add_zero] using blockMap_torus_shear (((6*(t:ℝ):ℝ):Circle),0)
lemma fibers_commute : Commute (fiberClass false) (fiberClass true) := by
  rw [shear_fiber]
  exact fiber_commutes_surface false (boundaryClass 4 (by norm_num))

theorem actual_loop_relations :
    ∃ a b c d : FundamentalGroup Manifold basePoint,
      Commute (fiberClass false) (fiberClass true) ∧
      Commute (fiberClass false) a ∧ Commute (fiberClass false) b ∧
      Commute (fiberClass true) c ∧ Commute (fiberClass true) d ∧
      fiberClass true = a*b*a⁻¹*b⁻¹ ∧
      fiberClass true * fiberClass false = c*d*c⁻¹*d⁻¹ := by
  obtain ⟨a,b,h,hfa,hfb⟩ := boundaryImage_commutator false
  obtain ⟨c,d,k,hhc,hhd⟩ := boundaryImage_commutator true
  exact ⟨a,b,c,d,fibers_commute,hfa,hfb,hhc,hhd,
    shear_fiber.trans h,(congrArg (fun z => z*fiberClass false) shear_fiber).trans (shear_boundary.symm.trans k)⟩
end ThreeManifold.GluedConstruction

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.NoConjugatePoints ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Countable passage assembly and the uniform no-conjugate-points theorem.
-/

section
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

end ThreeManifold.ReturningPassage
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Neck
open Turning ReturningPassage ReturningCoefficients

end ThreeManifold.Neck
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem realCompactMetric_noConjugatePoints {δ C : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ) :
    NoConjugatePoints (realCompactMetric hδ) := by
  apply noConjugatePoints_of_intrinsic_index
  intro U hU hUc γ hγ
  exact realCompactMetric_nonnegative_index hδ hC hsmall hB hU hUc hγ

theorem exists_uniform_compact_noConjugatePoints : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1/2 ∧
    ∀ δ (hδ : δ ∈ Ioc (0:ℝ) (1/2)), δ ≤ δ₀ → NoConjugatePoints (realCompactMetric hδ) := by
  obtain ⟨δ₀,C,hδ₀,hhalf,hC,hbounds⟩ := uniform_turning_parameters
  refine ⟨δ₀,hδ₀,hhalf,?_⟩
  intro δ hδ hsmall
  obtain ⟨hs,hB⟩ := hbounds δ ⟨hδ.1,hsmall⟩
  exact realCompactMetric_noConjugatePoints hδ hC hs hB
end ThreeManifold.CompactMetric

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.ThreeManifold ----
namespace OAI

noncomputable section

/-!
# The universal-cover shear obstruction and the three-manifold existence theorem.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.CompactMetric
open GluedConstruction HyperbolicCore LoopTopology RiemannianCoordinates
lemma lowPoint_clip : height (projection lowPoint) ≤ Real.log 4 := by
  rw [height_projection_high (by norm_num [lowPoint])]
  exact (Real.log_lt_log (by norm_num [lowPoint]) (by norm_num [lowPoint] : lowPoint.im < 4)).le
lemma blockMap_low (i : Bool) (t : ℝ) :
    blockMap i (projection lowPoint,((6*t : ℝ) : GluedConstruction.Circle)) =
      inclusion i (pieceFiber lowPoint lowPoint_core t) := by
  change inclusion i (clippedPiece (projection lowPoint,((6*t : ℝ) : GluedConstruction.Circle))) = _
  rw [clippedPiece_fixed _ lowPoint_clip]
  rfl
lemma compact_fiber_periodic (i : Bool) :
    (inclusion i ∘ pieceFiber lowPoint lowPoint_core) 1 =
      (inclusion i ∘ pieceFiber lowPoint lowPoint_core) 0 := by
  apply congrArg (inclusion i)
  apply Prod.ext
  · rfl
  · change ((6*(1:ℝ) : ℝ) : GluedConstruction.Circle) = ((6*(0:ℝ) : ℝ) : GluedConstruction.Circle)
    simp
lemma block_fiber_low_nontrivial (i : Bool) :
    FundamentalGroup.map (blockMap i) (projection lowPoint,0) (pair 1 circleClass) ≠ 1 := by
  obtain ⟨δ,hδ,hhalf,hn⟩ := exists_uniform_compact_noConjugatePoints
  let hd : δ ∈ Ioc (0:ℝ) (1/2) := ⟨hδ,hhalf⟩
  let γ := inclusion i ∘ pieceFiber lowPoint lowPoint_core
  have hg : IsGeodesicOn (realCompactMetric hd) γ univ := compact_fiber_geodesic hd i
  have hper : γ 1 = γ 0 := compact_fiber_periodic i
  let P := closedCurvePath (contMDiffOn_univ.mp hg.1).continuous hper
  have hessential : (Path.Homotopic.Quotient.mk P : FundamentalGroup Manifold (γ 0)) ≠ (1 : FundamentalGroup Manifold (γ 0)) :=
    closedGeodesic_essential (realCompactMetric hd) (hn δ hd le_rfl) hg hper (compact_fiber_velocity hd i)
  have hbase : blockMap i (projection lowPoint,0) = γ 0 := by
    dsimp only [γ,Function.comp_apply]
    simpa only [mul_zero,AddCircle.coe_zero] using blockMap_low i 0
  have he : FundamentalGroup.map (blockMap i) (projection lowPoint,0) (pair 1 circleClass) =
      Path.Homotopic.Quotient.cast (Path.Homotopic.Quotient.mk P) hbase hbase := by
    change Path.Homotopic.Quotient.mk ((((Path.refl (projection lowPoint)).prod circlePath).map (blockMap i).continuous)) =
      Path.Homotopic.Quotient.mk (P.cast hbase hbase)
    congr 1
    apply Path.ext
    funext t
    exact blockMap_low i t
  intro hnull
  apply hessential
  apply (loop_cast_eq_one_iff hbase (Path.Homotopic.Quotient.mk P)).mp
  exact he.symm.trans hnull

theorem fiberClass_ne_one (i : Bool) : fiberClass i ≠ 1 := by
  let : LocallyPathConnectedSpace Surface := ChartedSpace.locallyPathConnectedSpace ℂ Surface
  let : PathConnectedSpace Surface := PathConnectedSpace.of_locallyPathConnectedSpace
  intro hnull
  have hb : FundamentalGroup.map (blockMap i) wholeBase (pair 1 circleClass) = 1 :=
    (mapOfEq_eq_one_iff (blockMap i) (blockMap_base i) (pair 1 circleClass)).mp hnull
  apply block_fiber_low_nontrivial i
  exact (fiber_null_transfer (blockMap i)
    (PathConnectedSpace.somePath (projection lowPoint) baseSurface) circleClass).mpr hb
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff ENNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma universalMetric_radial_dist_of_le (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) {a b : ℝ} (hab : a ≤ b) :
    @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist (a • v) (b • v) =
      (b-a)*Real.sqrt (g.inner p v v) := by
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  apply le_antisymm
  · let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
    have hc : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) 1 (fun r : ℝ => r • v) :=
      (contDiff_id.smul contDiff_const).contMDiff
    have hh := riemannianEDist_le_pathELength hc.contMDiffOn rfl rfl hab
    rw [exponentialMetric_radial_length,← ENNReal.ofReal_mul (Real.sqrt_nonneg _),mul_comm] at hh
    change @edist E3 (universalMetric g hn p).toPseudoEMetricSpace.toEDist (a • v) (b • v) ≤ _ at hh
    rw [@edist_dist E3 (universalMetric g hn p).toPseudoMetricSpace] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hab) (Real.sqrt_nonneg _))).mp hh
  · have hh := universalMetric_lower g hn p (a • v) (b • v)
    have hs : Real.sqrt (g.inner p (b • v - a • v) (b • v - a • v)) =
        (b-a)*Real.sqrt (g.inner p v v) := by
      rw [← sub_smul,positive_form_smul,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (sub_nonneg.mpr hab)]
    rwa [hs] at hh

lemma universalMetric_radial_dist (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (a b : ℝ) :
    @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist (a • v) (b • v) =
      |a-b| * Real.sqrt (g.inner p v v) := by
  rcases le_total a b with hab | hba
  · rw [universalMetric_radial_dist_of_le g hn p v hab,abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [@dist_comm E3 (universalMetric g hn p).toPseudoMetricSpace,
      universalMetric_radial_dist_of_le g hn p v hba,abs_of_nonneg (sub_nonneg.mpr hba)]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma universalMetric_segments (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (a b : E3) :
    let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
    ∃ c : ℝ → E3, c 0 = a ∧ c 1 = b ∧ ∀ s t, D (c s) (c t) = |s-t| * D a b := by
  let q := exponential g p a
  have hbase : exponential g p a = exponential g q 0 := (exponential_zero g q).symm
  obtain ⟨e,he0,he,hc,hci,hi⟩ := exists_exponential_coordinates g hn a 0 hbase
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  let Q := @dist E3 (universalMetric g hn q).toPseudoMetricSpace.toDist
  have hid (x y : E3) : Q (e x) (e y) = D x y :=
    @Isometry.dist_eq E3 E3 (universalMetric g hn p).toPseudoMetricSpace
      (universalMetric g hn q).toPseudoMetricSpace e hi x y
  refine ⟨fun t => e.symm (t • e b),?_,?_,?_⟩
  · simp only [zero_smul,← he0,e.symm_apply_apply]
  · simp only [one_smul,e.symm_apply_apply]
  · intro s t
    change D (e.symm (s • e b)) (e.symm (t • e b)) = |s-t| * D a b
    rw [← hid,← hid a b,he0,e.apply_symm_apply,e.apply_symm_apply]
    dsimp only [Q]
    rw [universalMetric_radial_dist g hn q,universalMetric_radial_zero g hn q]

theorem npc_deck_shear_impossible [PathConnectedSpace M]
    (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M)
    (f h a b c d : UniversalDeck.group (exponential g p))
    (hf : f ≠ 1) (hh : h ≠ 1)
    (hfh : Commute f h) (hfa : Commute f a) (hfb : Commute f b)
    (hhc : Commute h c) (hhd : Commute h d)
    (hrel : h = a*b*a⁻¹*b⁻¹) (hrel2 : h*f = c*d*c⁻¹*d⁻¹) : False := by
  let : MetricSpace E3 := universalMetric g hn p
  let : PseudoMetricSpace E3 := (universalMetric g hn p).toPseudoMetricSpace
  let : PseudoEMetricSpace E3 := (universalMetric g hn p).toPseudoEMetricSpace
  let : ProperSpace E3 := universalMetric_proper g hn p
  let F := npcDeckIsometry g hn p
  have hfree (k : UniversalDeck.group (exponential g p)) (hk : k ≠ 1) (x : E3) : F k x ≠ x := by
    intro heq
    apply hk
    apply UniversalDeck.deck_ext (npc_exponential_isCoveringMap g hn p) (z := x)
    exact heq
  have hmin (k : UniversalDeck.group (exponential g p)) :
      (NonpositiveMetric.CNMidpoint.minset (F k : E3 → E3)).Nonempty :=
    npc_deck_displacement_minimum g hn p k
  apply (universalCN g hn p).cyclic_shear_obstruction (universalMetric_segments g hn p)
    (F f) (F h) (F a) (F b) (F c) (F d) (hmin f) (hmin h)
    (hfree f hf) (hfree h hh) (hfh.map F) (hfa.map F) (hfb.map F) (hhc.map F) (hhd.map F)
  · simpa only [map_mul,map_inv] using congrArg F hrel
  · simpa only [map_mul,map_inv] using congrArg F hrel2

end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.LoopTopology
variable {X : Type} [TopologicalSpace X]
end ThreeManifold.LoopTopology
namespace ThreeManifold.CompactMetric
open GluedConstruction RiemannianCoordinates LoopTopology

theorem realCompact_noNPC (g : SmoothMetric Manifold) : ¬ NonpositiveSectionalCurvature g := by
  let : LocallyPathConnectedSpace Manifold := ChartedSpace.locallyPathConnectedSpace E3 Manifold
  let : PathConnectedSpace Manifold := PathConnectedSpace.of_locallyPathConnectedSpace
  intro hn
  let hp := npc_exponential_isCoveringMap g hn basePoint
  let e : FundamentalGroup Manifold basePoint ≃* UniversalDeck.group (exponential g basePoint) :=
    ((groupBasepointEq (exponential_zero g basePoint).symm).trans
      (UniversalDeck.fundamentalGroupEquiv hp 0)).trans (MulEquiv.inv' _).symm
  have hne (x : FundamentalGroup Manifold basePoint) (hx : x ≠ 1) : e x ≠ 1 := by
    intro he
    apply hx
    apply e.injective
    exact he.trans e.map_one.symm
  obtain ⟨a,b,c,d,hfh,hfa,hfb,hhc,hhd,hrel,hrel2⟩ := actual_loop_relations
  apply npc_deck_shear_impossible g hn basePoint
    (e (fiberClass false)) (e (fiberClass true)) (e a) (e b) (e c) (e d)
    (hne _ (fiberClass_ne_one false)) (hne _ (fiberClass_ne_one true))
    (hfh.map e.toMonoidHom) (hfa.map e.toMonoidHom) (hfb.map e.toMonoidHom)
    (hhc.map e.toMonoidHom) (hhd.map e.toMonoidHom)
  · simpa only [map_mul,map_inv] using congrArg e hrel
  · simpa only [map_mul,map_inv] using congrArg e hrel2
end ThreeManifold.CompactMetric
end

namespace ThreeManifold
open Set GluedConstruction CompactMetric

theorem main_theorem : MainStatement := by
  obtain ⟨δ,hδ,hhalf,hn⟩ := exists_uniform_compact_noConjugatePoints
  let hd : δ ∈ Ioc (0:ℝ) (1/2) := ⟨hδ,hhalf⟩
  refine ⟨Manifold,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    realCharts,realSmooth,manifold_oriented,⟨realCompactMetric hd,hn δ hd le_rfl⟩,?_⟩
  rintro ⟨g,hg⟩
  exact realCompact_noNPC g hg
end ThreeManifold

end

end OAI

-- ---- mission target ----
open OAI OAI.ThreeManifold
open Set Manifold Bundle
open scoped ContDiff
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]
open Set GluedConstruction CompactMetric

theorem solution : MainStatement := by
  first
    | exact OAI.ThreeManifold.main_theorem
    | (apply OAI.ThreeManifold.main_theorem <;> assumption)
    | (intros; apply OAI.ThreeManifold.main_theorem <;> assumption)
