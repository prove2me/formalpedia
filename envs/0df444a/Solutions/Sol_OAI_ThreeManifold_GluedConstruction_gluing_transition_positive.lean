-- Prove2me | solution 1 for OAI.ThreeManifold.GluedConstruction.gluing_transition_positive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:12:27.673685+00:00
-- url     : https://prove2.me/submissions/f0cb0551-f4a4-4687-9f5d-a313ad7860ce

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Gluing.lean:L1326-L1377
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.GluedConstruction.gluing_transition_positive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Theorems.Thm_OAI_ThreeManifold_GluedConstruction_coverChart_component_smooth
import Theorems.Thm_OAI_ThreeManifold_HyperbolicCore_action_orientation
import Theorems.Thm_OAI_ThreeManifold_QuotientConstruction_manifold_projection_positive

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

end

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
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
end ThreeManifold.HyperbolicCore
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CircleConstruction
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.HyperbolicCore
lemma projection_chart_positive (b : Surface) (z : ℍ)
    (hy : projection z ∈ (chartAt ℂ b).source) :
    0 < LinearMap.det (fderiv ℝ
      (fun y : ℂ => chartAt ℂ b (projection (UpperHalfPlane.ofComplex y))) (z : ℂ)).toLinearMap := by
  have hpos := QuotientConstruction.manifold_projection_positive projection_cover
    sectionMap_rightInverse (fun k => (effective_smooth k).continuous)
    (fun k a b x hx hy => by
      obtain ⟨g,rfl⟩ := effect_surjective k
      exact action_orientation g.val a b x hx)
  have hx : (z : ℂ) ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source (mem_chart_source ℂ z)
  have hz : (chartAt ℂ z).symm (z : ℂ) = z := (chartAt ℂ z).left_inv (mem_chart_source ℂ z)
  have he : (fun y : ℂ => chartAt ℂ b (projection (UpperHalfPlane.ofComplex y))) =ᶠ[nhds (z : ℂ)]
      (fun y => chartAt ℂ b (projection ((chartAt ℂ z).symm y))) := by
    filter_upwards [(chartAt ℂ z).open_target.mem_nhds hx] with y hy
    have hy' : ((chartAt ℂ z).symm y : ℂ) = y := (chartAt ℂ z).right_inv hy
    have ho : UpperHalfPlane.ofComplex y = (chartAt ℂ z).symm y :=
      (congrArg UpperHalfPlane.ofComplex hy'.symm).trans (UpperHalfPlane.ofComplex_apply _)
    rw [ho]
  rw [he.fderiv_eq]
  exact hpos z b (z : ℂ) hx (by rw [hz]; exact hy)
end ThreeManifold.HyperbolicCore
namespace ThreeManifold.CircleConstruction
lemma projection_chart_positive (b : ℝ) (a : AddCircle b) (r : ℝ)
    (hr : (r : AddCircle b) ∈ (chartAt ℝ a).source) :
    0 < LinearMap.det (fderiv ℝ (fun t : ℝ => chartAt ℝ a (t : AddCircle b)) r).toLinearMap := by
  have hpos := QuotientConstruction.manifold_projection_positive (projection_cover b) (section_spec b)
    (fun k => (action_smooth b k).continuous) (fun k a c x hx hy => by
      change 0 < LinearMap.det (fderiv ℝ ((fun _ : ℝ => (Multiplicative.toAdd k).val) + id) x).toLinearMap
      rw [(hasFDerivAt_const (𝕜 := ℝ) (Multiplicative.toAdd k).val x |>.add (hasFDerivAt_id x)).fderiv]
      simp)
  exact hpos r a r (mem_univ _) hr
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

lemma coverChart_positive (b : Piece) (z : ℍ) (r : ℝ)
    (hz : projection z ∈ (chartAt ℂ b.1.1).source)
    (hr : (r : Circle) ∈ (chartAt ℝ b.2).source) :
    0 < LinearMap.det (fderiv ℝ (coverChart b) ((z : ℂ),r)).toLinearMap := by
  obtain ⟨h1,h2⟩ := coverChart_component_smooth b z r hz hr
  have hd := HasFDerivAt.prodMap ((z : ℂ),r)
    (h1.differentiableAt (by simp)).hasFDerivAt (h2.differentiableAt (by simp)).hasFDerivAt
  change 0 < LinearMap.det (fderiv ℝ (Prod.map _ _) ((z : ℂ),r)).toLinearMap
  rw [hd.fderiv]
  change (0 : ℝ) < LinearMap.det ((fderiv ℝ _ (z : ℂ)).toLinearMap.prodMap
    (fderiv ℝ _ r).toLinearMap)
  rw [LinearMap.det_prodMap]
  exact mul_pos (HyperbolicCore.projection_chart_positive _ z hz)
    (CircleConstruction.projection_chart_positive 6 _ r hr)

lemma coverChart_smooth (b : Piece) (z : ℍ) (r : ℝ)
    (hz : projection z ∈ (chartAt ℂ b.1.1).source)
    (hr : (r : Circle) ∈ (chartAt ℝ b.2).source) :
    ContDiffAt ℝ ∞ (coverChart b) ((z : ℂ),r) := by
  obtain ⟨h1,h2⟩ := coverChart_component_smooth b z r hz hr
  exact h1.prodMap h2

lemma coverChart_apply (b : Piece) (z : ℍ) (r : ℝ)
    (hz : height (projection z) < Real.log 8) :
    coverChart b ((z : ℂ),r) = chartAt (ℂ × ℝ) b ((⟨projection z,hz⟩ : OpenCore 8),(r : Circle)) := by
  simp only [coverChart,Prod.map_apply,UpperHalfPlane.ofComplex_apply]
  rfl
end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

lemma neckLift_gluing (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    gluingMap (neckLift z hz r) =
      neckLift (flipUpper z r) (flipUpper_band z hz r) (z.re-r) := by
  apply collarCoordinates.injective
  change collarCoordinates (collarCoordinates.symm
    ((collarFlip.prodCongr torusShear.symm) (collarCoordinates (neckLift z hz r)))) = _
  rw [Homeomorph.apply_symm_apply,neckLift_coordinates,neckLift_coordinates]
  apply Prod.ext
  · apply Subtype.ext
    exact (flipUpper_im z r).symm
  · change ((r : Circle),(z.re : Circle)-(r : Circle)) =
      (((flipUpper z r).re : Circle),((z.re-r : ℝ) : Circle))
    simp

lemma neckLift_chart (b : Piece) (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    chartAt (ℂ × ℝ) b (neckLift z hz r).1 = coverChart b ((z : ℂ),r) :=
  (coverChart_apply b z r _).symm

lemma neckLift_chart_source (b : Piece) (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    (neckLift z hz r).1 ∈ (chartAt (ℂ × ℝ) b).source ↔
      projection z ∈ (chartAt ℂ b.1.1).source ∧ (r : Circle) ∈ (chartAt ℝ b.2).source := by
  change ((neckLift z hz r).1.1 ∈ (chartAt ℂ b.1).source ∧ _) ↔ _
  change ((⟨projection z, (neckLift z hz r).1.1.2⟩ : coreOpens 8) ∈
    ((chartAt ℂ b.1.1).subtypeRestr (⟨b.1⟩ : Nonempty (coreOpens 8))).source ∧ _) ↔ _
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  rfl
end ThreeManifold.GluedConstruction

open Set Filter Topology
namespace ThreeManifold.Coordinates3

lemma det_shearD (d : ℝ) : LinearMap.det (shearD d).toLinearMap = -d := by
  let L := coordinates.toLinearEquiv.toLinearMap ∘ₗ (shearD d).toLinearMap ∘ₗ
    coordinates.symm.toLinearEquiv.toLinearMap
  have hL : LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3)) L =
      !![0,0,1;0,d,0;1,0,-1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L,coordinates,shearD]
  rw [← LinearMap.det_conj (shearD d).toLinearMap coordinates.toLinearEquiv]
  change LinearMap.det L = -d
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)),hL,Matrix.det_fin_three]
  simp

lemma liftedGluing_derivative {p : ℂ × ℝ} (hp : p.1.im ≠ 0) :
    HasFDerivAt liftedGluing (shearD (-(16 / p.1.im ^ 2))) p := by
  have hi := Complex.imCLM.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt
  have hr := Complex.reCLM.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt
  have hs := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt (x := p)
  have hd := (hasDerivAt_inv hp).comp_hasFDerivAt p hi |>.const_mul (16 : ℝ)
  have h1 := (Complex.ofRealCLM.hasFDerivAt.comp p hs).add
    ((Complex.ofRealCLM.hasFDerivAt.comp p hd).mul_const Complex.I)
  have h2 := hr.sub hs
  have h := h1.prodMk h2
  convert! h using 1
  ext x <;> simp [shearD,ContinuousLinearMap.comp_apply,div_eq_mul_inv]
  ring
end ThreeManifold.Coordinates3

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore Coordinates3 TwoGluing

lemma cover_transition_germ (a b : Piece) (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ)
    (ha : (neckLift z hz r).1 ∈ (chartAt (ℂ × ℝ) a).source) :
    ((fun x => chartAt (ℂ × ℝ) b (extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm x))) ∘
      coverChart a) =ᶠ[nhds ((z : ℂ),r)] (coverChart b ∘ liftedGluing) := by
  obtain ⟨ha1,ha2⟩ := (neckLift_chart_source a z hz r).mp ha
  have him : ContinuousAt (fun p : ℂ × ℝ => p.1.im) ((z : ℂ),r) :=
    (Complex.continuous_im.comp continuous_fst).continuousAt
  have hband : ∀ᶠ p : ℂ × ℝ in nhds ((z : ℂ),r), (2 : ℝ) < p.1.im ∧ p.1.im < 8 :=
    him (isOpen_Ioo.mem_nhds hz)
  have hof : ContinuousAt UpperHalfPlane.ofComplex (z : ℂ) :=
    (upperHalfPlane_ofComplex_real_smoothAt (z := (z : ℂ)) z.im_pos).continuousAt
  have hofst : ContinuousAt (fun p : ℂ × ℝ => UpperHalfPlane.ofComplex p.1) ((z : ℂ),r) :=
    hof.comp (f := fun p : ℂ × ℝ => p.1) (continuousAt_fst (p := ((z : ℂ),r)))
  have hproj : ContinuousAt projection (UpperHalfPlane.ofComplex (z : ℂ)) :=
    projection_cover.continuous.continuousAt
  have h1 : ContinuousAt (fun p : ℂ × ℝ => projection (UpperHalfPlane.ofComplex p.1)) ((z : ℂ),r) :=
    hproj.comp (f := fun p : ℂ × ℝ => UpperHalfPlane.ofComplex p.1) hofst
  have h2 : ContinuousAt (fun p : ℂ × ℝ => (p.2 : Circle)) ((z : ℂ),r) :=
    (CircleConstruction.projection_cover 6).continuous.continuousAt.comp continuousAt_snd
  have hsource1 : ∀ᶠ p : ℂ × ℝ in nhds ((z : ℂ),r),
      projection (UpperHalfPlane.ofComplex p.1) ∈ (chartAt ℂ a.1.1).source :=
    h1 ((chartAt ℂ a.1.1).open_source.mem_nhds (by simpa only [UpperHalfPlane.ofComplex_apply] using ha1))
  have hsource2 : ∀ᶠ p : ℂ × ℝ in nhds ((z : ℂ),r), (p.2 : Circle) ∈ (chartAt ℝ a.2).source :=
    h2 ((chartAt ℝ a.2).open_source.mem_nhds ha2)
  filter_upwards [hband,hsource1,hsource2] with p hp hpa hpb
  let w : ℍ := ⟨p.1,by linarith [hp.1]⟩
  have hw : UpperHalfPlane.ofComplex p.1 = w := UpperHalfPlane.ofComplex_apply_of_im_pos _
  have hws : (neckLift w hp p.2).1 ∈ (chartAt (ℂ × ℝ) a).source :=
    (neckLift_chart_source a w hp p.2).mpr ⟨hw ▸ hpa,hpb⟩
  change chartAt (ℂ × ℝ) b (extendedTransition collar gluingMap
    ((chartAt (ℂ × ℝ) a).symm (coverChart a ((w : ℂ),p.2)))) = _
  rw [← neckLift_chart a w hp p.2,(chartAt (ℂ × ℝ) a).left_inv hws,
    extendedTransition_apply collar gluingMap]
  calc
    _ = chartAt (ℂ × ℝ) b (neckLift (flipUpper w p.2) (flipUpper_band w hp p.2)
      (w.re-p.2)).1 := congrArg (fun t : collar => chartAt (ℂ × ℝ) b t.1)
        (neckLift_gluing w hp p.2)
    _ = _ := neckLift_chart b (flipUpper w p.2) (flipUpper_band w hp p.2) (w.re-p.2)

lemma gluing_transition_positive (a b : Piece) (x : ℂ × ℝ)
    (hx : x ∈ (chartAt (ℂ × ℝ) a).target)
    (hO : (chartAt (ℂ × ℝ) a).symm x ∈ collar)
    (hb : extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm x) ∈
      (chartAt (ℂ × ℝ) b).source) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => chartAt (ℂ × ℝ) b
        (extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm y))) x).toLinearMap := by
  obtain ⟨z,hz,r,he⟩ := neckLift_surjective ⟨(chartAt (ℂ × ℝ) a).symm x,hO⟩
  have hey : (neckLift z hz r).1 = (chartAt (ℂ × ℝ) a).symm x := congrArg Subtype.val he
  have ha : (neckLift z hz r).1 ∈ (chartAt (ℂ × ℝ) a).source := hey ▸ (chartAt (ℂ × ℝ) a).map_target hx
  have hax : coverChart a ((z : ℂ),r) = x := by
    rw [← neckLift_chart a z hz r,hey,(chartAt (ℂ × ℝ) a).right_inv hx]
  have hb' : (neckLift (flipUpper z r) (flipUpper_band z hz r) (z.re-r)).1 ∈
      (chartAt (ℂ × ℝ) b).source := by
    rw [← neckLift_gluing]
    rw [← hey,extendedTransition_apply collar gluingMap] at hb
    exact hb
  obtain ⟨ha1,ha2⟩ := (neckLift_chart_source a z hz r).mp ha
  obtain ⟨hb1,hb2⟩ := (neckLift_chart_source b (flipUpper z r) (flipUpper_band z hz r) (z.re-r)).mp hb'
  let T := fun y => chartAt (ℂ × ℝ) b
    (extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm y))
  have hT : ContDiffAt ℝ ∞ T x := by
    have h1 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ))
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ)) (n := ∞) a) hx
    have he' : ContMDiff 𝓘(ℝ,ℂ × ℝ) 𝓘(ℝ,ℂ × ℝ) ∞ gluingMap := by
      simpa only [modelWithCornersSelf_prod] using gluingMap_smooth
    have h2 := extendedTransition_smooth collar gluingMap he' ⟨_,hO⟩
    have h3 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ))
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ)) (n := ∞) b) hb
    exact ((h3.comp x (h2.comp x h1)).contDiffAt)
  have hca := (coverChart_smooth a z r ha1 ha2).differentiableAt (by simp)
  have hcb := (coverChart_smooth b (flipUpper z r) (z.re-r) hb1 hb2).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ T (coverChart a ((z : ℂ),r)) := by
    rw [hax]
    exact hT.differentiableAt (by simp)
  have hl := ht.hasFDerivAt.comp ((z : ℂ),r) hca.hasFDerivAt
  have hf := liftedGluing_derivative (p := ((z : ℂ),r)) (ne_of_gt z.im_pos)
  have hr := hcb.hasFDerivAt.comp ((z : ℂ),r) hf
  have hid := hl.unique (hr.congr_of_eventuallyEq (cover_transition_germ a b z hz r ha))
  rw [hax] at hid
  have hd := congrArg (fun L : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) => LinearMap.det L.toLinearMap) hid
  change LinearMap.det ((fderiv ℝ T x).toLinearMap ∘ₗ (fderiv ℝ (coverChart a) ((z : ℂ),r)).toLinearMap) =
      LinearMap.det ((fderiv ℝ (coverChart b) ((flipUpper z r : ℂ),z.re-r)).toLinearMap ∘ₗ
        (shearD (-(16 / z.im ^ 2))).toLinearMap) at hd
  rw [LinearMap.det_comp,LinearMap.det_comp,det_shearD,neg_neg] at hd
  have hp : 0 < 16 / z.im ^ 2 := by positivity
  exact pos_of_mul_pos_left (show 0 < LinearMap.det (fderiv ℝ T x).toLinearMap *
    LinearMap.det (fderiv ℝ (coverChart a) ((z : ℂ),r)).toLinearMap by
      rw [hd]
      exact mul_pos (coverChart_positive b (flipUpper z r) (z.re-r) hb1 hb2) hp)
    (coverChart_positive a z r ha1 ha2).le
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
end ThreeManifold.Rechart

open Set Filter Topology TopologicalSpace Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
variable (O : Opens X) (e : O ≃ₜ O)
end ThreeManifold.TwoGluing
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.GluedConstruction
end ThreeManifold.GluedConstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.GluedConstruction
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
open Set Topology TopologicalSpace
open Set Topology Filter Manifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff UpperHalfPlane MatrixGroups
open Set Topology Filter TopologicalSpace Manifold IsManifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff
open Set Topology Filter Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
open Set Filter Topology
open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
open HyperbolicCore Coordinates3 TwoGluing


theorem solution : type_of% @_root_.OAI.ThreeManifold.GluedConstruction.gluing_transition_positive := @_root_.OAI.ThreeManifold.GluedConstruction.gluing_transition_positive
