-- Prove2me | solution 1 for OAI.RuledApproximation.nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:19:43.68496+00:00
-- url     : https://prove2.me/submissions/6b1d3241-09be-4a9b-b2eb-a3e06272f04b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Nilpotent.lean:L55-L98
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.nilpotent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Theorems.Thm_OAI_RuledApproximation_Cylinder_translate_carrier
import Theorems.Thm_OAI_RuledApproximation_IsParallelogram_linear_image
import Theorems.Thm_OAI_RuledApproximation_IsSquareTile_parallelogram
import Theorems.Thm_OAI_RuledApproximation_globalize_local_covers
import Theorems.Thm_OAI_RuledApproximation_nilpotent_local_patch
import Theorems.Thm_OAI_RuledApproximation_projectedCylinder_carrier

-- ---- from OAI.Geometry.RuledCovering.Projection ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma physicalDirection_norm_sq (h : ℝ) (g : Plane) :
    ‖physicalDirection h g‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 := by
  rw [physicalDirection, norm_vec3_sq]
  ring

lemma inner_rawProjection (h : ℝ) (g p q : Plane) :
    inner ℝ (rawProjection h g p) (rawProjection h g q) =
      inner ℝ (planeEmbedding h p) (planeEmbedding h q) -
      inner ℝ (physicalDirection h g) (planeEmbedding h p) *
        inner ℝ (physicalDirection h g) (planeEmbedding h q) /
          ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  simp only [rawProjection, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (planeEmbedding h p) (physicalDirection h g)]
  field_simp [(physicalDirection_norm_pos h g).ne']
  ring

lemma rawProjection_normDet_sq (h : ℝ) (g : Plane) :
    (rawProjection h g).normDet ^ 2 = h ^ 2 / ‖physicalDirection h g‖ ^ 2 := by
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  have hd := (rawProjection h g).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hd
  rw [hd, Matrix.det_fin_two]
  simp only [Matrix.gram_apply, inner_rawProjection, EuclideanSpace.basisFun_apply,
    planeEmbedding_apply, physicalDirection, inner_vec3,
    PiLp.single_apply, Fin.isValue, ↓reduceIte, mul_zero, mul_one,
    one_mul, zero_add]
  simp only [Fin.reduceEq, ↓reduceIte]
  rw [show ‖vec3 1 (g 0) (h * g 1)‖ ^ 2 = 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 by
    rw [norm_vec3_sq]; ring]
  have hden : 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

lemma rawProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (rawProjection h g).normDet = h / ‖physicalDirection h g‖ := by
  have hn := physicalDirection_norm_pos h g
  have hs : ((rawProjection h g).normDet * ‖physicalDirection h g‖) ^ 2 = h ^ 2 := by
    rw [mul_pow, rawProjection_normDet_sq, div_mul_cancel₀ _ (pow_ne_zero 2 hn.ne')]
  have hnon := mul_nonneg (rawProjection h g).normDet_nonneg hn.le
  apply (eq_div_iff hn.ne').mpr
  nlinarith

lemma physicalWeight_eq_inv_norm (h : ℝ) (g : Plane) :
    physicalWeight h g = 1 / ‖physicalDirection h g‖ := by
  rw [physicalWeight, ← physicalDirection_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]

lemma perpendicularProjection_normDet {h : ℝ} (hh : 0 < h) (g : Plane) :
    (perpendicularProjection h g).normDet = h * physicalWeight h g := by
  rw [perpendicularProjection, LinearMap.normDet_codRestrict, rawProjection_normDet hh,
    physicalWeight_eq_inv_norm]
  ring

lemma perpendicularPlane_finrank (u : Space) (hu : ‖u‖ = 1) :
    Module.finrank ℝ ((Submodule.span ℝ ({u} : Set Space))ᗮ) = 2 := by
  have hne : u ≠ 0 := by intro hz; simp [hz] at hu
  have hd := (Submodule.span ℝ ({u} : Set Space)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne, finrank_euclideanSpace_fin] at hd
  omega

lemma perpendicularProjection_volume {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    volume.real (perpendicularProjection h g '' P) =
      h * physicalWeight h g * volume.real P := by
  have hf := (perpendicularProjection h g).euclideanHausdorffMeasure_image_eq_normDet_mul_volume P
  have hm : (MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ Plane) : Measure ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ)) = volume := by
    convert InnerProductSpace.euclideanHausdorffMeasure_eq_volume using 1
    simp only [finrank_euclideanSpace_fin, perpendicularPlane_finrank _ (physicalUnit_norm h g)]
  rw [hm] at hf
  rw [measureReal_def, hf, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (perpendicularProjection h g).normDet_nonneg,
    perpendicularProjection_normDet hh]
  rfl

lemma perpendicularProjection_injective {h : ℝ} (hh : 0 < h) (g : Plane) :
    Function.Injective (perpendicularProjection h g) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hn
  have hz := LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hn
  rw [perpendicularProjection_normDet hh, physicalWeight_eq_inv_norm] at hz
  have hp : 0 < h * (1 / ‖physicalDirection h g‖) :=
    mul_pos hh (one_div_pos.mpr (physicalDirection_norm_pos h g))
  exact hp.ne' hz

lemma projectedCylinder_area {h : ℝ} (hh : 0 < h) (g : Plane) (P : Set Plane) :
    (projectedCylinder h g P).area = h * volume.real P * physicalWeight h g := by
  rw [Cylinder.area, projectedCylinder, perpendicularProjection_volume hh]
  ring

lemma projectedCylinder_parallelogram {h : ℝ} (hh : 0 < h) (g : Plane)
    {P : Set Plane} (hP : IsParallelogram P) :
    (projectedCylinder h g P).parallelogram :=
  hP.linear_image _ (perpendicularProjection_injective hh g)

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.HyperbolicCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma HasFiniteCover.mono {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (h : HasFiniteCover shape T A) (hST : S ⊆ T) (hAB : A ≤ B) :
    HasFiniteCover shape S B := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := h
  exact ⟨n, C, hC, hST.trans hcov, hcost.trans hAB⟩

lemma physicalWeight_continuous (h : ℝ) : Continuous (physicalWeight h) := by
  apply continuous_const.div
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro g
    exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + g 0 ^ 2 + h ^ 2 * g 1 ^ 2)).ne'

lemma exists_inflation_budget (C : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 < B ∧ B * C < C + eps := by
  have hc : Continuous (fun d : ℝ => (1+d)*C) := by fun_prop
  have he : ∀ᶠ d : ℝ in 𝓝 0, (1+d)*C < C + eps :=
    hc.continuousAt.eventually (Iio_mem_nhds (by simpa using lt_add_of_pos_right C heps))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1+r/2, by linarith, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.Isometries ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.translate {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} (hP : IsParallelogram P) (a : E) :
    IsParallelogram ((fun x => a + x) '' P) := by
  obtain ⟨c, u, v, hli, rfl⟩ := hP
  refine ⟨a+c, u, v, hli, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
    exact ⟨s, hs, t, ht, by abel_nf⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨c+s•u+t•v, ⟨s, hs, t, ht, rfl⟩, by abel_nf⟩

lemma Cylinder.rotate_carrier (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).carrier = R '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    exact ⟨(b : Space) + t • C.axis, ⟨b, hb, t, rfl⟩, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    exact ⟨rotatedPlane C.axis R b, ⟨b, hb, rfl⟩, t, by change R ((b : Space) + t • C.axis) = R b + t • R C.axis; simp⟩

lemma Cylinder.rotate_area (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) :
    (C.rotate R).area = C.area := by
  change volume.real (rotatedPlane C.axis R '' C.base) = volume.real C.base
  have he := (rotatedPlane C.axis R).measurePreserving.setIntegral_image_emb
    (rotatedPlane C.axis R).toHomeomorph.measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.rotate_parallelogram {C : Cylinder} (hC : C.parallelogram)
    (R : Space ≃ₗᵢ[ℝ] Space) : (C.rotate R).parallelogram :=
  hC.linear_image (rotatedPlane C.axis R).toLinearMap (rotatedPlane C.axis R).injective

lemma Cylinder.translate_area (C : Cylinder) (q : Space) :
    (C.translate q).area = C.area := by
  change volume.real ((fun b => C.transversePart q + b) '' C.base) = volume.real C.base
  have he := (measurePreserving_add_left volume (C.transversePart q)).setIntegral_image_emb
    (Homeomorph.addLeft (C.transversePart q)).measurableEmbedding (fun _ => (1 : ℝ)) C.base
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using he

lemma Cylinder.translate_parallelogram {C : Cylinder} (hC : C.parallelogram) (q : Space) :
    (C.translate q).parallelogram := hC.translate (C.transversePart q)

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SquareCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Finite square-tile approximation, with unrestricted local shear and arbitrary
compact labels. -/
theorem nilpotent_physical_cover {h : ℝ} {D : Set Plane} {v : Plane → Plane}
    (hh : 0 < h) (hD : IsCompact D) (hv : SmoothNear 1 D v)
    (hnil : ∀ p ∈ D, (fderiv ℝ v p).comp (fderiv ℝ v p) = 0)
    {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h D v 1)
      (h * (∫ p in D, physicalWeight h (v p)) + eps) := by
  obtain ⟨U, hU, hDU, hv⟩ := hv
  have hF : IntegrableOn (fun p => physicalWeight h (v p)) D :=
    ((physicalWeight_continuous h).comp_continuousOn (hv.continuousOn.mono hDU)).integrableOn_compact hD
  obtain ⟨B, hB, hbudget⟩ := exists_inflation_budget
    (h * ∫ p in D, physicalWeight h (v p)) (half_pos heps)
  have hc := globalize_local_covers h 1 v (fun p => physicalWeight h (v p)) (h*B) hD hF
    (fun p hp => nilpotent_local_patch hh hB hU hv (hDU hp) (hnil p hp)) (half_pos heps)
  apply hc.mono Subset.rfl
  nlinarith

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.Nilpotent ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma physicalMaps_relation (h a : ℝ) (z : Space) :
    secondPhysicalMap h a z = vec3 0 0 (h*a) + swapReflect (firstPhysicalMap h z) := by
  ext i
  fin_cases i <;> simp [secondPhysicalMap,firstPhysicalMap,swapReflect,vec3]; ring

lemma firstPhysicalMap_injective {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (firstPhysicalMap h) := by
  intro x y he
  have he0 := congrArg (fun z : Space => z 0) he
  have he1 := congrArg (fun z : Space => z 1) he
  have he2 := congrArg (fun z : Space => z 2) he
  ext i
  fin_cases i
  · exact he0
  · exact he1
  · exact (mul_left_cancel₀ hh he2)

lemma firstPhysicalMap_ruled (h : ℝ) (D : Set Plane) (G : Plane → Plane) :
    firstPhysicalMap h '' physicalRuled 1 D G 1 = physicalRuled h D G 1 := by
  ext z
  constructor
  · rintro ⟨_,⟨p,hp,s,hs,rfl⟩,rfl⟩
    exact ⟨p,hp,s,hs,by simp [firstPhysicalMap]⟩
  · rintro ⟨p,hp,s,hs,rfl⟩
    exact ⟨vec3 s (p 0+s*G p 0) (p 1+s*G p 1),
      ⟨p,hp,s,hs,by simp⟩,rfl⟩

/-- Nilpotent approximation, with finite oriented square tiles and both exact
Euclidean physical realizations. Smoothness is more than the C1 producer needs. -/
theorem nilpotent : NilpotentStatement := by
  intro D G hD hG hnil h eps hh heps
  obtain ⟨U,hU,hDU,hG⟩ := hG
  have hG1 : SmoothNear 1 D G := ⟨U,hU,hDU,hG.of_le (by norm_num)⟩
  obtain ⟨n,C,hC,hcov,hcost⟩ := nilpotent_physical_cover hh hD hG1 hnil (mul_pos hh heps)
  choose T g hT hCT using hC
  refine ⟨n,T,g,hT,?_,?_,?_⟩
  · intro z hz
    have hz' : firstPhysicalMap h z ∈ physicalRuled h D G 1 := by
      rw [← firstPhysicalMap_ruled]
      exact mem_image_of_mem _ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hz')
    rw [hCT i,projectedCylinder_carrier] at hi
    obtain ⟨x,hx,hx'⟩ := hi
    have he : x = z := firstPhysicalMap_injective hh.ne' hx'
    exact mem_iUnion.mpr ⟨i, he ▸ hx⟩
  · simp_rw [familyArea,hCT,projectedCylinder_area hh] at hcost
    have he : (∑ i, h * volume.real (T i) * physicalWeight h (g i)) =
        h * ∑ i, volume.real (T i) * physicalWeight h (g i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hcost
    nlinarith
  · intro a
    let C₁ : Fin n → Cylinder := fun i => projectedCylinder h (g i) (T i)
    let C₂ : Fin n → Cylinder := fun i =>
      ((C₁ i).rotate swapReflect).translate (vec3 0 0 (h*a))
    refine ⟨C₁,C₂,fun i => ?_⟩
    have hP : (C₁ i).parallelogram := projectedCylinder_parallelogram hh _ (hT i).parallelogram
    refine ⟨hP,Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram hP swapReflect) _,
      projectedCylinder_carrier h _ _,?_,projectedCylinder_area hh _ _,?_⟩
    · dsimp only [C₂]
      rw [Cylinder.translate_carrier,Cylinder.rotate_carrier,projectedCylinder_carrier,
        ← image_comp,← image_comp]
      congr 1
      funext z
      exact (physicalMaps_relation h a z).symm
    · dsimp only [C₂]
      rw [Cylinder.translate_area,Cylinder.rotate_area]
      exact projectedCylinder_area hh _ _

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.nilpotent := @_root_.OAI.RuledApproximation.nilpotent
