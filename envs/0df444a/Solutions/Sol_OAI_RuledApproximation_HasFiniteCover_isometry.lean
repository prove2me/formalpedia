-- Prove2me | solution 1 for OAI.RuledApproximation.HasFiniteCover.isometry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:57:43.124032+00:00
-- url     : https://prove2.me/submissions/f96d2aaf-43eb-4943-a034-1dc594fff9cf

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Isometries.lean:L103-L119
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.HasFiniteCover.isometry. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_Cylinder_translate_carrier
import Theorems.Thm_OAI_RuledApproximation_IsParallelogram_linear_image

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

/-- Exact Euclidean isometry transport preserves finite covers and perpendicular area. -/
lemma HasFiniteCover.isometry {S : Set Space} {A : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (F : Space ≃ᵢ Space) :
    HasFiniteCover Cylinder.parallelogram (F '' S) A := by
  obtain ⟨n, C, hC, hcov, hcost⟩ := hc
  let R := F.toRealLinearIsometryEquiv
  have hF (x : Space) : F x = F 0 + R x := by
    simp [R, IsometryEquiv.toRealLinearIsometryEquiv_apply]
  let D : Fin n → Cylinder := fun i => ((C i).rotate R).translate (F 0)
  refine ⟨n, D, fun i => Cylinder.translate_parallelogram (Cylinder.rotate_parallelogram (hC i) R) (F 0), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change F x ∈ (((C i).rotate R).translate (F 0)).carrier
    rw [Cylinder.translate_carrier, Cylinder.rotate_carrier]
    exact ⟨R x, ⟨x, hi, rfl⟩, (hF x).symm⟩
  · simpa [familyArea, D, Cylinder.translate_area, Cylinder.rotate_area] using hcost

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.HasFiniteCover.isometry := @_root_.OAI.RuledApproximation.HasFiniteCover.isometry
