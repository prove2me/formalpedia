-- Prove2me | solution 1 for OAI.Paper092.simplexZonotope_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:57:14.011231+00:00
-- url     : https://prove2.me/submissions/a3ace680-a68c-4bd2-8e44-5033dca86a8b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexZonotope.lean:L38-L60
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.simplexZonotope_support. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian
import Definitions.Def_OAI_Geometry_ProjectionVolume_SupportGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_Extrusion
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexZonotope

-- ---- from OAI.Geometry.ProjectionVolume.SupportGeometry ----
namespace OAI

universe uE uF uι uH

open Set
open scoped Pointwise

namespace Paper092.SupportGeometry

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem support_add {A B : Set E} (hA : IsCompact A) (hneA : A.Nonempty)
    (hB : IsCompact B) (hneB : B.Nonempty) (f : E →L[ℝ] ℝ) :
    support (A + B) f = support A f + support B f := by
  unfold support
  rw [image_add]
  exact csSup_add (hneA.image f) (hA.image f.continuous).bddAbove
    (hneB.image f) (hB.image f.continuous).bddAbove

theorem support_sum {ι : Type uι} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hne : ∀ i ∈ s, (K i).Nonempty)
    (f : E →L[ℝ] ℝ) : support (∑ i ∈ s, K i) f = ∑ i ∈ s, support (K i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [support]
  | @insert i s hi ih =>
    have hKs : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hnes : ∀ j ∈ s, (K j).Nonempty := fun j hj => hne j (Finset.mem_insert_of_mem hj)
    have hcompact : IsCompact (∑ j ∈ s, K j) :=
      Finset.sum_induction K IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton hKs
    have hnonempty : (∑ j ∈ s, K j).Nonempty :=
      Finset.sum_induction K Set.Nonempty (fun _ _ ha hb => ha.add hb)
        (singleton_nonempty 0) hnes
    rw [Finset.sum_insert hi,
      support_add (hK i (Finset.mem_insert_self i s)) (hne i (Finset.mem_insert_self i s))
        hcompact hnonempty, ih hKs hnes, Finset.sum_insert hi]

theorem isCompact_segment (x y : E) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

theorem support_segment (x y : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ x y) f = max (f x) (f y) := by
  unfold support
  rw [show f '' segment ℝ x y = segment ℝ (f x) (f y) from
    image_segment ℝ f.toLinearMap.toAffineMap x y]
  rw [segment_eq_Icc', csSup_Icc (min_le_max)]

theorem support_centered_segment (v : E) (f : E →L[ℝ] ℝ) :
    support (segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)) f = |f v| / 2 := by
  simp only [support_segment, map_smul, smul_eq_mul, neg_mul]
  rw [max_comm, ← abs_eq_max_neg, abs_mul]
  norm_num
  ring

theorem support_sum_centered_segments {ι : Type uι} (s : Finset ι) (v : ι → E)
    (f : E →L[ℝ] ℝ) :
    support (∑ i ∈ s, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i)) f =
      (1 / 2 : ℝ) * ∑ i ∈ s, |f (v i)| := by
  rw [support_sum s _ (fun _ _ => isCompact_segment _ _)
    (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)]
  simp_rw [support_centered_segment, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

section InnerProduct

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end InnerProduct

end Paper092.SupportGeometry

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.SimplexZonotope ----
namespace OAI

universe uE uι

open Set MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace Paper092

theorem simplexZonotope_support (d : ℕ) (u : Euclidean d) :
    SupportGeometry.support (simplexZonotope d) (innerSL ℝ u) =
      ((∑ i : Fin d, |u i|) + |∑ i : Fin d, u i|) / (2 * ((d - 1).factorial : ℝ)) := by
  have hfac : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  have hcompact : IsCompact (∑ i : Fin d, segment ℝ
      (-(1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))
      ((1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))) :=
    Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
      isCompact_singleton (fun _ _ => SupportGeometry.isCompact_segment _ _)
  have hne : (∑ i : Fin d, segment ℝ
      (-(1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))
      ((1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))).Nonempty :=
    Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
      (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)
  rw [simplexZonotope, SupportGeometry.support_add hcompact hne
    (SupportGeometry.isCompact_segment _ _) ⟨_, left_mem_segment ℝ _ _⟩,
    SupportGeometry.support_sum_centered_segments, SupportGeometry.support_centered_segment]
  simp only [innerSL_apply_apply, inner_smul_right, EuclideanSpace.inner_single_right,
    one_mul, starRingEnd_apply, star_trivial, abs_mul, abs_inv, abs_of_pos hfac]
  have hw : inner ℝ u (WithLp.toLp 2 (1 : Fin d → ℝ)) = ∑ i : Fin d, u i := by
    simp [PiLp.inner_apply]
  rw [hw, ← Finset.mul_sum]
  field_simp

end Paper092

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
universe uE uι
open Set MeasureTheory
open scoped Pointwise RealInnerProductSpace

theorem solution (d : ℕ) (u : Euclidean d) :
    SupportGeometry.support (simplexZonotope d) (innerSL ℝ u) =
      ((∑ i : Fin d, |u i|) + |∑ i : Fin d, u i|) / (2 * ((d - 1).factorial : ℝ)) := by
  first
    | exact OAI.Paper092.simplexZonotope_support d u
    | exact OAI.Paper092.simplexZonotope_support
    | (apply OAI.Paper092.simplexZonotope_support <;> assumption)
    | (intros; apply OAI.Paper092.simplexZonotope_support <;> assumption)
