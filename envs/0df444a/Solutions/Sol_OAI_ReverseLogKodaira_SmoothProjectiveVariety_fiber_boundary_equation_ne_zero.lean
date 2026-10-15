-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:28:34.503796+00:00
-- url     : https://prove2.me/submissions/3f432ccc-71fb-45eb-a824-b76644157de6

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/BoundaryPullback.lean:L74-L120
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts

-- ---- from OAI.AlgebraicGeometry.LogKodaira.BoundaryPullback ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.IdealPullback

 
theorem ideal_comap_affine {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have hmap (J : X.IdealSheafData) :
      (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
        (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom := by
    exact J.ideal_map_of_isAffineHom f ⟨⊤, isAffineOpen_top Y⟩
  let eX := Scheme.IdealSheafData.equivOfIsAffine (X := X)
  let J := eX.symm ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom)
  have hJ : J.ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom :=
    eX.apply_symm_apply _
  apply le_antisymm
  · have hIJ : I ≤ J.map f := by
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [hmap, hJ]
      exact Ideal.le_comap_map
    have h := (Scheme.IdealSheafData.le_map_iff_comap_le.mp hIJ)
      ⟨⊤, isAffineOpen_top X⟩
    rw [hJ] at h
    exact h
  · rw [Ideal.map_le_iff_le_comap, ← hmap]
    exact (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩

end ReverseLogKodaira.IdealPullback

namespace ReverseLogKodaira.IdealPullback

lemma ideal_restriction_map {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens) :
    ((I.comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top U.1 U.2⟩).map U.1.topIso.hom.hom = I.ideal U := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact I.map_ideal (U := U)
    (V := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩)
    U.1.ι_image_top.ge

 

theorem ideal_comap_appLE {X Y : Scheme}
    (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U.1 V.1 e).hom := by
  let : IsAffine U.1 := U.2
  let : IsAffine V.1 := V.2
  have hc : (I.comap f).comap V.1.ι = (I.comap U.1.ι).comap (f.resLE U.1 V.1 e) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Scheme.Hom.resLE_comp_ι]
  rw [← ideal_restriction_map (I.comap f) V, hc, ideal_comap_affine]
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.hom_comp, Ideal.map_map, ← RingHom.comp_assoc]
  rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
    RingHom.id_comp, ← Ideal.map_map, ideal_restriction_map]

end ReverseLogKodaira.IdealPullback

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem fiber_boundary_equation_ne_zero
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (V : X.scheme.affineOpens) [Nonempty (F.inclusion ⁻¹ᵁ V.1)]
    (t : Γ(X.scheme, V.1)) (hEt : E.ideal.ideal V = Ideal.span {t}) :
    chartToFunctionField F.inclusion V.1 t ≠ 0 := by
  let P := F.inclusion ⁻¹ᵁ V.1
  have hgP : genericPoint F.variety.scheme ∈ P :=
    ((genericPoint_spec F.variety.scheme).mem_open_set_iff P.2).mpr
      (by simpa using (inferInstance : Nonempty P))
  obtain ⟨_, ⟨W, hW, rfl⟩, hgW, e⟩ :=
    F.variety.scheme.isBasis_affineOpens.exists_subset_of_mem_open hgP P.2
  let A : F.variety.scheme.affineOpens := ⟨W, hW⟩
  let : Nonempty W := ⟨⟨genericPoint F.variety.scheme, hgW⟩⟩
  let u := F.inclusion.appLE V.1 W e t
  have hI : F.boundary.ideal.ideal A = Ideal.span {u} := by
    rw [F.boundary_pullback, IdealPullback.ideal_comap_appLE E.ideal F.inclusion V A e,
      hEt, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  intro hn
  have hu : u = 0 := by
    apply F.variety.scheme.germToFunctionField_injective W
    rw [map_zero]
    change F.variety.scheme.presheaf.germ W (genericPoint F.variety.scheme) _
      (F.variety.scheme.presheaf.map (homOfLE e).op (F.inclusion.app V.1 t)) = 0
    exact (F.variety.scheme.presheaf.germ_res_apply
      (show W ⟶ F.inclusion ⁻¹ᵁ V.1 from homOfLE e)
      (genericPoint F.variety.scheme) _ (F.inclusion.app V.1 t)).trans hn
  have hgI : genericPoint F.variety.scheme ∈ F.boundary.ideal.support := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := A) hgW, hI, hu]
    simp [Scheme.mem_zeroLocus_iff]
  obtain ⟨B, hgB, v, hv, hB⟩ := F.boundary.union_cartier (genericPoint F.variety.scheme)
  have hbot : F.boundary.ideal = ⊥ := by
    apply Scheme.IdealSheafData.support_eq_top_iff.mp
    apply eq_top_iff.mpr
    intro z hz
    have hs := closure_minimal (Set.singleton_subset_iff.mpr hgI) F.boundary.ideal.support.isClosed
    rw [genericPoint_closure] at hs
    exact hs (Set.mem_univ z)
  change F.boundary.ideal.ideal B = Ideal.span {v} at hB
  rw [hbot] at hB
  change (⊥ : Ideal Γ(F.variety.scheme, B.1)) = Ideal.span {v} at hB
  have hz : v ∈ (⊥ : Ideal Γ(F.variety.scheme, B.1)) := by
    rw [hB]
    exact Ideal.subset_span (Set.mem_singleton v)
  exact hv hz

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (V : X.scheme.affineOpens) [Nonempty (F.inclusion ⁻¹ᵁ V.1)]
    (t : Γ(X.scheme, V.1)) (hEt : E.ideal.ideal V = Ideal.span {t}) :
    chartToFunctionField F.inclusion V.1 t ≠ 0 := by
  first
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero f y F V t hEt
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero
    | (apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.fiber_boundary_equation_ne_zero <;> assumption)
