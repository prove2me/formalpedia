-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5349d99c-be24-5734-a4b5-32e17e565dc7

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_flat_of_grpObj_over_spec
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

universe u

set_option maxHeartbeats 6400000 in
theorem solution
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃
            L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n,
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) =
            L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by
  obtain ⟨gK, gKcomm, pts, hmul, hnat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_schemeKer_eq L hcomm n
  letI := gK; letI := gKcomm
  haveI := hfin; haveI := hflat
  haveI : IsFinite (Over.mk (L.schemeKerStr n)).hom := by
    show IsFinite (L.schemeKerStr n); infer_instance
  haveI : Flat (Over.mk (L.schemeKerStr n)).hom := by
    show Flat (L.schemeKerStr n); infer_instance
  obtain ⟨H, iCR, iHA, hFinH, hFlatH, hCocomm, e', he'mul, he'nat⟩ :=
    AlgebraicGeometry.exists_hopfAlgebra_flat_of_grpObj_over_spec R (Over.mk (L.schemeKerStr n))
  refine ⟨H, iCR, iHA, hFinH, hFlatH, hCocomm,
    fun T _ _ => (e' T).trans (pts (Spec.map (CommRingCat.ofHom (algebraMap R T)))), ?_, ?_⟩
  · intro T _ _ φ ψ
    show ((pts _) ((e' T) (φ * ψ))).val = L.mul _ ((pts _) ((e' T) φ)).val ((pts _) ((e' T) ψ)).val
    rw [he'mul T φ ψ]
    exact hmul _ (e' T φ) (e' T ψ)
  · intro T T' _ _ _ _ g φ
    show ((pts _) ((e' T') (.toConv (g.comp φ.ofConv)))).val.1 =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ ((pts _) ((e' T) φ)).val.1
    have hψ : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) =
        Spec.map (CommRingCat.ofHom (algebraMap R T')) := by
      rw [← Spec.map_comp]; congr 1; ext r; exact g.commutes r
    have hLeft := he'nat T T' g φ
    have hOverEq : (e' T') (.toConv (g.comp φ.ofConv)) =
        (Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) hψ :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T'))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T)))) ≫ (e' T) φ := by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left]
      exact hLeft
    rw [hOverEq]
    have := hnat (Spec.map (CommRingCat.ofHom (algebraMap R T)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T')))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) hψ ((e' T) φ)
    rw [this]
    rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul (solution)
