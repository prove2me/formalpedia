-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/19ccda27-16e4-5d79-9a6a-69246a6b2b37

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_exists_iso_spec_of_forall_equiv_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace K5Furniture

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

private theorem schemeHomOverComp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
  Subtype.ext (Category.comp_id x.1)

private theorem nsmul_coe_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (G.nsmul f n RelativeGroupLaw.idPoint)
      = G.nsmul t n (GoodReductionJacobian.schemeHomOverComp x.1 x.2 RelativeGroupLaw.idPoint) :=
    G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [schemeHomOverComp_idPoint] at h
  exact (congrArg Subtype.val h).symm

private theorem one_coe_eq_comp_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h : GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) (G.one (𝟙 _)) = G.one t :=
    G.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

private theorem schemeKer_fst_comp_f (G : RelativeGroupLaw R f) (n : ℕ) :
    (pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ f
        : G.schemeKer n ⟶ Spec (CommRingCat.of R))
      = pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 := by
  have h := congrArg (· ≫ f)
    (pullback.condition (f := G.schemeNsmul n) (g := (G.one (𝟙 _)).1))
  simp only [Category.assoc, G.schemeNsmul_over n, (G.one (𝟙 _)).2, Category.comp_id] at h
  exact h

private def torsionSubsetEquivKerPoints (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.torsionSubset t n ≃
      SchemeHomOver t (pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1) where
  toFun x :=
    ⟨pullback.lift x.1.1 t
        (by
          have hx : (G.nsmul t n x.1).1 = (G.one t).1 := congrArg Subtype.val x.2
          rw [nsmul_coe_eq_comp_schemeNsmul, one_coe_eq_comp_one] at hx
          exact hx),
      pullback.lift_snd _ _ _⟩
  invFun ψ :=
    ⟨⟨ψ.1 ≫ pullback.fst _ _, by rw [Category.assoc, schemeKer_fst_comp_f, ψ.2]⟩,
      show G.nsmul t n _ = G.one t from Subtype.ext (by
        have hcond := congrArg (ψ.1 ≫ ·)
          (pullback.condition (f := G.schemeNsmul n) (g := (G.one (𝟙 _)).1))
        simp only [← Category.assoc, ψ.2] at hcond
        rw [nsmul_coe_eq_comp_schemeNsmul]
        exact hcond.trans (one_coe_eq_comp_one G t).symm)⟩
  left_inv x := Subtype.ext (Subtype.ext (pullback.lift_fst _ _ _))
  right_inv ψ := Subtype.ext
    (pullback.hom_ext (by rw [pullback.lift_fst]) (by rw [pullback.lift_snd, ψ.2]))

private theorem torsionSubsetEquivKerPoints_apply_fst (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : G.torsionSubset t n) :
    (torsionSubsetEquivKerPoints G t n x).1 ≫ pullback.fst _ _ = x.1.1 :=
  pullback.lift_fst _ _ _

private theorem torsionSubsetEquivKerPoints_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (x : G.torsionSubset t n) (x' : G.torsionSubset t' n)
    (h : x'.1.1 = ψ ≫ x.1.1) :
    (torsionSubsetEquivKerPoints G t' n x').1 = ψ ≫ (torsionSubsetEquivKerPoints G t n x).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, torsionSubsetEquivKerPoints_apply_fst, torsionSubsetEquivKerPoints_apply_fst]
    exact h
  · rw [Category.assoc, (torsionSubsetEquivKerPoints G t n x).2, (torsionSubsetEquivKerPoints G t' n x').2]
    exact hψ.symm

private theorem specMap_algHom_comp_algebraMap {T T' : Type u} [CommRing T] [CommRing T'] [Algebra R T]
    [Algebra R T'] (a : T →ₐ[R] T') :
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]

end K5Furniture

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) [IsAffineHom (L.schemeKerStr n)]
    (H : Type u) [CommRing H] [Algebra R H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
      ((e T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e T φ).val.1) :
    ∃ i : Spec (CommRingCat.of H) ≅ L.schemeKer n,
      i.hom ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R H)) ∧
      ∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
        ((e T φ).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ i.hom ≫
            pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  haveI : IsAffine (L.schemeKer n) := isAffine_of_isAffineHom (L.schemeKerStr n)
  let E : ∀ (T : Type u) [CommRing T] [Algebra R T],
      (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) (L.schemeKerStr n) :=
    fun T _ _ => ((WithConv.equiv (H →ₐ[R] T)).symm.trans (e T)).trans
      (K5Furniture.torsionSubsetEquivKerPoints L _ n)
  have hE : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (φ : H →ₐ[R] T),
      (E T' (a.comp φ)).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (E T φ).1 :=
    fun T T' _ _ _ _ a φ =>
      K5Furniture.torsionSubsetEquivKerPoints_natural L _ _ _ (K5Furniture.specMap_algHom_comp_algebraMap a) n
        (e T (.toConv φ)) (e T' (.toConv (a.comp φ))) (he_nat T T' a (.toConv φ))
  obtain ⟨i, hi, hiE⟩ := AlgebraicGeometry.SchemeHomOver.exists_iso_spec_of_forall_equiv_algHom (L.schemeKerStr n) H E hE
  refine ⟨i, hi, ?_⟩
  intro T _ _ φ
  rw [← Category.assoc, ← hiE T φ.ofConv]
  exact (K5Furniture.torsionSubsetEquivKerPoints_apply_fst L _ n (e T φ)).symm

end

#print axioms solution
#check @solution

end S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset (solution)
