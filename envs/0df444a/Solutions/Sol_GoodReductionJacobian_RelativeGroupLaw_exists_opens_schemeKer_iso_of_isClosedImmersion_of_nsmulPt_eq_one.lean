-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/979b4796-d1eb-593d-9e26-767982453c38

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

namespace LevelIsClopenAux

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem comp_schemeNsmul_eq (L : RelativeGroupLaw R f) (n : ℕ) {C : Scheme.{u}} (lev : C ⟶ A)
    (h : nsmulPt L (lev ≫ f) n ⟨lev, rfl⟩ = L.one (lev ≫ f)) :
    lev ≫ L.schemeNsmul n = (lev ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h1 : schemeHomOverComp lev rfl (L.nsmul f n RelativeGroupLaw.idPoint) =
      L.nsmul (lev ≫ f) n (schemeHomOverComp lev rfl RelativeGroupLaw.idPoint) :=
    L.nsmul_natural f (lev ≫ f) lev rfl n _
  have h2 : schemeHomOverComp lev (rfl : lev ≫ f = lev ≫ f)
      (RelativeGroupLaw.idPoint (f := f)) = ⟨lev, rfl⟩ :=
    Subtype.ext (Category.comp_id lev)
  have h3 := L.one_natural (𝟙 _) (lev ≫ f) (lev ≫ f) (Category.comp_id _)
  calc lev ≫ L.schemeNsmul n
      = (schemeHomOverComp lev rfl (L.nsmul f n RelativeGroupLaw.idPoint)).1 := rfl
    _ = (L.nsmul (lev ≫ f) n ⟨lev, rfl⟩).1 := by rw [h1, h2]
    _ = (L.one (lev ≫ f)).1 := by rw [← nsmulPt_eq_nsmul, h]
    _ = (lev ≫ f) ≫ (L.one (𝟙 _)).1 := by rw [← h3]; rfl

end LevelIsClopenAux

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) [Etale (L.schemeKerStr n)]
    {C : Scheme.{u}} (lev : C ⟶ A) [IsClosedImmersion lev]
    [Flat (lev ≫ f)] [LocallyOfFinitePresentation (lev ≫ f)]
    (htor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t n P = L.one t) :
    ∃ (U : (L.schemeKer n).Opens) (e : C ≅ (U : Scheme.{u})),
      IsClosed (U : Set ↥(L.schemeKer n)) ∧
      e.hom ≫ U.ι ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = lev ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
        FactorsThrough lev P ↔
          ∃ κ : T ⟶ L.schemeKer n,
            κ ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = P.1 ∧
            Set.range κ.base ⊆ (U : Set ↥(L.schemeKer n)) := by

  have he₀ : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  haveI : Mono (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := ⟨fun g h hgh => by
    simpa [Category.assoc, he₀] using congrArg (· ≫ f) hgh⟩

  have hlev : nsmulPt L (lev ≫ f) n ⟨lev, rfl⟩ = L.one (lev ≫ f) :=
    htor (lev ≫ f) ⟨lev, rfl⟩ ⟨𝟙 C, Category.id_comp _⟩
  have hcomm : lev ≫ L.schemeNsmul n = (lev ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
    LevelIsClopenAux.comp_schemeNsmul_eq L n lev hlev
  let j : C ⟶ L.schemeKer n := pullback.lift lev (lev ≫ f) hcomm
  have hj₁ : j ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = lev :=
    pullback.lift_fst _ _ _
  have hj₂ : j ≫ L.schemeKerStr n = lev ≫ f := pullback.lift_snd _ _ _

  haveI : IsClosedImmersion
      (j ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) := by
    rw [hj₁]; infer_instance
  haveI hjci : IsClosedImmersion j :=
    IsClosedImmersion.of_comp j (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1)

  haveI : Flat (j ≫ L.schemeKerStr n) := by rw [hj₂]; infer_instance
  haveI : LocallyOfFinitePresentation (j ≫ L.schemeKerStr n) := by rw [hj₂]; infer_instance
  haveI hjoi : IsOpenImmersion j :=
    (AlgebraicGeometry.IsOpenImmersion.of_isClosedImmersion_of_flat_comp_of_etale
      j (L.schemeKerStr n)).1
  refine ⟨j.opensRange, j.isoOpensRange, ?_, ?_, ?_⟩
  · exact j.isClosedEmbedding.isClosed_range
  · rw [Scheme.Hom.isoOpensRange_hom_ι_assoc, hj₁]
  · intro T t P
    constructor
    · rintro ⟨P₀, hP₀⟩
      refine ⟨P₀ ≫ j, by rw [Category.assoc, hj₁, hP₀], ?_⟩
      rintro _ ⟨x, rfl⟩
      exact ⟨P₀ x, rfl⟩
    · rintro ⟨κ, hκ, hU⟩
      refine ⟨IsOpenImmersion.lift j κ hU, ?_⟩
      rw [← hj₁, ← Category.assoc, IsOpenImmersion.lift_fac, hκ]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_iso_of_isClosedImmersion_of_nsmulPt_eq_one (solution)
