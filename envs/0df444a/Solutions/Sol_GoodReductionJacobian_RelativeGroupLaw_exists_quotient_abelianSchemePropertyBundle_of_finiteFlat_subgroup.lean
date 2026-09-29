-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7f5a5910-102b-57eb-9cc1-d956f5f482d1

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option maxHeartbeats 3200000 in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (hAF : ∀ S : Finset J, ∃ U : J.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U)
    {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
    [IsFinite (ι ≫ f)] [Flat (ι ≫ f)] [LocallyOfFinitePresentation (ι ≫ f)]
    (hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      ∃ e : T ⟶ E, e ≫ ι = (L.one t).1)
    (hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
        ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1)
    (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1) :
    ∃ (P : Scheme.{u}) (g : P ⟶ Spec (CommRingCat.of R)) (LP : RelativeGroupLaw R g)
      (p : J ⟶ P) (hg : p ≫ g = f) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p),
      AbelianSchemePropertyBundle R g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        LP.mul t x y = LP.mul t y x) ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ : SchemeHomOver t g) = LP.one t ↔
          ∃ e : T ⟶ E, e ≫ ι = x.1) ∧
      IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p ∧
      Nonempty (IsColimit (Cofork.ofπ p w)) := by

  obtain ⟨h1, h2, h3, h4, h5, h6, hmono, hequiv, haff⟩ :=
    RelativeGroupLaw.finiteLocallyFree_equivalenceRelation_action L ι hE_one hE_mul hE_inv hAF
  haveI := h1; haveI := h2; haveI := h3; haveI := h4; haveI := h5; haveI := h6

  obtain ⟨P, p, w, hfin, hflat, hlfp, hsurj, hR, ⟨hcoeq⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.snd (ι ≫ f) f) (L.action ι) hmono hequiv haff
  haveI := hfin; haveI := hflat; haveI := hlfp; haveI := hsurj

  obtain ⟨g, hg, LP, hp, hPcomm, hker⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_quotient_of_isColimit L ι hE_one hE_mul hE_inv hcomm p w hR hcoeq

  have hB : AbelianSchemePropertyBundle R g :=
    RelativeGroupLaw.abelianSchemePropertyBundle_quotient L ι hE_one hE_mul hE_inv hJ p w hR g hg LP hp
  exact ⟨P, g, LP, p, hg, w, hB, hPcomm, hfin, hflat, hlfp, hsurj, hp, hker, hR, ⟨hcoeq⟩⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup (solution)
