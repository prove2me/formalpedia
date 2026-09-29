-- Prove2me | solution 1 for NeronModelInfra.exists_opens_relativeGroupLaw_isOpenImmersion_genericFibre_iso_of_isOpenImmersion_lift_mul_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/55dd3185-f43f-51f3-a4c4-2ca18b5c5492

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul
import Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_relativeGroupLaw_isOpenImmersion_genericFibre_iso_of_isOpenImmersion_lift_mul_of_henselianLocalRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.DescentAction.toTriple_fst_assoc AlgebraicGeometry.DescentAction.invol_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst AlgebraicGeometry.DescentAction.flipMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst_assoc AlgebraicGeometry.DescentAction.unitMap_snd AlgebraicGeometry.DescentAction.eRel_snd AlgebraicGeometry.DescentAction.toTriple_fst AlgebraicGeometry.DescentAction.invol_invol AlgebraicGeometry.DescentAction.proj₁₃_snd AlgebraicGeometry.DescentAction.eRel_snd_assoc AlgebraicGeometry.DescentAction.invol_invol_assoc AlgebraicGeometry.DescentAction.invol_act AlgebraicGeometry.DescentAction.actMap_fst_assoc AlgebraicGeometry.DescentAction.flipMap_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst AlgebraicGeometry.DescentAction.invol_act_assoc AlgebraicGeometry.DescentAction.invol_fst_assoc AlgebraicGeometry.DescentAction.proj₁₃_snd_assoc AlgebraicGeometry.DescentAction.mk.injEq AlgebraicGeometry.DescentAction.flipMap_fst AlgebraicGeometry.DescentAction.proj₁₃_fst AlgebraicGeometry.DescentAction.invol_fst AlgebraicGeometry.DescentAction.unitMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_fst AlgebraicGeometry.DescentAction.toTriple_snd_assoc AlgebraicGeometry.DescentAction.invol_snd AlgebraicGeometry.DescentAction.actMap_snd AlgebraicGeometry.DescentAction.flipMap_snd AlgebraicGeometry.DescentAction.proj₁₃_fst_assoc AlgebraicGeometry.DescentAction.mk.sizeOf_spec AlgebraicGeometry.DescentAction.toTriple_snd RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :
    ∃ (X' : X.Opens) (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X') ∧
      (∀ x : X, f.base x = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X') ∧
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsOpenImmersion jY.1 ∧
      (∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base) ∧
      (∀ b : B, g.base b = IsLocalRing.closedPoint R →
        (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base) ∧
      IsIso e'.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y e')) ∧
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) e' =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e := by

  obtain ⟨X', U, hUW, hX'₁, hX'₂, hU₁, hU₂, hU₃⟩ :=
    NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul
      K LXK f e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂

  obtain ⟨B, g, LB, jY, e', hg₁, hg₂, hg₃, hg₄, hjY, hjY₁, hjY₂, he', hhom, hcompat, -⟩ :=
    NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂ X' U hUW hX'₁ hX'₂ hU₁ hU₂ hU₃
  exact ⟨X', B, g, LB, jY, e', hX'₁, hX'₂, hg₁, hg₂, hg₃, hg₄, hjY, hjY₁, hjY₂, he', hhom, hcompat⟩

end S_NeronModelInfra_exists_opens_relativeGroupLaw_isOpenImmersion_genericFibre_iso_of_isOpenImmersion_lift_mul_of_henselianLocalRing
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_relativeGroupLaw_isOpenImmersion_genericFibre_iso_of_isOpenImmersion_lift_mul_of_henselianLocalRing (solution)
