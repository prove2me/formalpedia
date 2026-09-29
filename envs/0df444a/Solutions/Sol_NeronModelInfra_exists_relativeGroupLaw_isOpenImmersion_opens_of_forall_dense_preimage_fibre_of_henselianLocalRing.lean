-- Prove2me | solution 1 for NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/970cf199-e5cc-5e40-9463-d50b2e4dbf67

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_finite_etale_relativeGroupLaw_isOpenImmersion_of_forall_dense_preimage_fibre_of_henselianLocalRing
import Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.DescentAction.toTriple_fst_assoc AlgebraicGeometry.DescentAction.invol_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst AlgebraicGeometry.DescentAction.flipMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst_assoc AlgebraicGeometry.DescentAction.unitMap_snd AlgebraicGeometry.DescentAction.eRel_snd AlgebraicGeometry.DescentAction.toTriple_fst AlgebraicGeometry.DescentAction.invol_invol AlgebraicGeometry.DescentAction.proj₁₃_snd AlgebraicGeometry.DescentAction.eRel_snd_assoc AlgebraicGeometry.DescentAction.invol_invol_assoc AlgebraicGeometry.DescentAction.invol_act AlgebraicGeometry.DescentAction.actMap_fst_assoc AlgebraicGeometry.DescentAction.flipMap_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst AlgebraicGeometry.DescentAction.invol_act_assoc AlgebraicGeometry.DescentAction.invol_fst_assoc AlgebraicGeometry.DescentAction.proj₁₃_snd_assoc AlgebraicGeometry.DescentAction.mk.injEq AlgebraicGeometry.DescentAction.flipMap_fst AlgebraicGeometry.DescentAction.proj₁₃_fst AlgebraicGeometry.DescentAction.invol_fst AlgebraicGeometry.DescentAction.unitMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_fst AlgebraicGeometry.DescentAction.toTriple_snd_assoc AlgebraicGeometry.DescentAction.invol_snd AlgebraicGeometry.DescentAction.actMap_snd AlgebraicGeometry.DescentAction.flipMap_snd AlgebraicGeometry.DescentAction.proj₁₃_fst_assoc AlgebraicGeometry.DescentAction.mk.sizeOf_spec AlgebraicGeometry.DescentAction.toTriple_snd RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~DescentAction NeronModelInfra GoodReductionJacobian"

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
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
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
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        NeronModelInfra.schemeHomOverComp c jY =
          LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b jY)) := by

  obtain ⟨R', _, _, _, _, _, _, _, B', g', LB', jY', hg'₁, hg'₂, hg'₃, hg'₄, hjY', hjY'₁, hjY'₂, hres'⟩ :=
    NeronModelInfra.exists_finite_etale_relativeGroupLaw_isOpenImmersion_of_forall_dense_preimage_fibre_of_henselianLocalRing
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂ X' U hUW hX'₁ hX'₂ hU₁ hU₂ hU₃
  haveI := hg'₁; haveI := hg'₂; haveI := hg'₃; haveI := hg'₄; haveI := hjY'

  exact
    NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂ X' U hUW hX'₁ hX'₂ hU₁ hU₂ hU₃ R' g' LB' jY' hjY'₁ hjY'₂ hres'

end S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
end P2MW
export P2MW.S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing (solution)
