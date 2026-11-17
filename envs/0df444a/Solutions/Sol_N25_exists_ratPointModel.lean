-- Prove2me | solution 1 for N25.exists_ratPointModel
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:09.361087+00:00
-- url     : https://prove2.me/submissions/94298747-9306-49dc-900a-c03109f62c9d

import Mathlib
import Definitions.Def_N25_RatPointModel
import Theorems.Thm_ModularCurve_exists_abelianSchemePropertyBundle_model_jH
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace N25

/-- Changing the proof of a point's structure morphism preserves multiplication. -/
private theorem mul_transport {R : Type} [CommRing R] {A T : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x y : SchemeHomOver t f) :
    (L.mul t x y).1 =
      (L.mul t' ⟨x.1, x.2.trans h⟩ ⟨y.1, y.2.trans h⟩).1 := by
  subst t'
  rfl

/-- The generic fibre of the model at 71 realizes all geometric points and their Galois action. -/
theorem _root_.solution : Nonempty RatPointModel := by
  letI : Fact (Nat.Prime 71) := ⟨by decide⟩
  obtain ⟨B, f, L, pts, hB, hc, hadd, hgal, _⟩ :=
    ModularCurve.exists_abelianSchemePropertyBundle_model_jH 25 H25 71 (by decide)
  let s := specGenericFibreInclusion ↥(GaloisRep.ratLocalizedAt 71) ℚ
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
  let k := Spec.map (CommRingCat.ofHom
    (algebraMap ↥(GaloisRep.ratLocalizedAt 71) (AlgebraicClosure ℚ)))
  have hbs : b ≫ s = k := by
    dsimp [b, s, k, specGenericFibreInclusion]
    rw [← Spec.map_comp]
    congr 1
  let G := L.genericFibre ℚ
  have hcomm : G.IsCommutative := RelativeGroupLaw.IsCommutative.baseChange s hc
  let E : SchemeHomOver k f ≃ SchemeHomOver b (RelativeGroupLaw.genericFibreStr ℚ f) :=
    { toFun := fun x => RelativeGroupLaw.baseChangePointOfBase s ⟨x.1, x.2.trans hbs.symm⟩
      invFun := fun x => ⟨(RelativeGroupLaw.baseChangePointToBase s x).1,
        (RelativeGroupLaw.baseChangePointToBase s x).2.trans hbs⟩
      left_inv := fun x => Subtype.ext (pullback.lift_fst _ _ _)
      right_inv := fun x => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · exact (pullback.lift_snd _ _ _).trans x.2.symm }
  have hEbase (z : SchemeHomOver k f) :
      RelativeGroupLaw.baseChangePointToBase s (E z) = ⟨z.1, z.2.trans hbs.symm⟩ :=
    RelativeGroupLaw.baseChangePointToBase_ofBase s _
  have hEfst (z : SchemeHomOver k f) : (E z).1 ≫ pullback.fst f s = z.1 :=
    congrArg Subtype.val (hEbase z)
  have hEsnd (z : SchemeHomOver k f) : (E z).1 ≫ pullback.snd f s = b := (E z).2
  have hEmul (z w : SchemeHomOver k f) : E (L.mul k z w) = G.mul b (E z) (E w) := by
    apply (RelativeGroupLaw.baseChangePointEquiv s b).injective
    change RelativeGroupLaw.baseChangePointToBase s (E (L.mul k z w)) =
      RelativeGroupLaw.baseChangePointToBase s ((L.baseChange s).mul b (E z) (E w))
    rw [hEbase, RelativeGroupLaw.baseChangePointToBase_mul, hEbase, hEbase]
    apply Subtype.ext
    exact mul_transport L hbs.symm z w
  let e : J ≃+ G.AlgPoints hcomm (AlgebraicClosure ℚ) :=
    { toEquiv := pts.trans (E.trans RelativeGroupLaw.AlgPoints.equivPoint.symm)
      map_add' := fun x y => by
        apply RelativeGroupLaw.AlgPoints.toPoint_injective
        change E (pts (x + y)) = G.mul b (E (pts x)) (E (pts y))
        rw [hadd]
        exact hEmul (pts x) (pts y) }
  refine ⟨⟨_, _, G, hcomm,
    hB.of_isPullback (IsPullback.of_hasPullback f s), e, ?_⟩⟩
  intro σ x
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  apply Subtype.ext
  apply pullback.hom_ext
  · change (E (pts (σ • x))).1 ≫ pullback.fst f s =
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (E (pts x)).1) ≫ pullback.fst f s
    rw [Category.assoc]
    rw [hEfst, hEfst]
    exact hgal σ x
  · change (E (pts (σ • x))).1 ≫ pullback.snd f s =
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (E (pts x)).1) ≫ pullback.snd f s
    rw [Category.assoc]
    rw [hEsnd, hEsnd]
    dsimp [b]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact (σ.commutes a).symm

end N25
