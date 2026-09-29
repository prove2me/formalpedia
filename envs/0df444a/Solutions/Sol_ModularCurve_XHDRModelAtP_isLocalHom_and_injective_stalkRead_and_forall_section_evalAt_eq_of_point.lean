-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isLocalHom_and_injective_stalkRead_and_forall_section_evalAt_eq_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ae3b1f93-5a9e-57bc-b9ef-262b0a3cfbdc

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isLocalHom_and_injective_stalkRead_and_forall_section_evalAt_eq_of_point

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

private theorem isIso_stalkSpecializes_of_eq' {X : TopCat} (F : X.Presheaf CommRingCat) {x y : X} (h : x = y) :
    IsIso (F.stalkSpecializes (specializes_of_eq h)) := by
  subst h
  have : F.stalkSpecializes (specializes_of_eq (rfl : x = x)) = 𝟙 _ := F.stalkSpecializes_refl x
  rw [this]; infer_instance

private theorem base_eq_genericPoint_of_flat' {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IrreducibleSpace Y]
    (x : X) (hx : IsGenericPoint x (⊤ : Set X)) : f.base x = genericPoint Y := by
  obtain ⟨x', hx'sp, hx'eq⟩ := Flat.generalizingMap f ((genericPoint_spec Y).specializes (Set.mem_univ (f.base x)))
  have : x' = x := (hx'sp.antisymm (hx.specializes (Set.mem_univ _))).eq
  rw [← hx'eq, this]

private theorem flat_pullbackMap' {X S T T' : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S) (i : T' ⟶ T)
    [Flat i] (e₁ : f ≫ 𝟙 S = 𝟙 X ≫ f) (e₂ : g' ≫ 𝟙 S = i ≫ g) :
    Flat (pullback.map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂) := by
  have hcomp : i ≫ g = g' := by simpa using e₂.symm
  let e2 := pullbackLeftPullbackSndIso f g i ≪≫ pullback.congrHom rfl hcomp
  have : pullback.map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂ = e2.inv ≫ pullback.fst _ _ := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.comp_id, e2, Iso.trans_inv, Category.assoc, pullback.congrHom_inv,
        pullbackLeftPullbackSndIso_inv_fst, pullback.map]
    · simp only [pullback.map, pullback.lift_snd, e2, Iso.trans_inv, Category.assoc, pullback.congrHom_inv,
        pullback.condition, pullbackLeftPullbackSndIso_inv_snd_snd_assoc, pullback.lift_snd_assoc, Category.comp_id]
  rw [this]; infer_instance

private theorem stalkClosedPointTo_barPt_comp' {X : Scheme.{0}} (A : ValuationSubring (AlgebraicClosure ℚ))
    (s' : Spec (CommRingCat.of ↥A) ⟶ X) (b : X.presheaf.stalk (s'.base (IsLocalRing.closedPoint ↥A))) :
    (Scheme.stalkClosedPointTo (barPt A ≫ s')).hom
      ((X.presheaf.stalkSpecializes (s'.base.hom.map_specializes
        (IsLocalRing.specializes_closedPoint ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))))).hom b) =
    (((Scheme.stalkClosedPointTo s').hom b : ↥A) : AlgebraicClosure ℚ) := by
  have hsp0 := IsLocalRing.specializes_closedPoint ((barPt A).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))
  have hM : (Spec (CommRingCat.of ↥A)).presheaf.stalkSpecializes hsp0 ≫ Scheme.stalkClosedPointTo (barPt A) =
      (stalkClosedPointIso (CommRingCat.of ↥A)).hom ≫ CommRingCat.ofHom A.subtype := by
    haveI hepi : Epi ((Spec (CommRingCat.of ↥A)).presheaf.germ ⊤ (IsLocalRing.closedPoint ↥A) trivial) := by
      rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]; infer_instance
    rw [← cancel_epi ((Spec (CommRingCat.of ↥A)).presheaf.germ ⊤ (IsLocalRing.closedPoint ↥A) trivial),
      TopCat.Presheaf.germ_stalkSpecializes_assoc, germ_stalkClosedPointIso_hom_assoc]
    exact Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom A.subtype)
  rw [Scheme.stalkClosedPointTo_comp]
  change (Scheme.stalkClosedPointTo (barPt A)).hom ((s'.stalkMap _).hom ((X.presheaf.stalkSpecializes _).hom b)) = _
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]
  change ((Spec (CommRingCat.of ↥A)).presheaf.stalkSpecializes hsp0 ≫ Scheme.stalkClosedPointTo (barPt A)).hom
    ((s'.stalkMap _).hom b) = _
  rw [hM]
  rfl

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (ρO' : R p →+* O')
    (ιA' : O' →+* ↥A) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA') (hιA'ρ : ιA'.comp ρO' = ρ)
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ)

    (x' : ↥(XO (ΓM M H) hj ρO'))
    (hx' : (XO.toBase (ΓM M H) hj ρO').base x' = IsLocalRing.closedPoint O') :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))

    (IsLocalHom σB ∧ Function.Injective emb ∧
      emb.comp σB = (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp jO') ∧

    (∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
      ∀ (s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO'),
        s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') →
        barPt A ≫ s' = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ' →
        ∀ (hx : s'.base (IsLocalRing.closedPoint ↥A) = x'),
        letI χ : ↥B →+* ↥A :=
          (Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx)).hom
        IsLocalHom χ ∧ χ.comp σB = ιA' ∧
        ∀ b : ↥B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ)) := by
  intro hsp
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  let B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
  let σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
    (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
  let emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
    ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
        ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))

  have hp0' : ((p : ℕ) : O') ≠ 0 := by
    intro h
    have h1 : jO' ((p : ℕ) : O') = ((p : ℕ) : AlgebraicClosure ℚ) := map_natCast jO' p
    rw [h, map_zero] at h1
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1.symm
  have hp' : ((p : ℕ) : O') ∈ IsLocalRing.maximalIdeal O' := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (ιA' ((p : ℕ) : O')) := hu.map ιA'
    rw [map_natCast] at hu'

    have hpA : ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]; push_cast; exact hA
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hpA) hu'
  haveI hint : IsIntegral (XO (ΓM M H) hj ρO') :=
    ModularCurve.XHDRModelAtP.isIntegral_xO_of_mem_maximalIdeal p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O' ρO' hp0' hp'

  have C1 : (XO.toBase (ΓM M H) hj ρO').base x' = IsLocalRing.closedPoint O' := hx'

  have H1 : IsLocalHom σB := by
    constructor
    intro a ha
    have e : σB a = ((XO.toBase (ΓM M H) hj ρO').stalkMap x').hom
        (((Spec (CommRingCat.of O')).presheaf.germ ⊤ ((XO.toBase (ΓM M H) hj ρO').base x') trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of O')).inv a)) := by
      show ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom
        (((XO.toBase (ΓM M H) hj ρO').appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a)) = _
      rw [Scheme.Hom.germ_stalkMap_apply]
      rfl
    rw [e] at ha
    have ha2 := (isUnit_map_iff ((XO.toBase (ΓM M H) hj ρO').stalkMap x').hom _).mp ha
    rw [C1] at ha2
    have ha3 := ha2.map (stalkClosedPointIso (CommRingCat.of O')).hom.hom
    rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, ← CommRingCat.comp_apply, Iso.inv_hom_id] at ha3
    simpa using ha3

  have H2 : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) = genericPoint (XO (ΓM M H) hj ρO') := by

    have hjinj : Function.Injective jO' := by
      rw [← hιA'j]; exact Subtype.coe_injective.comp hιA'inj
    have hflatj : (CommRingCat.ofHom jO').hom.Flat := by
      rw [CommRingCat.hom_ofHom]
      letI : Algebra O' (AlgebraicClosure ℚ) := jO'.toAlgebra
      haveI : FaithfulSMul O' (AlgebraicClosure ℚ) := (faithfulSMul_iff_algebraMap_injective O' _).mpr hjinj
      show Module.Flat O' (AlgebraicClosure ℚ)
      infer_instance
    haveI : Flat (Spec.map (CommRingCat.ofHom jO')) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hflatj
    haveI : Flat prJ' := flat_pullbackMap' _ _ _ _ _ _
    have hgenQ : IsGenericPoint (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) (⊤ : Set ↥XQ) := by
      have hsurj : Function.Surjective 𝔛.eeta.base := (Scheme.homeoOfIso (asIso 𝔛.eeta)).surjective
      have h := (genericPoint_spec (𝔛.Meta).C).image 𝔛.eeta.continuous
      rw [Set.image_univ_of_surjective hsurj, closure_univ] at h
      exact h
    exact base_eq_genericPoint_of_flat' prJ' _ hgenQ

  have H3 : Function.Injective emb := by

    let G : (XO (ΓM M H) hj ρO').functionField →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq H2)).hom))
    have key : emb = G.comp (algebraMap ↥B (XO (ΓM M H) hj ρO').functionField) := by
      apply RingHom.ext
      intro b
      show (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
          (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom b))) =
        (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
          (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq H2)).hom
            (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes
              ((genericPoint_spec (XO (ΓM M H) hj ρO')).specializes trivial)).hom b))))
      congr 3
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rw [key]
    exact G.injective.comp (IsFractionRing.injective ↥B (XO (ΓM M H) hj ρO').functionField)

  have H4 : emb.comp σB = (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp jO' := by
    apply RingHom.ext
    intro a

    have hstr : 𝔛.eeta ≫ prJ' ≫ XO.toBase (ΓM M H) hj ρO' =
        (𝔛.Meta).toBase ≫ Spec.map (CommRingCat.ofHom jO') := by
      simp only [prJ', XO.toBase, pullback.map, pullback.lift_snd, ← Category.assoc, 𝔛.heeta]
    show (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
          (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom
            (((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom
              (((XO.toBase (ΓM M H) hj ρO').appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a)))))) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO' a)
    rw [← CommRingCat.comp_apply _ ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp),
      TopCat.Presheaf.germ_stalkSpecializes]
    erw [Scheme.Hom.germ_stalkMap_apply prJ' ⊤ (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) trivial]
    erw [Scheme.Hom.germ_stalkMap_apply 𝔛.eeta ⊤ (genericPoint (𝔛.Meta).C) trivial]

    have happ : (𝔛.eeta.app ⊤).hom ((prJ'.app ⊤).hom (((XO.toBase (ΓM M H) hj ρO').appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a))) =
        ((𝔛.Meta).toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv.hom (jO' a)) := by
      have h1 := congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a)) hstr
      dsimp only at h1
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
      have h2 : ((Spec.map (CommRingCat.ofHom jO')).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a) =
          (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv.hom (jO' a) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]; rfl
      rw [h2] at h1
      exact h1
    erw [happ, RingEquiv.symm_apply_eq, (𝔛.Meta).ffEquiv_algebraMap]
    rfl

  have H8 : ∀ (s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO'),
      s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') →
      ∀ (hx : s'.base (IsLocalRing.closedPoint ↥A) = x'),
        ((Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx)).hom).comp σB = ιA' := by
    intro s' hs'2 hx

    have hmemA : s'.base (IsLocalRing.closedPoint ↥A) ∈ (⊤ : (XO (ΓM M H) hj ρO').Opens) := trivial
    have k1 : (XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial ≫
        (XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx) =
        (XO (ΓM M H) hj ρO').presheaf.germ ⊤ (s'.base (IsLocalRing.closedPoint ↥A)) hmemA :=
      (XO (ΓM M H) hj ρO').presheaf.germ_stalkSpecializes _ _
    have k2 := Scheme.germ_stalkClosedPointTo s' ⊤ hmemA

    have k3 : (XO.toBase (ΓM M H) hj ρO').appTop ≫ s'.app ⊤ =
        (s' ≫ pullback.snd _ _).appTop := by
      rw [Scheme.Hom.comp_appTop]; rfl
    apply RingHom.ext
    intro a
    show (Scheme.stalkClosedPointTo s').hom (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx)).hom
      (((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom
        (((XO.toBase (ΓM M H) hj ρO').appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a)))) = ιA' a
    rw [← CommRingCat.comp_apply _ ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes _), k1,
      ← CommRingCat.comp_apply _ (Scheme.stalkClosedPointTo s'), k2,
      ← CommRingCat.comp_apply ((XO.toBase (ΓM M H) hj ρO').appTop), ← Category.assoc, k3, hs'2]

    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op, Category.assoc,
      CommRingCat.comp_apply]
    erw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ (Spec.map (CommRingCat.ofHom ιA')).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of ↥A)).hom = CommRingCat.ofHom ιA' := by
      rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
    have h4 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3) a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h4
    show ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).hom).hom (((Spec.map (CommRingCat.ofHom ιA')).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a)) = ιA' a
    exact h4

  have H9 : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
      ∀ (s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO'),
        s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') →
        barPt A ≫ s' = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ' →
        ∀ (hx : s'.base (IsLocalRing.closedPoint ↥A) = x') (b : ↥B),
          emb b ∈ W.toValuationSubring ∧
          W.evalAt (emb b) = ((((Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx)).hom) b : ↥A) : AlgebraicClosure ℚ) := by
    intro W hrat s' hs'2 hs2' hx b

    let pt := (𝔛.Meta).pointEquivPlace.symm W
    have hW : (𝔛.Meta).pointEquivPlace pt = W := Equiv.apply_symm_apply _ _
    let φ : (𝔛.Meta).C ⟶ XO (ΓM M H) hj ρO' := 𝔛.eeta ≫ prJ'

    have hptσ : pt.1 ≫ φ = barPt A ≫ s' := hs2'.symm

    let xW := pt.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))
    have hspA : (barPt A ≫ s').base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ x' := by
      rw [← hx]
      exact s'.base.hom.map_specializes (IsLocalRing.specializes_closedPoint _)
    have hspW : φ.base xW ⤳ x' := by
      show (pt.1 ≫ φ).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ x'
      rw [hptσ]; exact hspA
    let sC : (𝔛.Meta).C.presheaf.stalk xW :=
      (φ.stalkMap xW).hom (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hspW).hom b)

    have V1 : (𝔛.Meta).ffEquiv.symm (algebraMap _ (𝔛.Meta).C.functionField sC) = emb b := by
      show (𝔛.Meta).ffEquiv.symm (((𝔛.Meta).C.presheaf.stalkSpecializes
          ((genericPoint_spec (𝔛.Meta).C).specializes trivial)).hom
            ((φ.stalkMap xW).hom (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hspW).hom b))) =
        (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
          ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
            (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom b)))
      congr 1
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, ← CommRingCat.comp_apply _ ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes _),
        TopCat.Presheaf.stalkSpecializes_comp]
      show ((𝔛.eeta ≫ prJ').stalkMap (genericPoint (𝔛.Meta).C)).hom _ = _
      rw [Scheme.Hom.stalkMap_comp]
      rfl

    obtain ⟨hmemC, -, hevC⟩ :=
      AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo (𝔛.Meta) pt sC
    rw [hW, V1] at hmemC hevC
    refine ⟨hmemC, ?_⟩
    rw [hevC]

    have gen2 : ∀ (ψ₁ ψ₂ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ XO (ΓM M H) hj ρO') (_ : ψ₁ = ψ₂)
        (h1 : ψ₁.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ x')
        (h2 : ψ₂.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ x'),
        (Scheme.stalkClosedPointTo ψ₁).hom (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes h1).hom b) =
        (Scheme.stalkClosedPointTo ψ₂).hom (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes h2).hom b) := by
      rintro ψ _ rfl _ _; rfl
    have step1 : (Scheme.stalkClosedPointTo pt.1).hom sC =
        (Scheme.stalkClosedPointTo (pt.1 ≫ φ)).hom (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hspW).hom b) := by
      rw [Scheme.stalkClosedPointTo_comp]; rfl
    have step2 := gen2 _ _ hptσ hspW hspA
    have step3 := stalkClosedPointTo_barPt_comp' A s'
      (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx)).hom b)
    rw [← CommRingCat.comp_apply _ ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes _),
      TopCat.Presheaf.stalkSpecializes_comp] at step3
    exact step1.trans (step2.trans step3)

  refine ⟨⟨H1, H3, H4⟩, ?_⟩
  intro W hrat s' hs'2 hs2' hx
  refine ⟨?_, H8 s' hs'2 hx, H9 W hrat s' hs'2 hs2' hx⟩
  haveI : IsIso ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx)) :=
    isIso_stalkSpecializes_of_eq' _ hx
  exact RingHom.isLocalHom_comp _ _

end S_ModularCurve_XHDRModelAtP_isLocalHom_and_injective_stalkRead_and_forall_section_evalAt_eq_of_point
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isLocalHom_and_injective_stalkRead_and_forall_section_evalAt_eq_of_point (solution)
