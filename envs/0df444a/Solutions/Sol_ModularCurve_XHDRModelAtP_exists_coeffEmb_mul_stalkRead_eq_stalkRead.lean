-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_coeffEmb_mul_stalkRead_eq_stalkRead
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c3b7c715-2952-5f4e-85bd-c71f3fbf780d

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_XHDRLevel_isFractionRing_chartAlgFin_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_coeffEmb_mul_stalkRead_eq_stalkRead
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

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

set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (σ : O →+* O') (ιA' : O' →+* ↥A) (hσ : ιA'.comp σ = ιA) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
    letI prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    letI B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ xn'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
    Function.Injective emb ∧
    emb.comp σB = (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp jO' ∧
    ∀ a : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
      ∃ r s : ↥B, s ≠ 0 ∧
        (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (a : LaurentSeries ℚ),
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) a.2⟩ : ↥(xHFunctionFieldBar M H)) * emb s =
          emb r := by
  intro hsp
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  let bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
  let xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
  let prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  let prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  let B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
  let σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
    (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
  let emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
    ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
        ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))

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
  haveI hint : IsIntegral (XO (ΓM M H) hj (σ.comp ρO)) :=
    ModularCurve.XHDRModelAtP.isIntegral_xO_of_mem_maximalIdeal p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O' (σ.comp ρO) hp0' hp'
  have H2 : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) = genericPoint (XO (ΓM M H) hj (σ.comp ρO)) := by

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

  let G : (XO (ΓM M H) hj (σ.comp ρO)).functionField →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq H2)).hom))
  have key : emb = G.comp (algebraMap ↥B (XO (ΓM M H) hj (σ.comp ρO)).functionField) := by
    apply RingHom.ext
    intro b
    show (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
        (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom b))) =
      (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
        (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq H2)).hom
          (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes
            ((genericPoint_spec (XO (ΓM M H) hj (σ.comp ρO))).specializes trivial)).hom b))))
    congr 3
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  have H4 : emb.comp σB = (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp jO' := by
    apply RingHom.ext
    intro a

    have hstr : 𝔛.eeta ≫ prJ' ≫ XO.toBase (ΓM M H) hj (σ.comp ρO) =
        (𝔛.Meta).toBase ≫ Spec.map (CommRingCat.ofHom jO') := by
      simp only [prJ', XO.toBase, pullback.map, pullback.lift_snd, ← Category.assoc, 𝔛.heeta]
    show (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
          (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom
            (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom
              (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom a)))))) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO' a)
    rw [← CommRingCat.comp_apply _ ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp),
      TopCat.Presheaf.germ_stalkSpecializes]
    erw [Scheme.Hom.germ_stalkMap_apply prJ' ⊤ (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) trivial]
    erw [Scheme.Hom.germ_stalkMap_apply 𝔛.eeta ⊤ (genericPoint (𝔛.Meta).C) trivial]

    have happ : (𝔛.eeta.app ⊤).hom ((prJ'.app ⊤).hom (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom
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
  have H3 : Function.Injective emb := by
    rw [key]
    exact G.injective.comp (IsFractionRing.injective ↥B (XO (ΓM M H) hj (σ.comp ρO)).functionField)
  refine ⟨H3, H4, ?_⟩

  have hchart : ∀ c : ↥(chartAlgFin p (ΓM M H) hj),
      (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (c : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ :
        ↥(xHFunctionFieldBar M H)) ∈ Set.range G := by
    intro c
    let W : (XHDRLevel.X p (ΓM M H) hj).Opens := (ιFin p (ΓM M H) hj) ''ᵁ ⊤
    let fQ : (𝔛.Meta).C ⟶ XHDRLevel.X p (ΓM M H) hj :=
      𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    let t : Γ(XHDRLevel.X p (ΓM M H) hj, W) :=
      ((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv c)
    have hpin := 𝔛.Meta_pin c
    have hE : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((c : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (c : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ :
        ↥(xHFunctionFieldBar M H)) =
        (𝔛.Meta).ffEquiv.symm ((𝔛.Meta).C.germToFunctionField (fQ ⁻¹ᵁ W) ((fQ.app W).hom t)) :=
      Subtype.ext hpin.symm
    rw [hE]
    have hfQ : fQ = (𝔛.eeta ≫ prJ') ≫ pullback.fst _ _ := by
      simp only [fQ, prJ', Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
    have hgenW : fQ.base (genericPoint (𝔛.Meta).C) ∈ W :=
      ((genericPoint_spec (𝔛.Meta).C).mem_open_set_iff (fQ ⁻¹ᵁ W).isOpen).mpr (by
        obtain ⟨⟨x, hx⟩⟩ := 𝔛.Meta_chart_nonempty
        exact ⟨x, Set.mem_univ _, hx⟩)
    have hgenW' : ((𝔛.eeta ≫ prJ') ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (σ.comp ρO)))).base
        (genericPoint (𝔛.Meta).C) ∈ W := hfQ ▸ hgenW
    have step1 : (𝔛.Meta).C.germToFunctionField (fQ ⁻¹ᵁ W) ((fQ.app W).hom t) =
        (fQ.stalkMap (genericPoint (𝔛.Meta).C)).hom (((XHDRLevel.X p (ΓM M H) hj).presheaf.germ W _ hgenW).hom t) :=
      (Scheme.Hom.germ_stalkMap_apply fQ W (genericPoint _) hgenW t).symm
    have gen_eq : ∀ (φ ψ : (𝔛.Meta).C ⟶ XHDRLevel.X p (ΓM M H) hj) (_ : φ = ψ)
        (h1 : φ.base (genericPoint (𝔛.Meta).C) ∈ W) (h2 : ψ.base (genericPoint (𝔛.Meta).C) ∈ W),
        (φ.stalkMap (genericPoint (𝔛.Meta).C)).hom (((XHDRLevel.X p (ΓM M H) hj).presheaf.germ W _ h1).hom t) =
        (ψ.stalkMap (genericPoint (𝔛.Meta).C)).hom (((XHDRLevel.X p (ΓM M H) hj).presheaf.germ W _ h2).hom t) := by
      rintro φ _ rfl _ _; rfl
    have step2 := gen_eq _ _ hfQ hgenW hgenW'
    let u : (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk (prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C))) :=
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (σ.comp ρO)))).stalkMap _).hom
        (((XHDRLevel.X p (ΓM M H) hj).presheaf.germ W _ hgenW').hom t)
    have step3 : (((𝔛.eeta ≫ prJ') ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (σ.comp ρO)))).stalkMap
        (genericPoint (𝔛.Meta).C)).hom (((XHDRLevel.X p (ΓM M H) hj).presheaf.germ W _ hgenW').hom t) =
        (𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom u) := by
      rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]; rfl
    refine ⟨((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq H2.symm)).hom u, ?_⟩
    show (𝔛.Meta).ffEquiv.symm ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom
        (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq H2)).hom
          (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq H2.symm)).hom u)))) = _
    rw [← CommRingCat.comp_apply _ ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq H2)),
      TopCat.Presheaf.stalkSpecializes_comp,
      show (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes
        ((specializes_of_eq H2).trans (specializes_of_eq H2.symm)) = 𝟙 _ from
        (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes_refl _]
    rw [step1, step2, step3]
    rfl

  haveI hfrac : IsFractionRing ↥(chartAlgFin p (ΓM M H) hj) ↥(qExpFunctionFieldC ℚ (ΓM M H)) :=
    ModularCurve.XHDRLevel.isFractionRing_chartAlgFin_qExpFunctionFieldC p M H hj

  let ιh : ↥(qExpFunctionFieldC ℚ (ΓM M H)) →+* ↥(xHFunctionFieldBar M H) :=
    { toFun := fun x => ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
        ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  intro a
  obtain ⟨c₁, c₂, hc₂, hac⟩ := IsFractionRing.div_surjective (A := ↥(chartAlgFin p (ΓM M H) hj)) a
  have hmem : ιh a ∈ G.fieldRange := by
    rw [← hac, map_div₀]
    exact div_mem (hchart c₁) (hchart c₂)
  obtain ⟨k, hk⟩ := RingHom.mem_fieldRange.mp hmem
  obtain ⟨b, s, hs, hbs⟩ := IsFractionRing.div_surjective (A := ↥B) k
  refine ⟨b, s, nonZeroDivisors.ne_zero hs, ?_⟩
  show ιh a * emb s = emb b
  rw [← hk, key]
  show G k * G (algebraMap _ _ s) = G (algebraMap _ _ b)
  rw [← map_mul, ← hbs,
    div_mul_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective ↥B _)).mpr (nonZeroDivisors.ne_zero hs))]

end S_ModularCurve_XHDRModelAtP_exists_coeffEmb_mul_stalkRead_eq_stalkRead
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_coeffEmb_mul_stalkRead_eq_stalkRead (solution)
