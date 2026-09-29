-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4c2ad0c6-261e-5048-90c1-6c8e4b25db38

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
import Theorems.Thm_ValuationSubring_exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Scheme_range_pullbackMap_id_id_eq_preimage_range
import Theorems.Thm_AlgebraicGeometry_Scheme_mem_asIdeal_base_iff_residue_germ_appTop_eq_zero
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_point

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
    (hx' : (XO.toBase (ΓM M H) hj ρO').base x' = IsLocalRing.closedPoint O')
    (ϖ' : O') (hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'}) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    ∀ P : Ideal ↥B, P.IsPrime → P ≠ ⊥ → σB ϖ' ∉ P →
      ∃ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (_ : W.IsRational)
        (s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO')
        (_ : s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA'))
        (_ : barPt A ≫ s' = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ')
        (hx : s'.base (IsLocalRing.closedPoint ↥A) = x'),
        letI χ : ↥B →+* ↥A :=
          (Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hx)).hom
        ∀ b : ↥B, b ∈ P ↔ χ b = 0 := by
  intro P hP hP0 hϖP
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  let B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
  let σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
    (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)

  haveI : P.IsPrime := hP

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

  obtain ⟨hη, hPker, hgeniff⟩ :=
    AlgebraicGeometry.Scheme.exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff x' P
  have hηne : ((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩ ≠ genericPoint _ :=
    fun h => hP0 (hgeniff.mp h)

  let r : ↥B →+* ↥((XO (ΓM M H) hj ρO').residueField (((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩)) :=
    ((XO (ΓM M H) hj ρO').residue _).hom.comp ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hη).hom
  have hrker : ∀ b : ↥B, b ∈ P ↔ r b = 0 := hPker

  have hηgen : (XO.toBase (ΓM M H) hj ρO').base (((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩) ∈
      Set.range (Spec.map (CommRingCat.ofHom jO')).base := by
    have hjinj : Function.Injective jO' := by
      rw [← hιA'j]; exact Subtype.coe_injective.comp hιA'inj

    have hnot : ϖ' ∉ ((XO.toBase (ΓM M H) hj ρO').base
        (((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩)).asIdeal := by
      rw [AlgebraicGeometry.Scheme.mem_asIdeal_base_iff_residue_germ_appTop_eq_zero]
      intro h0
      apply hϖP
      rw [hrker]

      refine Eq.trans ?_ h0
      show ((XO (ΓM M H) hj ρO').residue _).hom (((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hη).hom
        (((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom
          (((XO.toBase (ΓM M H) hj ρO').appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom ϖ')))) = _
      rw [← CommRingCat.comp_apply _ ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hη),
        TopCat.Presheaf.germ_stalkSpecializes]
    have hbot : ((XO.toBase (ΓM M H) hj ρO').base
        (((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩)).asIdeal = ⊥ := by
      by_contra hne
      apply hnot
      have hmax := Ideal.IsPrime.isMaximal (inferInstance : (_ : Ideal O').IsPrime) hne
      rw [IsLocalRing.eq_maximalIdeal hmax, hϖ']
      exact Ideal.subset_span rfl
    refine ⟨IsLocalRing.closedPoint (AlgebraicClosure ℚ), ?_⟩
    apply PrimeSpectrum.ext
    rw [hbot]
    show Ideal.comap (CommRingCat.ofHom jO').hom (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥
    rw [CommRingCat.hom_ofHom, show (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥ from
      (IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)), Ideal.comap_bot_of_injective jO' hjinj]

  have hrangeJ := AlgebraicGeometry.Scheme.range_pullbackMap_id_id_eq_preimage_range (toBase p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom ρO')) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    (Spec.map (CommRingCat.ofHom jO'))
    (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  obtain ⟨ζ, hζ⟩ : ((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩ ∈ Set.range prJ'.base := by
    have hr : Set.range prJ'.base = _ := hrangeJ
    rw [hr]; exact hηgen
  let ζC : ↥(𝔛.Meta).C := (inv 𝔛.eeta).base ζ
  have hζC : 𝔛.eeta.base ζC = ζ := by
    show (inv 𝔛.eeta ≫ 𝔛.eeta).base ζ = ζ
    rw [IsIso.inv_hom_id]; rfl
  have hζCne : ζC ≠ genericPoint (𝔛.Meta).C := by
    intro hgenC
    apply hηne

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
    have H2 := base_eq_genericPoint_of_flat' prJ' _ hgenQ
    rw [← hζ, ← hζC, hgenC, H2]
  have hclosed : IsClosed ({ζC} : Set ↥(𝔛.Meta).C) :=
    AlgebraicCurve.isClosed_singleton_of_ne_genericPoint (𝔛.Meta).toBase ζC hζCne
  let x0 := (pointEquivClosedPoint (𝔛.Meta).toBase).symm ⟨ζC, hclosed⟩
  have hx0 : x0.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = ζC :=
    congrArg Subtype.val (Equiv.apply_symm_apply (pointEquivClosedPoint (𝔛.Meta).toBase) ⟨ζC, hclosed⟩)

  have he₀ : ∃ e₀ : ↥((XO (ΓM M H) hj ρO').residueField (((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩)) →+*
      AlgebraicClosure ℚ, e₀.comp (r.comp σB) = A.subtype.comp ιA' := by
    let q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ XO (ΓM M H) hj ρO' := x0.1 ≫ 𝔛.eeta ≫ prJ'
    have hq : q.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
        ((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩ := by
      show prJ'.base (𝔛.eeta.base (x0.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) = _
      rw [hx0, hζC, hζ]
    have hq2 : q ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom jO') := by
      simp only [q, prJ', Category.assoc, pullback.map, pullback.lift_snd]
      rw [← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, x0.2, Category.id_comp]
    let e₀ : ↥((XO (ΓM M H) hj ρO').residueField (((XO (ΓM M H) hj ρO').fromSpecStalk x').base ⟨P, hP⟩)) →+*
        AlgebraicClosure ℚ :=
      (((XO (ΓM M H) hj ρO').residueFieldCongr hq).inv ≫
        (XO (ΓM M H) hj ρO').descResidueField (Scheme.stalkClosedPointTo q)).hom
    refine ⟨e₀, ?_⟩

    have k0 : (XO (ΓM M H) hj ρO').residue _ ≫ (((XO (ΓM M H) hj ρO').residueFieldCongr hq).inv ≫
        (XO (ΓM M H) hj ρO').descResidueField (Scheme.stalkClosedPointTo q)) =
        ((XO (ΓM M H) hj ρO').presheaf.stalkCongr (.of_eq hq.symm)).hom ≫ Scheme.stalkClosedPointTo q := by
      rw [Scheme.residueFieldCongr_inv, Scheme.residue_residueFieldCongr_assoc, Scheme.residue_descResidueField]
    have hmemq : q.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ (⊤ : (XO (ΓM M H) hj ρO').Opens) := trivial
    have k1 : (XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial ≫
        (XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hη ≫
        ((XO (ΓM M H) hj ρO').presheaf.stalkCongr (.of_eq hq.symm)).hom =
        (XO (ΓM M H) hj ρO').presheaf.germ ⊤ (q.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hmemq := by
      rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
    have k2 := Scheme.germ_stalkClosedPointTo q ⊤ hmemq
    have k3 : (XO.toBase (ΓM M H) hj ρO').appTop ≫ q.app ⊤ = (q ≫ pullback.snd _ _).appTop := by
      rw [Scheme.Hom.comp_appTop]; rfl
    have k12 : (XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial ≫
        (XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hη ≫
        ((XO (ΓM M H) hj ρO').presheaf.stalkCongr (.of_eq hq.symm)).hom ≫ Scheme.stalkClosedPointTo q =
        q.app ⊤ ≫ ((Spec (CommRingCat.of (AlgebraicClosure ℚ))).presheaf.mapIso
          (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem q hmemq).symm).op ≪≫
          Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom := by
      rw [← k2, ← k1]; simp only [Category.assoc]
    have main : (Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ (XO.toBase (ΓM M H) hj ρO').appTop ≫
        (XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial ≫ (XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hη ≫
        (XO (ΓM M H) hj ρO').residue _ ≫ (((XO (ΓM M H) hj ρO').residueFieldCongr hq).inv ≫
        (XO (ΓM M H) hj ρO').descResidueField (Scheme.stalkClosedPointTo q)) = CommRingCat.ofHom jO' := by
      rw [k0, k12, reassoc_of% k3, hq2]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op, Category.assoc]
      erw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
      have h3 : (Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ (Spec.map (CommRingCat.ofHom jO')).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom = CommRingCat.ofHom jO' := by
        rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
      exact h3
    apply RingHom.ext
    intro a
    have h4 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom main) a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h4
    rw [← hιA'j] at h4
    exact h4
  obtain ⟨e₀, he₀⟩ := he₀

  obtain ⟨τ, χ₀, hτ, hχτ, hχloc⟩ :=
    ValuationSubring.exists_ringHom_comp_eq_and_subtype_comp_eq_and_isLocalHom_of_isDiscreteValuationRing A O' ιA' hιA'inj hιA'loc
      ↥B σB H1 _ r e₀ he₀
  haveI : IsLocalHom χ₀ := hχloc
  have hkerχ : ∀ b : ↥B, b ∈ P ↔ χ₀ b = 0 := by
    intro b
    rw [hrker b]
    constructor
    · intro h
      apply Subtype.coe_injective
      show A.subtype (χ₀ b) = ((0 : ↥A) : AlgebraicClosure ℚ)
      rw [show A.subtype (χ₀ b) = τ (r b) from RingHom.congr_fun hχτ b, h, map_zero]; rfl
    · intro h
      have h1 : τ (r b) = 0 := by rw [← show A.subtype (χ₀ b) = τ (r b) from RingHom.congr_fun hχτ b, h, map_zero]
      exact (map_eq_zero_iff τ τ.injective).mp h1

  let s'₀ : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO' :=
    Spec.map (CommRingCat.ofHom χ₀) ≫ (XO (ΓM M H) hj ρO').fromSpecStalk x'
  haveI : IsLocalHom (CommRingCat.ofHom χ₀).hom := by rw [CommRingCat.hom_ofHom]; exact hχloc
  have hs'₀pt : s'₀.base (IsLocalRing.closedPoint ↥A) = x' := by
    show ((XO (ΓM M H) hj ρO').fromSpecStalk x').base ((Spec.map (CommRingCat.ofHom χ₀)).base (IsLocalRing.closedPoint ↥A)) = x'
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hχσ : χ₀.comp σB = ιA' := by
    apply RingHom.ext; intro a; apply Subtype.coe_injective
    show A.subtype (χ₀ (σB a)) = A.subtype (ιA' a)
    rw [show A.subtype (χ₀ (σB a)) = τ (r (σB a)) from RingHom.congr_fun hχτ (σB a)]
    exact RingHom.congr_fun hτ a
  have hfacΓ : XO.toBase (ΓM M H) hj ρO' = (XO (ΓM M H) hj ρO').toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ (XO.toBase (ΓM M H) hj ρO').appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hs'₀snd : s'₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') := by
    show (Spec.map (CommRingCat.ofHom χ₀) ≫ (XO (ΓM M H) hj ρO').fromSpecStalk x') ≫
      XO.toBase (ΓM M H) hj ρO' = _
    rw [Category.assoc, hfacΓ, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    rw [← hχσ]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl

  let Qτ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ XO (ΓM M H) hj ρO' := barPt A ≫ s'₀
  have hQτsnd : Qτ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom jO') := by
    show (barPt A ≫ s'₀) ≫ _ = _
    rw [Category.assoc, hs'₀snd, barPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hιA'j]
  have hQτbase : (Qτ ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hQτsnd, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hjO']
  let xτ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (𝔛.Meta).C // q ≫ (𝔛.Meta).toBase = 𝟙 _} :=
    ⟨pullback.lift (Qτ ≫ pullback.fst _ _) (𝟙 _) hQτbase ≫ inv 𝔛.eeta, by
      rw [Category.assoc, ← 𝔛.heeta, IsIso.inv_hom_id_assoc, pullback.lift_snd]⟩
  have hxτ : xτ.1 ≫ 𝔛.eeta ≫ prJ' = Qτ := by
    show (pullback.lift (Qτ ≫ pullback.fst _ _) (𝟙 _) hQτbase ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ prJ' = Qτ
    rw [Category.assoc, IsIso.inv_hom_id_assoc]
    apply pullback.hom_ext
    · simp only [prJ', Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
    · simp only [prJ', Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, hQτsnd]
  let W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := (𝔛.Meta).pointEquivPlace xτ
  have hrat : W.IsRational := AlgebraicCurve.CurveModel.isRational_pointEquivPlace (𝔛.Meta) xτ

  have hbar : barPt A ≫ s'₀ = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ' := by
    show Qτ = ((𝔛.Meta).pointEquivPlace.symm ((𝔛.Meta).pointEquivPlace xτ)).1 ≫ 𝔛.eeta ≫ prJ'
    rw [Equiv.symm_apply_apply, hxτ]
  refine ⟨W, hrat, s'₀, hs'₀snd, hbar, hs'₀pt, ?_⟩
  intro b
  rw [hkerχ b]
  have hχ : ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes (specializes_of_eq hs'₀pt) ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom χ₀) ≫ (XO (ΓM M H) hj ρO').fromSpecStalk x')) =
      CommRingCat.ofHom χ₀ := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hV
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]
  have := congrArg (fun φ => φ.hom b) hχ
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← this]
  rfl

end S_ModularCurve_XHDRModelAtP_exists_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_point
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_point (solution)
