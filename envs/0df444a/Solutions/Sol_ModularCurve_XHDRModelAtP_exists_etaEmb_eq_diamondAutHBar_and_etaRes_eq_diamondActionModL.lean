-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6a8328bf-91e3-5005-90ce-2b62581723fa

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra IsLocalRing ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups Pointwise

namespace P2mEtaDia

section VS

variable {L : Type*} [Field L]

theorem mem_nonunits_iff_mem_and_inv_not_mem (O : ValuationSubring L) (x : L) :
    x ∈ O.nonunits ↔ x ∈ O ∧ (x ≠ 0 → x⁻¹ ∉ O) := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨hx, fun hx0 hinv => ?_⟩
    have hu : IsUnit (⟨x, hx⟩ : O) := by
      refine IsUnit.of_mul_eq_one ⟨x⁻¹, hinv⟩ (Subtype.ext ?_)
      show x * x⁻¹ = 1
      exact mul_inv_cancel₀ hx0
    exact ((IsLocalRing.mem_maximalIdeal _).mp hm) hu
  · rintro ⟨hx, h⟩
    refine ⟨hx, (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_⟩
    obtain ⟨u, hu⟩ := hu
    have hmul : x * (((u⁻¹ : Oˣ) : O) : L) = 1 := by
      have := congrArg (fun a : O => (a : L)) u.mul_inv
      simpa [hu] using this
    have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hmul
    apply h hx0
    rw [inv_eq_of_mul_eq_one_right hmul]
    exact ((u⁻¹ : Oˣ) : O).2

theorem sub_mem_nonunits (O : ValuationSubring L) {a b : L} (ha : a ∈ O.nonunits) (hb : b ∈ O.nonunits) :
    a - b ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at ha hb ⊢
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  exact ⟨O.toSubring.sub_mem ha hb, Ideal.sub_mem _ ha' hb'⟩

theorem map_mem_nonunits_of_mem_nonunits {K : Type*} [Field K] [Algebra K L]
    (σ : L →ₐ[K] L) (Ov Ow : ValuationSubring L) (h : ∀ x, x ∈ Ow ↔ σ x ∈ Ov)
    {x : L} (hx : x ∈ Ow.nonunits) : σ x ∈ Ov.nonunits := by
  rw [mem_nonunits_iff_mem_and_inv_not_mem] at hx ⊢
  refine ⟨(h x).mp hx.1, fun h0 hinv => ?_⟩
  have hx0 : x ≠ 0 := fun e => h0 (by rw [e, map_zero])
  exact hx.2 hx0 ((h _).mpr (by rwa [map_inv₀]))

theorem mem_inv_ofAlgAut_smul_iff {K : Type*} [Field K] [Algebra K L] (σ : L ≃ₐ[K] L) (v : Place K L) (x : L) :
    x ∈ ((SemilinearAut.ofAlgAut σ)⁻¹ • v).toValuationSubring ↔ σ x ∈ v.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_inv_pointwise_smul_iff]
  rfl

end VS

section Germs

universe u

theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    [h : Nonempty (Scheme.Opens.toScheme U)] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)

theorem germToFunctionField_eq_germ {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    [Nonempty (Scheme.Opens.toScheme U)] (h : genericPoint X ∈ U) (s : Γ(X, U)) :
    X.germToFunctionField U s = X.presheaf.germ U (genericPoint X) h s := rfl

theorem mem_closedPoints_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] {x : X}
    (hx : x ∈ closedPoints X) : f.base x ∈ closedPoints Y := by
  have h := (Scheme.homeoOfIso (asIso f)).isClosedMap {x} hx
  rw [Set.image_singleton] at h
  exact h

theorem base_genericPoint_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y :=
  genericPoint_eq_of_isOpenImmersion f

theorem germ_app_congr {C X : Scheme.{u}} {f f' : C ⟶ X} (h : f = f') (U : X.Opens) (c : C)
    (hc : f.base c ∈ U) (hc' : f'.base c ∈ U) (s : Γ(X, U)) :
    (C.presheaf.germ (f ⁻¹ᵁ U) c hc) ((f.app U) s) = (C.presheaf.germ (f' ⁻¹ᵁ U) c hc') ((f'.app U) s) := by
  subst h; rfl

end Germs

section Core

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]

theorem ffEquiv_symm_germToFunctionField_app_eq_of_placeOfPoint_eq
    (M : CurveModel K L) (σ : L →ₐ[K] L) (Φ : Place K L → Place K L)
    (hΦ : ∀ (v : Place K L) (x : L), x ∈ (Φ v).toValuationSubring ↔ σ x ∈ v.toValuationSubring)
    (Fr : M.C ⟶ M.C) (hFrb : Fr ≫ M.toBase = M.toBase)
    (hFr : ∀ P : closedPoints M.C, ∃ h : Fr.base P.1 ∈ closedPoints M.C,
      M.placeOfPoint ⟨_, h⟩ = Φ (M.placeOfPoint P))
    (V : M.C.Opens) [Nonempty (Scheme.Opens.toScheme V)] [Nonempty (Scheme.Opens.toScheme (Fr ⁻¹ᵁ V))]
    (s : Γ(M.C, V)) :
    M.ffEquiv.symm (M.C.germToFunctionField (Fr ⁻¹ᵁ V) ((Fr.app V).hom s)) =
      σ (M.ffEquiv.symm (M.C.germToFunctionField V s)) := by
  by_contra hne
  have hw0 : M.ffEquiv.symm (M.C.germToFunctionField (Fr ⁻¹ᵁ V) ((Fr.app V).hom s)) -
      σ (M.ffEquiv.symm (M.C.germToFunctionField V s)) ≠ 0 := sub_ne_zero.mpr hne

  obtain ⟨W, hηW, t, ht⟩ := TopCat.Presheaf.exists_germ_eq M.C.presheaf (x := genericPoint M.C)
    (M.ffEquiv (M.ffEquiv.symm (M.C.germToFunctionField (Fr ⁻¹ᵁ V) ((Fr.app V).hom s)) -
      σ (M.ffEquiv.symm (M.C.germToFunctionField V s)))⁻¹)
  haveI hWne : Nonempty (Scheme.Opens.toScheme W) := ⟨⟨_, hηW⟩⟩
  have hRt : M.ffEquiv.symm (M.C.germToFunctionField W t) =
      (M.ffEquiv.symm (M.C.germToFunctionField (Fr ⁻¹ᵁ V) ((Fr.app V).hom s)) -
        σ (M.ffEquiv.symm (M.C.germToFunctionField V s)))⁻¹ := by
    rw [germToFunctionField_eq_germ W hηW]
    erw [ht]
    exact M.ffEquiv.symm_apply_apply _

  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  have hηV : genericPoint M.C ∈ Fr ⁻¹ᵁ V := genericPoint_mem_of_nonempty _
  obtain ⟨x, ⟨hxW, hxV⟩, hxc⟩ := nonempty_inter_closedPoints (X := M.C)
    (Z := ((W ⊓ Fr ⁻¹ᵁ V : M.C.Opens) : Set M.C)) ⟨genericPoint M.C, hηW, hηV⟩ (W ⊓ Fr ⁻¹ᵁ V).isOpen.isLocallyClosed

  obtain ⟨z, hz⟩ : ∃ z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      z = (pointEquivClosedPoint M.toBase).symm ⟨x, hxc⟩ := ⟨_, rfl⟩
  have hzx : ∀ a, z.1.base a = x := fun a => by
    rw [hz, pointEquivClosedPoint_symm_apply_coe]
    exact pointOfClosedPoint_apply _ _ _ _
  let z' : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨z.1 ≫ Fr, by rw [Category.assoc, hFrb]; exact z.2⟩
  have hz'x : ∀ a, z'.1.base a = Fr.base x := fun a => by
    show (z.1 ≫ Fr).base a = _
    rw [Scheme.Hom.comp_apply, hzx]
  have hzV : ⊤ ≤ z.1 ⁻¹ᵁ (Fr ⁻¹ᵁ V) := fun a _ => show Fr.base (z.1.base a) ∈ V by rw [hzx]; exact hxV
  have hzW : ⊤ ≤ z.1 ⁻¹ᵁ W := fun a _ => show z.1.base a ∈ W by rw [hzx]; exact hxW
  have hz'V : ⊤ ≤ z'.1 ⁻¹ᵁ V := fun a _ => show z'.1.base a ∈ V by rw [hz'x]; exact hxV

  have hvz : M.pointEquivPlace z = M.placeOfPoint ⟨x, hxc⟩ := by
    rw [CurveModel.pointEquivPlace_apply, hz, Equiv.apply_symm_apply]
  obtain ⟨hFx, hFxpl⟩ := hFr ⟨x, hxc⟩
  have hvz' : M.pointEquivPlace z' = Φ (M.placeOfPoint ⟨x, hxc⟩) := by
    rw [CurveModel.pointEquivPlace_apply, ← hFxpl]
    congr 1
    apply Subtype.ext
    rw [pointEquivClosedPoint_apply_coe]
    exact hz'x _

  have e1 := (CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
    M W t z hzW).1
  have e2 := (CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
    M (Fr ⁻¹ᵁ V) ((Fr.app V).hom s) z hzV).2
  have e3 := (CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
    M V s z' hz'V).2
  rw [hvz] at e1 e2
  rw [hvz'] at e3
  rw [hRt] at e1

  have hval : (z'.1.appLE V ⊤ hz'V) s = (z.1.appLE (Fr ⁻¹ᵁ V) ⊤ hzV) ((Fr.app V).hom s) := by
    show ((z.1 ≫ Fr).appLE V ⊤ hz'V) s = _
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [hval] at e3

  have e3' := map_mem_nonunits_of_mem_nonunits σ _ _ (hΦ (M.placeOfPoint ⟨x, hxc⟩)) e3
  rw [map_sub, AlgHom.commutes] at e3'
  have e4 := sub_mem_nonunits _ e2 e3'
  rw [sub_sub_sub_cancel_right] at e4

  exact ((mem_nonunits_iff_mem_and_inv_not_mem _ _).mp e4).2 hw0 e1

theorem ffEquiv_symm_stalkMap_stalkSpecializes_eq
    (M : CurveModel K L) (σ : L →ₐ[K] L) (Φ : Place K L → Place K L)
    (hΦ : ∀ (v : Place K L) (x : L), x ∈ (Φ v).toValuationSubring ↔ σ x ∈ v.toValuationSubring)
    (Fr : M.C ⟶ M.C) (hFrb : Fr ≫ M.toBase = M.toBase)
    (hFr : ∀ P : closedPoints M.C, ∃ h : Fr.base P.1 ∈ closedPoints M.C,
      M.placeOfPoint ⟨_, h⟩ = Φ (M.placeOfPoint P))
    (hξ : Fr.base (genericPoint M.C) = genericPoint M.C) (f : M.C.functionField) :
    M.ffEquiv.symm ((Fr.stalkMap (genericPoint M.C)).hom
        ((M.C.presheaf.stalkSpecializes (specializes_of_eq hξ)).hom f)) =
      σ (M.ffEquiv.symm f) := by
  obtain ⟨V, hξV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.C.presheaf f
  haveI : Nonempty (Scheme.Opens.toScheme V) := ⟨⟨_, hξV⟩⟩
  have hξV' : Fr.base (genericPoint M.C) ∈ V := by rw [hξ]; exact hξV
  haveI : Nonempty (Scheme.Opens.toScheme (Fr ⁻¹ᵁ V)) := ⟨⟨genericPoint M.C, hξV'⟩⟩
  have h1 : (M.C.presheaf.stalkSpecializes (specializes_of_eq hξ)).hom
      ((M.C.presheaf.germ V (genericPoint M.C) hξV) s) =
        (M.C.presheaf.germ V (Fr.base (genericPoint M.C)) hξV') s :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  have h2 : (Fr.stalkMap (genericPoint M.C)).hom ((M.C.presheaf.germ V (Fr.base (genericPoint M.C)) hξV') s) =
      (M.C.presheaf.germ (Fr ⁻¹ᵁ V) (genericPoint M.C) hξV') ((Fr.app V).hom s) :=
    Scheme.Hom.germ_stalkMap_apply Fr V (genericPoint M.C) hξV' s
  erw [h1, h2]
  exact ffEquiv_symm_germToFunctionField_app_eq_of_placeOfPoint_eq M σ Φ hΦ Fr hFrb hFr V s

theorem placeOfPoint_law_of_pointEquivPlace_law
    (M : CurveModel K L) (Φ : Place K L → Place K L)
    (Fr : M.C ⟶ M.C) (hFrb : Fr ≫ M.toBase = M.toBase)
    (h : ∀ z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      M.pointEquivPlace ⟨z.1 ≫ Fr, by rw [Category.assoc, hFrb]; exact z.2⟩ = Φ (M.pointEquivPlace z))
    (P : closedPoints M.C) :
    ∃ h : Fr.base P.1 ∈ closedPoints M.C, M.placeOfPoint ⟨_, h⟩ = Φ (M.placeOfPoint P) := by
  obtain ⟨z, hz⟩ : ∃ z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      z = (pointEquivClosedPoint M.toBase).symm P := ⟨_, rfl⟩
  have hzx : ∀ a, z.1.base a = P.1 := fun a => by
    rw [hz, pointEquivClosedPoint_symm_apply_coe]
    exact pointOfClosedPoint_apply _ _ _ _
  let z' : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨z.1 ≫ Fr, by rw [Category.assoc, hFrb]; exact z.2⟩
  have hz'x : (pointEquivClosedPoint M.toBase z').1 = Fr.base P.1 := by
    rw [pointEquivClosedPoint_apply_coe]
    show (z.1 ≫ Fr).base _ = _
    rw [Scheme.Hom.comp_apply, hzx]
  refine ⟨hz'x ▸ (pointEquivClosedPoint M.toBase z').2, ?_⟩
  have hP : M.placeOfPoint P = M.pointEquivPlace z := by
    rw [CurveModel.pointEquivPlace_apply, hz, Equiv.apply_symm_apply]
  rw [hP, ← h z, CurveModel.pointEquivPlace_apply]
  congr 1
  exact Subtype.ext hz'x.symm

end Core

section Square

universe u

theorem stalkMap_square_apply {C X : Scheme.{u}} (g : C ⟶ X) (δ : X ⟶ X) (θ : C ⟶ C) (H : θ ≫ g = g ≫ δ)
    (c : C) (hθ : θ.base c = c) (η : X) (hδ : δ.base η = η) (hsp : g.base c ⤳ η) (s : X.presheaf.stalk η) :
    (g.stalkMap c).hom ((X.presheaf.stalkSpecializes hsp).hom
      ((δ.stalkMap η).hom ((X.presheaf.stalkSpecializes (specializes_of_eq hδ)).hom s))) =
    (θ.stalkMap c).hom ((C.presheaf.stalkSpecializes (specializes_of_eq hθ)).hom
      ((g.stalkMap c).hom ((X.presheaf.stalkSpecializes hsp).hom s))) := by
  obtain ⟨U, hηU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  have hδη : δ.base η ∈ U := by rw [hδ]; exact hηU
  have hgc : g.base c ∈ δ ⁻¹ᵁ U := hsp.mem_open (δ ⁻¹ᵁ U).isOpen hδη
  have hgc' : g.base c ∈ U := hsp.mem_open U.isOpen hηU
  have hθc : θ.base c ∈ g ⁻¹ᵁ U := by show g.base (θ.base c) ∈ U; rw [hθ]; exact hgc'

  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hηU (specializes_of_eq hδ)]
  erw [Scheme.Hom.germ_stalkMap_apply δ U η hδη]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf (show η ∈ δ ⁻¹ᵁ U from hδη) hsp]
  erw [Scheme.Hom.germ_stalkMap_apply g (δ ⁻¹ᵁ U) c hgc]

  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hηU hsp]
  erw [Scheme.Hom.germ_stalkMap_apply g U c hgc']
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply C.presheaf (show c ∈ g ⁻¹ᵁ U from hgc') (specializes_of_eq hθ)]
  erw [Scheme.Hom.germ_stalkMap_apply θ (g ⁻¹ᵁ U) c hθc]

  have hL : (C.presheaf.germ (g ⁻¹ᵁ (δ ⁻¹ᵁ U)) c hgc) ((g.app (δ ⁻¹ᵁ U)) ((δ.app U) s)) =
      (C.presheaf.germ ((g ≫ δ) ⁻¹ᵁ U) c hgc) (((g ≫ δ).app U) s) := rfl
  have hR : (C.presheaf.germ (θ ⁻¹ᵁ (g ⁻¹ᵁ U)) c hθc) ((θ.app (g ⁻¹ᵁ U)) ((g.app U) s)) =
      (C.presheaf.germ ((θ ≫ g) ⁻¹ᵁ U) c hθc) (((θ ≫ g).app U) s) := rfl
  erw [hL, hR]
  exact (germ_app_congr H U c hθc hgc s).symm

theorem stalkMap_square_apply' {C X : Scheme.{u}} (g : C ⟶ X) (δ : X ⟶ X) (θ : C ⟶ C) (H : θ ≫ g = g ≫ δ)
    (c : C) (hθ : θ.base c = c) (hδ : δ.base (g.base c) = g.base c) (s : X.presheaf.stalk (g.base c)) :
    (g.stalkMap c).hom ((δ.stalkMap (g.base c)).hom ((X.presheaf.stalkSpecializes (specializes_of_eq hδ)).hom s)) =
    (θ.stalkMap c).hom ((C.presheaf.stalkSpecializes (specializes_of_eq hθ)).hom ((g.stalkMap c).hom s)) := by
  have h := stalkMap_square_apply g δ θ H c hθ (g.base c) hδ (specializes_refl _) s
  simpa only [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] using h

end Square

section Fibre

variable {p : ℕ} {Γ Γ' : Subgroup SL(2, ℤ)} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  {κ : Type} [CommRing κ] (toκ : R p →+* κ)

theorem fibreMap_fst (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) :
    fibreMap φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  rw [XHDRLevel.fibreMap, pullback.lift_fst]

theorem fibreMap_snd (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) :
    fibreMap φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [XHDRLevel.fibreMap, pullback.lift_snd, Category.comp_id]

def overOfIsoInv (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) :
    SchemeHomOver (toBase p Γ hj) (toBase p Γ hj) :=
  ⟨w.inv, by rw [Iso.inv_comp_eq]; exact hw.symm⟩

@[scoped simp] theorem overOfIsoInv_val (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) :
    (overOfIsoInv w hw).1 = w.inv := rfl

theorem fibreMap_overOfIso_comp_overOfIsoInv (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) :
    fibreMap (overOfIso w hw) toκ ≫ fibreMap (overOfIsoInv w hw) toκ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst, ← Category.assoc, fibreMap_fst, Category.id_comp, Category.assoc]
    show _ ≫ w.hom ≫ w.inv = _
    rw [Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, fibreMap_snd, fibreMap_snd, Category.id_comp]

theorem fibreMap_overOfIsoInv_comp_overOfIso (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) :
    fibreMap (overOfIsoInv w hw) toκ ≫ fibreMap (overOfIso w hw) toκ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst, ← Category.assoc, fibreMap_fst, Category.id_comp, Category.assoc]
    show _ ≫ w.inv ≫ w.hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, fibreMap_snd, fibreMap_snd, Category.id_comp]

theorem isIso_fibreMap_overOfIsoInv (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) :
    IsIso (fibreMap (overOfIsoInv w hw) toκ) :=
  ⟨⟨fibreMap (overOfIso w hw) toκ, fibreMap_overOfIsoInv_comp_overOfIso toκ w hw,
    fibreMap_overOfIso_comp_overOfIsoInv toκ w hw⟩⟩

end Fibre

section XH

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
  (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
  (e : (ZMod M)ˣ)

abbrev deltaAt {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibre (Γ := ΓM M H) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ :=
  fibreMap (overOfIsoInv (𝔛.dia e) (𝔛.dia_over e)) toκ

abbrev delta0 :
    fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶
      fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) :=
  fibreMap (overOfIsoInv (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (𝔛.dia0_over _))
    ((IsLocalRing.residue ↥Pl).comp ρ)

abbrev thetaM : 𝔛.Meta.C ⟶ 𝔛.Meta.C :=
  𝔛.eeta ≫ deltaAt 𝔛 e (algebraMap (R p) (AlgebraicClosure ℚ)) ≫ inv 𝔛.eeta

abbrev thetaF : (𝔛.Mfib Pl hPl ρ hρ).C ⟶ (𝔛.Mfib Pl hPl ρ hρ).C :=
  𝔛.efib Pl hPl ρ hρ ≫ delta0 𝔛 Pl ρ e ≫ inv (𝔛.efib Pl hPl ρ hρ)

theorem inv_eeta_toBase : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
  rw [IsIso.inv_comp_eq]
  exact 𝔛.heeta.symm

theorem thetaM_toBase : thetaM 𝔛 e ≫ 𝔛.Meta.toBase = 𝔛.Meta.toBase := by
  simp only [Category.assoc, inv_eeta_toBase]
  rw [fibreMap_snd, 𝔛.heeta]

scoped instance isIso_thetaM : IsIso (thetaM 𝔛 e) := by
  haveI := isIso_fibreMap_overOfIsoInv (algebraMap (R p) (AlgebraicClosure ℚ)) (𝔛.dia e) (𝔛.dia_over e)
  infer_instance

theorem thetaM_genericPoint : (thetaM 𝔛 e).base (genericPoint 𝔛.Meta.C) = genericPoint 𝔛.Meta.C :=
  base_genericPoint_of_isIso _

theorem thetaM_eeta_fst :
    thetaM 𝔛 e ≫ 𝔛.eeta ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ≫ (𝔛.dia e).inv := by
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [fibreMap_fst]
  rfl

theorem thetaM_pointEquivPlace
    (z : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) :
    𝔛.Meta.pointEquivPlace ⟨z.1 ≫ thetaM 𝔛 e, by rw [Category.assoc, thetaM_toBase]; exact z.2⟩ =
      (SemilinearAut.ofAlgAut (diamondAutHBar M H e))⁻¹ • 𝔛.Meta.pointEquivPlace z := by
  rw [eq_inv_smul_iff]
  symm
  apply 𝔛.dia_generic e ⟨z.1 ≫ thetaM 𝔛 e, _⟩ z
  show z.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = (z.1 ≫ thetaM 𝔛 e) ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ (𝔛.dia e).hom
  rw [Category.assoc, ← Category.assoc (𝔛.eeta) (pullback.fst _ _) (𝔛.dia e).hom, ← Category.assoc (thetaM 𝔛 e),
    thetaM_eeta_fst]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem thetaM_placeOfPoint (P : closedPoints 𝔛.Meta.C) :
    ∃ h : (thetaM 𝔛 e).base P.1 ∈ closedPoints 𝔛.Meta.C,
      𝔛.Meta.placeOfPoint ⟨_, h⟩ =
        (SemilinearAut.ofAlgAut (diamondAutHBar M H e))⁻¹ • 𝔛.Meta.placeOfPoint P :=
  placeOfPoint_law_of_pointEquivPlace_law 𝔛.Meta _ (thetaM 𝔛 e) (thetaM_toBase 𝔛 e)
    (thetaM_pointEquivPlace 𝔛 e) P

theorem ffEquiv_symm_thetaM_stalk (f : 𝔛.Meta.C.functionField) :
    𝔛.Meta.ffEquiv.symm (((thetaM 𝔛 e).stalkMap (genericPoint 𝔛.Meta.C)).hom
        ((𝔛.Meta.C.presheaf.stalkSpecializes (specializes_of_eq (thetaM_genericPoint 𝔛 e))).hom f)) =
      diamondAutHBar M H e (𝔛.Meta.ffEquiv.symm f) :=
  ffEquiv_symm_stalkMap_stalkSpecializes_eq 𝔛.Meta (diamondAutHBar M H e : _ →ₐ[AlgebraicClosure ℚ] _)
    (fun v => (SemilinearAut.ofAlgAut (diamondAutHBar M H e))⁻¹ • v)
    (fun v x => mem_inv_ofAlgAut_smul_iff _ v x)
    (thetaM 𝔛 e) (thetaM_toBase 𝔛 e) (thetaM_placeOfPoint 𝔛 e) (thetaM_genericPoint 𝔛 e) f

theorem inv_efib_toBase :
    inv (𝔛.efib Pl hPl ρ hρ) ≫ (𝔛.Mfib Pl hPl ρ hρ).toBase = pullback.snd _ _ := by
  rw [IsIso.inv_comp_eq]
  exact (𝔛.hefib Pl hPl ρ hρ).symm

theorem thetaF_toBase :
    thetaF 𝔛 Pl hPl ρ hρ e ≫ (𝔛.Mfib Pl hPl ρ hρ).toBase = (𝔛.Mfib Pl hPl ρ hρ).toBase := by
  simp only [Category.assoc, inv_efib_toBase]
  rw [fibreMap_snd, 𝔛.hefib]

scoped instance isIso_thetaF : IsIso (thetaF 𝔛 Pl hPl ρ hρ e) := by
  haveI := isIso_fibreMap_overOfIsoInv ((IsLocalRing.residue ↥Pl).comp ρ)
    (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (𝔛.dia0_over _)
  infer_instance

theorem thetaF_genericPoint :
    (thetaF 𝔛 Pl hPl ρ hρ e).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) = genericPoint (𝔛.Mfib Pl hPl ρ hρ).C :=
  base_genericPoint_of_isIso _

theorem thetaF_comp_forward :
    thetaF 𝔛 Pl hPl ρ hρ e ≫ 𝔛.efib Pl hPl ρ hρ ≫
      fibreMap (overOfIso (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (𝔛.dia0_over _))
        ((IsLocalRing.residue ↥Pl).comp ρ) ≫ inv (𝔛.efib Pl hPl ρ hρ) = 𝟙 _ := by
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← Category.assoc (delta0 𝔛 Pl ρ e), fibreMap_overOfIsoInv_comp_overOfIso, Category.id_comp,
    IsIso.hom_inv_id]

theorem thetaF_placeOfPoint (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C) :
    ∃ h : (thetaF 𝔛 Pl hPl ρ hρ e).base P.1 ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
      (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
        (SemilinearAut.ofAlgAut (diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e))))⁻¹ •
            (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P := by
  have hc : (thetaF 𝔛 Pl hPl ρ hρ e).base P.1 ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C :=
    mem_closedPoints_of_isIso _ P.2
  refine ⟨hc, ?_⟩
  obtain ⟨h, hh⟩ := ModularCurve.XHDRModelAtP.exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
    p M H hpM hpM2 hHp hj 𝔛 Pl hPl ρ hρ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e) ⟨_, hc⟩

  have hpt : (inv (𝔛.efib Pl hPl ρ hρ)).base
      ((fibreMap (overOfIso (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (𝔛.dia0_over _))
          ((IsLocalRing.residue ↥Pl).comp ρ)).base
        ((𝔛.efib Pl hPl ρ hρ).base ((thetaF 𝔛 Pl hPl ρ hρ e).base P.1))) = P.1 := by
    have := congrArg (fun φ => φ.base P.1) (thetaF_comp_forward 𝔛 Pl hPl ρ hρ e)
    first
      | simpa only [Scheme.Hom.comp_apply] using this
      | (simp only [Scheme.Hom.comp_apply] at this; exact this)
  have hP : (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ = (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P :=
    congrArg _ (Subtype.ext hpt)
  rw [hP] at hh
  rw [eq_inv_smul_iff]
  exact hh.symm

theorem ffEquiv_symm_thetaF_stalk (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (f : (𝔛.Mfib Pl hPl ρ hρ).C.functionField) :
    (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm (((thetaF 𝔛 Pl hPl ρ hρ e).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
        (((𝔛.Mfib Pl hPl ρ hρ).C.presheaf.stalkSpecializes
          (specializes_of_eq (thetaF_genericPoint 𝔛 Pl hPl ρ hρ e))).hom f)) =
      diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) ((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm f) :=
  ffEquiv_symm_stalkMap_stalkSpecializes_eq (𝔛.Mfib Pl hPl ρ hρ)
    (diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) : _ →ₐ[IsLocalRing.ResidueField ↥Pl] _)
    (fun v => (SemilinearAut.ofAlgAut (diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e))))⁻¹ • v)
    (fun v x => mem_inv_ofAlgAut_smul_iff _ v x)
    (thetaF 𝔛 Pl hPl ρ hρ e) (thetaF_toBase 𝔛 Pl hPl ρ hρ e) (thetaF_placeOfPoint 𝔛 Pl hPl ρ hρ e hpM2 hHp)
    (thetaF_genericPoint 𝔛 Pl hPl ρ hρ e) f

theorem thetaM_gA
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl) :
    thetaM 𝔛 e ≫ gA = gA ≫ deltaAt 𝔛 e ρ := by
  apply pullback.hom_ext
  · rw [Category.assoc, hgA₁, thetaM_eeta_fst, Category.assoc, fibreMap_fst, overOfIsoInv_val, ← Category.assoc gA, hgA₁,
      Category.assoc]
  · rw [Category.assoc, hgA₂, ← Category.assoc, thetaM_toBase, Category.assoc, fibreMap_snd, hgA₂]

theorem bc_delta
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶
      (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) :
    bc ≫ deltaAt 𝔛 e ρ = deltaAt 𝔛 e ((IsLocalRing.residue ↥Pl).comp ρ) ≫ bc := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_fst, ← Category.assoc, hbc₁, Category.assoc, hbc₁, fibreMap_fst]
  · rw [Category.assoc, fibreMap_snd, hbc₂, Category.assoc, hbc₂, ← Category.assoc, fibreMap_snd]

theorem comp0_delta :
    𝔛.comp Pl hPl ρ hρ 0 ≫ deltaAt 𝔛 e ((IsLocalRing.residue ↥Pl).comp ρ) =
      delta0 𝔛 Pl ρ e ≫ 𝔛.comp Pl hPl ρ hρ 0 := by
  have hcd := 𝔛.comp_dia Pl hPl ρ hρ 0 e
  calc 𝔛.comp Pl hPl ρ hρ 0 ≫ deltaAt 𝔛 e ((IsLocalRing.residue ↥Pl).comp ρ)
      = (delta0 𝔛 Pl ρ e ≫
          fibreMap (overOfIso (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (𝔛.dia0_over _))
            ((IsLocalRing.residue ↥Pl).comp ρ)) ≫
          𝔛.comp Pl hPl ρ hρ 0 ≫ deltaAt 𝔛 e ((IsLocalRing.residue ↥Pl).comp ρ) := by
        rw [fibreMap_overOfIsoInv_comp_overOfIso, Category.id_comp]
    _ = delta0 𝔛 Pl ρ e ≫ (𝔛.comp Pl hPl ρ hρ 0 ≫
          fibreMap (overOfIso (𝔛.dia e) (𝔛.dia_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)) ≫
          deltaAt 𝔛 e ((IsLocalRing.residue ↥Pl).comp ρ) := by
        rw [hcd]; simp only [Category.assoc]
    _ = delta0 𝔛 Pl ρ e ≫ 𝔛.comp Pl hPl ρ hρ 0 := by
        rw [Category.assoc, fibreMap_overOfIso_comp_overOfIsoInv, Category.comp_id]

theorem thetaF_phi
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶
      (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) :
    thetaF 𝔛 Pl hPl ρ hρ e ≫ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) =
      (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ≫ deltaAt 𝔛 e ρ := by
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [bc_delta 𝔛 Pl ρ e bc hbc₁ hbc₂, ← Category.assoc (𝔛.comp Pl hPl ρ hρ 0), comp0_delta, Category.assoc]

end XH

end P2mEtaDia
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL.P2mEtaDia"

open P2mEtaDia in
set_option maxHeartbeats 12800000 in
open Classical in
theorem solution

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :

    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    letI res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
    haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩

    ∀ (hDPκ : ∃ ρκ : CongruenceSubgroup.Gamma0 (M / p) →*
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≃ₐ[IsLocalRing.ResidueField ↥Pl]
            ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))),
        IsDiamondPullbackModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM) ρκ)
      (e : (ZMod M)ˣ) (g : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)))),
      ∃ g' : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))),
        emb g' = diamondAutHBar M H e (emb g) ∧
        res g' = diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (res g) := by
  intro hDPκ e g
  haveI : NeZero (M / p) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩

  have HM := thetaM_gA 𝔛 Pl ρ e gA hgA₁ hgA₂
  have HF := thetaF_phi 𝔛 Pl hPl ρ hρ e bc hbc₁ hbc₂
  have hξM := thetaM_genericPoint 𝔛 e
  have hξF := thetaF_genericPoint 𝔛 Pl hPl ρ hρ e
  have hδη : (deltaAt 𝔛 e ρ).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base
      (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) =
      (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) := by
    have h1 := congrArg (fun φ => φ.base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) HF
    dsimp only at h1
    rw [Scheme.Hom.comp_apply (thetaF 𝔛 Pl hPl ρ hρ e), hξF, Scheme.Hom.comp_apply _ (deltaAt 𝔛 e ρ)] at h1
    exact h1.symm

  refine ⟨((deltaAt 𝔛 e ρ).stalkMap _).hom
    (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes
      (specializes_of_eq hδη)).hom g), ?_, ?_⟩
  ·
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [stalkMap_square_apply gA (deltaAt 𝔛 e ρ) (thetaM 𝔛 e) HM (genericPoint 𝔛.Meta.C) hξM _ hδη hsp g]
    exact ffEquiv_symm_thetaM_stalk 𝔛 e _
  ·
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [stalkMap_square_apply' (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) (deltaAt 𝔛 e ρ)
      (thetaF 𝔛 Pl hPl ρ hρ e) HF (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) hξF hδη g]
    exact ffEquiv_symm_thetaF_stalk 𝔛 Pl hPl ρ hρ e hpM2 hHp _

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL.P2mEtaDia"

end S_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL (solution)
