-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.eq_inl_iff_toDR_base_mem_range_compInf_of_mem_comp_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/e0394324-5318-569b-a707-41e45cc65f7a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_eq_inl_iff_toDR_base_mem_range_compInf_of_mem_comp_support
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

open AlgebraicGeometry.RelPicard

set_option maxHeartbeats 1600000 in

/-!                                                                                                                      -/

namespace StrictCompAux

variable {p : ℕ} [Fact p.Prime]

theorem baseChangeMap_fst {O κ : Type} [CommRing O] [CommRing κ] (toκ : O →+* κ) :
    DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp only [DRModel.baseChangeMap, pullback.map, pullback.lift_fst, Category.comp_id]

variable (𝔛 : DRModelPackage p) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

theorem specMap_closedPoint (hker : ∀ a ∈ IsLocalRing.maximalIdeal O, toκ a = 0) :
    (Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint O := by
  change PrimeSpectrum.comap toκ (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint O
  apply PrimeSpectrum.ext
  change Ideal.comap toκ (IsLocalRing.closedPoint κ).asIdeal = IsLocalRing.maximalIdeal O
  have hle : IsLocalRing.maximalIdeal O ≤ Ideal.comap toκ (IsLocalRing.closedPoint κ).asIdeal := by
    intro a ha
    rw [Ideal.mem_comap, hker a ha]
    exact Ideal.zero_mem _
  exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

theorem exists_comp_eq_toDR (C : 𝔛reg.Y.IdealSheafData)
    (cκ : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
    (hiso : ∃ e : pullback (C.subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
      IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
        e ≫ cκ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ C.subschemeι ≫ 𝔛reg.toDR)
    (hker : ∀ a ∈ IsLocalRing.maximalIdeal O, toκ a = 0)
    (y₀ : 𝔛reg.Y) (hy₀ : y₀ ∈ C.support) (hbase : 𝔛reg.toBase.base y₀ = IsLocalRing.closedPoint O) :
    ∃ c₀ : (𝔛.ratModel κ).C, (cκ ≫ DRModel.baseChangeMap toκ).base c₀ = 𝔛reg.toDR.base y₀ := by
  obtain ⟨e, -, -, hcomp⟩ := hiso
  have hy₀' : y₀ ∈ Set.range C.subschemeι.base := by rw [Scheme.IdealSheafData.range_subschemeι]; exact hy₀
  obtain ⟨y', rfl⟩ := hy₀'
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.subschemeι ≫ 𝔛reg.toBase)
    (g := Spec.map (CommRingCat.ofHom toκ)) y' (IsLocalRing.closedPoint κ)
    (by rw [Scheme.Hom.comp_apply, hbase, specMap_closedPoint toκ hker])
  refine ⟨e.base w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Category.assoc] at *
  have := congrArg (fun φ => φ.base w) hcomp
  simp only [Scheme.Hom.comp_apply] at this ⊢
  rw [this, hw]

theorem exists_mem_support_toDR_eq (C : 𝔛reg.Y.IdealSheafData)
    (cκ : (𝔛.ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))
    (hiso : ∃ e : pullback (C.subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C,
      IsIso e ∧ e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _ ∧
        e ≫ cκ ≫ DRModel.baseChangeMap toκ = pullback.fst _ _ ≫ C.subschemeι ≫ 𝔛reg.toDR)
    (b₀ : (𝔛.ratModel κ).C) :
    ∃ y₁ : 𝔛reg.Y, y₁ ∈ C.support ∧ 𝔛reg.toDR.base y₁ = (cκ ≫ DRModel.baseChangeMap toκ).base b₀ := by
  obtain ⟨e, he, -, hcomp⟩ := hiso
  haveI := he
  obtain ⟨w, rfl⟩ : ∃ w, e.base w = b₀ := ⟨(inv e).base b₀, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  refine ⟨C.subschemeι.base ((pullback.fst (C.subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))).base w), ?_, ?_⟩
  · have hmem : C.subschemeι.base ((pullback.fst (C.subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))).base w) ∈
        Set.range C.subschemeι.base := ⟨_, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at hmem
    exact hmem
  · have := congrArg (fun φ => φ.base w) hcomp
    simp only [Scheme.Hom.comp_apply] at this ⊢
    exact this.symm

theorem toDR_injective_of_mem_smoothLocus (y₀ y₁ : 𝔛reg.Y) (h : 𝔛reg.toDR.base y₀ = 𝔛reg.toDR.base y₁)
    (hW : 𝔛reg.toDR.base y₀ ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus)) :
    y₀ = y₁ := by
  haveI := 𝔛reg.toDR_iso_smoothLocus
  set W := (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus) with hWdef
  have h0 : y₀ ∈ 𝔛reg.toDR ⁻¹ᵁ W := hW
  have h1 : y₁ ∈ 𝔛reg.toDR ⁻¹ᵁ W := by change 𝔛reg.toDR.base y₁ ∈ W; rw [← h]; exact hW
  have hinj := (𝔛reg.toDR ∣_ W).isOpenEmbedding.injective
  have key : (𝔛reg.toDR ∣_ W).base ⟨y₀, h0⟩ = (𝔛reg.toDR ∣_ W).base ⟨y₁, h1⟩ := by
    apply Subtype.ext
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    exact h
  exact congrArg Subtype.val (hinj key)

theorem chainPos_zero {node : Type} (width : node → ℕ) (n : node) :
    DRResolvedModelPackage.chainPos width n 0 = Sum.inl 0 := by
  simp [DRResolvedModelPackage.chainPos]

theorem chainPos_one_ne {node : Type} (width : node → ℕ) (n : node) :
    DRResolvedModelPackage.chainPos width n 1 ≠ Sum.inl 0 := by
  unfold DRResolvedModelPackage.chainPos
  split_ifs <;> simp_all

theorem caseB_inf (hker : ∀ a ∈ IsLocalRing.maximalIdeal O, toκ a = 0)
    (y₀ : 𝔛reg.Y) (hy₀ : y₀ ∈ (𝔛reg.comp (Sum.inl 0)).support)
    (honly : ∀ v, v ≠ Sum.inl 0 → y₀ ∉ (𝔛reg.comp v).support)
    (hbase : 𝔛reg.toBase.base y₀ = IsLocalRing.closedPoint O)
    (hB : ∃ c₀ : (𝔛.ratModel κ).C, (𝔛.compInf κ).base c₀ ∈ Set.range (𝔛.compZero κ).base ∧
      ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base c₀ = 𝔛reg.toDR.base y₀) : False := by
  classical
  obtain ⟨c₀, ha0, haz⟩ := hB
  obtain ⟨e, he, -, hcomp⟩ := 𝔛reg.strict_iso_inf
  haveI := he
  haveI : IsClosedImmersion (𝔛.compInf κ) := 𝔛.compInf_isClosedImmersion κ
  haveI : IsClosedImmersion (𝔛.compZero κ) := 𝔛.compZero_isClosedImmersion κ

  have hξ : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base ((𝔛.compInf κ).base c₀) ∉
      (𝔛.smoothLocus : Set ↥(DRModel p)) := fun h =>
    (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _).mp h
      ⟨⟨c₀, rfl⟩, ha0⟩
  have hfstz : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (𝔛reg.toDR.base y₀) =
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base ((𝔛.compInf κ).base c₀) := by
    rw [← haz, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (pullback.fst _ _), baseChangeMap_fst]

  have hbase_of : ∀ y : 𝔛reg.Y, 𝔛reg.toDR.base y = 𝔛reg.toDR.base y₀ → 𝔛reg.toBase.base y = IsLocalRing.closedPoint O := by
    intro y hy
    rw [← hbase, ← 𝔛reg.toDR_over, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]

  let P := {y : 𝔛reg.Y // y ∈ (𝔛reg.comp (Sum.inl 0)).support ∧ 𝔛reg.toDR.base y = 𝔛reg.toDR.base y₀}
  let S := {n : 𝔛reg.node // (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base
    (𝔛reg.nodeEquiv n) = 𝔛reg.toDR.base y₀}

  have hw0 : ∀ n : 𝔛reg.node, 0 < 𝔛reg.width n := fun n => 𝔛reg.one_le_width n
  have edge_mem : ∀ n : S, 𝔛reg.edgePt n.1 ⟨0, hw0 n.1⟩ ∈ (𝔛reg.comp (Sum.inl 0)).support ∧
      𝔛reg.toDR.base (𝔛reg.edgePt n.1 ⟨0, hw0 n.1⟩) = 𝔛reg.toDR.base y₀ := by
    intro n
    constructor
    · have := (𝔛reg.edgePt_mem n.1 ⟨0, hw0 n.1⟩).1
      rwa [show DRResolvedModelPackage.chainPos 𝔛reg.width n.1 ((⟨0, hw0 n.1⟩ : Fin (𝔛reg.width n.1)) : ℕ) = Sum.inl 0 from
        chainPos_zero 𝔛reg.width n.1] at this
    · rw [𝔛reg.edgePt_over]; exact n.2
  let ε : S → P := fun n => ⟨𝔛reg.edgePt n.1 ⟨0, hw0 n.1⟩, edge_mem n⟩
  have hε : Function.Injective ε := by
    intro n n' h
    have h1 : 𝔛reg.edgePt n.1 ⟨0, hw0 n.1⟩ = 𝔛reg.edgePt n'.1 ⟨0, hw0 n'.1⟩ := congrArg Subtype.val h
    have h2 := 𝔛reg.edgePt_injective (a₁ := ⟨n.1, ⟨0, hw0 n.1⟩⟩) (a₂ := ⟨n'.1, ⟨0, hw0 n'.1⟩⟩) h1
    exact Subtype.ext (congrArg Sigma.fst h2)

  have hex : ∀ y : P, ∃ (n : 𝔛reg.node)
      (w : ↥(pullback ((𝔛reg.comp (Sum.inl 0)).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ)))),
      (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n) =
          𝔛reg.toDR.base y₀ ∧
        (𝔛reg.comp (Sum.inl 0)).subschemeι.base
            ((pullback.fst ((𝔛reg.comp (Sum.inl 0)).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))).base w) = y.1 ∧
        (𝔛.compInf κ).base (e.base w) = ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)) ≫ 𝔛.compInf κ).base (𝔛reg.nodeEquiv n) := by
    rintro ⟨y, hyC, hyz⟩
    have hy' : y ∈ Set.range (𝔛reg.comp (Sum.inl 0)).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hyC
    obtain ⟨y', rfl⟩ := hy'
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (𝔛reg.comp (Sum.inl 0)).subschemeι ≫ 𝔛reg.toBase)
      (g := Spec.map (CommRingCat.ofHom toκ)) y' (IsLocalRing.closedPoint κ)
      (by rw [Scheme.Hom.comp_apply, hbase_of _ hyz, specMap_closedPoint toκ hker])

    have ha : ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base (e.base w) = 𝔛reg.toDR.base y₀ := by
      have := congrArg (fun φ => φ.base w) hcomp
      simp only [Scheme.Hom.comp_apply] at this ⊢
      rw [this, hw, hyz]

    have hns : (𝔛.compInf κ).base (e.base w) ∉
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
      intro h
      apply hξ
      change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base ((𝔛.compInf κ).base (e.base w)) ∈
        (𝔛.smoothLocus : Set ↥(DRModel p)) at h
      rwa [← baseChangeMap_fst (p := p) toκ, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (DRModel.baseChangeMap toκ), ha, hfstz] at h
    have hboth := not_not.mp ((not_congr
      (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _)).mp hns)
    obtain ⟨-, ⟨b, hb⟩⟩ := hboth
    obtain ⟨x, hx, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝔛.compInf κ) (g := 𝔛.compZero κ) (e.base w) b hb.symm
    refine ⟨𝔛reg.nodeEquiv.symm x, w, ?_, by rw [hw], ?_⟩
    · rw [Equiv.apply_symm_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
      simpa only [Scheme.Hom.comp_apply] using ha
    · rw [Equiv.apply_symm_apply, Scheme.Hom.comp_apply, hx]
  choose φ w hφz hφy hφa using hex
  let π : P → S := fun y => ⟨φ y, hφz y⟩
  have hπ : Function.Injective π := by
    intro y y' h
    have hn : φ y = φ y' := congrArg Subtype.val h
    have h1 : (𝔛.compInf κ).base (e.base (w y)) = (𝔛.compInf κ).base (e.base (w y')) := by rw [hφa, hφa, hn]
    have h2 : e.base (w y) = e.base (w y') := (𝔛.compInf κ).isClosedEmbedding.injective h1
    have h3 : w y = w y' := e.isOpenEmbedding.injective h2
    apply Subtype.ext
    rw [← hφy y, ← hφy y', h3]

  haveI : Finite P := Finite.of_injective π hπ
  have hcard : Nat.card P = Nat.card S :=
    le_antisymm (Nat.card_le_card_of_injective π hπ) (Nat.card_le_card_of_injective ε hε)
  have hsurj : Function.Surjective ε := (hε.bijective_of_nat_card_le hcard.le).2
  obtain ⟨n, hn⟩ := hsurj ⟨y₀, hy₀, rfl⟩
  have hy₀edge : 𝔛reg.edgePt n.1 ⟨0, hw0 n.1⟩ = y₀ := congrArg Subtype.val hn
  have hmem1 := (𝔛reg.edgePt_mem n.1 ⟨0, hw0 n.1⟩).2
  rw [hy₀edge] at hmem1
  exact honly _ (by simpa using chainPos_one_ne 𝔛reg.width n.1) hmem1

theorem chainPos_width {node : Type} (width : node → ℕ) (n : node) (h : 1 ≤ width n) :
    DRResolvedModelPackage.chainPos width n (width n - 1 + 1) = Sum.inl 1 := by
  unfold DRResolvedModelPackage.chainPos
  split_ifs <;> first | simp_all | omega

theorem chainPos_width_pred_ne {node : Type} (width : node → ℕ) (n : node) (h : 1 ≤ width n) :
    DRResolvedModelPackage.chainPos width n (width n - 1) ≠ Sum.inl 1 := by
  unfold DRResolvedModelPackage.chainPos
  split_ifs <;> first | simp_all | omega

theorem caseB_zero (hker : ∀ a ∈ IsLocalRing.maximalIdeal O, toκ a = 0)
    (y₀ : 𝔛reg.Y) (hy₀ : y₀ ∈ (𝔛reg.comp (Sum.inl 1)).support)
    (honly : ∀ v, v ≠ Sum.inl 1 → y₀ ∉ (𝔛reg.comp v).support)
    (hbase : 𝔛reg.toBase.base y₀ = IsLocalRing.closedPoint O)
    (hB : ∃ c₀ : (𝔛.ratModel κ).C, (𝔛.compZero κ).base c₀ ∈ Set.range (𝔛.compInf κ).base ∧
      ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base c₀ = 𝔛reg.toDR.base y₀) : False := by
  classical
  obtain ⟨c₀, ha0, haz⟩ := hB
  obtain ⟨e, he, -, hcomp⟩ := 𝔛reg.strict_iso_zero
  haveI := he
  haveI : IsClosedImmersion (𝔛.compInf κ) := 𝔛.compInf_isClosedImmersion κ
  haveI : IsClosedImmersion (𝔛.compZero κ) := 𝔛.compZero_isClosedImmersion κ

  have hξ : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base ((𝔛.compZero κ).base c₀) ∉
      (𝔛.smoothLocus : Set ↥(DRModel p)) := fun h =>
    (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _).mp h
      ⟨ha0, ⟨c₀, rfl⟩⟩
  have hfstz : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (𝔛reg.toDR.base y₀) =
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base ((𝔛.compZero κ).base c₀) := by
    rw [← haz, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (pullback.fst _ _), baseChangeMap_fst]

  have hbase_of : ∀ y : 𝔛reg.Y, 𝔛reg.toDR.base y = 𝔛reg.toDR.base y₀ → 𝔛reg.toBase.base y = IsLocalRing.closedPoint O := by
    intro y hy
    rw [← hbase, ← 𝔛reg.toDR_over, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]

  let P := {y : 𝔛reg.Y // y ∈ (𝔛reg.comp (Sum.inl 1)).support ∧ 𝔛reg.toDR.base y = 𝔛reg.toDR.base y₀}
  let S := {n : 𝔛reg.node // (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base
    (𝔛reg.nodeEquiv n) = 𝔛reg.toDR.base y₀}

  have hw0 : ∀ n : 𝔛reg.node, 𝔛reg.width n - 1 < 𝔛reg.width n := fun n => by have := 𝔛reg.one_le_width n; omega
  have edge_mem : ∀ n : S, 𝔛reg.edgePt n.1 ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩ ∈ (𝔛reg.comp (Sum.inl 1)).support ∧
      𝔛reg.toDR.base (𝔛reg.edgePt n.1 ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩) = 𝔛reg.toDR.base y₀ := by
    intro n
    constructor
    · have := (𝔛reg.edgePt_mem n.1 ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩).2
      rwa [show DRResolvedModelPackage.chainPos 𝔛reg.width n.1 (((⟨𝔛reg.width n.1 - 1, hw0 n.1⟩ : Fin (𝔛reg.width n.1)) : ℕ) + 1) =
        Sum.inl 1 from chainPos_width 𝔛reg.width n.1 (𝔛reg.one_le_width n.1)] at this
    · rw [𝔛reg.edgePt_over]; exact n.2
  let ε : S → P := fun n => ⟨𝔛reg.edgePt n.1 ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩, edge_mem n⟩
  have hε : Function.Injective ε := by
    intro n n' h
    have h1 : 𝔛reg.edgePt n.1 ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩ = 𝔛reg.edgePt n'.1 ⟨𝔛reg.width n'.1 - 1, hw0 n'.1⟩ :=
      congrArg Subtype.val h
    have h2 := 𝔛reg.edgePt_injective (a₁ := ⟨n.1, ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩⟩) (a₂ := ⟨n'.1, ⟨𝔛reg.width n'.1 - 1, hw0 n'.1⟩⟩) h1
    exact Subtype.ext (congrArg Sigma.fst h2)

  have hex : ∀ y : P, ∃ (n : 𝔛reg.node)
      (w : ↥(pullback ((𝔛reg.comp (Sum.inl 1)).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ)))),
      (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n) =
          𝔛reg.toDR.base y₀ ∧
        (𝔛reg.comp (Sum.inl 1)).subschemeι.base
            ((pullback.fst ((𝔛reg.comp (Sum.inl 1)).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))).base w) = y.1 ∧
        (𝔛.compZero κ).base (e.base w) = ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)) ≫ 𝔛.compZero κ).base (𝔛reg.nodeEquiv n) := by
    rintro ⟨y, hyC, hyz⟩
    have hy' : y ∈ Set.range (𝔛reg.comp (Sum.inl 1)).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hyC
    obtain ⟨y', rfl⟩ := hy'
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (𝔛reg.comp (Sum.inl 1)).subschemeι ≫ 𝔛reg.toBase)
      (g := Spec.map (CommRingCat.ofHom toκ)) y' (IsLocalRing.closedPoint κ)
      (by rw [Scheme.Hom.comp_apply, hbase_of _ hyz, specMap_closedPoint toκ hker])

    have ha : ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base (e.base w) = 𝔛reg.toDR.base y₀ := by
      have := congrArg (fun φ => φ.base w) hcomp
      simp only [Scheme.Hom.comp_apply] at this ⊢
      rw [this, hw, hyz]

    have hns : (𝔛.compZero κ).base (e.base w) ∉
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
      intro h
      apply hξ
      change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base ((𝔛.compZero κ).base (e.base w)) ∈
        (𝔛.smoothLocus : Set ↥(DRModel p)) at h
      rwa [← baseChangeMap_fst (p := p) toκ, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (DRModel.baseChangeMap toκ), ha, hfstz] at h
    have hboth := not_not.mp ((not_congr
      (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _)).mp hns)
    obtain ⟨⟨b, hb⟩, -⟩ := hboth
    obtain ⟨x, -, hx⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝔛.compInf κ) (g := 𝔛.compZero κ) b (e.base w) hb
    refine ⟨𝔛reg.nodeEquiv.symm x, w, ?_, by rw [hw], ?_⟩
    · rw [Equiv.apply_symm_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
        ← Scheme.Hom.comp_apply (pullback.fst _ _) (𝔛.compInf κ), pullback.condition, Scheme.Hom.comp_apply, hx]
      simpa only [Scheme.Hom.comp_apply] using ha
    · rw [Equiv.apply_symm_apply, Scheme.Hom.comp_apply, hx]
  choose φ w hφz hφy hφa using hex
  let π : P → S := fun y => ⟨φ y, hφz y⟩
  have hπ : Function.Injective π := by
    intro y y' h
    have hn : φ y = φ y' := congrArg Subtype.val h
    have h1 : (𝔛.compZero κ).base (e.base (w y)) = (𝔛.compZero κ).base (e.base (w y')) := by rw [hφa, hφa, hn]
    have h2 : e.base (w y) = e.base (w y') := (𝔛.compZero κ).isClosedEmbedding.injective h1
    have h3 : w y = w y' := e.isOpenEmbedding.injective h2
    apply Subtype.ext
    rw [← hφy y, ← hφy y', h3]

  haveI : Finite P := Finite.of_injective π hπ
  have hcard : Nat.card P = Nat.card S :=
    le_antisymm (Nat.card_le_card_of_injective π hπ) (Nat.card_le_card_of_injective ε hε)
  have hsurj : Function.Surjective ε := (hε.bijective_of_nat_card_le hcard.le).2
  obtain ⟨n, hn⟩ := hsurj ⟨y₀, hy₀, rfl⟩
  have hy₀edge : 𝔛reg.edgePt n.1 ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩ = y₀ := congrArg Subtype.val hn
  have hmem1 := (𝔛reg.edgePt_mem n.1 ⟨𝔛reg.width n.1 - 1, hw0 n.1⟩).1
  rw [hy₀edge] at hmem1
  exact honly _ (by simpa using chainPos_width_pred_ne 𝔛reg.width n.1 (𝔛reg.one_le_width n.1)) hmem1

end StrictCompAux

open StrictCompAux in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (c : X0MqComponents 𝔛reg.width)
    (hc : t.1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp c).support ∧
      ∀ w, w ≠ c → t.1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support) :
    (c = Sum.inl 0 ↔ ((t.1 ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) ∈ Set.range ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base ∧ (t.1 ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) ∉ Set.range ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base)) ∧
    (c = Sum.inl 1 ↔ ((t.1 ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) ∈ Set.range ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base ∧ (t.1 ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) ∉ Set.range ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base)) := by
  classical

  have hp : p.Prime := Fact.out
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal O, toκ a = 0 := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_natCast, CharP.cast_eq_zero κ p, zero_mul]
  set y₀ := t.1.base (IsLocalRing.closedPoint O) with hy₀def
  have hbase : 𝔛reg.toBase.base y₀ = IsLocalRing.closedPoint O := by
    rw [hy₀def, ← Scheme.Hom.comp_apply, t.2]; rfl
  have hz : (t.1 ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = 𝔛reg.toDR.base y₀ := Scheme.Hom.comp_apply _ _ _
  rw [hz]
  set z := 𝔛reg.toDR.base y₀ with hzdef

  have hcross : ∀ n : 𝔛reg.node,
      (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n) ∈
          Set.range ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base ∧
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n) ∈
          Set.range ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base := by
    intro n
    refine ⟨⟨(pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base (𝔛reg.nodeEquiv n), ?_⟩,
      ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base (𝔛reg.nodeEquiv n), ?_⟩⟩
    · simp only [Scheme.Hom.comp_apply]
    · simp only [Scheme.Hom.comp_apply]
      rw [← Scheme.Hom.comp_apply (pullback.snd _ _) (𝔛.compZero κ), ← pullback.condition, Scheme.Hom.comp_apply]

  have HAinf := exists_comp_eq_toDR 𝔛 toκ 𝔛reg (𝔛reg.comp (Sum.inl 0)) (𝔛.compInf κ) 𝔛reg.strict_iso_inf hker y₀
  have HAzero := exists_comp_eq_toDR 𝔛 toκ 𝔛reg (𝔛reg.comp (Sum.inl 1)) (𝔛.compZero κ) 𝔛reg.strict_iso_zero hker y₀
  have HBinf := exists_mem_support_toDR_eq 𝔛 toκ 𝔛reg (𝔛reg.comp (Sum.inl 0)) (𝔛.compInf κ) 𝔛reg.strict_iso_inf
  have HBzero := exists_mem_support_toDR_eq 𝔛 toκ 𝔛reg (𝔛reg.comp (Sum.inl 1)) (𝔛.compZero κ) 𝔛reg.strict_iso_zero

  have fwd_inf : c = Sum.inl 0 → (z ∈ Set.range ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base ∧
      z ∉ Set.range ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base) := by
    rintro rfl
    obtain ⟨c₀, hc₀⟩ := HAinf hc.1 hbase
    refine ⟨⟨c₀, hc₀⟩, ?_⟩
    rintro ⟨b₀, hb₀⟩
    obtain ⟨y₁, hy₁, hy₁z⟩ := HBzero b₀
    by_cases hA : (𝔛.compInf κ).base c₀ ∈ Set.range (𝔛.compZero κ).base
    ·
      exact caseB_inf 𝔛 toκ 𝔛reg hker y₀ hc.1 (fun v hv => hc.2 v hv) hbase ⟨c₀, hA, hc₀⟩
    ·
      have hsm : (𝔛.compInf κ).base c₀ ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⁻¹ᵁ 𝔛.smoothLocus) :=
        (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _).mpr
          (fun h => hA h.2)
      have hW : z ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus) := by
        change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base z ∈
          (𝔛.smoothLocus : Set ↥(DRModel p))
        rw [hzdef, ← hc₀, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (pullback.fst _ _), baseChangeMap_fst]
        exact hsm
      have := toDR_injective_of_mem_smoothLocus 𝔛 toκ 𝔛reg y₀ y₁ (hy₁z.trans hb₀).symm hW
      exact hc.2 (Sum.inl 1) (by simp) (this ▸ hy₁)
  have fwd_zero : c = Sum.inl 1 → (z ∈ Set.range ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base ∧
      z ∉ Set.range ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base) := by
    rintro rfl
    obtain ⟨c₀, hc₀⟩ := HAzero hc.1 hbase
    refine ⟨⟨c₀, hc₀⟩, ?_⟩
    rintro ⟨b₀, hb₀⟩
    obtain ⟨y₁, hy₁, hy₁z⟩ := HBinf b₀
    by_cases hA : (𝔛.compZero κ).base c₀ ∈ Set.range (𝔛.compInf κ).base
    · exact caseB_zero 𝔛 toκ 𝔛reg hker y₀ hc.1 (fun v hv => hc.2 v hv) hbase ⟨c₀, hA, hc₀⟩
    · have hsm : (𝔛.compZero κ).base c₀ ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⁻¹ᵁ 𝔛.smoothLocus) :=
        (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ _).mpr
          (fun h => hA h.1)
      have hW : z ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus) := by
        change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base z ∈
          (𝔛.smoothLocus : Set ↥(DRModel p))
        rw [hzdef, ← hc₀, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (pullback.fst _ _), baseChangeMap_fst]
        exact hsm
      have := toDR_injective_of_mem_smoothLocus 𝔛 toκ 𝔛reg y₀ y₁ (hy₁z.trans hb₀).symm hW
      exact hc.2 (Sum.inl 0) (by simp) (this ▸ hy₁)

  have exc : ∀ (n : 𝔛reg.node) (i : Fin (𝔛reg.width n - 1)), c = Sum.inr ⟨n, i⟩ →
      z ∈ Set.range ((𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base ∧
        z ∈ Set.range ((𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base := by
    rintro n i rfl
    rw [hzdef, 𝔛reg.exc_image n i y₀ hc.1]
    exact hcross n

  refine ⟨⟨fwd_inf, fun h => ?_⟩, ⟨fwd_zero, fun h => ?_⟩⟩
  · rcases c with j | ⟨n, i⟩
    · fin_cases j
      · rfl
      · exact absurd (fwd_zero rfl).1 h.2
    · exact absurd (exc n i rfl).2 h.2
  · rcases c with j | ⟨n, i⟩
    · fin_cases j
      · exact absurd (fwd_inf rfl).1 h.2
      · rfl
    · exact absurd (exc n i rfl).1 h.2

end S_ModularCurve_DRResolvedModelPackage_eq_inl_iff_toDR_base_mem_range_compInf_of_mem_comp_support
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_eq_inl_iff_toDR_base_mem_range_compInf_of_mem_comp_support (solution)
