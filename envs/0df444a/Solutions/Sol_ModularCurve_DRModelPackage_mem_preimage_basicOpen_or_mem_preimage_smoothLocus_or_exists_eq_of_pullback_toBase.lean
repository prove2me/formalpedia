-- Prove2me | solution 1 for ModularCurve.DRModelPackage.mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/35f5851e-6305-56c2-9b61-4f44fa18af05

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero" namespace DRModel p2m_export "ModularCurve.DRModel" "baseChangeMap toBase" end ModularCurve.DRModel
p2m_open_scoped "ModularCurve ModularCurve.DRModel" in

theorem ModularCurve.DRModel.exists_baseChangeMap_eq_of_natCast_mem
    (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] (toκ : O →+* κ)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hx : ((p : ℕ) : O) ∈ ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x).asIdeal) :
    ∃ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      (DRModel.baseChangeMap (p := p) toκ).base y = x := by

  have hOpt : ∀ (𝔮 : Ideal O) [𝔮.IsPrime], ((p : ℕ) : O) ∈ 𝔮 → 𝔮 = IsLocalRing.maximalIdeal O := by
    intro 𝔮 _ hq
    have hle : IsLocalRing.maximalIdeal O ≤ 𝔮 := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]; exact hq
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top ‹_›) hle).symm
  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    haveI : (RingHom.ker toκ).IsPrime := RingHom.ker_isPrime toκ
    exact hOpt _ (by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero])
  have hz : (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x = IsLocalRing.closedPoint O :=
    PrimeSpectrum.ext (hOpt _ hx)
  have hr := Scheme.Pullback.range_map (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
    (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.ext_int (toκ.comp (algebraMap ℤ O)) (algebraMap ℤ κ)])
  have hx' : x ∈ Set.range ⇑(pullback.map (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
    (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.ext_int (toκ.comp (algebraMap ℤ O)) (algebraMap ℤ κ)])) := by
    rw [hr]
    refine ⟨by simp, ?_⟩
    show (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x ∈
      Set.range (Spec.map (CommRingCat.ofHom toκ)).base
    refine ⟨IsLocalRing.closedPoint κ, ?_⟩
    rw [hz]
    apply PrimeSpectrum.ext
    change Ideal.comap toκ (IsLocalRing.closedPoint κ).asIdeal = (IsLocalRing.closedPoint O).asIdeal
    rw [show (IsLocalRing.closedPoint κ).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot (R := κ) |>.symm ▸ rfl,
      ← RingHom.ker_eq_comap_bot, hker]
    rfl
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy⟩

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModelPackage_mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase.ModularCurve ModularCurve.DRModelPackage in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) :
    x ∈ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) ∨
    x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus ∨
    ∃ n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      x = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n := by
  classical
  by_cases h1 : x ∈ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  · exact Or.inl h1
  by_cases h2 : x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus
  · exact Or.inr (Or.inl h2)
  right; right

  have hp : ((p : ℕ) : O) ∈ ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x).asIdeal := by
    by_contra hn
    exact h1 hn

  obtain ⟨y, hy⟩ := ModularCurve.DRModel.exists_baseChangeMap_eq_of_natCast_mem p O hϖ toκ x hp

  have hbc₁ : DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  have hfst : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base y =
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x := by
    rw [← hy]
    exact (congrArg (fun k => k.base y) hbc₁).symm
  have hy2 : ¬ y ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ 𝔛.smoothLocus := by
    intro hmem
    apply h2
    show (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base x ∈ 𝔛.smoothLocus
    rw [← hfst]
    exact hmem
  rw [ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero, not_not] at hy2
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hy2

  obtain ⟨n, hn₁, hn₂⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
  refine ⟨n, ?_⟩
  rw [← hy, ← ha, ← hn₁]
  rfl

end S_ModularCurve_DRModelPackage_mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase (solution)
