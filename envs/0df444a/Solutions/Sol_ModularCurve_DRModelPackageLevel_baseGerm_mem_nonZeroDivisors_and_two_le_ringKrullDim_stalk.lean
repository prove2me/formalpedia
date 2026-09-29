-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d2c22275-5122-53d5-8ca4-458f78054dee

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isIntegral_pullback_toBase_specMap
import Theorems.Thm_ModularCurve_DRModelPackageLevel_not_branchIdeal_le_branchIdeal_crossingPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hinf : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) (hzero : 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) :
    DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O) ∈ nonZeroDivisors ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) ∧
    (2 : WithBot ℕ∞) ≤ ringKrullDim ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) := by
  haveI : IsIntegral (DRLevel.XO (N₀ := N₀) ρO) :=
    ModularCurve.DRModelPackageLevel.isIntegral_pullback_toBase_specMap N₀ q hqN 𝔛 O hϖ ρO
  haveI : Flat (DRLevel.XO.toBase (N₀ := N₀) ρO) := by
    haveI := 𝔛.flat
    infer_instance
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  have hp0 : ((q : ℕ) : O) ≠ 0 :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖ).ne_zero

  have hsec : (DRLevel.XO.toBase (N₀ := N₀) ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((q : ℕ) : O)) ≠ 0 := by
    intro h0
    let η : Spec (CommRingCat.of O) := ⟨⊥, Ideal.isPrime_bot⟩
    have hspec : η ⤳ (DRLevel.XO.toBase (N₀ := N₀) ρO).base (𝔛.crossingPt ρO toκ n) :=
      (PrimeSpectrum.le_iff_specializes η _).mp bot_le
    obtain ⟨y, -, hy⟩ := Flat.generalizingMap (DRLevel.XO.toBase (N₀ := N₀) ρO) hspec
    have hunit : IsUnit ((Spec (CommRingCat.of O)).presheaf.germ ⊤ ((DRLevel.XO.toBase (N₀ := N₀) ρO).base y) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((q : ℕ) : O))) := by
      rw [← Scheme.mem_basicOpen_top, basicOpen_eq_of_affine]
      change (DRLevel.XO.toBase (N₀ := N₀) ρO).base y ∈ PrimeSpectrum.basicOpen ((q : ℕ) : O)
      rw [hy]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr (by simp [η, hp0])
    have := hunit.map ((DRLevel.XO.toBase (N₀ := N₀) ρO).stalkMap y).hom
    rw [Scheme.Hom.germ_stalkMap_apply] at this
    change IsUnit ((DRLevel.XO (N₀ := N₀) ρO).presheaf.germ ⊤ y trivial
      ((DRLevel.XO.toBase (N₀ := N₀) ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((q : ℕ) : O)))) at this
    rw [h0, map_zero] at this
    exact not_isUnit_zero this
  have hne : DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O) ≠ 0 := by
    intro h
    apply hsec
    apply germ_injective_of_isIntegral _ (𝔛.crossingPt ρO toκ n) (U := ⊤) trivial
    rw [map_zero]
    exact h
  refine ⟨mem_nonZeroDivisors_of_ne_zero hne, ?_⟩

  have htoκ : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top toκ) ?_).symm
    rw [hϖ, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hξbase : (DRLevel.XO.toBase (N₀ := N₀) ρO).base (𝔛.ξinf ρO toκ) ∉
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    intro hmem
    have h1 : (DRLevel.XO.toBase (N₀ := N₀) ρO).base (𝔛.ξinf ρO toκ) =
        (Spec.map (CommRingCat.ofHom toκ)).base
          ((𝔛.comp κ (toκ.comp ρO) 0 ≫ pullback.snd _ _).base (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc,
        show DRLevel.bcMap ρO toκ ≫ DRLevel.XO.toBase (N₀ := N₀) ρO = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) from
          pullback.lift_snd _ _ _,
        ← Category.assoc, Scheme.Hom.comp_apply]
    rw [h1] at hmem
    have hmem' := (PrimeSpectrum.mem_basicOpen _ _).mp hmem
    apply hmem'
    change ((q : ℕ) : O) ∈ Ideal.comap toκ _
    have : ((q : ℕ) : O) ∈ RingHom.ker toκ := by rw [htoκ, hϖ]; exact Ideal.mem_span_singleton_self _
    exact Ideal.ker_le_comap toκ this
  have hpP : DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O) ∈ Scheme.branchIdeal hinf := by
    rw [Scheme.mem_branchIdeal_iff]
    change ((DRLevel.XO (N₀ := N₀) ρO).presheaf.germ ⊤ _ trivial ≫ (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalkSpecializes hinf).hom _ ∈ _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    have key : (DRLevel.XO (N₀ := N₀) ρO).presheaf.germ ⊤ (𝔛.ξinf ρO toκ) trivial
        ((DRLevel.XO.toBase (N₀ := N₀) ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((q : ℕ) : O))) =
        ((DRLevel.XO.toBase (N₀ := N₀) ρO).stalkMap (𝔛.ξinf ρO toκ)).hom
          ((Spec (CommRingCat.of O)).presheaf.germ ⊤ ((DRLevel.XO.toBase (N₀ := N₀) ρO).base (𝔛.ξinf ρO toκ)) trivial
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((q : ℕ) : O))) := by
      rw [Scheme.Hom.germ_stalkMap_apply]; rfl
    change (DRLevel.XO (N₀ := N₀) ρO).presheaf.germ ⊤ (𝔛.ξinf ρO toκ) trivial
        ((DRLevel.XO.toBase (N₀ := N₀) ρO).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((q : ℕ) : O))) ∈ _
    rw [key]
    apply map_nonunit
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top,
      basicOpen_eq_of_affine]
    exact hξbase

  have hbot : (⊥ : Ideal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n))) < Scheme.branchIdeal hinf :=
    bot_lt_iff_ne_bot.mpr fun h => hne (Ideal.mem_bot.mp (h ▸ hpP))
  obtain ⟨hQP, -⟩ := ModularCurve.DRModelPackageLevel.not_branchIdeal_le_branchIdeal_crossingPt N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero
  have htop : Scheme.branchIdeal hinf < IsLocalRing.maximalIdeal _ := by
    refine (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)).lt_of_ne fun h => hQP ?_
    rw [h]
    exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  let qq : Fin 3 → PrimeSpectrum ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) :=
    ![⟨⊥, Ideal.isPrime_bot⟩, ⟨Scheme.branchIdeal hinf, inferInstance⟩, IsLocalRing.closedPoint _]
  let s : LTSeries (PrimeSpectrum ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n))) :=
    { length := 2, toFun := qq, step := by
        intro i
        fin_cases i
        · exact hbot
        · exact htop }
  have := Order.LTSeries.length_le_krullDim s
  simpa [ringKrullDim, s] using this

end S_ModularCurve_DRModelPackageLevel_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk (solution)
