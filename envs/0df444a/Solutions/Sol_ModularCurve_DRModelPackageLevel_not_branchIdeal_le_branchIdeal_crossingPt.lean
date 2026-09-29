-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.not_branchIdeal_le_branchIdeal_crossingPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f1406cb3-f25f-54c2-858e-d6b59b3be03a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackageLevel_eq_xi_of_specializes
import Theorems.Thm_ModularCurve_DRModelPackageLevel_xiInf_ne_xiZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_not_branchIdeal_le_branchIdeal_crossingPt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve IsLocalRing

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace ECL_NotLe
open AlgebraicGeometry.Scheme

universe u

private theorem comap_maximalIdeal_eq_map_of_isLocalization_atPrime
    {A Sp Sq : Type*} [CommRing A] [CommRing Sp] [CommRing Sq] [Algebra A Sp] [Algebra A Sq]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] [IsLocalization.AtPrime Sp p] [IsLocalization.AtPrime Sq q]
    [IsLocalRing Sq] (φ : Sp →+* Sq) (hφ : ∀ a, φ (algebraMap A Sp a) = algebraMap A Sq a) :
    (maximalIdeal Sq).comap φ = q.map (algebraMap A Sp) := by
  apply le_antisymm
  · intro z hz
    rw [Ideal.mem_comap] at hz
    set a : A := (IsLocalization.sec p.primeCompl z).1
    set s : p.primeCompl := (IsLocalization.sec p.primeCompl z).2
    have hz' : IsLocalization.mk' Sp a s = z := IsLocalization.mk'_sec Sp z
    rw [← hz'] at hz ⊢
    have h1 : IsLocalization.mk' Sp a s * algebraMap A Sp s = algebraMap A Sp a := IsLocalization.mk'_spec Sp a s
    have h2 : φ (IsLocalization.mk' Sp a s) * algebraMap A Sq s = algebraMap A Sq a := by
      rw [← hφ, ← hφ, ← map_mul, h1]
    have ha : a ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q, ← h2]
      exact Ideal.mul_mem_right _ _ hz
    have hu : IsUnit (algebraMap A Sp s) := IsLocalization.map_units Sp s
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, h1]
    exact Ideal.mem_map_of_mem _ ha
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q a).mpr ha

private theorem map_primeIdealOf_eq_branchIdeal {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {a x : X} (h : a ⤳ x)
    (hx : x ∈ U) (ha : a ∈ U) :
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
    ((hU.primeIdealOf ⟨a, ha⟩).asIdeal).map (algebraMap Γ(X, U) (X.presheaf.stalk x)) = branchIdeal h := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  letI := X.presheaf.algebra_section_stalk (⟨a, ha⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨a, ha⟩
  symm
  refine comap_maximalIdeal_eq_map_of_isLocalization_atPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (hU.primeIdealOf ⟨a, ha⟩).asIdeal (X.presheaf.stalkSpecializes h).hom (fun s => ?_)
  change (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U x hx).hom s) = (X.presheaf.germ U a ha).hom s
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

private theorem specializes_of_branchIdeal_le {X : Scheme.{u}} {a b x : X} (ha : a ⤳ x) (hb : b ⤳ x)
    (h : branchIdeal hb ≤ branchIdeal ha) : b ⤳ a := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have haU : a ∈ U := ha.mem_open U.isOpen hxU
  have hbU : b ∈ U := hb.mem_open U.isOpen hxU
  letI := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  rw [← map_primeIdealOf_eq_branchIdeal hU ha hxU haU, ← map_primeIdealOf_eq_branchIdeal hU hb hxU hbU] at h

  have hle : ∀ {c : X} (hc : c ⤳ x) (hcU : c ∈ U), hU.primeIdealOf ⟨c, hcU⟩ ≤ hU.primeIdealOf ⟨x, hxU⟩ := by
    intro c hc hcU
    have hsp : hU.fromSpec.base (hU.primeIdealOf ⟨c, hcU⟩) ⤳ hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) := by
      rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact hc
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp)
  have hdisj : ∀ {c : X} (hc : c ⤳ x) (hcU : c ∈ U),
      Disjoint ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl : Set Γ(X, U)) (hU.primeIdealOf ⟨c, hcU⟩).asIdeal :=
    fun hc hcU => Set.disjoint_left.mpr fun s hs hsQ => hs (hle hc hcU hsQ)
  have ea := IsLocalization.under_map_of_isPrime_disjoint (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (hU.primeIdealOf ⟨a, haU⟩).isPrime (hdisj ha haU)
  have eb := IsLocalization.under_map_of_isPrime_disjoint (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (hU.primeIdealOf ⟨b, hbU⟩).isPrime (hdisj hb hbU)
  have hab : hU.primeIdealOf ⟨b, hbU⟩ ≤ hU.primeIdealOf ⟨a, haU⟩ := by
    change (hU.primeIdealOf ⟨b, hbU⟩).asIdeal ≤ (hU.primeIdealOf ⟨a, haU⟩).asIdeal
    rw [← ea, ← eb]
    exact Ideal.comap_mono h
  have hsp := ((PrimeSpectrum.le_iff_specializes _ _).mp hab).map hU.fromSpec.base.hom.continuous
  rwa [hU.fromSpec_primeIdealOf ⟨b, hbU⟩, hU.fromSpec_primeIdealOf ⟨a, haU⟩] at hsp

end ECL_NotLe

open ECL_NotLe in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hinf : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) (hzero : 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) :
    ¬ Scheme.branchIdeal hzero ≤ Scheme.branchIdeal hinf ∧ ¬ Scheme.branchIdeal hinf ≤ Scheme.branchIdeal hzero := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  have hne := ModularCurve.DRModelPackageLevel.xiInf_ne_xiZero N₀ q hqN 𝔛 O ρO hϖ κ toκ
  have hmax := ModularCurve.DRModelPackageLevel.eq_xi_of_specializes N₀ q hqN 𝔛 O ρO hϖ κ toκ
  have hV : ∀ z : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)), (DRLevel.bcMap ρO toκ).base z ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    intro z h
    have hcomm : DRLevel.bcMap ρO toκ ≫ DRLevel.XO.toBase (N₀ := N₀) ρO = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) :=
      pullback.lift_snd _ _ _
    have h' : (DRLevel.bcMap ρO toκ ≫ DRLevel.XO.toBase (N₀ := N₀) ρO).base z ∈
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := h
    rw [hcomm] at h'
    change PrimeSpectrum.comap toκ ((pullback.snd (DRLevel.toBase N₀ q)
        (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base z) ∈ PrimeSpectrum.basicOpen ((q : ℕ) : O) at h'
    rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast,
      CharP.cast_eq_zero] at h'
    exact h' (Ideal.zero_mem _)
  have hVinf : 𝔛.ξinf ρO toκ ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    rw [show 𝔛.ξinf ρO toκ = (DRLevel.bcMap ρO toκ).base ((𝔛.comp κ (toκ.comp ρO) 0).base
      (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) from Scheme.Hom.comp_apply _ _ _]
    exact hV _
  have hVzero : 𝔛.ξzero ρO toκ ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    rw [show 𝔛.ξzero ρO toκ = (DRLevel.bcMap ρO toκ).base ((𝔛.comp κ (toκ.comp ρO) 1).base
      (genericPoint (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) from Scheme.Hom.comp_apply _ _ _]
    exact hV _
  constructor
  · intro h
    exact hne (hmax.1 _ hVzero (specializes_of_branchIdeal_le hinf hzero h)).symm
  · intro h
    exact hne (hmax.2 _ hVinf (specializes_of_branchIdeal_le hzero hinf h))

end S_ModularCurve_DRModelPackageLevel_not_branchIdeal_le_branchIdeal_crossingPt
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_not_branchIdeal_le_branchIdeal_crossingPt (solution)
