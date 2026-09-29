-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/02c7295a-1202-5c89-9944-9be164955167

import Theorems.Thm_ModularCurve_FullLevel_exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_three
import Theorems.Thm_ValuationSubring_exists_algEquiv_comap_eq_of_isGalois
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation
import Theorems.Thm_ModularCurve_FullLevel_ramificationIdx_comap_gauss_eq_one_of_levelH_of_eq_three
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
p2m_attr_erase "instance" "CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply"
p2m_attr_erase "simp" "AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open IsLocalRing

set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle : K₀ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (K₀' : IntermediateField L (LaurentSeries L))
    (hK₀' : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hle₀ : K₀ ≤ K₀') (hle' : K₀' ≤ K)
    (O₀' : ValuationSubring ↥K₀')
    (hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    letI : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra
    ∀ (B : ValuationSubring ↥K), (∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ B ↔ x ∈ O₀') →

      (∃ τ : ↥K ≃ₐ[L] ↥K, (∀ x : ↥K₀', τ (algebraMap ↥K₀' ↥K x) = algebraMap ↥K₀' ↥K x) ∧
        B = W₀.comap τ.toAlgHom.toRingHom) ∧

      (∃ hB : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ B ↔ x ∈ O₀,
        letI : Algebra ↥O₀ ↥B :=
          (((algebraMap ↥K₀ ↥K).comp O₀.subtype).codRestrict B.toSubring fun a => (hB a).mpr a.2).toAlgebra
        (IsLocalRing.maximalIdeal ↥O₀).ramificationIdx' (IsLocalRing.maximalIdeal ↥B) = 1 ∧
        ∃ _ : IsLocalHom (algebraMap ↥O₀ ↥B),
          Algebra.IsSeparable (IsLocalRing.ResidueField ↥O₀) (IsLocalRing.ResidueField ↥B)) := by
  classical
  letI algK : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI algK' : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra
  intro B hB'

  have hτex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_three q hq3 M' hqM' L ζ hζ K hK
  let τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K) := fun γ =>
    if h : γ ∈ CongruenceSubgroup.Gamma0 M' then (hτex γ h).choose else AlgEquiv.refl
  have hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ) := by
    intro γ h; simp only [τ, dif_pos h]; exact (hτex γ h).choose_spec

  obtain ⟨G, hGfin, hGmem⟩ :=
    ModularCurve.FullLevel.exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_three q hq3 M' hqM' L ζ hζ hι K hK τ hτ
  haveI : Finite ↥G := hGfin
  set SB : Set (↥K ≃ₐ[L] ↥K) := {σ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧ σ = τ γ} with hSBdef
  set GB : Subgroup (↥K ≃ₐ[L] ↥K) := Subgroup.closure SB with hGBdef
  have hGBle : GB ≤ G := by
    rw [hGBdef, Subgroup.closure_le]
    rintro σ ⟨γ, hγ, -, rfl⟩
    exact (hGmem _).mpr ⟨γ, hγ, rfl⟩
  haveI : Finite ↥GB := Finite.of_injective (fun g : ↥GB => (⟨g.1, hGBle g.2⟩ : ↥G))
    (fun a b h => Subtype.ext (by simpa using congrArg (fun x : ↥G => (x : ↥K ≃ₐ[L] ↥K)) h))
  haveI : FaithfulSMul ↥GB ↥K := ⟨fun {g h} hgh => by
    apply Subtype.ext; apply AlgEquiv.ext; intro x; exact hgh x⟩
  set E : Subfield ↥K := FixedPoints.subfield ↥GB ↥K with hEdef
  have memE : ∀ w : ↥K, w ∈ E ↔ ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 → τ γ w = w := by
    intro w
    rw [hEdef]
    show (∀ g : ↥GB, g • w = w) ↔ _
    constructor
    · intro h γ hγ hdvd
      exact h ⟨τ γ, Subgroup.subset_closure ⟨γ, hγ, hdvd, rfl⟩⟩
    · intro h g
      show (g.1 : ↥K ≃ₐ[L] ↥K) w = w
      refine Subgroup.closure_induction (p := fun σ _ => σ w = w) ?_ ?_ ?_ ?_ g.2
      · rintro σ ⟨γ, hγ, hdvd, rfl⟩; exact h γ hγ hdvd
      · rfl
      · intro σ ρ _ _ hσ hρ; show σ (ρ w) = w; rw [hρ, hσ]
      · intro σ _ hσ; show σ.symm w = w
        conv_lhs => rw [← hσ]
        exact σ.symm_apply_apply w

  have hFFB := ModularCurve.FullLevel.forall_isLevelAutAt_apply_eq_of_dvd_iff_mem_laurentBaseChange_gamma0_mul_of_eq_three q hq3 M' hqM' L ζ hζ hι K hK τ hτ
  have memE' : ∀ w : ↥K, w ∈ E ↔ ((w : ↥K) : LaurentSeries L) ∈ K₀' := by
    intro w; rw [memE, hFFB, hK₀']

  let V : ValuationSubring ↥E := W₀.comap E.subtype
  have hVmem : ∀ e : ↥E, e ∈ V ↔ (e : ↥K) ∈ W₀ := fun e => ValuationSubring.mem_comap

  have hVne : V ≠ ⊤ := by
    obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
    have hϖ : maximalIdeal A = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
    have hϖm : ϖ ∈ maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ

    set ϖK : ↥K := algebraMap L ↥K (algebraMap A L ϖ) with hϖKdef
    have hϖKE : ϖK ∈ E := by
      rw [memE]; intro γ hγ hdvd; rw [hϖKdef]; exact (τ γ).commutes _
    intro htop
    have hmem : (⟨ϖK, hϖKE⟩ : ↥E)⁻¹ ∈ V := by rw [htop]; trivial
    rw [hVmem] at hmem
    have hcoe : (((⟨ϖK, hϖKE⟩ : ↥E)⁻¹ : ↥E) : ↥K) = ϖK⁻¹ := rfl
    rw [hcoe, hW₀] at hmem
    obtain ⟨x, y, hy, hxy⟩ := hmem

    have hϖcoe : ((ϖK : ↥K) : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ L (PowerSeries.C (algebraMap A L ϖ)) := rfl
    have hϖ0 : ((ϖK : ↥K) : LaurentSeries L) ≠ 0 := by
      rw [hϖcoe]; intro h0
      have h1 : PowerSeries.C (algebraMap A L ϖ) = 0 := HahnSeries.ofPowerSeries_injective (by rw [h0]; simp)
      have h2 : algebraMap A L ϖ = 0 := by
        have := congrArg (PowerSeries.coeff 0) h1; simpa [PowerSeries.coeff_C] using this
      have h3 : ϖ = 0 := (IsFractionRing.injective A L) (by rw [h2, map_zero])
      exact hϖirr.ne_zero h3
    have hinvcoe : (((ϖK : ↥K)⁻¹ : ↥K) : LaurentSeries L) = ((ϖK : ↥K) : LaurentSeries L)⁻¹ := rfl
    rw [hinvcoe] at hxy
    have hyeq : HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C ϖ * x).map (algebraMap A L)) := by
      rw [map_mul, PowerSeries.map_C, map_mul, ← hϖcoe, ← hxy, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
    have hy' : y = PowerSeries.C ϖ * x :=
      PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L) (HahnSeries.ofPowerSeries_injective hyeq)
    apply hy
    rw [hy', map_mul, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr hϖm]
    simp
  haveI : IsDiscreteValuationRing ↥V :=
    ValuationSubring.isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation
      (ι := ((IntermediateField.val K).toRingHom).comp E.subtype) V (fun e => by rw [hVmem, hW₀]; rfl) hVne

  have hWover : ∀ e : ↥E, algebraMap ↥E ↥K e ∈ W₀ ↔ e ∈ V := fun e => (hVmem e).symm
  have hBover : ∀ e : ↥E, algebraMap ↥E ↥K e ∈ B ↔ e ∈ V := by
    intro e
    have he : ((e : ↥K) : LaurentSeries L) ∈ K₀' := (memE' e).mp e.2
    set e' : ↥K₀' := ⟨((e : ↥K) : LaurentSeries L), he⟩ with he'def
    have hee : (e : ↥K) = algebraMap ↥K₀' ↥K e' := Subtype.ext rfl
    rw [hVmem]
    show (e : ↥K) ∈ B ↔ (e : ↥K) ∈ W₀
    rw [hee, hB' e', hO₀' e', hW₀]
    rfl

  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_algEquiv_comap_eq_of_isGalois (E := ↥E) (K := ↥K) V W₀ B hWover hBover
  obtain ⟨g, hg⟩ := (FixedPoints.toAlgAut_surjective ↥GB ↥K) σ
  have hfun : ∀ x : ↥K, σ x = (g.1 : ↥K ≃ₐ[L] ↥K) x := by
    intro x; rw [← hg]; rfl
  have hBg : B = W₀.comap (g.1 : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom := by
    rw [hσ]; ext x
    simp only [ValuationSubring.mem_comap]
    show σ.toAlgHom.toRingHom x ∈ W₀ ↔ (g.1 : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom x ∈ W₀
    simp [hfun x]
  subst hBg
  refine ⟨⟨g.1, ?_, rfl⟩, ?_⟩
  ·
    intro x
    have hxE : algebraMap ↥K₀' ↥K x ∈ E := (memE' _).mpr x.2
    exact (⟨algebraMap ↥K₀' ↥K x, hxE⟩ : ↥E).2 g
  ·
    have hB : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ W₀.comap (g.1 : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ↔ x ∈ O₀ := by
      intro x
      have h1 : algebraMap ↥K₀ ↥K x = algebraMap ↥K₀' ↥K (IntermediateField.inclusion hle₀ x) := Subtype.ext rfl
      rw [h1, hB', hO₀', hO₀]
      rfl
    refine ⟨hB, ?_, ?_⟩
    · exact ModularCurve.FullLevel.ramificationIdx_comap_gauss_eq_one_of_levelH_of_eq_three
        q hq3 M' hqM' L ζ hζ K hK K₀ hK₀ hle A hAq hζA W₀ hW₀ O₀ hO₀ g.1 hB
    · have hfixK₀ : ∀ x : ↥K₀, (g.1 : ↥K ≃ₐ[L] ↥K) (algebraMap ↥K₀ ↥K x) = algebraMap ↥K₀ ↥K x := by
        intro x
        have h1 : algebraMap ↥K₀ ↥K x = algebraMap ↥K₀' ↥K (IntermediateField.inclusion hle₀ x) := Subtype.ext rfl
        have hxE : algebraMap ↥K₀' ↥K (IntermediateField.inclusion hle₀ x) ∈ E := (memE' _).mpr (IntermediateField.inclusion hle₀ x).2
        rw [h1]
        exact (⟨_, hxE⟩ : ↥E).2 g
      obtain ⟨hB', hsep⟩ := ModularCurve.FullLevel.exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_three
        q hq3 M' hqM' L ζ hζ hι K hK K₀ hK₀ hle A hAq hζA W₀ hW₀ O₀ hO₀ g.1 hfixK₀
      exact hsep

end S_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three (solution)
