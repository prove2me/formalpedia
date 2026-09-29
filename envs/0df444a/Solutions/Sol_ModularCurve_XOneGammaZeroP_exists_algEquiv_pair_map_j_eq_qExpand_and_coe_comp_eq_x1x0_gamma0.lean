-- Prove2me | solution 1 for ModularCurve.XOneGammaZeroP.exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b00b03bb-9b91-5bba-8b8d-0bb9f3428f96

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneGammaZeroP_exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower"
p2m_attr_erase "instance" "CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero"
p2m_attr_erase "simp" "TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (ι₂ : ↥K₂ →+* ↥K₁) (hι₂ : ∀ y : ↥K₂, (((ι₂ y : ↥K₁) : LaurentSeries L)) = ((y : ↥K₂) : LaurentSeries L))
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p] :
    ∃ (σ : ↥K₁ ≃ₐ[L] ↥K₁) (σ₂ : ↥K₂ ≃ₐ[L] ↥K₂),
      ((σ j : ↥K₁) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) ∧
      ∀ y : ↥K₂, ((σ (ι₂ y) : ↥K₁) : LaurentSeries L) = ((σ₂ y : ↥K₂) : LaurentSeries L) := by
  classical
  obtain ⟨σ, hσj, hσw⟩ := ModularCurve.XOneGammaZeroP.exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0
    p M hpM L K₁ hK₁ j hj

  have hle : K₂ ≤ K₁ := by
    intro x hx
    have h := hι₂ ⟨x, hx⟩
    have : x = ((ι₂ ⟨x, hx⟩ : ↥K₁) : LaurentSeries L) := h.symm
    rw [this]; exact (ι₂ ⟨x, hx⟩).2
  have hι₂' : ∀ y : ↥K₂, ι₂ y = IntermediateField.inclusion hle y := fun y => Subtype.ext (hι₂ y)

  set S : Set (LaurentSeries L) := ⇑(ModularCurve.coeffEmb L) '' ((ModularCurve.modularFunctionFieldFull (M * p) : Set (LaurentSeries ℚ))) with hS
  have hK₂S : K₂ = IntermediateField.adjoin L S := by
    rw [hK₂, ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]; rfl
  have hSK₂ : S ⊆ (K₂ : Set (LaurentSeries L)) := by rw [hK₂S]; exact IntermediateField.subset_adjoin L S

  have hσS : ∀ x ∈ S, ∀ hx : x ∈ K₁, ((σ ⟨x, hx⟩ : ↥K₁) : LaurentSeries L) ∈ S := by
    rintro _ ⟨f, hf, rfl⟩ hx
    refine ⟨_, (ModularCurve.atkinLehnerInvolutionFull M p ⟨f, hf⟩).2, ?_⟩
    exact (hσw ⟨f, hf⟩ hx).symm
  have hσS' : ∀ x ∈ S, ∃ x' ∈ S, ∃ hx' : x' ∈ K₁, ((σ ⟨x', hx'⟩ : ↥K₁) : LaurentSeries L) = x := by
    rintro _ ⟨f, hf, rfl⟩
    let g : ↥(ModularCurve.modularFunctionFieldFull (M * p)) := (ModularCurve.atkinLehnerInvolutionFull M p).symm ⟨f, hf⟩
    refine ⟨ModularCurve.coeffEmb L (g : LaurentSeries ℚ), ⟨g, g.2, rfl⟩, hle (hSK₂ ⟨g, g.2, rfl⟩), ?_⟩
    rw [hσw g, AlgEquiv.apply_symm_apply]

  let valθ : ↥K₁ →ₐ[L] LaurentSeries L := (K₁.val).comp (σ : ↥K₁ ≃ₐ[L] ↥K₁).toAlgHom
  let W : IntermediateField L ↥K₁ := K₂.comap valθ
  let S' : Set ↥K₁ := {x | (x : LaurentSeries L) ∈ S}
  have hS'W : S' ⊆ (W : Set ↥K₁) := by
    intro x hx
    change ((K₁.val).comp (σ : ↥K₁ ≃ₐ[L] ↥K₁).toAlgHom) x ∈ K₂
    exact hSK₂ (hσS _ hx x.2)
  have hadjW : IntermediateField.adjoin L S' ≤ W := IntermediateField.adjoin_le_iff.mpr hS'W

  have himg : (K₁.val : ↥K₁ → LaurentSeries L) '' S' = S := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩; exact hx'
    · intro hx; exact ⟨⟨x, hle (hSK₂ hx)⟩, hx, rfl⟩
  have hmapS' : (IntermediateField.adjoin L S').map K₁.val = K₂ := by
    apply le_antisymm
    · refine IntermediateField.map_le_iff_le_comap.mpr (IntermediateField.adjoin_le_iff.mpr ?_)
      intro x hx
      show K₁.val x ∈ K₂
      exact hSK₂ hx
    · intro y hy
      have hy' : y ∈ IntermediateField.adjoin L S := hK₂S ▸ hy
      exact (IntermediateField.adjoin_le_iff.mpr (fun x hx =>
        show x ∈ (IntermediateField.adjoin L S').map K₁.val from ⟨⟨x, hle (hSK₂ hx)⟩, IntermediateField.subset_adjoin L S' hx, rfl⟩)) hy'
  have hstab : ∀ y : ↥K₂, ((σ (IntermediateField.inclusion hle y) : ↥K₁) : LaurentSeries L) ∈ K₂ := by
    intro y
    have hy : (y : LaurentSeries L) ∈ (IntermediateField.adjoin L S').map K₁.val := by rw [hmapS']; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    have hxW : ((K₁.val).comp (σ : ↥K₁ ≃ₐ[L] ↥K₁).toAlgHom) x ∈ K₂ := hadjW hx
    have : IntermediateField.inclusion hle y = x := Subtype.ext hxy.symm
    rw [this]; exact hxW

  let ψ : ↥K₂ →ₐ[L] ↥K₂ :=
    { toFun := fun y => ⟨((σ (IntermediateField.inclusion hle y) : ↥K₁) : LaurentSeries L), hstab y⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; simp
      commutes' := fun c => by
        apply Subtype.ext
        show ((σ (IntermediateField.inclusion hle (algebraMap L ↥K₂ c)) : ↥K₁) : LaurentSeries L) = _
        rw [show IntermediateField.inclusion hle (algebraMap L ↥K₂ c) = algebraMap L ↥K₁ c from Subtype.ext rfl,
          AlgEquiv.commutes]; rfl }
  have hψ : ∀ y : ↥K₂, ((ψ y : ↥K₂) : LaurentSeries L) = ((σ (IntermediateField.inclusion hle y) : ↥K₁) : LaurentSeries L) :=
    fun _ => rfl
  have hψsurj : Function.Surjective ψ := by

    have hrange : ∀ (x : LaurentSeries L) (hx : x ∈ S), (⟨x, hSK₂ hx⟩ : ↥K₂) ∈ ψ.fieldRange := by
      intro x hx
      obtain ⟨x', hx'S, hx'K, hx'⟩ := hσS' x hx
      exact ⟨⟨x', hSK₂ hx'S⟩, Subtype.ext hx'⟩

    have hT : ∀ y ∈ K₂, y ∈ (ψ.fieldRange).map K₂.val := by
      intro y hy
      have hy' : y ∈ IntermediateField.adjoin L S := hK₂S ▸ hy
      exact (IntermediateField.adjoin_le_iff.mpr (fun x hx =>
        show x ∈ (ψ.fieldRange).map K₂.val from ⟨⟨x, hSK₂ hx⟩, hrange x hx, rfl⟩)) hy'
    intro y
    obtain ⟨z, hz, hzy⟩ := hT y y.2
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, (show ψ x = z from hx).trans (Subtype.ext hzy)⟩
  let σ₂ : ↥K₂ ≃ₐ[L] ↥K₂ := AlgEquiv.ofBijective ψ ⟨ψ.toRingHom.injective, hψsurj⟩
  refine ⟨σ, σ₂, hσj, fun y => ?_⟩
  rw [hι₂' y]
  rfl

#print axioms solution

end S_ModularCurve_XOneGammaZeroP_exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0
end P2MW
export P2MW.S_ModularCurve_XOneGammaZeroP_exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0 (solution)
