-- Prove2me | solution 1 for ModularCurve.XOneP.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7c4582e2-9cd1-5de8-884b-bbb511782e62

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1Diamond
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
import Theorems.Thm_ModularCurve_exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_x1_mul
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

set_option maxHeartbeats 3200000 in
theorem DiamondL.core
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF₀ : F₀ = ModularCurve.x1FunctionField (M * p))
    (hF₁ : F₁ = ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))
    (j : ↥(ModularCurve.laurentBaseChange L F₀)) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (jp : ↥(ModularCurve.laurentBaseChange L F₀)) (hjp : ((jp : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hle : ModularCurve.laurentBaseChange L F₁ ≤ ModularCurve.laurentBaseChange L F₀) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥(ModularCurve.laurentBaseChange L F₀)),
      (letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
       SMulCommClass G ↥(ModularCurve.laurentBaseChange L F₁) ↥(ModularCurve.laurentBaseChange L F₀) ∧ Algebra.IsInvariant ↥(ModularCurve.laurentBaseChange L F₁) ↥(ModularCurve.laurentBaseChange L F₀) G) ∧
      SMulCommClass G L ↥(ModularCurve.laurentBaseChange L F₀) ∧
      (∀ g : G, g • j = j ∧ g • jp = jp) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩
  haveI : NeZero (1 * (M * p)) := ⟨by rw [one_mul]; exact NeZero.ne _⟩

  have hGamma1 : CongruenceSubgroup.Gamma1 1 = ⊤ := by
    refine eq_top_iff.mpr fun A _ => ?_
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hS : ModularCurve.x1x0FunctionFieldC ℚ 1 (M * p) = F₁ := by
    rw [hF₁]
    show ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 1 ⊓ CongruenceSubgroup.Gamma0 (M * p)) = _
    rw [hGamma1, top_inf_eq]
  have aux : ∀ (E E' : IntermediateField ℚ (LaurentSeries ℚ)) (_ : E = E') (G : Type) [Group G]
      (δ : G →* (↥E ≃ₐ[ℚ] ↥E)) (S : IntermediateField ℚ (LaurentSeries ℚ))
      (_ : ∀ x : ↥E, (x : LaurentSeries ℚ) ∈ S ↔ ∀ u : G, δ u x = x),
      ∃ δ' : G →* (↥E' ≃ₐ[ℚ] ↥E'), ∀ x : ↥E', (x : LaurentSeries ℚ) ∈ S ↔ ∀ u : G, δ' u x = x := by
    rintro E _ rfl G _ δ S h; exact ⟨δ, h⟩
  obtain ⟨δ₀, -, hfix₀⟩ := ModularCurve.exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff 1 (M * p)
    (Nat.coprime_one_left _) (fun d hd => ModularCurve.exists_isDiamondAut (1 * (M * p)) hd)
  let G : Type := ↥(ZMod.unitsMap (dvd_mul_right 1 (M * p))).ker
  have hE : ModularCurve.x1FunctionField (1 * (M * p)) = F₀ := by rw [hF₀, one_mul]
  obtain ⟨δ, hfix⟩ := aux _ _ hE G δ₀ (ModularCurve.x1x0FunctionFieldC ℚ 1 (M * p)) hfix₀
  rw [hS] at hfix

  obtain ⟨δL, hδL⟩ := ModularCurve.exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb L F₀ G δ

  have hle₁ : F₁ ≤ F₀ := by
    rw [hF₀, hF₁]; exact ModularCurve.qExpFunctionFieldC_mono ℚ (CongruenceSubgroup.Gamma1_in_Gamma0 (M * p))
  have hFIX := ModularCurve.forall_algEquiv_laurentBaseChange_apply_eq_iff_mem_laurentBaseChange_of_fixedField
    L F₀ F₁ hle₁ G δ hfix δL hδL

  have hgen : ∀ {d : ℕ} [NeZero d], d ∣ M * p →
      ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq) ∈ ModularCurve.laurentBaseChange L F₁ := by
    intro d _ hd
    refine ModularCurve.coeffEmb_mem_laurentBaseChange L ?_
    rw [hF₁, ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact ModularCurve.jqd_mem_full (M * p) hd
  have hjmem : ((j : LaurentSeries L)) ∈ ModularCurve.laurentBaseChange L F₁ := by
    rw [hj, ← ModularCurve.qExpand_one_apply (R := ℚ) ModularCurve.jq]
    exact hgen (one_dvd _)
  have hjpmem : ((jp : LaurentSeries L)) ∈ ModularCurve.laurentBaseChange L F₁ := by
    rw [hjp]; exact hgen (dvd_mul_left p M)

  letI instG : MulSemiringAction G ↥(ModularCurve.laurentBaseChange L F₀) := MulSemiringAction.compHom _ δL
  have hsmul : ∀ (g : G) (x : ↥(ModularCurve.laurentBaseChange L F₀)), g • x = δL g x := fun _ _ => rfl
  refine ⟨G, inferInstance, Fintype.ofFinite G, instG, ?_, ?_, ?_⟩
  · letI instA := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    have hfixK₂ : ∀ (g : G) (k : ↥(ModularCurve.laurentBaseChange L F₁)), δL g (IntermediateField.inclusion hle k) = IntermediateField.inclusion hle k :=
      fun g k => (hFIX _).mpr (by simpa using k.2) g
    refine ⟨⟨fun g k x => ?_⟩, ⟨fun b hb => ?_⟩⟩
    · show δL g (IntermediateField.inclusion hle k * x) = IntermediateField.inclusion hle k * δL g x
      rw [map_mul, hfixK₂]
    · have hb' : ∀ g : G, δL g b = b := fun g => hb g
      refine ⟨⟨(b : LaurentSeries L), (hFIX b).mp hb'⟩, ?_⟩
      apply Subtype.ext
      show (((⟨(b : LaurentSeries L), (hFIX b).mp hb'⟩ : ↥(ModularCurve.laurentBaseChange L F₁)) : LaurentSeries L)) = (b : LaurentSeries L)
      rfl
  · refine ⟨fun g c x => ?_⟩
    rw [hsmul, hsmul]
    exact (δL g).toLinearEquiv.map_smul c x
  · intro g
    exact ⟨(hFIX j).mpr hjmem g, (hFIX jp).mpr hjpmem g⟩

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (jp : ↥K) (hjp : ((jp : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥K),
      (letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
       SMulCommClass G ↥K₂ ↥K ∧ Algebra.IsInvariant ↥K₂ ↥K G) ∧
      SMulCommClass G L ↥K ∧
      (∀ g : G, g • j = j ∧ g • jp = jp) := by
  subst hK hK₂
  exact DiamondL.core p M L _ _ rfl rfl j hj jp hjp hle

end S_ModularCurve_XOneP_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_x1_mul (solution)
