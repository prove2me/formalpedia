-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/800bde64-04e9-5525-b047-074d3179dca8

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset dedekindPsi coeffMap_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 coeffMap_ofPowerSeries finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed Gamma0_index jqModC_mem_intFormRatiosC"
namespace FullnessGamma1
p2m_open "ModularCurve~coeffEmb_injective"

p2m_open "ModularCurve~coeffEmb_injective P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index.ModularCurve IntermediateField"

theorem finrank_adjoin_eq_relfinrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (x : F) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F =
      (IntermediateField.adjoin K ({(x : E)} : Set E)).relfinrank F := by
  have hlift : IntermediateField.lift (IntermediateField.adjoin K ({x} : Set F)) =
      IntermediateField.adjoin K ({(x : E)} : Set E) := by
    rw [IntermediateField.lift_adjoin]; simp
  have hle : IntermediateField.adjoin K ({(x : E)} : Set E) ≤ F := by
    rw [← hlift]; exact IntermediateField.lift_le _
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  let i : (IntermediateField.adjoin K ({x} : Set F)) ≃+*
      (IntermediateField.adjoin K ({(x : E)} : Set E)) :=
    ((IntermediateField.liftAlgEquiv (IntermediateField.adjoin K ({x} : Set F))).trans
      (IntermediateField.equivOfEq hlift)).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars hle) := RingEquiv.refl _
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext a
  rfl

section BaseChange

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeffEmb_injective : Function.Injective (coeffEmb K) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff n) h
  simp only [coeffEmb_coeff] at h1
  exact (algebraMap ℚ K).injective h1

theorem coeffEmb_ne_zero_iff (x : LaurentSeries ℚ) : coeffEmb K x ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, ← map_zero (coeffEmb K), (coeffEmb_injective K).eq_iff]

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb K (intSeriesC ℚ p) = intSeriesC K p := by
  rw [coeffEmb, intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem algebraMap_laurentSeries_eq_C {L : Type*} [Field L] (a : L) :
    algebraMap L (LaurentSeries L) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap L (PowerSeries L) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem coeffEmb_algebraMap (a : ℚ) :
    coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) a) = algebraMap K (LaurentSeries K) (algebraMap ℚ K a) := by
  rw [algebraMap_laurentSeries_eq_C, algebraMap_laurentSeries_eq_C, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffEmb, coeffMap_single]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem image_intFormRatiosC : (coeffEmb K) '' intFormRatiosC ℚ Γ = intFormRatiosC K Γ := by
  ext z
  constructor
  · rintro ⟨y, ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨w, f, g, pf, pg, hf, hg, ?_, ?_⟩
    · rw [← coeffEmb_intSeriesC K]; exact (coeffEmb_ne_zero_iff K _).mpr hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨w, f, g, pf, pg, hf, hg, ?_, rfl⟩, ?_⟩
    · rw [← coeffEmb_ne_zero_iff K, coeffEmb_intSeriesC]; exact hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

variable {Γ}

theorem coeffEmb_mem_adjoin {S : Set (LaurentSeries ℚ)} {y : LaurentSeries ℚ} (hy : y ∈ adjoin ℚ S) :
    coeffEmb K y ∈ adjoin K ((coeffEmb K) '' S) := by
  have hy' : y ∈ (adjoin ℚ S).toSubfield := hy
  rw [adjoin_toSubfield] at hy'
  have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ S) ≤
      (adjoin K ((coeffEmb K) '' S)).toSubfield.comap (coeffEmb K) := by
    rw [Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · change coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) a) ∈ adjoin K ((coeffEmb K) '' S)
      rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · change coeffEmb K z ∈ adjoin K ((coeffEmb K) '' S)
      exact subset_adjoin K _ ⟨z, hz, rfl⟩
  exact hle hy'

variable (Γ)

theorem laurentBaseChange_qExpFunctionFieldC_eq :
    laurentBaseChange K (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC K Γ := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h := coeffEmb_mem_adjoin K (S := intFormRatiosC ℚ Γ) hy
    rwa [image_intFormRatiosC] at h
  · rw [qExpFunctionFieldC, ← image_intFormRatiosC K Γ, laurentBaseChange]
    exact IntermediateField.adjoin.mono K _ _ (Set.image_mono (intFormRatiosC_subset ℚ Γ))

end BaseChange

end ModularCurve.FullnessGamma1

open scoped MatrixGroups in
p2m_open "ModularCurve~coeffEmb_injective" in open ModularCurve.FullnessGamma1 _root_.P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index.ModularCurve IntermediateField CongruenceSubgroup in
set_option maxHeartbeats 3200000 in
theorem solution
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (N : ℕ) [NeZero N]
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    Module.finrank
        ↥(IntermediateField.adjoin K ({y} : Set ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)))))
        ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))) =
      (CongruenceSubgroup.Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  haveI hfi0 : (Gamma0 N).FiniteIndex := (CongruenceSubgroup.Gamma0_is_congruence N).finiteIndex
  have hT0 : ModularGroup.T ∈ Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]

  have hneg1 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp
  have hsup : Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) = Gamma0 N :=
    sup_eq_left.mpr ((Subgroup.zpowers_le).mpr hneg1)
  have hneg : ∀ γ ∈ Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)), γ ∈ Gamma0 N ∨ -γ ∈ Gamma0 N := by
    intro γ hγ
    rw [hsup] at hγ
    exact Or.inl hγ

  have hle := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index K
    (Gamma0 N) hT0 (Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left hneg y hy
  refine le_antisymm hle ?_

  have hidx : (Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = dedekindPsi N := by
    rw [hsup, ModularCurve.Gamma0_index]
  have hEE : laurentBaseChange K (qExpFunctionFieldC ℚ (Gamma0 N)) = qExpFunctionFieldC K (Gamma0 N) :=
    laurentBaseChange_qExpFunctionFieldC_eq K (Gamma0 N)
  have hjF0 : jqModC K ∈ qExpFunctionFieldC K (Gamma0 N) :=
    intFormRatiosC_subset K (Gamma0 N) (ModularCurve.jqModC_mem_intFormRatiosC K (Gamma0 N))
  have eJE' : Module.finrank
        ↥(IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K (qExpFunctionFieldC ℚ (Gamma0 N)))))
        ↥(laurentBaseChange K (qExpFunctionFieldC ℚ (Gamma0 N))) =
      (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank
        (laurentBaseChange K (qExpFunctionFieldC ℚ (Gamma0 N))) := by
    have h := finrank_adjoin_eq_relfinrank (laurentBaseChange K (qExpFunctionFieldC ℚ (Gamma0 N))) y
    rw [hy] at h
    exact h
  have eJF0 : dedekindPsi N ≤
      (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank (qExpFunctionFieldC K (Gamma0 N)) := by
    obtain ⟨hfin, -⟩ := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed K
      (Gamma0 N) hT0 (Gamma0 N) le_rfl (fun γ hγ => Or.inl hγ) ⟨jqModC K, hjF0⟩ rfl
    haveI := hfin
    have h := ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 K N hNK ⟨jqModC K, hjF0⟩ rfl
    have e := finrank_adjoin_eq_relfinrank (qExpFunctionFieldC K (Gamma0 N)) ⟨jqModC K, hjF0⟩
    exact e ▸ h
  calc (Gamma0 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
      = dedekindPsi N := hidx
    _ ≤ (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).relfinrank
        (laurentBaseChange K (qExpFunctionFieldC ℚ (Gamma0 N))) := by rw [hEE]; exact eJF0
    _ = _ := eJE'.symm

end S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index (solution)
