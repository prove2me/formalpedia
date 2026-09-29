-- Prove2me | solution 1 for ModularCurve.relfinrank_eq_sub_one_x1FunctionField_mul_x1x0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fb7538c0-3b4b-5a48-8a92-ac842c679362

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1Diamond
import Theorems.Thm_CongruenceSubgroup_relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_eq_sub_one_x1FunctionField_mul_x1x0
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "ModularCurve~coeffEmb_jq CongruenceSubgroup"
open scoped MatrixGroups

namespace DiamondDeg

theorem T_mem_gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]

theorem coeffEmb_jq (K : Type*) [Field K] [Algebra ℚ K] : coeffEmb K jq = jqModC K := by
  ext k
  rw [coeffEmb_coeff, jqModC_eq_map_intCast (K := K), ← jqModC_rat, jqModC_eq_map_intCast (K := ℚ),
    HahnSeries.map_coeff, HahnSeries.map_coeff]
  simp

theorem relfinrank_lift_eq_finrank {k X : Type*} [Field k] [Field X] [Algebra k X]
    (E : IntermediateField k X) (K' : IntermediateField k ↥E) :
    IntermediateField.relfinrank (IntermediateField.lift K') E = Module.finrank ↥K' ↥E := by
  have hE : E = IntermediateField.map E.val ⊤ := by
    rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  conv_lhs => rw [show IntermediateField.lift K' = IntermediateField.map E.val K' from rfl]; arg 2; rw [hE]
  rw [IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right]

theorem relfinrank_adjoin_coe_eq_finrank {k X : Type*} [Field k] [Field X] [Algebra k X]
    (E : IntermediateField k X) (y : ↥E) :
    IntermediateField.relfinrank (IntermediateField.adjoin k ({(y : X)} : Set X)) E =
      Module.finrank ↥(IntermediateField.adjoin k ({y} : Set ↥E)) ↥E := by
  rw [← relfinrank_lift_eq_finrank, IntermediateField.lift_adjoin, Set.image_singleton]

def subfieldLift {k X : Type*} [Field k] [Field X] [Algebra k X] (E : IntermediateField k X) (S : Subfield ↥E)
    (h : ∀ c : k, algebraMap k ↥E c ∈ S) : IntermediateField k X :=
  IntermediateField.lift (S.toIntermediateField h)

theorem mem_subfieldLift_iff {k X : Type*} [Field k] [Field X] [Algebra k X] (E : IntermediateField k X)
    (S : Subfield ↥E) (h : ∀ c : k, algebraMap k ↥E c ∈ S) (x : X) :
    x ∈ subfieldLift E S h ↔ ∃ y : ↥E, y ∈ S ∧ (y : X) = x := by
  unfold subfieldLift IntermediateField.lift
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem relfinrank_subfieldLift {k X : Type*} [Field k] [Field X] [Algebra k X] (E : IntermediateField k X)
    (S : Subfield ↥E) (h : ∀ c : k, algebraMap k ↥E c ∈ S) :
    IntermediateField.relfinrank (subfieldLift E S h) E = Module.finrank ↥S ↥E :=
  relfinrank_lift_eq_finrank E _

end DiamondDeg

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K) :
    IntermediateField.relfinrank K₁ K = p - 1 := by
  classical
  have pp : p.Prime := Fact.out
  haveI : NeZero p := ⟨pp.ne_zero⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) pp.ne_zero⟩
  have hcop : Nat.Coprime M p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd pp).mpr hpM))
  obtain ⟨hΓle, hT, hneg, hrel⟩ :=
    CongruenceSubgroup.relIndex_gamma1_mul_sup_zpowers_neg_one_gamma1_inf_gamma0_eq_sub_one M p (by omega) hpM

  obtain ⟨δ, -, hfix⟩ :=
    ModularCurve.exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff M p hcop
      (fun d hd => ModularCurve.exists_isDiamondAut (M * p) hd)

  have hX : x1x0FunctionFieldC ℚ M p = qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p) := rfl
  rw [hX] at hfix hK₁

  have hF₁F : qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p) ≤ x1FunctionField (M * p) := qExpFunctionFieldC_mono ℚ hΓle
  have hjqF₁ : jq ∈ qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p) := by
    have h := intFormRatiosC_subset ℚ (Gamma1 M ⊓ Gamma0 p) (jqModC_mem_intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 p))
    rwa [jqModC_rat] at h
  have hjqF : jq ∈ x1FunctionField (M * p) := hF₁F hjqF₁
  have hJF₁ : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p) :=
    IntermediateField.adjoin_simple_le_iff.mpr hjqF₁
  obtain ⟨y₁, hy₁⟩ : ∃ y : ↥(qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)), (y : LaurentSeries ℚ) = jq := ⟨⟨jq, hjqF₁⟩, rfl⟩

  have hce : ∀ x : LaurentSeries ℚ, coeffEmb ℚ x = x := fun x => by
    ext k
    rw [coeffEmb_coeff]
    simp
  have htr : Transcendental ℚ jq := by
    have hmem : jq ∈ laurentBaseChange ℚ (x1FunctionField (M * p)) := by
      have h := coeffEmb_mem_laurentBaseChange ℚ (F₀ := x1FunctionField (M * p)) hjqF
      rwa [hce] at h
    obtain ⟨htr', -⟩ :=
      ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC ℚ
        (Gamma1 (M * p)) (DiamondDeg.T_mem_gamma1 _) ⟨jq, hmem⟩ jqModC_rat.symm
    exact fun halg => htr' (IntermediateField.isAlgebraic_iff.mpr halg)

  have hd : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (x1FunctionField (M * p)) =
      (Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    have hyb : jqModC (AlgebraicClosure ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField (M * p)) := by
      rw [← DiamondDeg.coeffEmb_jq]
      exact coeffEmb_mem_laurentBaseChange _ hjqF
    have h1 := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma1_eq_index
      (AlgebraicClosure ℚ) (M * p) ⟨_, hyb⟩ rfl
    have h2 := ModularCurve.relfinrank_laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField (M * p)) jq hjqF htr
    rw [← h2, DiamondDeg.coeffEmb_jq, DiamondDeg.relfinrank_adjoin_coe_eq_finrank _ ⟨_, hyb⟩]
    exact h1

  haveI : (Gamma1 M ⊓ Gamma0 p).FiniteIndex := Subgroup.finiteIndex_of_le hΓle
  haveI : ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  obtain ⟨hfd₁, hd'le⟩ :=
    ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (Gamma1 M ⊓ Gamma0 p) hT
      ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left hneg y₁ (by rw [hy₁, jqModC_rat])
  haveI := hfd₁
  have hcoe := DiamondDeg.relfinrank_adjoin_coe_eq_finrank (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) y₁
  rw [hy₁] at hcoe
  replace hd'le : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) ≤
      ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := hcoe.trans_le hd'le

  have htower := IntermediateField.relfinrank_mul_relfinrank hJF₁ hF₁F
  haveI : (Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  have hd'pos : 0 < IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) := by
    rcases Nat.eq_zero_or_pos
        (IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p))) with h0 | h0
    · exfalso
      have h' := htower
      rw [h0, zero_mul, hd] at h'
      exact Subgroup.FiniteIndex.index_ne_zero h'.symm
    · exact h0

  have hker : Nat.card ↥(ZMod.unitsMap (dvd_mul_right M p)).ker = p - 1 := by
    have h1 := Subgroup.index_ker (ZMod.unitsMap (dvd_mul_right M p))
    rw [MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective _), Subgroup.card_top] at h1
    have h2 := (ZMod.unitsMap (dvd_mul_right M p)).ker.index_mul_card
    rw [h1, Nat.card_eq_fintype_card (α := (ZMod M)ˣ), Nat.card_eq_fintype_card (α := (ZMod (M * p))ˣ),
      ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Nat.totient_mul hcop, Nat.totient_prime pp] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr (NeZero.pos M)) h2
  letI act : MulSemiringAction ↥(ZMod.unitsMap (dvd_mul_right M p)).ker ↥(x1FunctionField (M * p)) :=
    MulSemiringAction.compHom _ δ
  haveI : Fintype ↥(ZMod.unitsMap (dvd_mul_right M p)).ker := Fintype.ofFinite _

  have hmem : ∀ x : ↥(x1FunctionField (M * p)),
      x ∈ FixedPoints.subfield ↥(ZMod.unitsMap (dvd_mul_right M p)).ker ↥(x1FunctionField (M * p)) ↔ ∀ g : ↥(ZMod.unitsMap (dvd_mul_right M p)).ker, δ g x = x :=
    fun x => @MulAction.mem_fixedPoints ↥(ZMod.unitsMap (dvd_mul_right M p)).ker ↥(x1FunctionField (M * p)) _ act.toDistribMulAction.toMulAction x
  have hS : ∀ x : ↥(x1FunctionField (M * p)),
      x ∈ FixedPoints.subfield ↥(ZMod.unitsMap (dvd_mul_right M p)).ker ↥(x1FunctionField (M * p)) ↔
        (x : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p) := fun x => (hmem x).trans (hfix x).symm
  have hlift : DiamondDeg.subfieldLift (x1FunctionField (M * p))
      (FixedPoints.subfield ↥(ZMod.unitsMap (dvd_mul_right M p)).ker ↥(x1FunctionField (M * p)))
      (fun c => by
        rw [eq_ratCast]
        exact (hmem _).mpr fun g => map_ratCast (δ g) c) = qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p) := by
    apply le_antisymm
    · intro x hx
      rw [DiamondDeg.mem_subfieldLift_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (hS y).mp hy
    · intro x hx
      rw [DiamondDeg.mem_subfieldLift_iff]
      exact ⟨⟨x, hF₁F hx⟩, (hS _).mpr hx, rfl⟩
  have hr_le : IntermediateField.relfinrank (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) (x1FunctionField (M * p)) ≤ p - 1 := by
    rw [← hlift, DiamondDeg.relfinrank_subfieldLift]
    calc Module.finrank ↥(FixedPoints.subfield ↥(ZMod.unitsMap (dvd_mul_right M p)).ker ↥(x1FunctionField (M * p))) ↥(x1FunctionField (M * p))
        ≤ Fintype.card ↥(ZMod.unitsMap (dvd_mul_right M p)).ker := FixedPoints.finrank_le_card _ _
      _ = Nat.card ↥(ZMod.unitsMap (dvd_mul_right M p)).ker := Fintype.card_eq_nat_card
      _ = p - 1 := hker

  have hidx : (Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      (p - 1) * ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
    rw [← Subgroup.relIndex_mul_index (sup_le_sup_right hΓle _), hrel]
  have hI'pos : 0 < ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hr : IntermediateField.relfinrank (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) (x1FunctionField (M * p)) = p - 1 := by
    have key : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) *
        IntermediateField.relfinrank (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) (x1FunctionField (M * p)) =
        (p - 1) * ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
      rw [htower, hd, hidx]
    have h1 : (p - 1) * ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
        ((Gamma1 M ⊓ Gamma0 p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index *
          IntermediateField.relfinrank (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) (x1FunctionField (M * p)) := by
      rw [← key]
      exact Nat.mul_le_mul_right _ hd'le
    have h2 : p - 1 ≤ IntermediateField.relfinrank (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) (x1FunctionField (M * p)) := by
      rw [mul_comm] at h1
      exact Nat.le_of_mul_le_mul_left h1 hI'pos
    omega

  subst hK
  subst hK₁
  have hJL : IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) ≤
      laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) :=
    IntermediateField.adjoin_simple_le_iff.mpr (coeffEmb_mem_laurentBaseChange L hjqF₁)
  have e1 := ModularCurve.relfinrank_laurentBaseChange L (x1FunctionField (M * p)) jq hjqF htr
  have e2 := ModularCurve.relfinrank_laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)) jq hjqF₁ htr
  have htL := IntermediateField.relfinrank_mul_relfinrank hJL hle
  rw [e1, e2, ← htower, hr] at htL
  exact Nat.eq_of_mul_eq_mul_left hd'pos htL

end S_ModularCurve_relfinrank_eq_sub_one_x1FunctionField_mul_x1x0
end P2MW
export P2MW.S_ModularCurve_relfinrank_eq_sub_one_x1FunctionField_mul_x1x0 (solution)
