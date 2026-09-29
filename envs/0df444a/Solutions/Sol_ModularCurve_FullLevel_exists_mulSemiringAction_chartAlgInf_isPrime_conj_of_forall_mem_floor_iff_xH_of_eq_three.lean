-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/c4809f7d-ff97-5188-af3c-2c8975a9153b

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped Pointwise

namespace COAux

def restrictAction {G : Type} [Group G] {A K : Type} [CommRing A] [Field K] [Algebra A K] [MulSemiringAction G K]
    (B : Subalgebra A K) (hstab : ∀ (g : G) (b : K), b ∈ B → g • b ∈ B) : MulSemiringAction G ↥B where
  smul g b := ⟨g • (b : K), hstab g b.1 b.2⟩
  one_smul b := Subtype.ext (one_smul G (b : K))
  mul_smul g h b := Subtype.ext (mul_smul g h (b : K))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g a b := Subtype.ext (smul_add g (a : K) (b : K))
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g a b := Subtype.ext (MulSemiringAction.smul_mul g (a : K) (b : K))

theorem restrictAction_smul_coe {G : Type} [Group G] {A K : Type} [CommRing A] [Field K] [Algebra A K] [MulSemiringAction G K]
    (B : Subalgebra A K) (hstab : ∀ (g : G) (b : K), b ∈ B → g • b ∈ B) (g : G) (b : ↥B) :
    letI := restrictAction B hstab
    ((g • b : ↥B) : K) = g • (b : K) := rfl

theorem exists_conj_of_agree_on_fixed {G : Type} [Group G] [Fintype G] {B : Type} [CommRing B] [MulSemiringAction G B]
    (y y' : Ideal B) [y.IsPrime] [y'.IsPrime]
    (hagree : ∀ b : B, (∀ g : G, g • b = b) → (b ∈ y ↔ b ∈ y')) :
    ∃ g : G, y' = g • y := by
  let S : Subring B :=
    { carrier := {b | ∀ g : G, g • b = b}
      mul_mem' := fun {a b} ha hb g => by rw [smul_mul', ha g, hb g]
      one_mem' := fun g => smul_one g
      add_mem' := fun {a b} ha hb g => by rw [smul_add, ha g, hb g]
      zero_mem' := fun g => smul_zero g
      neg_mem' := fun {a} ha g => by rw [smul_neg, ha g] }
  letI : Algebra ↥S B := S.subtype.toAlgebra
  haveI : Algebra.IsInvariant ↥S B G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI : SMulCommClass G ↥S B :=
    ⟨fun g s b => by
      change g • ((s : B) * b) = (s : B) * g • b
      rw [smul_mul', s.2 g]⟩
  have hunder : y.under ↥S = y'.under ↥S := by
    ext s
    simp only [Ideal.under, Ideal.mem_comap]
    exact hagree s s.2
  exact Algebra.IsInvariant.exists_smul_of_under_eq ↥S B G y y' hunder

end COAux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥K),
      SMulCommClass G L ↥K ∧

      (∀ (g : G) (x : ↥K), (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → g • x = x) ∧
      (∀ x : ↥K, (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M'))) ∧

      (∀ (g : G) (a : A), g • algebraMap A ↥K a = algebraMap A ↥K a) ∧
      (∀ g : G, g • j = j) ∧
      (∀ (g : G) (b : ↥K), b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j → g • b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j) ∧

      (∀ (y y' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j)), y.IsPrime → y'.IsPrime →
        (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j), ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → (b ∈ y ↔ b ∈ y')) →
        ∃ g : G, ∀ b b' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j), (b' : ↥K) = g • (b : ↥K) → (b ∈ y ↔ b' ∈ y')) := by
  classical

  have eK : ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) =
      ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) :=
    ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq L _
  have eK₂ : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) = ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) := by
    rw [← ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull,
      ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq]
  have hle : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) ≤ K := by
    rw [hK, eK, eK₂]
    exact ModularCurve.qExpFunctionFieldC_mono L (CohCarrier.GammaH_le_Gamma0 _)
  obtain ⟨G, iG, iF, iM, ⟨hcommK₂, hinv⟩, hcommL, -, hgj⟩ :=
    ModularCurve.FullLevel.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three q hq3 M' hqM' L K hK
      j hj (ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M'))) rfl hle

  have hfix : ∀ (g : G) (x : ↥K), (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → g • x = x := by
    intro g x hx
    letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    have h := @smul_comm G ↥(ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M'))) ↥K _ _ hcommK₂ g ⟨(x : LaurentSeries L), hx⟩ (1 : ↥K)
    rw [smul_one, Algebra.smul_def, mul_one] at h
    have hx' : algebraMap ↥(ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M'))) ↥K ⟨(x : LaurentSeries L), hx⟩ = x := Subtype.ext rfl
    rwa [hx'] at h

  have hinv' : ∀ x : ↥K, (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) := by
    intro x hx
    letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    obtain ⟨a, ha⟩ := hinv.isInvariant x hx
    rw [← ha]
    exact a.2

  have hA : ∀ (g : G) (a : A), g • algebraMap A ↥K a = algebraMap A ↥K a := by
    intro g a
    rw [IsScalarTower.algebraMap_apply A L ↥K a, Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

  have hR : ∀ (g : G) (r : ↥K), r ∈ Algebra.adjoin A ({j⁻¹} : Set ↥K) → g • r = r := by
    intro g r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [smul_inv'', hgj]
    | algebraMap a => exact hA g a
    | add x y _ _ hx hy => rw [smul_add, hx, hy]
    | mul x y _ _ hx hy => rw [smul_mul', hx, hy]
  have hstab : ∀ (g : G) (b : ↥K), b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j → g • b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j := by
    intro g b hb
    rw [AlgebraicCurve.TwoChartIntegralModel.chartAlgInf, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at hb ⊢
    let φ : ↥K →ₐ[↥(Algebra.adjoin A ({j⁻¹} : Set ↥K))] ↥K :=
      { (MulSemiringAction.toRingHom G ↥K g) with commutes' := fun r => hR g r.1 r.2 }
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨p, hp, ?_⟩
    change Polynomial.eval₂ (algebraMap _ ↥K) (φ b) p = 0
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hpb, map_zero]
  refine ⟨G, iG, iF, iM, hcommL, hfix, hinv', hA, hgj, hstab, ?_⟩

  intro y y' hy hy' hagree
  letI actB : MulSemiringAction G ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j) := COAux.restrictAction (AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j) hstab
  haveI := hy
  haveI := hy'
  have hagree' : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j), (∀ g : G, g • b = b) → (b ∈ y ↔ b ∈ y') := by
    intro b hb
    apply hagree b
    apply hinv' (b : ↥K)
    intro g
    have := congrArg Subtype.val (hb g)
    exact this
  obtain ⟨g, hg⟩ := COAux.exists_conj_of_agree_on_fixed y y' hagree'
  refine ⟨g, fun b b' hbb' => ?_⟩
  have hb' : b' = g • b := Subtype.ext hbb'
  rw [hg, hb', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]

end S_ModularCurve_FullLevel_exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH_of_eq_three (solution)
