-- Prove2me | solution 1 for ModularCurve.fTorsionFor_pic0_residueField_modularFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/21a42418-d34f-5436-ada2-29dd214a18d3

import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq_zero_of_charP_of_forall_pow_eq_self
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Definitions.Def_ModularCurve_JZeroGoodReductionV2
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_fTorsionFor_pic0_residueField_modularFunctionFieldC
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve AlgebraicCurve IsLocalRing IntermediateField

attribute [local instance] ModularCurve.instDecEqResidueFieldF3nrp
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCF3nrp

namespace Ws22B

theorem exists_pow_prime_pow_eq_self_of_isAlgebraic_zmod
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K] (a : K) :
    ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a := by
  classical
  let L := IntermediateField.adjoin (ZMod p) ({a} : Set K)
  haveI : FiniteDimensional (ZMod p) L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite L := Module.finite_of_finite (ZMod p)
  haveI : Fintype L := Fintype.ofFinite L
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  obtain ⟨n, hp, hcard⟩ := FiniteField.card L p
  refine ⟨n, n.pos, ?_⟩
  have ha : a ∈ L := IntermediateField.subset_adjoin _ _ (Set.mem_singleton a)
  have key := FiniteField.pow_card (⟨a, ha⟩ : L)
  rw [hcard] at key
  have := congrArg (fun x : L => (x : K)) key
  simpa using this

theorem exists_transcendental_finiteDimensional_adjoin
    (K : Type*) [Field K] {LF : Type*} [Field LF] [Algebra K LF]
    (x : LF) (hx : Transcendental K x) (T : Finset LF) (hT : ∀ t ∈ T, IsIntegral K⟮x⟯ t) :
    ∃ x' : IntermediateField.adjoin K (insert x (T : Set LF)),
      Transcendental K x' ∧
      FiniteDimensional
        (IntermediateField.adjoin K ({x'} : Set (IntermediateField.adjoin K (insert x (T : Set LF)))))
        (IntermediateField.adjoin K (insert x (T : Set LF))) := by
  set F : IntermediateField K LF := IntermediateField.adjoin K (insert x (T : Set LF)) with hF
  have hxF : x ∈ F := subset_adjoin K _ (Set.mem_insert x _)
  have hTF : ∀ t ∈ T, t ∈ F := fun t ht => subset_adjoin K _ (Set.mem_insert_of_mem x ht)
  set x' : F := ⟨x, hxF⟩ with hx'
  have hx't : Transcendental K x' :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := LF) Subtype.val_injective).mp hx
  refine ⟨x', hx't, ?_⟩
  set A : IntermediateField K F := IntermediateField.adjoin K ({x'} : Set F) with hA
  have hliftA : lift A = K⟮x⟯ := by
    rw [hA, lift_adjoin_simple]
  let e : A ≃ₐ[K] K⟮x⟯ := (liftAlgEquiv A).trans (equivOfEq hliftA)
  have he : ∀ a : A, ((e a : K⟮x⟯) : LF) = ((a : F) : LF) := by
    intro a; rfl
  have hcomp' : (algebraMap A LF).comp (e.symm : K⟮x⟯ →+* A)
      = (RingHom.id LF).comp (algebraMap K⟮x⟯ LF) := by
    ext b
    change (((e.symm b : A) : F) : LF) = ((b : K⟮x⟯) : LF)
    rw [← he (e.symm b), AlgEquiv.apply_symm_apply]
  have hint : ∀ t (ht : t ∈ T), IsIntegral A (⟨t, hTF t ht⟩ : F) := by
    intro t ht
    have h1 : IsIntegral A (t : LF) :=
      (hT t ht).map_of_comp_eq (R := K⟮x⟯) (S := LF) (T := A) (U := LF)
        (e.symm : K⟮x⟯ →+* A) (RingHom.id LF) hcomp'
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A F LF) Subtype.val_injective).mp h1
  set T' : Set F := (fun t : T => (⟨(t : LF), hTF t t.2⟩ : F)) '' Set.univ with hT'
  haveI : Finite T' := Set.Finite.to_subtype ((Set.finite_univ).image _)
  have hT'int : ∀ y ∈ T', IsIntegral A y := by
    rintro _ ⟨t, -, rfl⟩; exact hint t t.2
  haveI : FiniteDimensional A (IntermediateField.adjoin A T') := finiteDimensional_adjoin hT'int
  have htop : IntermediateField.adjoin A T' = ⊤ := by
    apply restrictScalars_injective K
    rw [restrictScalars_adjoin, restrictScalars_top]
    apply lift_injective
    rw [lift_top, lift_adjoin]
    apply le_antisymm (adjoin_le_iff.mpr ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩; exact y.2
    · show IntermediateField.adjoin K (insert x (T : Set LF)) ≤ _
      apply adjoin.mono
      intro z hz
      rcases hz with rfl | hz
      · exact ⟨x', Or.inl (subset_adjoin K _ (Set.mem_singleton _)), rfl⟩
      · exact ⟨⟨z, hTF z hz⟩, Or.inr ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩, rfl⟩
  have hfin : FiniteDimensional A (IntermediateField.adjoin A T') := inferInstance
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := A) (E := F)).toLinearEquiv

theorem exists_transcendental_finiteDimensional_modularFunctionFieldC
    (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    ∃ x : modularFunctionFieldC K N, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (modularFunctionFieldC K N)))
        (modularFunctionFieldC K N) := by
  have h : modularFunctionFieldC K N = IntermediateField.adjoin K
      (insert (jqModC K) ((({jqNModC K N} : Finset (LaurentSeries K)) : Set (LaurentSeries K)))) := by
    rw [Finset.coe_singleton]; rfl
  have key : ∀ E : IntermediateField K (LaurentSeries K),
      E = IntermediateField.adjoin K
        (insert (jqModC K) ((({jqNModC K N} : Finset (LaurentSeries K)) : Set (LaurentSeries K)))) →
      ∃ x : E, Transcendental K x ∧
        FiniteDimensional (IntermediateField.adjoin K ({x} : Set E)) E := by
    rintro E rfl
    refine exists_transcendental_finiteDimensional_adjoin K (jqModC K) (transcendental_jqModC K)
      {jqNModC K N} ?_
    intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    exact isIntegral_jqNModC_all K N
  exact key _ h

end Ws22B

theorem solution
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (N : ℕ) [NeZero N] :
    FTorsionFor (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := by
  intro c
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hchar : CharP (ResidueField A) ℓ := ValuationSubring.charP_residueField_of_liesOverPrime_def hℓ hA
  haveI : IsAlgClosed (ResidueField A) := inferInstance
  haveI : PerfectField (ResidueField A) := IsAlgClosed.perfectField _
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) N
  have hC : ConstantsAreBase (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    ModularCurve.constantsAreBase_modularFunctionFieldC_of_perfectField (ResidueField A) N
  have halg : ∀ a : ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a := by
    letI : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra (ResidueField A) ℓ
    haveI : Algebra.IsAlgebraic (ZMod ℓ) (ResidueField A) :=
      (ValuationSubring.isAlgClosure_residueField (ℓ := ℓ) A).isAlgebraic
    exact Ws22B.exists_pow_prime_pow_eq_self_of_isAlgebraic_zmod ℓ (ResidueField A)
  exact AlgebraicCurve.Pic0.exists_nsmul_eq_zero_of_charP_of_forall_pow_eq_self
    (ResidueField A) (modularFunctionFieldC (ResidueField A) N) ℓ halg
    (Ws22B.exists_transcendental_finiteDimensional_modularFunctionFieldC (ResidueField A) N)
    hC c

end S_ModularCurve_fTorsionFor_pic0_residueField_modularFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_fTorsionFor_pic0_residueField_modularFunctionFieldC (solution)
