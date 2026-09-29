-- Prove2me | solution 1 for ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3b199469-0472-5cf4-aa63-3893f2e6bf8e

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.EssentialFiniteness
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place FunctionFieldRiemannRoch HasCanonicalDivisor IsCurveOver HasLocalResidue HasCanonicalLocalResidueKStar HasSeparableResidue functionFieldRiemannRoch_of_isAlgClosed dCoordGenerates_of_isCurveOver instIsCurveOverRatFunc"
p2m_open "AlgebraicCurve"

namespace RDOCK

section Adjoin

variable (K : Type*) [Field K] {LF : Type*} [Field LF] [Algebra K LF]

private theorem exists_transcendental_finiteDimensional (x : LF) (hx : Transcendental K x)
    (T : Finset LF) (hT : ∀ t ∈ T, IsIntegral K⟮x⟯ t) :
    ∃ x' : IntermediateField.adjoin K (insert x (T : Set LF)), Transcendental K x' ∧
      FiniteDimensional K⟮x'⟯ (IntermediateField.adjoin K (insert x (T : Set LF))) := by
  set F : IntermediateField K LF := IntermediateField.adjoin K (insert x (T : Set LF)) with hF
  have hxF : x ∈ F := subset_adjoin K _ (Set.mem_insert x _)
  have hTF : ∀ t ∈ T, t ∈ F := fun t ht => subset_adjoin K _ (Set.mem_insert_of_mem x ht)
  set x' : F := ⟨x, hxF⟩ with hx'

  have hx't : Transcendental K x' :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := LF) Subtype.val_injective).mp hx

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

  have hfd : FiniteDimensional A F := by
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
    rw [htop] at this
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := A) (E := F)).toLinearEquiv
  exact ⟨x', hx't, hfd⟩

end Adjoin

end RDOCK

end AlgebraicCurve

end

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar.AlgebraicCurve"

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6400000 in

theorem solution (N : ℕ) [NeZero N] :
    FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by

  have hpair : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      = IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N} :=
    laurentBaseChange_adjoin_pair (AlgebraicClosure ℚ) N (functionFieldGeneration N)
  have h : ∀ E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)),
      E = IntermediateField.adjoin (AlgebraicClosure ℚ)
        (insert (jqModC (AlgebraicClosure ℚ)) ((({jqNModC (AlgebraicClosure ℚ) N} : Finset (LaurentSeries (AlgebraicClosure ℚ))) : Set (LaurentSeries (AlgebraicClosure ℚ))))) →
      ∃ x' : E, Transcendental (AlgebraicClosure ℚ) x' ∧ FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set E)) E := by
    rintro E rfl
    refine AlgebraicCurve.RDOCK.exists_transcendental_finiteDimensional (AlgebraicClosure ℚ) (jqModC (AlgebraicClosure ℚ))
      (transcendental_jqModC (AlgebraicClosure ℚ)) {jqNModC (AlgebraicClosure ℚ) N} ?_
    intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    exact isIntegral_jqNModC_all (AlgebraicClosure ℚ) N
  obtain ⟨x', hx', hfd⟩ := h (modularFunctionFieldBar N) (by rw [Finset.coe_singleton]; exact hpair)

  let e := RatFunc.algEquivOfTranscendental x' hx'
  letI : Algebra (RatFunc (AlgebraicClosure ℚ)) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N))) := e.toAlgHom.toRingHom.toAlgebra
  letI : Algebra (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
    ((algebraMap (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)).comp e.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc (AlgebraicClosure ℚ)) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq fun q => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) r = algebraMap (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) (e (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) r))
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) r
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N))) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc (AlgebraicClosure ℚ)) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N)))) e.surjective
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) := Module.Finite.trans (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
  haveI : Algebra.IsIntegral (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) := Algebra.IsIntegral.of_finite (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N)
  haveI : CharZero (RatFunc (AlgebraicClosure ℚ)) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))).injective
  haveI : PerfectField (RatFunc (AlgebraicClosure ℚ)) := PerfectField.ofCharZero

  haveI := isCurveOver_modularFunctionFieldBar N
  haveI := hasCanonicalDivisor_modularFunctionFieldBar N
  haveI := essFiniteType_modularFunctionFieldBar N
  haveI : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  haveI := AlgebraicCurve.instIsCurveOverRatFunc (AlgebraicClosure ℚ)
  haveI : Algebra.EssFiniteType (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc (AlgebraicClosure ℚ)) (nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)))
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.comp (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
  haveI : ∀ v : Place (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)), v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  exact @functionFieldRiemannRoch_of_isAlgClosed (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
    _ _ (Classical.decEq _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

#print axioms solution

end S_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar (solution)
