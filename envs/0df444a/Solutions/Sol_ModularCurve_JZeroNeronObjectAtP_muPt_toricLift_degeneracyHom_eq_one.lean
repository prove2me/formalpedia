-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.muPt_toricLift_degeneracyHom_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c8ca5717-437e-5697-9a90-d6cbdb3cb7e6

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_bialgHom_apply_eq_algebraMap_counit_of_etale_cartierDual_of_sub_mem_map_maximalIdeal
import Theorems.Thm_CartierDual_algebraEtale_addMonoidAlgebra
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul
import Theorems.Thm_ModularCurve_isFinite_and_flat_schemeNsmul_baseChange_of_jZeroC_points
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_muPt_toricLift_degeneracyHom_eq_one
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace PtsTriv

theorem mem_map_of_forall_apply_mem {S : Type} [CommRing S] (I : Ideal S) {M : Type} [AddCommMonoid M]
    (x : AddMonoidAlgebra S M) (hx : ∀ j : M, x.coeff j ∈ I) :
    x ∈ I.map (algebraMap S (AddMonoidAlgebra S M)) := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  have : (AddMonoidAlgebra.single j (x.coeff j) : AddMonoidAlgebra S M) =
      algebraMap S (AddMonoidAlgebra S M) (x.coeff j) * AddMonoidAlgebra.single j 1 := by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hx j))

theorem eq_one_of_mul_self {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

end PtsTriv

open PtsTriv in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (i : Fin 2)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    (muPt A O.toricRank m χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ (O.degeneracyHom i).1 =
      (Λ.L.one (barPt A ≫ Λ.σA)).1 := by
  classical

  obtain ⟨hbundle, hcomm, -, -, hspadd, -, -⟩ :=
    (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from hΛ)

  obtain ⟨hfin, hflat⟩ := ModularCurve.isFinite_and_flat_schemeNsmul_baseChange_of_jZeroC_points
      N₀ p hpN₀ Λ.L hbundle hcomm A hA Λ.σA Λ.ptsSp hspadd Λ.σA m hm

  have hcommA : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A))
      (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)),
      (Λ.L.baseChange Λ.σA).mul t x y = (Λ.L.baseChange Λ.σA).mul t y x :=
    fun t x y => RelativeGroupLaw.IsCommutative.baseChange (ι := Λ.σA) (G := Λ.L) hcomm t x y
  obtain ⟨H, _instCR, _instHopf, hHfin, hHflat, hHcocomm, e, he_mul, he_nat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat_schemeNsmul
      (Λ.L.baseChange Λ.σA) hcommA m hfin hflat
  haveI := hHfin
  haveI := hHflat
  haveI := hHcocomm
  haveI : Module.Free ↥A H := Module.free_of_flat_of_isLocalRing

  obtain ⟨φ, hφ⟩ := ModularCurve.JZeroNeronObjectAtP.exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq
    N₀ p hpN₀ A hA Λ hΛ O m hm i H e he_mul he_nat

  have he_one : ∀ (T : Type) [CommRing T] [Algebra ↥A T],
      ((e T 1).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)) = (Λ.L.baseChange Λ.σA).one _ := by
    intro T _ _
    apply eq_one_of_mul_self
    rw [← he_mul, mul_one]

  have hone_fst : ∀ (T : Type) [CommRing T] [Algebra ↥A T],
      ((Λ.L.baseChange Λ.σA).one (Spec.map (CommRingCat.ofHom (algebraMap ↥A T)))).1 ≫ pullback.fst Λ.f Λ.σA =
        (Λ.L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥A T)) ≫ Λ.σA)).1 := by
    intro T _ _
    rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]

  set κ := ResidueField ↥A with hκ
  set Tκ := muCoord κ O.toricRank m with hTκ

  let ψ₀ : muCoord ↥A O.toricRank m →ₐ[↥A] Tκ :=
    { AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (residue ↥A) with
      commutes' := fun r => by
        change AddMonoidAlgebra.mapRingHom _ (residue ↥A) (algebraMap ↥A (muCoord ↥A O.toricRank m) r) =
          algebraMap ↥A Tκ r
        rw [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
          Function.comp_apply, AddMonoidAlgebra.mapRingHom_single]
        rfl }
  have hψ₀ : Spec.map (CommRingCat.ofHom ψ₀.toRingHom) = muBaseChange (residue ↥A) O.toricRank m := rfl
  have hcong : ∀ a : H, φ a - algebraMap ↥A _ (Coalgebra.counit a) ∈
      (IsLocalRing.maximalIdeal ↥A).map (algebraMap ↥A (muCoord ↥A O.toricRank m)) := by

    have h1 : ((e Tκ (.toConv (ψ₀.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m)))).val :
        SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)).1 ≫ pullback.fst Λ.f Λ.σA =
          (Λ.L.one (muStr κ O.toricRank m ≫ resPt A ≫ Λ.σA)).1 := by
      rw [hφ Tκ ψ₀, hψ₀]
      exact ModularCurve.JZeroNeronObjectAtP.muBaseChange_toricLift_degeneracyHom_eq_one N₀ p hpN₀ A hA Λ hΛ O m hm i
    have hbase : Spec.map (CommRingCat.ofHom (algebraMap ↥A Tκ)) = muStr κ O.toricRank m ≫ resPt A := by
      rw [IsScalarTower.algebraMap_eq ↥A κ Tκ, CommRingCat.ofHom_comp, Spec.map_comp]
      rfl
    have h2 : ((e Tκ 1).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)).1 ≫
        pullback.fst Λ.f Λ.σA = (Λ.L.one (muStr κ O.toricRank m ≫ resPt A ≫ Λ.σA)).1 := by
      rw [he_one, hone_fst, hbase, Category.assoc]
    have h12 : e Tκ (.toConv (ψ₀.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m))) = e Tκ 1 := by
      apply Subtype.ext
      apply Subtype.ext
      apply pullback.hom_ext
      · rw [h1, h2]
      · rw [(e Tκ _).val.2, (e Tκ 1).val.2]
    have h3 : ψ₀.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m) =
        (Algebra.ofId ↥A Tκ).comp (Bialgebra.counitAlgHom ↥A H) := by
      have := (e Tκ).injective h12
      rw [AlgHom.convOne_def] at this
      exact WithConv.toConv_injective this
    intro a
    have hdiff : ψ₀ (φ a - algebraMap ↥A _ (Coalgebra.counit a)) = 0 := by
      have ha := congrArg (fun f : H →ₐ[↥A] Tκ => f a) h3
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply] at ha
      rw [map_sub, AlgHom.commutes, sub_eq_zero]
      exact ha
    apply mem_map_of_forall_apply_mem
    intro j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have hj := congrArg (fun y : Tκ => AddMonoidAlgebra.coeff y j) hdiff
    change AddMonoidAlgebra.coeff (AddMonoidAlgebra.mapRingHom _ (residue ↥A) _) j = AddMonoidAlgebra.coeff (0 : Tκ) j at hj
    rwa [AddMonoidAlgebra.coeff_mapRingHom] at hj

  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : Algebra.Etale (↥A) (CartierDual (↥A) (muCoord ↥A O.toricRank m)) :=
    CartierDual.algebraEtale_addMonoidAlgebra (↥A) (Fin O.toricRank → ZMod m)
  have hrig := HopfAlgebra.bialgHom_apply_eq_algebraMap_counit_of_etale_cartierDual_of_sub_mem_map_maximalIdeal
    (muCoord ↥A O.toricRank m) H φ hcong
  have hcomp : χ.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m) =
      (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (Bialgebra.counitAlgHom ↥A H) := by
    ext a
    simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
    rw [show (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m) a = φ a from rfl, hrig a, AlgHom.commutes]

  have hQ := hφ (AlgebraicClosure ℚ) χ
  rw [hcomp, ← AlgHom.convOne_def, he_one, hone_fst] at hQ

  exact hQ.symm

#print axioms solution

end

end S_ModularCurve_JZeroNeronObjectAtP_muPt_toricLift_degeneracyHom_eq_one
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_muPt_toricLift_degeneracyHom_eq_one (solution)
