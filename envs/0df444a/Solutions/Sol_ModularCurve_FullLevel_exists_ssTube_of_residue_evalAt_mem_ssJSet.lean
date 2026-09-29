-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_ssTube_of_residue_evalAt_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/32903560-951d-5699-a665-96f44bbdef42

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
import Theorems.Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_ModularCurve_FullLevel_isIntegral_inclusion_modularFunctionFieldBar_fieldBar
import Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffEmb_jq ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace N2RedPole

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem T_mem_gamma0 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.T]

theorem transcendental_and_finiteDimensional_bar (M' : ℕ) [NeZero M']
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (y : ↥E) (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    Transcendental (AlgebraicClosure ℚ) y ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥E)) ↥E := by
  subst hE
  exact ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
    (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma0 M') (T_mem_gamma0 M') y hy

theorem finrank_adjoin_bar (M' : ℕ) [NeZero M']
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = modularFunctionFieldFullC (AlgebraicClosure ℚ) M')
    (y : ↥E) (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥E)) ↥E = dedekindPsi M' := by
  subst hE
  obtain rfl : y = ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) M'⟩ := Subtype.ext hy
  exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (AlgebraicClosure ℚ) M'
    (Nat.cast_ne_zero.mpr (NeZero.ne M'))

theorem finrank_adjoin_geom (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type*) [Field κ] [CharP κ q] :
    Module.finrank ↥(IntermediateField.adjoin κ ({(⟨jqModC κ, jqModC_mem κ M'⟩ : ↥(modularFunctionFieldC κ M'))} :
        Set ↥(modularFunctionFieldC κ M'))) ↥(modularFunctionFieldC κ M') = dedekindPsi M' := by
  have h1 := IntermediateField.lift_adjoin_simple κ (modularFunctionFieldC κ M') ⟨jqModC κ, jqModC_mem κ M'⟩
  have h2 : IntermediateField.adjoin κ ({jqModC κ} : Set (LaurentSeries κ)) =
      IntermediateField.map (modularFunctionFieldC κ M').val
        (IntermediateField.adjoin κ ({(⟨jqModC κ, jqModC_mem κ M'⟩ : ↥(modularFunctionFieldC κ M'))} :
          Set ↥(modularFunctionFieldC κ M'))) := h1.symm
  have hE : IntermediateField.comap (modularFunctionFieldC κ M').val (IntermediateField.adjoin κ ({jqModC κ} : Set (LaurentSeries κ))) =
      IntermediateField.adjoin κ ({(⟨jqModC κ, jqModC_mem κ M'⟩ : ↥(modularFunctionFieldC κ M'))} :
        Set ↥(modularFunctionFieldC κ M')) := by
    rw [h2, IntermediateField.comap_map]
  have h := IntermediateField.finrank_comap (IntermediateField.adjoin κ ({jqModC κ} : Set (LaurentSeries κ)))
    (modularFunctionFieldC κ M').val
  rw [IntermediateField.fieldRange_val,
    ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi κ M' q hqM'] at h
  have h' := congrArg (fun K' : IntermediateField κ ↥(modularFunctionFieldC κ M') =>
    Module.finrank ↥K' ↥(modularFunctionFieldC κ M')) hE
  exact h'.symm.trans h

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
  (A : ValuationSubring (AlgebraicClosure ℚ))
  (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))

theorem mem_integers_j (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :
    ∃ hjO : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers, R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩ = jGeomGen (ResidueField A) M' := by
  have e : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [coeffMap_jqModC, coeffEmb_jq]
  have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [e]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨h, hres⟩ := hR₀ (jqModC ↥A) hy
  have helt : (⟨coeffMap A.subtype (jqModC ↥A), hy⟩ : ↥(modularFunctionFieldBar M')) = (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) := Subtype.ext e
  refine ⟨helt ▸ h, ?_⟩
  apply Subtype.ext
  rw [coe_jGeomGen, ← coeffMap_jqModC (IsLocalRing.residue ↥A), ← hres]
  congr 2
  exact Subtype.ext helt.symm

theorem cuspPole_data (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M')
    (hjO : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) (hres : R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩ = jGeomGen (ResidueField A) M') :
    ∃ (Du : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'))
      (Dū : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')),
      (∀ P, Du P = max 0 (-(P.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))))) ∧
      (∀ Q, Dū Q = max 0 (-(Q.ord (R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩)))) ∧
      Divisor.degree Dū = Divisor.degree Du ∧ Dū ≠ 0 ∧
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) < 0 → 0 < P.deg) := by
  classical

  have hBar : modularFunctionFieldBar M' =
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  have hcoe : (((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
    coeffEmb_jq
  obtain ⟨htr, hfd⟩ := transcendental_and_finiteDimensional_bar M' _ hBar (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hcoe
  haveI := hfd
  obtain ⟨Du, hDu⟩ := AlgebraicCurve.exists_poleDivisor_of_transcendental (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) htr
  have hdegu : Divisor.degree Du = (dedekindPsi M' : ℤ) := by
    rw [AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) htr Du hDu,
      finrank_adjoin_bar M' _ (ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
        (AlgebraicClosure ℚ) M') (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hcoe]

  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  have htr' : Transcendental (ResidueField ↥A) (jGeomGen (ResidueField ↥A) M') := by
    rw [← transcendental_algebraMap_iff
      (A := LaurentSeries (ResidueField ↥A)) (modularFunctionFieldC (ResidueField ↥A) M').val.toRingHom.injective]
    exact transcendental_jqModC (ResidueField ↥A)
  haveI hfd' : FiniteDimensional ↥(IntermediateField.adjoin (ResidueField ↥A)
      ({jGeomGen (ResidueField ↥A) M'} : Set ↥(modularFunctionFieldC (ResidueField ↥A) M')))
      ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    ModularCurve.finiteDimensional_adjoin_jqModC A
  obtain ⟨Dū, hDū⟩ := AlgebraicCurve.exists_poleDivisor_of_transcendental (jGeomGen (ResidueField ↥A) M') htr'
  have hdegū : Divisor.degree Dū = (dedekindPsi M' : ℤ) := by
    rw [AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental _ htr' Dū hDū]
    exact_mod_cast finrank_adjoin_geom q M' hqM' (ResidueField ↥A)
  have hpos : 0 < Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A)
      ({jGeomGen (ResidueField ↥A) M'} : Set ↥(modularFunctionFieldC (ResidueField ↥A) M')))
      ↥(modularFunctionFieldC (ResidueField ↥A) M') := Module.finrank_pos
  refine ⟨Du, Dū, hDu, fun Q => by rw [hDū Q, hres], by rw [hdegu, hdegū], ?_, ?_⟩
  · intro h0
    have := AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental _ htr' Dū hDū
    rw [h0, map_zero] at this
    omega
  · intro P _
    rw [AlgebraicCurve.Place.deg_eq_one_of_isRational (ModularCurve.isRational_place_modularFunctionFieldBar M' P)]
    exact Nat.one_pos

theorem ord_residue_j_neg (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M') (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (hjO : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) :
    ∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P'.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) < 0 →
      (R₀.placeMap P').ord (R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩) < 0 := by
  obtain ⟨hjO', hres⟩ := mem_integers_j M' A R₀ hR₀
  obtain ⟨Du, Dū, hDu, hDū, hdeg, hnc, hfin⟩ := cuspPole_data q M' A R₀ hA hqM' hjO hres
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M'
  exact (AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
    R₀ (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hjO Du hDu Dū hDū hdeg hnc hfin).2.1

theorem placeMap_ne_of_ord_j_neg (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M') (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (P₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) (hP₀ : P₀.IsRational)
    (hjP₀ : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ P₀.toValuationSubring) (hjA₀ : P₀.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ A) :
    ∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P'.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) < 0 → R₀.placeMap P' ≠ R₀.placeMap P₀ := by
  obtain ⟨hjO, hres⟩ := mem_integers_j M' A R₀ hR₀
  obtain ⟨Du, Dū, hDu, hDū, hdeg, hnc, hfin⟩ := cuspPole_data q M' A R₀ hA hqM' hjO hres
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M'
  exact (AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
    R₀ (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hjO Du hDu Dū hDū hdeg hnc hfin).2.2 P₀ hP₀ hjP₀ hjA₀

end N2RedPole

namespace N2RedPole

theorem jNGeomGen_mem_of_jGeomGen_mem (κ : Type*) [Field κ] (M' : ℕ) [NeZero M']
    (w : Place κ ↥(modularFunctionFieldC κ M'))
    (hj : jGeomGen κ M' ∈ w.toValuationSubring) : jNGeomGen κ M' ∈ w.toValuationSubring := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData M'
  let φ : Polynomial ℤ →+* ↥w.toValuationSubring :=
    Polynomial.eval₂RingHom (Int.castRingHom ↥w.toValuationSubring) ⟨jGeomGen κ M', hj⟩
  have hint : IsIntegral ↥w.toValuationSubring (jNGeomGen κ M') := by
    refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥w.toValuationSubring ↥(modularFunctionFieldC κ M')).comp φ =
        Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC κ M')) (jGeomGen κ M') := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp only [φ, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
    rw [hcomp]
    exact evalModularPair_jGeomGen_eq_zero κ M' data
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥w.toValuationSubring)
    (K := ↥(modularFunctionFieldC κ M'))).mp hint
  rw [← hy]
  exact y.2

end N2RedPole

namespace N2Spine

open AlgebraicCurve

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_contra h
  push_neg at h
  have hf0 : f ≠ 0 := by rintro rfl; simp at h
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    Place.mem_toValuationSubring_of_ord_nonneg_alt v (inv_ne_zero hf0) (by rw [Place.ord_inv]; omega)
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩
  have h0 := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at h0
  change v.ord f = 0 at h0
  omega

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem evalAt_restrictAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (hw : w.IsRational)
    (hw₀ : (w.restrictAlong φ hφ).IsRational) (f : F) (hf : f ∈ (w.restrictAlong φ hφ).toValuationSubring) :
    (w.restrictAlong φ hφ).evalAt f = w.evalAt (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have hf' : φ f ∈ w.toValuationSubring := hf
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw hf']
  change algebraMap K w.ResidueField ((w.restrict F).evalAt f) = _
  rw [IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField,
    (w.restrict F).algebraMap_evalAt hw₀ hf, Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue]
  rfl

end N2Spine

set_option maxHeartbeats 0 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :

    ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
      ∀ (hjP : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ P.toValuationSubring) (hjA : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ A),
        IsLocalRing.residue ↥A ⟨_, hjA⟩ ∈ ModularCurve.ssJSet q (ResidueField ↥A) →
      ∃ s : ↥W, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ maximalIdeal A := by
  classical
  intro P hPrat hjP hjA hss
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M'

  have hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral :=
    ModularCurve.FullLevel.isIntegral_inclusion_modularFunctionFieldBar_fieldBar q M' hle
  let P₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') := P.restrictAlong (IntermediateField.inclusion hle) hint
  have hmem : ∀ f, f ∈ P₀.toValuationSubring ↔ IntermediateField.inclusion hle f ∈ P.toValuationSubring :=
    fun f => N2Spine.mem_restrictAlong_iff _ hint P f
  have hrat₀ : P₀.IsRational := ModularCurve.isRational_place_modularFunctionFieldBar M' P₀
  have hev : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ P₀.toValuationSubring),
      P₀.evalAt f = P.evalAt (IntermediateField.inclusion hle f) :=
    fun f hf => N2Spine.evalAt_restrictAlong _ hint P hPrat hrat₀ f hf

  have hj0P : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ P₀.toValuationSubring := (hmem _).mpr hjP
  have hj0A : P₀.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ A := by rw [hev _ hj0P]; exact hjA
  obtain ⟨hjO, hjres⟩ := N2RedPole.mem_integers_j M' A R₀ hR₀
  have hpole := N2RedPole.placeMap_ne_of_ord_j_neg q M' A R₀ hA hqM' hR₀ P₀ hrat₀ hj0P hj0A

  obtain ⟨hm_j, h_j, hcomp_j⟩ :=
    AlgebraicCurve.ConstantReduction.exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
      R₀ P₀ hrat₀ _ hjO hj0P hpole

  have hsrat : (R₀.placeMap P₀).IsRational :=
    (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField _).mp
      (by rw [R₀.deg_placeMap, AlgebraicCurve.Place.deg_eq_one_of_isRational hrat₀])
  have hjG : jGeomGen (ResidueField ↥A) M' ∈ (R₀.placeMap P₀).toValuationSubring := by
    rw [← hjres]; exact hm_j
  have hjN : jNGeomGen (ResidueField ↥A) M' ∈ (R₀.placeMap P₀).toValuationSubring :=
    N2RedPole.jNGeomGen_mem_of_jGeomGen_mem (ResidueField ↥A) M' _ hjG
  have hsval : (R₀.placeMap P₀).evalAt (jGeomGen (ResidueField ↥A) M') = IsLocalRing.residue ↥A ⟨P₀.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), h_j⟩ := by
    apply (R₀.placeMap P₀).algebraMap_residueField_injective
    rw [(R₀.placeMap P₀).algebraMap_evalAt hsrat hjG, hcomp_j]
    congr 1
    exact Subtype.ext hjres.symm
  have hss' : (R₀.placeMap P₀).evalAt (jGeomGen (ResidueField ↥A) M') ∈ ModularCurve.ssJSet q (ResidueField ↥A) := by
    rw [hsval]
    have e : (⟨P₀.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), h_j⟩ : ↥A) = ⟨_, hjA⟩ := Subtype.ext (hev _ hj0P)
    rw [e]; exact hss
  have hsW : R₀.placeMap P₀ ∈ W :=
    (hW _).mpr ((ModularCurve.mem_ssPlaces_iff q M' (ResidueField ↥A)).mpr ⟨hsrat, ⟨hjG, hjN⟩, hss'⟩)
  refine ⟨⟨R₀.placeMap P₀, hsW⟩, ?_⟩

  intro f hf hguard hfs a ha
  have hj0ord : 0 ≤ P₀.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) := N2Spine.ord_nonneg_of_mem P₀ hj0P
  have hfP₀ : f ∈ P₀.toValuationSubring := by
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _
    · exact AlgebraicCurve.Place.mem_toValuationSubring_of_ord_nonneg_alt P₀ hf0 (hguard P₀ hj0ord)
  have hpole_f : ∀ P', P'.ord (f : ↥(modularFunctionFieldBar M')) < 0 → R₀.placeMap P' ≠ R₀.placeMap P₀ := by
    intro P' h
    apply hpole P'
    by_contra hn
    push_neg at hn
    exact absurd (hguard P' hn) (not_le.mpr h)
  obtain ⟨hm_f, h_f, hcomp_f⟩ :=
    AlgebraicCurve.ConstantReduction.exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
      R₀ P₀ hrat₀ f hf hfP₀ hpole_f
  have hres : IsLocalRing.residue ↥A ⟨P₀.evalAt f, h_f⟩ = IsLocalRing.residue ↥A a := by
    apply (algebraMap (ResidueField ↥A) (R₀.placeMap P₀).ResidueField).injective
    rw [hcomp_f, ha, (R₀.placeMap P₀).algebraMap_evalAt hsrat hm_f]
  have hdiff : (⟨P₀.evalAt f, h_f⟩ : ↥A) - a ∈ maximalIdeal ↥A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  rw [← hev f hfP₀]
  exact ⟨((⟨P₀.evalAt f, h_f⟩ : ↥A) - a).2, hdiff⟩

end S_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet (solution)
