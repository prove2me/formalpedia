-- Prove2me | solution 1 for ModularCurve.FullLevel.isIntegral_adjoin_residue_jq_residue_of_mem_admissible_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/cf879d87-9861-5dfe-949b-b2cd6383176b

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_isCurveOver_and_essFiniteType_of_le_of_transcendental_mem
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_AlgebraicCurve_mem_integralClosure_iff_forall_place
import Theorems.Thm_ModularCurve_FullLevel_residue_mem_toValuationSubring_of_cuspRegular_of_isRational
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isIntegral_adjoin_residue_jq_residue_of_mem_admissible_of_prime
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 12800000
open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups
attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)

    (𝒜 : Subring (LaurentSeries ℚ))
    (h𝒜 : ∀ gf : LaurentSeries ℚ, gf ∈ 𝒜 ↔
      ∃ (hgf : gf ∈ modularFunctionFieldFull M')
        (_ : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M')))
    (hj𝒜 : jq ∈ 𝒜) :
    ∀ (gf : LaurentSeries ℚ) (hgf : gf ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      gf ∈ 𝒜 →
      ∀ (hji : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      IsIntegral ↥(Algebra.adjoin (ResidueField A) ({(R₀.residue ⟨_, hji⟩ : modularFunctionFieldC (ResidueField A) M')} : Set (modularFunctionFieldC (ResidueField A) M')))
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') := by
  intro gf hgf hgi hgA hji
  classical
  obtain ⟨_, _, hcusp⟩ := (h𝒜 gf).mp hgA

  haveI hκ : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) M'
  haveI instFullEFT : Algebra.EssFiniteType (ResidueField ↥A) ↥(ModularCurve.modularFunctionFieldFullC (ResidueField ↥A) M') :=
    ModularCurve.essFiniteType_modularFunctionFieldFullC (ResidueField ↥A) M'
  haveI instFullCO : IsCurveOver (ResidueField ↥A) ↥(ModularCurve.modularFunctionFieldFullC (ResidueField ↥A) M') :=
    ModularCurve.isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) M'
  have htF : Transcendental (ResidueField ↥A)
      (⟨jqModC (ResidueField ↥A), ModularCurve.jqModC_mem_full (ResidueField ↥A) M'⟩ : ↥(ModularCurve.modularFunctionFieldFullC (ResidueField ↥A) M')) := fun halg =>
    ModularCurve.transcendental_jqModC (ResidueField ↥A) (halg.algebraMap (A := LaurentSeries (ResidueField ↥A)))
  have hfdF := @AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
    (ResidueField ↥A) ↥(ModularCurve.modularFunctionFieldFullC (ResidueField ↥A) M') _ _ _ instFullCO instFullEFT _ htF

  haveI : Algebra.EssFiniteType (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    (AlgebraicCurve.isCurveOver_and_essFiniteType_of_le_of_transcendental_mem (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))
      (modularFunctionFieldC (ResidueField ↥A) M') (ModularCurve.modularFunctionFieldFullC (ResidueField ↥A) M')
      (ModularCurve.modularFunctionFieldC_le_full (ResidueField ↥A) M') (jqModC (ResidueField ↥A))
      (ModularCurve.jqModC_mem (ResidueField ↥A) M') (ModularCurve.transcendental_jqModC (ResidueField ↥A))
      ⟨_, htF, hfdF⟩).2.1

  have hrat : ∀ w : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'), w.IsRational := by
    intro w
    haveI : Module.Finite (ResidueField ↥A) w.ResidueField := IsCurveOver.finiteResidue w
    haveI : Algebra.IsIntegral (ResidueField ↥A) w.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField ↥A) (K := w.ResidueField)).2

  have hfloor : (R₀.residue ⟨_, hji⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')) = jGeomGen (ResidueField ↥A) M' := by
    have hid1 : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
      show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ)
      exact coeffMap_jqModC _
    have hy1 : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
      rw [coeffMap_jqModC, ← hid1]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
    obtain ⟨h1, hval⟩ := hR₀ (jqModC ↥A) hy1
    have hsub : (⟨⟨coeffMap A.subtype (jqModC ↥A), hy1⟩, h1⟩ : ↥R₀.integers) = ⟨_, hji⟩ := by
      apply Subtype.ext; apply Subtype.ext
      show coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq
      rw [coeffMap_jqModC, hid1]
    rw [hsub, coeffMap_jqModC] at hval
    apply Subtype.ext
    rw [hval, ModularCurve.coe_jGeomGen]

  set R : Subalgebra (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    Algebra.adjoin (ResidueField ↥A) ({(R₀.residue ⟨_, hji⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M'))} : Set ↥(modularFunctionFieldC (ResidueField ↥A) M')) with hR
  have hmem : (R₀.residue ⟨_, hgi⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')) ∈ integralClosure ↥R ↥(modularFunctionFieldC (ResidueField ↥A) M') := by
    rw [AlgebraicCurve.mem_integralClosure_iff_forall_place]
    intro v hv
    have hjv : jGeomGen (ResidueField ↥A) M' ∈ v.toValuationSubring := by
      rw [← hfloor]
      exact hv (Algebra.self_mem_adjoin_singleton (ResidueField ↥A) _)
    exact ModularCurve.FullLevel.residue_mem_toValuationSubring_of_cuspRegular_of_isRational
      q M' hqM' A hA R₀ hR₀ gf hgf hgi hcusp v (hrat v) hjv
  first
    | exact hmem
    | exact (_root_.mem_integralClosure_iff).mp hmem
    | exact Subalgebra.mem_carrier.mp hmem

end S_ModularCurve_FullLevel_isIntegral_adjoin_residue_jq_residue_of_mem_admissible_of_prime
end P2MW
export P2MW.S_ModularCurve_FullLevel_isIntegral_adjoin_residue_jq_residue_of_mem_admissible_of_prime (solution)
