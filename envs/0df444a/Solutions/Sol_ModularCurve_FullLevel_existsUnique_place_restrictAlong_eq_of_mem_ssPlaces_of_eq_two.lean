-- Prove2me | solution 1 for ModularCurve.FullLevel.existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a3d7f8f7-8b60-504e-8488-b28736368bd7

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

namespace RamInftyQ2

open AlgebraicCurve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_restrictAlong_iff {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

theorem inclusion_self_apply (S : IntermediateField K L) (h : S ≤ S) (x : S) :
    IntermediateField.inclusion h x = x :=
  Subtype.ext rfl

theorem restrictAlong_inclusion_self (S : IntermediateField K L) (h : S ≤ S)
    (hint : (IntermediateField.inclusion h).toRingHom.IsIntegral) (w : Place K S) :
    w.restrictAlong (IntermediateField.inclusion h) hint = w := by
  ext x
  rw [mem_restrictAlong_iff, inclusion_self_apply]

theorem existsUnique_of_eq {S T : IntermediateField K L} (hTS : T = S) (hle : S ≤ T)
    (hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral) (s : Place K S) :
    ∃! w : Place K T, w.restrictAlong (IntermediateField.inclusion hle) hint = s := by
  subst hTS
  refine ⟨s, restrictAlong_inclusion_self _ hle hint s, fun w hw => ?_⟩
  have hw' : w.restrictAlong (IntermediateField.inclusion hle) hint = s := hw
  rw [restrictAlong_inclusion_self _ hle hint w] at hw'
  exact hw'

end RamInftyQ2

set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))
    (hint : RingHom.IsIntegral (IntermediateField.inclusion hle).toRingHom)
    (s : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hs : s ∈ ssPlaces q M' (ResidueField A)) :
    ∃! w : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      w.restrictAlong (IntermediateField.inclusion hle) hint = s :=
  RamInftyQ2.existsUnique_of_eq
    (xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_liesOverPrime_of_eq_two q hq2 M' hqM' A hA) hle hint s

end S_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_two (solution)
