-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspLabel.root_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:50:58.907351+00:00
-- url     : https://prove2.me/submissions/691efe3f-b5e7-4c7c-bc9c-c4a20c034241

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterCuspidalRootSumRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumUnipotentRadicalEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSumStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_isIntegral
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspLabel
namespace GlobalTheory.CompanionTheory.TyFin.CuspLabel
theorem _root_.solution {K : Type} [Field K] [Fintype K] {P : K[X]} (hmon : P.Monic) (hirr : Irreducible P)
    (hX : P ≠ X) {x : AlgebraicClosure K} (hx : aeval x P = 0) :
    x ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hirr hx hmon
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfr : Module.finrank K (IntermediateField.adjoin K {x}) = P.natDegree := by
    rw [hmin, IntermediateField.adjoin.finrank hint]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hX (hmin.trans (minpoly.zero K _))
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI := Fintype.ofFinite (IntermediateField.adjoin K {x})
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ P.natDegree := by
    rw [← hfr]; exact Module.card_eq_pow_finrank
  have hy : IntermediateField.AdjoinSimple.gen K x ≠ 0 := by
    intro h
    exact hx0 (by simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h)
  have h := FiniteField.pow_card_sub_one_eq_one _ hy
  rw [hcard] at h
  simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h
end GlobalTheory.CompanionTheory.TyFin.CuspLabel
