-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.normsEscape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:33:05.035885+00:00
-- url     : https://prove2.me/submissions/75064ce1-5800-47b6-b144-6e5277c75de0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_NormsEscape_of_odd_top
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_normsEscape_of_pow_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormBaseChange
open NormIndex
variable {A : Type} [Field A] [CharZero A]
  (hA : ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B], IndexTwo B)
include hA
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B] :
    NormsEscape A B := by
  let M := IntermediateField.normalClosure A B (AlgebraicClosure B)
  haveI : IsGalois A M := {}
  haveI : FiniteDimensional B M := Module.Finite.of_restrictScalars_finite A B M
  haveI : IsGalois B M := IsGalois.tower_top_of_isGalois A B M
  let P : Sylow 2 (M ≃ₐ[B] M) := default
  let C := IntermediateField.fixedField (P : Subgroup (M ≃ₐ[B] M))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have hC : Module.finrank C M = 2 ^ n := by
    rw [IntermediateField.finrank_fixedField_eq_card, hn]
  have hodd : Odd (Module.finrank B C) := by
    have h1 := Module.finrank_mul_finrank B C M
    have h2 := (P : Subgroup (M ≃ₐ[B] M)).index_mul_card
    rw [IsGalois.card_aut_eq_finrank, ← h1, hn, hC] at h2
    rw [← Nat.eq_of_mul_eq_mul_right (by positivity) h2, ← Nat.not_even_iff_odd,
      even_iff_two_dvd]
    exact P.not_dvd_index
  have h : NormsEscape A C :=
    normsEscape_of_pow_two hA M _ (C.restrictScalars A) n rfl hC
  exact h.of_odd_top hodd
end GlobalTheory.QuadSymbol.NormBaseChange
