-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.indexTwo_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:35.716241+00:00
-- url     : https://prove2.me/submissions/9f12cae2-39cf-4709-a21e-f2b79c6f7495

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
import Theorems.Thm_GlobalTheory_QuadraticValuationIndexTwo_norm_index_two


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
open GlobalTheory.CNorm
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] : IndexTwo B := by
  first
  | (rename_i h_1 h_2 h_5 h_6 h_7; revert F h_1 h_2 v B h_5 h_6 h_7; exact @_root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two)
  | exact @_root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two
  | exact _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two
  | (apply _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuadraticValuationIndexTwo.norm_index_two ..)
end GlobalTheory.QuadSymbol.NormBaseChange
