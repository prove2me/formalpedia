-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:17:11.753568+00:00
-- url     : https://prove2.me/submissions/f4565427-1277-4bde-b2e8-ebc27784fef5

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_indexTwo_infinite
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_indexTwo_finite
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_baseChangeAt

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
open NormBaseChange
namespace GlobalTheory.QuadSymbol
theorem _root_.solution : ∀ (F E K L : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra F E] [Algebra F K] [Algebra K L]
    [Algebra E L] [Algebra F L] [IsScalarTower F K L] [IsScalarTower F E L]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsQuadraticExtension K L],
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F E K L (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F E K L v.Completion := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hgen
  have hE := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hL := Algebra.IsQuadraticExtension.finrank_eq_two K L
  exact ⟨fun v => baseChangeAt F E K L _ hE hL hgen (indexTwo_finite F v),
    fun w => baseChangeAt F E K L _ hE hL hgen (indexTwo_infinite F w)⟩
end GlobalTheory.QuadSymbol
