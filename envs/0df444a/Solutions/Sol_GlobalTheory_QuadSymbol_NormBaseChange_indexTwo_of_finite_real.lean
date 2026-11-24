-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.indexTwo_of_finite_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:22.076695+00:00
-- url     : https://prove2.me/submissions/aca3d924-1f6a-4595-bf86-0da9dc0338b5

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
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_IndexTwo_of_ringEquiv
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_indexTwo_real
import Theorems.Thm_GlobalTheory_QuadSymbol_NormBaseChange_indexTwo_of_isAlgClosed

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
namespace GlobalTheory.QuadSymbol.NormBaseChange
theorem _root_.solution (B : Type) [Field B] [Algebra ℝ B] [Algebra.IsAlgebraic ℝ B] :
    IndexTwo B := by
  rcases Real.nonempty_algEquiv_or B with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact indexTwo_real.of_ringEquiv e.toRingEquiv
  · exact (indexTwo_of_isAlgClosed ℂ).of_ringEquiv e.toRingEquiv
end GlobalTheory.QuadSymbol.NormBaseChange
