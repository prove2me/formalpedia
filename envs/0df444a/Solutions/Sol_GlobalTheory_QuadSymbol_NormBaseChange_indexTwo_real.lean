-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormBaseChange.indexTwo_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:05.689166+00:00
-- url     : https://prove2.me/submissions/7ca2a3a0-87ef-4a20-b3e0-962890ca59df

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
import Theorems.Thm_GlobalTheory_Published_HasseNormSt_of_isSquare
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_of_isSquare


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
theorem _root_.solution : IndexTwo ℝ := by
  intro d hd
  rw [Real.isSquare_iff, not_le] at hd
  refine ⟨⟨-1, by norm_num, ?_⟩, fun x y _ _ hx hy => Nm.of_isSquare _ ?_⟩
  · rintro ⟨a, b, h⟩
    nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg (neg_nonneg.2 hd.le) (sq_nonneg b)]
  · have h1 : x < 0 := not_le.1 fun h => hx (Nm.of_isSquare _ (Real.isSquare_iff.2 h))
    have h2 : y < 0 := not_le.1 fun h => hy (Nm.of_isSquare _ (Real.isSquare_iff.2 h))
    exact Real.isSquare_iff.2 (mul_pos_of_neg_of_neg h1 h2).le
end GlobalTheory.QuadSymbol.NormBaseChange
