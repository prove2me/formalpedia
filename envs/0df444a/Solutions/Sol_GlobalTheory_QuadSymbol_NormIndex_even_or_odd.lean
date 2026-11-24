-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormIndex.even_or_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:42:41.004796+00:00
-- url     : https://prove2.me/submissions/d7ee3434-defb-4e5d-bb2a-d11972c132be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormIndex
variable {K : Type} [Field K]
variable (w : Valuation K ℤᵐ⁰)
namespace GlobalTheory.QuadSymbol.NormIndex
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    (∃ n : ℤ, w x = WithZero.exp (2 * n)) ∨ ∃ n : ℤ, w x = WithZero.exp (2 * n + 1) := by
  have h := (WithZero.exp_log ((Valuation.ne_zero_iff w).2 hx)).symm
  rcases Int.even_or_odd' (WithZero.log (w x)) with ⟨k, hk | hk⟩
  · exact Or.inl ⟨k, by rw [h, hk]⟩
  · exact Or.inr ⟨k, by rw [h, hk]⟩
end GlobalTheory.QuadSymbol.NormIndex
