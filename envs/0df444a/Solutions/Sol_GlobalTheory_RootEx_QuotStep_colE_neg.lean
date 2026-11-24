-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.colE_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:48.204238+00:00
-- url     : https://prove2.me/submissions/a260b613-165b-41d3-a4a9-8e5ba5b9c9e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution (q : ℕ) (β : n → k) : colE c q β * colE c q (-β) = 1 := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply, Units.val_one, ← fromBlocks_one]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = q <;> simp [h]
end GlobalTheory.RootEx.QuotStep
