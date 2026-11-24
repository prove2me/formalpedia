-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.conj_colE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:49.802386+00:00
-- url     : https://prove2.me/submissions/73a4e4e6-f25e-41f1-9978-fdc4b4f35f32

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
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_val
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
theorem _root_.solution (q : ℕ) (x : GL n k) (β : n → k) :
    embX c x * colE c q β * (embX c x)⁻¹ = colE c q (x.val.mulVec β) := by
  apply Units.ext
  rw [Radical.conj_val]
  simp only [colE, upU, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_one, Units.mul_inv, Matrix.zero_mul]
  congr 1
  ext r i
  simp only [Matrix.mul_apply, Matrix.of_apply]
  split_ifs <;> simp [mulVec, dotProduct]
end GlobalTheory.RootEx.QuotStep
