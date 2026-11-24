-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.col_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:08.584065+00:00
-- url     : https://prove2.me/submissions/1708845b-9202-41ac-94ba-b788eba446b7

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
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
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
theorem _root_.solution {p : ℕ} (hp : p < c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p ⊓ N k n c (p + 1)) (β : n → k)
    (x : n) : (g * colE c (p + 1) β).val (Sum.inl x) (Sum.inr ⟨p, hp⟩) = β x := by
  have h1 := (Radical.mem_N_iff _).1 hg.2
  have h2 : ∀ y, g.val (Sum.inl x) (Sum.inl y) = (1 : Matrix n n k) x y := fun y => by
    rw [h1 _ _ (by simp [lev])]; simp [Matrix.one_apply]
  have h3 : g.val (Sum.inl x) (Sum.inr ⟨p, hp⟩) = 0 := by
    rw [h1 _ _ (by simp [lev])]; simp
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, h2, h3, Matrix.one_apply]
end GlobalTheory.RootEx.QuotStep
