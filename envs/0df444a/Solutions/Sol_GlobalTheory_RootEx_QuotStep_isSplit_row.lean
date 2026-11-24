-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.isSplit_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:12.763421+00:00
-- url     : https://prove2.me/submissions/724b697c-9473-4f75-a935-d4f68511f4eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_measurePreserving_mul
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chartN_entries
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chartB_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Model_rowE_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_rowE_mem
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
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution {p : ℕ} (hp1 : 1 ≤ p) (hp : p < c) : IsSplit (n := n) ν p (p + 1) (rowE c p) := by
  refine ⟨_, measurePreserving_mul (b := lev (p + 1)) (S := Both n c p) (fun _ h => h.2) ν
    (fun x => (Sum.inr ⟨p - 1, by omega⟩, Sum.inl x)) (fun x y h => by simpa using h)
    (fun x => by simp [lev]; omega)
    (fun x => by simp [lev]; omega) ?_ (rowE c p) (fun β x => by simp [rowE, lowU]; omega) ?_,
    fun y => chartN_entries (mul_mem (chartB_mem p _).2 (Radical.rowE_mem _ (Nat.lt_succ_self p)))⟩
  · rintro ⟨r | r, s | s⟩ <;> simp [Both, lev, Fin.ext_iff] <;> omega
  · rintro β (r | r) (s | s) h <;> simp [rowE, lowU, Matrix.one_apply]
    intro hs
    exact absurd (by simp [Fin.ext_iff, ← hs]) (h s)
end GlobalTheory.RootEx.QuotStep
