-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.mem_inf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:46.6918+00:00
-- url     : https://prove2.me/submissions/5676daf2-98a3-45eb-ba1b-4a7740b508e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution {p : ℕ} (g : GL (n ⊕ Fin c) k) : g ∈ N k n c p ⊓ N k n c (p + 1) ↔
    ∀ r s, ¬ Both n c p (r, s) → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rw [Subgroup.mem_inf, Radical.mem_N_iff, Radical.mem_N_iff]
  constructor
  · rintro ⟨h1, h2⟩ r s h
    rcases not_and_or.1 h with h | h
    · exact h1 r s (not_lt.1 h)
    · exact h2 r s (not_lt.1 h)
  · exact fun h => ⟨fun r s hrs => h r s fun h' => absurd h'.1 (not_lt.2 hrs),
      fun r s hrs => h r s fun h' => absurd h'.2 (not_lt.2 hrs)⟩
end GlobalTheory.RootEx.QuotStep
