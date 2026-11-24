-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.exists_of_mem_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:09.61329+00:00
-- url     : https://prove2.me/submissions/3981336b-56fb-4165-82f6-10f9166010bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_entries
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_mem_inf_iff
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_VolN_exists_of_mem_R
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001


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
theorem _root_.solution {p : ℕ} {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p ⊓ R k n c (p + 1)) :
    ∃ x e, r = embX c x * chartB p e := by
  obtain ⟨x, g, hg, rfl⟩ := Radical.exists_of_mem_R hr.1
  obtain ⟨y, g', hg', e⟩ := Radical.exists_of_mem_R hr.2
  obtain rfl : y = x := by
    apply Units.ext
    rw [← Radical.toBlocks₁₁_embX_mul x hg, ← Radical.toBlocks₁₁_embX_mul y hg', e]
  obtain rfl : g = g' := mul_left_cancel e
  exact ⟨y, _, by rw [chartB, chart_entries _ g ((mem_inf_iff g).1 ⟨hg, hg'⟩)]⟩
end GlobalTheory.RootEx.QuotStep
