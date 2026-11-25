-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:05.667648+00:00
-- url     : https://prove2.me/submissions/7ecd85d8-7b90-475c-bce7-6c51fefcf3db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoinStatement
import Theorems.Thm_GlobalTheory_CycSpanFin_finiteDimensional_span_adjoin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  first | exact @GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | exact GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | (intros; apply GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin <;> assumption)
end _root_.GlobalTheory.T
