-- Prove2me | solution 1 for GlobalTheory.T.exists_compact_preimage_embX_mul_colE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:11.922244+00:00
-- url     : https://prove2.me/submissions/10990fde-0cbd-42b4-8d53-31afeb58ad24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTriple
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTripleStatement
import Theorems.Thm_GlobalTheory_RootEx_ProperTriple_proper_triple


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C), ∃ D : Set (GL n k × N k n c (ρ + 1) × (n → k)), IsCompact D ∧ ∀ z : GL n k × N k n c (ρ + 1) × (n → k), embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  first | exact @GlobalTheory.RootEx.ProperTriple.proper_triple | exact GlobalTheory.RootEx.ProperTriple.proper_triple | (intros; apply GlobalTheory.RootEx.ProperTriple.proper_triple <;> assumption)
end _root_.GlobalTheory.T
