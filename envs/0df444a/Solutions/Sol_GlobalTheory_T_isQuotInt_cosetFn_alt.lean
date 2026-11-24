-- Prove2me | solution 1 for GlobalTheory.T.isQuotInt_cosetFn_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:06.422826+00:00
-- url     : https://prove2.me/submissions/d93c00ce-58c7-4983-b9b1-22b9887fbc95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFn
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsQuotIntCosetFnStatement
import Theorems.Thm_GlobalTheory_CosetQuotInt_isQuotInt_cosetFn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (h : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) (v : ℝ), v ≠ 0 → (∀ u₀ ∈ N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : N k n c 1, (Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * embX c g₀)) ∂(volN ν n c 1)) ∂m = ((deltaR c g₀ * v : ℝ) : ℂ)) → ∀ (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ), IsCosetFn J h f → IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  first | exact @GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | exact GlobalTheory.CosetQuotInt.isQuotInt_cosetFn | (intros; apply GlobalTheory.CosetQuotInt.isQuotInt_cosetFn <;> assumption)
end _root_.GlobalTheory.T
