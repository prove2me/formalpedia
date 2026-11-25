-- Prove2me | solution 1 for GlobalTheory.T.exists_sum_pureTensor_of_isTensor_depth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:18.912155+00:00
-- url     : https://prove2.me/submissions/87c0c6d3-33fe-4fcf-bc1b-8f5a1e42a347

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepthStatement
import Theorems.Thm_GlobalTheory_TensorExpansion_exists_sum_pureTensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  first | exact @GlobalTheory.TensorExpansion.exists_sum_pureTensor | exact GlobalTheory.TensorExpansion.exists_sum_pureTensor | (intros; apply GlobalTheory.TensorExpansion.exists_sum_pureTensor <;> assumption)
end _root_.GlobalTheory.T
