-- Prove2me | solution 1 for GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:12.510011+00:00
-- url     : https://prove2.me/submissions/7fd212eb-aefa-45d8-bb67-9f3e56e00777

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MemSpanMapOfEvalMemOfNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MemSpanMapOfEvalMemOfNeZeroStatement
import Theorems.Thm_GlobalTheory_mem_span_map_of_eval_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [Infinite k] (σ τ : Type) (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k), D ≠ 0 → ∀ P : MvPolynomial σ (MvPolynomial τ k), (∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) → P ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  first | exact @GlobalTheory.mem_span_map_of_eval_mem | exact GlobalTheory.mem_span_map_of_eval_mem | (intros; apply GlobalTheory.mem_span_map_of_eval_mem <;> assumption)
end _root_.GlobalTheory.T
