-- Prove2me | solution 1 for GlobalTheory.FibLine.eq_zero_of_eval_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:25.855298+00:00
-- url     : https://prove2.me/submissions/5776451b-3582-4370-8294-04c99c2a5862

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine
namespace GlobalTheory.FibLine
theorem _root_.solution {σ : Type} (Q : MvPolynomial σ ℂ)
    (h : ∀ x : σ → ℝ, eval (fun i => (x i : ℂ)) Q = 0) : Q = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) ?_
  intro x hx
  have hx' : ∀ i, ∃ r : ℝ, (r : ℂ) = x i := fun i => hx i (Set.mem_univ i)
  choose r hr using hx'
  have : x = fun i => (r i : ℂ) := funext fun i => (hr i).symm
  rw [this, h, map_zero]
end GlobalTheory.FibLine
