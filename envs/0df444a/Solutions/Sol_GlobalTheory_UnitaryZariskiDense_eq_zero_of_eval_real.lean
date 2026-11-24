-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:26.345729+00:00
-- url     : https://prove2.me/submissions/c3493e30-43ca-408e-ad4c-a9c5a4573bcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ u : σ → ℝ, eval (fun v => (u v : ℂ)) P = 0) : P = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun x hx => ?_
  have hx' : x = fun v => ((x v).re : ℂ) := by
    funext v
    obtain ⟨r, hr⟩ := hx v (Set.mem_univ _)
    rw [← hr, Complex.ofReal_re]
  rw [hx', h, map_zero]
end GlobalTheory.UnitaryZariskiDense
