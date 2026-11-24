-- Prove2me | solution 1 for GlobalTheory.PMonE.moore_step_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:55.305021+00:00
-- url     : https://prove2.me/submissions/8165d7be-68d9-4c3f-b51b-1982370404fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Theorems.Thm_GlobalTheory_PMonE_moore_step_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ c : ℤ, r ≤ ‖x + (c : F) * t‖) : r ^ p ≤ ‖x ^ p - t ^ (p - 1) * x‖ := by
  rw [moore_step_eq_prod, norm_prod]
  have : r ^ p = ∏ _c : ZMod p, r := by simp
  rw [this]
  refine Finset.prod_le_prod (fun _ _ => hr) fun c _ => ?_
  have := h (-(c.val : ℤ))
  simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, ← sub_eq_add_neg] using this
end GlobalTheory.PMonE
