-- Prove2me | solution 1 for GlobalTheory.BasicFlow.entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:37.670429+00:00
-- url     : https://prove2.me/submissions/4bcec543-629c-457d-a2b2-ce840d804341

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow
namespace GlobalTheory.BasicFlow
theorem _root_.solution (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d W x) (a : ZMod d) (i : ℕ) (hi : i ∈ oddLevels d) : x a i ≤ W a := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have e1 : (l : ℝ) ^ i * x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
    Finset.single_le_sum (f := fun i => (l : ℝ) ^ i * x a i)
      (fun j _ => mul_nonneg (by positivity) (h0 a j)) hi
  have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
  have e3 : x a i ≤ (l : ℝ) ^ i * x a i := le_mul_of_one_le_left (h0 a i) (one_le_pow₀ hl1)
  have := h2 a
  linarith
end GlobalTheory.BasicFlow
