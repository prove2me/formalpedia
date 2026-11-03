-- Prove2me | solution 1 for LX.ForwardCarrier.carrier_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:58:13.413538+00:00
-- url     : https://prove2.me/submissions/63a0af1d-c2ad-4b6c-99ef-dd632688e9e2

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_ForwardCarrier

namespace Int
end Int
namespace LX
end LX
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace List
end List

section
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u



theorem ite_eq_right {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := if_neg h

end LX

namespace List
universe u

end List

/-
The following proof is adapted from Mathlib, copyright (c) 2026 Seewoo Lee,
licensed under Apache 2.0. Source revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Order/Floor/BigOperators.lean, lines 28-45.
-/
namespace Int
open scoped BigOperators


end Int

end

section
namespace LX.ForwardCarrier





theorem prefix_tail (F : ℕ → ℤ) (k j : ℕ) (hkj : k < j) : sweepPrefix F k j = F j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sweepPrefix, compareAt, ite_eq_right (by omega : j ≠ k), ite_eq_right (by omega : j ≠ k+1)]
    exact ih (by omega)

theorem carrier_step (F : ℕ → ℤ) (k : ℕ) :
    sweepPrefix F (k+1) (k+1) = max (sweepPrefix F k k) (F (k+1)) := by
  simp only [sweepPrefix, compareAt, ite_eq_right (by omega : k+1 ≠ k), ite_true]
  rw [prefix_tail F k (k+1) (by omega)]







end LX.ForwardCarrier

end

namespace LX.ForwardCarrier
end LX.ForwardCarrier
open LX
open LX.ForwardCarrier

/-- The actual carried target is the maximum of all targets already encountered. -/
theorem solution (F : ℕ → ℤ) (k : ℕ) (x : ℤ) :
    sweepPrefix F k k ≤ x ↔ ∀ j ≤ k, F j ≤ x := by
  induction k with
  | zero => simp [sweepPrefix]
  | succ k ih =>
    rw [carrier_step, max_le_iff, ih]
    constructor
    · rintro ⟨h, hx⟩ j hj
      by_cases he : j=k+1
      · simpa only [he] using hx
      · exact h j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h (k+1) (by omega)⟩
