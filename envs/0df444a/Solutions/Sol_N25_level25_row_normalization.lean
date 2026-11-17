-- Prove2me | solution 1 for N25.level25_row_normalization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:58.751745+00:00
-- url     : https://prove2.me/submissions/168c3391-e9f1-41cb-9415-435f465d6bdf

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- Minimum code is attained on the scaling orbit and invariant under scaling.
The generator list is the four powers of seven, ordered by their values. -/
theorem _root_.solution :
    let R := Fin 25 × Fin 25
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let labels : Fin 4 → ℕ := ![1,7,18,24]
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    (∀ r : R, ∃ i : Fin 4, code (scale (labels i) r) = normcode r) ∧
    (∀ r : R, ∀ i : Fin 4, normcode (scale (labels i) r) = normcode r) ∧
    (∀ i j : Fin 4, ∃ k : Fin 4, ∀ r : R,
      scale (labels i) r = scale (labels j) (scale (labels k) r)) ∧
    (∀ i : Fin 4, ∃ j : Fin 4, ∀ r : R,
      scale (labels j) (scale (labels i) r) = r) := by
  decide +kernel

end N25
