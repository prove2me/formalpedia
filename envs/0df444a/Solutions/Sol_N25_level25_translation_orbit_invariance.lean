-- Prove2me | solution 1 for N25.level25_translation_orbit_invariance
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:55.57466+00:00
-- url     : https://prove2.me/submissions/b24441fb-6ab5-4fff-9907-7bceb7abeebf

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- The translation-orbit code is invariant under the level subgroup and
the cusp generator; primitive rows are preserved. -/
theorem _root_.solution :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let labels : Fin 4 → ℕ := ![1,7,18,24]
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    let translate : ℕ → R → R := fun n r =>
      (r.1, ⟨(r.2.val+n*r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let tnorm : R → ℕ := fun r =>
      if r.1.val=0 then normcode r
      else if r.1.val%5=0 then
        25 + 5 * ((r.1.val/5) * ((r.2.val : ZMod 5)⁻¹).val % 5)
      else min (min r.1.val (7*r.1.val%25))
        (min (18*r.1.val%25) (24*r.1.val%25))
    (∀ r : R, primitive r → ∀ i : Fin 4,
      tnorm (scale (labels i) r) = tnorm r ∧
      (primitive (scale (labels i) r) ↔ primitive r)) ∧
    (∀ r : R, primitive r → tnorm (translate 1 r) = tnorm r ∧
      (primitive (translate 1 r) ↔ primitive r)) ∧
    (∀ r : R, primitive r →
      (code r = tnorm r ↔ ∀ n : Fin 25, code r ≤ normcode (translate n.val r))) := by
  decide +kernel

end N25
