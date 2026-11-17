-- Prove2me | solution 1 for N25.level25_elliptic_orbit_normalization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:24.405181+00:00
-- url     : https://prove2.me/submissions/73814d7e-9fbf-4470-8798-b33c8dd42a46

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- Canonical codes for the two elliptic orbits are attained and invariant
under their generators, and the generators preserve primitive rows. -/
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
    let S : R → R := fun r => (r.2, ⟨(25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let ST : R → R := fun r =>
      (r.2, ⟨(r.2.val+25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let snorm : R → ℕ := fun r => min (normcode r) (normcode (S r))
    let stnorm : R → ℕ := fun r =>
      min (normcode r) (min (normcode (ST r)) (normcode (ST (ST r))))
    (∀ r : R, primitive r →
      ∃ i : Fin 4, ∃ n : Fin 2,
        code (scale (labels i) (if n.val=0 then r else S r)) = snorm r) ∧
    (∀ r : R, primitive r →
      ∃ i : Fin 4, ∃ n : Fin 3,
        code (scale (labels i) (if n.val=0 then r else if n.val=1 then ST r else ST (ST r))) = stnorm r) ∧
    (∀ r : R, ∀ i : Fin 4,
      snorm (scale (labels i) r) = snorm r ∧
      stnorm (scale (labels i) r) = stnorm r ∧
      (primitive (scale (labels i) r) ↔ primitive r)) ∧
    (∀ r : R, snorm (S r) = snorm r ∧ stnorm (ST r) = stnorm r ∧
      (primitive (S r) ↔ primitive r) ∧ (primitive (ST r) ↔ primitive r)) := by
  decide +kernel

end N25
