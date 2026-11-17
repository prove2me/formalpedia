-- Prove2me | solution 1 for N25.level25_translation_orbit_attainment
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:54.894915+00:00
-- url     : https://prove2.me/submissions/7468d64d-fa2d-4e7e-b535-99cdfa526b25

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- Translation-orbit codes are represented by an actual residue translate
and an actual level-subgroup scalar. -/
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
    ∀ r : R, primitive r → ∃ i : Fin 4, ∃ n : Fin 25,
      code (scale (labels i) (translate n.val r)) = tnorm r := by
  decide +kernel

end N25
