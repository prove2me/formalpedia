-- Prove2me | solution 1 for N25.level25_gamma0_finite_census
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:25.571118+00:00
-- url     : https://prove2.me/submissions/3574175b-ec78-44f0-b30c-6f7cddd6e295

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- Replacing the four-element subgroup by all units gives the finite
projective-line model for the Gamma-zero comparison: 30, 16, 10, 6. -/
theorem _root_.solution :
    let R := ZMod 25 × ZMod 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let normal : R → R := fun r =>
      if r.1.val % 5 ≠ 0 then (1,r.1⁻¹*r.2) else (r.2⁻¹*r.1,1)
    let code : R → ℕ := fun r => r.1.val + 25*r.2.val
    let reps := (Finset.univ : Finset R).filter (fun r => primitive r ∧ normal r = r)
    let S : R → R := fun r => (r.2,-r.1)
    let ST : R → R := fun r => (r.2,r.2-r.1)
    let translate : Fin 25 → R → R := fun n r => (r.1,r.2+(n.val:ZMod 25)*r.1)
    reps.card = 30 ∧
    (reps.filter (fun r => code r ≤ code (normal (S r)))).card = 16 ∧
    (reps.filter (fun r => code r ≤ code (normal (ST r)) ∧
      code r ≤ code (normal (ST (ST r))))).card = 10 ∧
    (reps.filter (fun r => ∀ n : Fin 25,
      code r ≤ code (normal (translate n r)))).card = 6 := by
  decide +kernel

end N25
