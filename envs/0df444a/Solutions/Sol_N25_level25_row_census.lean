-- Prove2me | solution 1 for N25.level25_row_census
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:41.108998+00:00
-- url     : https://prove2.me/submissions/80634732-40ea-4d82-9a45-0a8a9fd85be9

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- Primitive residue rows, their four-element scaling orbits, and the two
elliptic permutations are represented by explicit finite formulas. -/
theorem _root_.solution :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    let canonical : R → Prop := fun r => code r = normcode r
    let rows := (Finset.univ : Finset R).filter primitive
    let reps := rows.filter canonical
    let S : R → R := fun r => (r.2, ⟨(25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let ST : R → R := fun r =>
      (r.2, ⟨(r.2.val+25-r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    rows.card = 600 ∧ reps.card = 150 ∧
    (reps.filter (fun r => ∃ h ∈ ([1,7,18,24] : List ℕ), scale h r = S r)).card = 10 ∧
    (reps.filter (fun r => ∃ h ∈ ([1,7,18,24] : List ℕ), scale h r = ST r)).card = 0 ∧
    (reps.filter (fun r => code r ≤ normcode (S r))).card = 80 ∧
    (reps.filter (fun r => code r ≤ normcode (ST r) ∧
      code r ≤ normcode (ST (ST r)))).card = 50 := by
  decide +kernel

end N25
