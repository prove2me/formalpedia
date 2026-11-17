-- Prove2me | solution 1 for N25.level25_cusp_width_census
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:23.7398+00:00
-- url     : https://prove2.me/submissions/d3796672-4651-4fd6-8034-ace309acb835

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

namespace N25

/-- The cusp translation acts on residue rows by adding a multiple of the first
coordinate to the second. Its orbit widths have distribution five, four, five. -/
theorem _root_.solution :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    let translate : ℕ → R → R := fun n r =>
      (r.1, ⟨(r.2.val+n*r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
    let cusps := (Finset.univ : Finset R).filter (fun r => primitive r ∧
      ∀ n : Fin 25, code r ≤ normcode (translate n.val r))
    let width : R → ℕ := fun r =>
      if r.1.val = 0 then 1 else if r.1.val % 5 = 0 then 5 else 25
    cusps.card = 14 ∧
    (cusps.filter (fun r => width r = 1)).card = 5 ∧
    (cusps.filter (fun r => width r = 5)).card = 4 ∧
    (cusps.filter (fun r => width r = 25)).card = 5 ∧
    (∑ r ∈ cusps, width r) = 150 ∧
    (∀ r : R, primitive r →
      normcode (translate (width r) r) = normcode r ∧
      ∀ n : Fin 25, 0 < n.val → n.val < width r →
        normcode (translate n.val r) ≠ normcode r) := by
  decide +kernel

end N25
