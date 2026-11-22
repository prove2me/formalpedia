-- Prove2me | solution 1 for GridHam.mem_colSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:08.805647+00:00
-- url     : https://prove2.me/submissions/3eede854-0d00-466a-8490-d3cb68c9b3fb

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (c lo : ℕ) : ∀ k (v : Coord),
    v ∈ colSeg c lo k ↔ v.1 = c ∧ lo ≤ v.2 ∧ v.2 ≤ lo + k := by
  intro k
  induction k with
  | zero =>
    intro v
    rw [show colSeg c lo 0 = [(c, lo)] from rfl, List.mem_singleton]
    constructor
    · intro h
      rw [h]
      exact ⟨rfl, Nat.le_refl _, show lo ≤ lo + 0 by omega⟩
    · rintro ⟨h1, h2, h3⟩
      ext
      · show v.1 = c
        exact h1
      · show v.2 = lo
        omega
  | succ k ih =>
    intro v
    rw [show colSeg c lo (k + 1) = (c, lo + (k + 1)) :: colSeg c lo k from rfl,
      List.mem_cons, ih v]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · rw [h]
        exact ⟨rfl, show lo ≤ lo + (k + 1) by omega, show lo + (k + 1) ≤ lo + (k + 1) by omega⟩
      · exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      by_cases hk : v.2 = lo + (k + 1)
      · left
        ext
        · show v.1 = c
          exact h1
        · show v.2 = lo + (k + 1)
          exact hk
      · right
        exact ⟨h1, h2, by omega⟩
end GridHam
