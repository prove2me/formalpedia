-- Prove2me | solution 1 for GridHam.exists_col_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:26.488807+00:00
-- url     : https://prove2.me/submissions/672b1775-7067-4251-b4ee-e6c79bdd8cd2

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (X : ℕ) : ∀ (l : List Coord), chainAdjacent l = true → l.Nodup →
    (∀ u ∈ l, u.1 ≤ X) → ∀ v ∈ l, v.1 = X → l.head? ≠ some v → l.getLast? ≠ some v →
    ∃ l1 a b l2, l = l1 ++ a :: b :: l2 ∧ a.1 = X ∧ b.1 = X := by
  intro l
  induction l with
  | nil => intro _ _ _ v hv; simp at hv
  | cons a rest ih =>
    intro hch hnd hle v hv hvx hhd hlst
    rcases List.mem_cons.mp hv with hva | hvr
    · exfalso
      apply hhd
      rw [hva]
      rfl
    · cases rest with
      | nil => simp at hvr
      | cons b rest' =>
        have hc' : (adjacentB a b && chainAdjacent (b :: rest')) = true := by
          simpa [chainAdjacent] using hch
        simp at hc'
        obtain ⟨hab, hcl⟩ := hc'
        have hadjab : Adjacent a b := by
          unfold adjacentB at hab
          by_contra hcon
          simp [hcon] at hab
        obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
        have hlst' : (b :: rest').getLast? ≠ some v := by
          have e : (a :: b :: rest').getLast? = (b :: rest').getLast? := rfl
          rw [e] at hlst
          exact hlst
        have hle' : ∀ u ∈ b :: rest', u.1 ≤ X :=
          fun u hu => hle u (List.mem_cons.mpr (Or.inr hu))
        by_cases hvb : v = b
        · cases rest' with
          | nil =>
            exfalso
            apply hlst'
            rw [hvb]
            rfl
          | cons c rest'' =>
            have hc2 : (adjacentB b c && chainAdjacent (c :: rest'')) = true := by
              simpa [chainAdjacent] using hcl
            simp at hc2
            obtain ⟨hbc, _⟩ := hc2
            have hadjbc : Adjacent b c := by
              unfold adjacentB at hbc
              by_contra hcon
              simp [hcon] at hbc
            have hax := hle a (by simp)
            have hcx := hle c (by simp)
            have hbx : b.1 = X := by
              rw [← hvb]
              exact hvx
            by_cases ha : a.1 = X
            · exact ⟨[], a, b, c :: rest'', rfl, ha, hbx⟩
            · by_cases hc : c.1 = X
              · exact ⟨[a], b, c, rest'', rfl, hbx, hc⟩
              · exfalso
                have hac : a = c := by
                  unfold Adjacent at hadjab hadjbc
                  ext
                  · omega
                  · omega
                apply hanot
                rw [hac]
                simp
        · have hhd' : (b :: rest').head? ≠ some v := by
            intro h
            apply hvb
            have hbv : b = v := by simpa using h
            exact hbv.symm
          obtain ⟨l1, x, y, l2, heq, hx, hy⟩ := ih hcl hndt hle' v hvr hvx hhd' hlst'
          exact ⟨a :: l1, x, y, l2, by simp [heq], hx, hy⟩
end GridHam
