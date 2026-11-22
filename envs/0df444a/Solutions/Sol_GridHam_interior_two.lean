-- Prove2me | solution 1 for GridHam.interior_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:34:16.123122+00:00
-- url     : https://prove2.me/submissions/2591e8ee-bee0-406f-8ae9-78f260b95576

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_split_unique
public import Theorems.Thm_P2M_GridHam_getLast__append_cons_527000d4767a


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {x : Coord} (hnd : p.Nodup) (hx : x ∈ p)
    (hh : p.head? ≠ some x) (hl : p.getLast? ≠ some x) :
    ∃ a b, a ≠ b ∧ PNext p a x ∧ PNext p x b := by
  obtain ⟨l1, r, e⟩ := List.append_of_mem hx
  cases r with
  | nil =>
    exfalso
    apply hl
    rw [e, getLast?_append_cons]
    rfl
  | cons b r' =>
    by_cases hl1 : l1 = []
    · exfalso
      apply hh
      rw [e, hl1]
      rfl
    · obtain ⟨l0, a, hl0a⟩ : ∃ l0 a, l1 = l0 ++ [a] :=
        ⟨l1.dropLast, l1.getLast hl1, (List.dropLast_append_getLast hl1).symm⟩
      have e2 : p = l0 ++ a :: x :: b :: r' := by
        rw [e, hl0a]
        simp
      refine ⟨a, b, ?_, ⟨l0, b :: r', e2⟩, ⟨l1, r', e⟩⟩
      intro hab
      have hnd' : (l0 ++ a :: (x :: b :: r')).Nodup := by rw [← e2]; exact hnd
      have e3 : l0 ++ a :: (x :: b :: r') = (l0 ++ [a, x]) ++ a :: r' := by
        rw [hab]
        simp
      have hsu := split_unique l0 (l0 ++ [a, x]) (x :: b :: r') r' a hnd' e3
      have hlen := congrArg List.length hsu.1
      simp at hlen
end GridHam
