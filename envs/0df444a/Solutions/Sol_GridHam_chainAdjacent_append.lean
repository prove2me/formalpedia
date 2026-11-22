-- Prove2me | solution 1 for GridHam.chainAdjacent_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:41:36.404821+00:00
-- url     : https://prove2.me/submissions/bba509fd-856f-48f6-a76d-137a4e57f58a

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 : List Coord) (b : Coord) (l2 : List Coord) (a : Coord),
    l1.getLast? = some a → chainAdjacent l1 = true → Adjacent a b →
    chainAdjacent (b :: l2) = true → chainAdjacent (l1 ++ b :: l2) = true := by
  intro l1
  induction l1 with
  | nil => intro b l2 a hl; simp at hl
  | cons x l ih =>
    intro b l2 a hl hc hadj hc2
    cases l with
    | nil =>
      have hxa : x = a := by simpa using hl
      have hAB : adjacentB x b = true := by
        unfold adjacentB
        rw [hxa]
        exact decide_eq_true hadj
      have e : chainAdjacent ([x] ++ b :: l2) = (adjacentB x b && chainAdjacent (b :: l2)) := rfl
      simp only [e, hAB, hc2, Bool.and_self]
    | cons y rest =>
      have hc' : (adjacentB x y && chainAdjacent (y :: rest)) = true := by
        simpa [chainAdjacent] using hc
      simp at hc'
      obtain ⟨hxy, hct⟩ := hc'
      have hl' : (y :: rest).getLast? = some a := by
        have e1 : (x :: y :: rest).getLast? = (y :: rest).getLast? := rfl
        rw [e1] at hl
        exact hl
      have hrec := ih b l2 a hl' hct hadj hc2
      have e : chainAdjacent ((x :: y :: rest) ++ b :: l2) =
          (adjacentB x y && chainAdjacent ((y :: rest) ++ b :: l2)) := rfl
      simp only [e, hxy, hrec, Bool.and_self]
end GridHam
