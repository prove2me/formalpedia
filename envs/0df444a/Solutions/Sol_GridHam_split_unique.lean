-- Prove2me | solution 1 for GridHam.split_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:31:06.936273+00:00
-- url     : https://prove2.me/submissions/5d2dff6b-5bae-4947-99f3-549b75b6da12

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution : ∀ (l1 l1' r r' : List Coord) (x : Coord),
    (l1 ++ x :: r).Nodup → l1 ++ x :: r = l1' ++ x :: r' → l1 = l1' ∧ r = r' := by
  intro l1
  induction l1 with
  | nil =>
    intro l1' r r' x hnd he
    have hnd' : (x :: r).Nodup := hnd
    cases l1' with
    | nil =>
      have he' : x :: r = x :: r' := he
      exact ⟨rfl, (List.cons.inj he').2⟩
    | cons a l1'' =>
      exfalso
      have he' : x :: r = a :: (l1'' ++ x :: r') := he
      have hr := (List.cons.inj he').2
      apply (List.nodup_cons.mp hnd').1
      rw [hr]
      simp
  | cons a l ih =>
    intro l1' r r' x hnd he
    have hnd' : (a :: (l ++ x :: r)).Nodup := hnd
    obtain ⟨han, hrest⟩ := List.nodup_cons.mp hnd'
    cases l1' with
    | nil =>
      exfalso
      have he' : a :: (l ++ x :: r) = x :: r' := he
      have hax := (List.cons.inj he').1
      apply han
      rw [hax]
      simp
    | cons b l1'' =>
      have he' : a :: (l ++ x :: r) = b :: (l1'' ++ x :: r') := he
      obtain ⟨hab, htl⟩ := List.cons.inj he'
      obtain ⟨hl, hr⟩ := ih l1'' r r' x hrest htl
      exact ⟨by rw [hab, hl], hr⟩
end GridHam
