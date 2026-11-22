-- Prove2me | solution 1 for GridHam.nodup_map_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:17:37.961456+00:00
-- url     : https://prove2.me/submissions/f18ba1af-5ec4-465e-9db9-c08662e1b8bb

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → ℕ) : ∀ (l : List Coord),
    (∀ v ∈ l, ∀ w ∈ l, f v = f w → v = w) → l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
    intro hinj hnd
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    have e : (a :: l).map f = f a :: l.map f := rfl
    rw [e, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
      have hwa : w = a :=
        hinj w (List.mem_cons.mpr (Or.inr hw)) a (List.mem_cons.mpr (Or.inl rfl)) hwe
      rw [hwa] at hw
      exact hanot hw
    · exact ih (fun v hv w hw =>
        hinj v (List.mem_cons.mpr (Or.inr hv)) w (List.mem_cons.mpr (Or.inr hw))) hndt
end GridHam
