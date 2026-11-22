-- Prove2me | solution 1 for GridHam.path_split_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:10:19.108485+00:00
-- url     : https://prove2.me/submissions/bfa9146e-318a-4a44-8efc-879afd62e06d

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity
public import Theorems.Thm_P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {width height : ℕ} {s t : Coord} {p : List Coord}
    (hv : ValidPath width height s t p) (hbig : 2 ≤ width * height) :
    ∃ m, p = s :: (m ++ [t]) := by
  obtain ⟨hlen, hhead, hlast, _, _, _, _⟩ := hv
  cases p with
  | nil => simp at hhead
  | cons a rest =>
    have has : a = s := by simpa using hhead
    have hlen' : rest.length + 1 = width * height := hlen
    have hrne : rest ≠ [] := by
      intro e
      rw [e, List.length_nil] at hlen'
      omega
    have hlast' : rest.getLast? = some t := by
      cases rest with
      | nil => exact absurd rfl hrne
      | cons b r => exact hlast
    have hdl := List.dropLast_append_getLast hrne
    rw [getLast?_eq_getLast_of_ne_nil rest hrne t hlast'] at hdl
    exact ⟨rest.dropLast, by rw [has, hdl]⟩
end GridHam
