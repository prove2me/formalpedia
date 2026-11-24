-- Prove2me | solution 1 for Kirkman.SteinerOp.isSTSOn_triples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:08.1688+00:00
-- url     : https://prove2.me/submissions/3ca5555e-ac8d-4b50-b9da-ac302ded1664

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Theorems.Thm_Kirkman_SteinerOp_card_tri
public import Theorems.Thm_Kirkman_SteinerOp_tri_eq
public import Theorems.Thm_Kirkman_SteinerOp_mem_tri_left
public import Theorems.Thm_Kirkman_SteinerOp_mem_tri_right

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}
open Kirkman.SteinerOp
variable (S : SteinerOp P)
variable [DecidableEq P]
variable [Fintype P]
namespace Kirkman.SteinerOp
theorem _root_.solution : IsSTSOn S.triples := by
  refine ⟨fun T hT => ?_, fun x y hxy => ?_⟩
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hT
    exact S.card_tri (mem_filter.1 hab).2
  · refine ⟨S.tri x y, ⟨mem_image.2 ⟨(x, y), mem_filter.2 ⟨mem_univ _, hxy⟩, rfl⟩,
      S.mem_tri_left x y, S.mem_tri_right x y⟩, ?_⟩
    rintro T ⟨hT, hxT, hyT⟩
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hT
    exact S.tri_eq (mem_filter.1 hab).2 hxy hxT hyT
end Kirkman.SteinerOp
