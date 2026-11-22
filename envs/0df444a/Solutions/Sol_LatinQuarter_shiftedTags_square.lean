-- Prove2me | solution 1 for LatinQuarter.shiftedTags_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:34.483342+00:00
-- url     : https://prove2.me/submissions/3b9e8996-28eb-4e2a-9fed-04d061751600

module
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_Shifted
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply
attribute [local simp] LatinQuarter.allTagsExponent_support
attribute [local simp] LatinQuarter.tag_sq



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
namespace LatinQuarter
theorem _root_.solution {N : Type*} {k h : ℕ}
    (e : Fin k ⊕ Fin h ≃ N) (c s : N) :
    squareHom (shiftedTags e c s) = algebraMap (ZMod 2) _ (markedConstant e c s) := by
  classical
  simp only [shiftedTags, map_add, squareHom, frobenius_def]
  rw [pow_two, tag_sq, zero_add]
  unfold markedConstant
  split_ifs <;> simp
end LatinQuarter
