-- Prove2me | solution 1 for Konig.col_snd_of_kempe_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:58.772034+00:00
-- url     : https://prove2.me/submissions/012086d7-fc36-4368-9c01-162a80f5be7c

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}
namespace Konig
theorem _root_.solution (c : PEC G C) {a b : C} {y : V}
    (hy : c.IsFree y b) {u : V} (p : (c.kempeGraph a b).Walk u y) (hp : p.IsPath)
    (hlen : 0 < p.length) :
    c.col u p.snd = some (if p.length % 2 = 1 then a else b) := by
  induction p with
  | nil => simp at hlen
  | @cons u w y h r ih =>
    have hcol := h.2
    rw [Walk.snd_cons]
    rw [Walk.cons_isPath_iff] at hp
    rcases Nat.eq_zero_or_pos r.length with h0 | hpos
    · -- `r` is trivial: `w = y`
      have hwy : w = y := Walk.eq_of_length_eq_zero h0
      subst hwy
      rw [Walk.length_cons, h0, zero_add]
      rcases hcol with hcol | hcol
      · simpa using hcol
      · exact absurd ((c.col_symm w u).trans hcol) (hy u)
    · have hih := ih hy hp.1 hpos
      have hne : u ≠ r.snd := by
        intro he
        exact hp.2 (by rw [he]; exact r.getVert_mem_support 1)
      rw [Walk.length_cons]
      -- the colours of `w u` and `w r.snd` differ
      have hdiff : c.col w u ≠ c.col w r.snd := by
        intro he
        rw [hih] at he
        exact hne (c.col_proper he hih)
      rw [c.col_symm w u] at hdiff
      rcases Nat.mod_two_eq_zero_or_one r.length with hr | hr
      · have h1 : (r.length + 1) % 2 = 1 := by omega
        rw [hr] at hih
        simp only [zero_ne_one, ite_false] at hih
        rw [hih] at hdiff
        simp only [h1, ite_true]
        rcases hcol with hcol | hcol
        · exact hcol
        · exact absurd hcol hdiff
      · have h1 : (r.length + 1) % 2 = 0 := by omega
        rw [hr] at hih
        simp only [ite_true] at hih
        rw [hih] at hdiff
        simp only [h1, zero_ne_one, ite_false]
        rcases hcol with hcol | hcol
        · exact absurd hcol hdiff
        · exact hcol
end Konig
