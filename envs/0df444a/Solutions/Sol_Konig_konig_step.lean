-- Prove2me | solution 1 for Konig.konig_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:39:04.584479+00:00
-- url     : https://prove2.me/submissions/e906f55b-e649-4693-b849-d2106e0646a9

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
public import Theorems.Thm_Konig_exists_free_of_none
public import Theorems.Thm_Konig_colour_walk
public import Theorems.Thm_Konig_col_snd_of_kempe_path
public import Theorems.Thm_Konig_kempeGraph_le
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans
public import Theorems.Thm_LeanPool_Vizing_PEC_extends_kempeSwap
public import Theorems.Thm_LeanPool_Vizing_PEC_extends_setEdge
public import Theorems.Thm_LeanPool_Vizing_PEC_isFree_kempeSwap_of_not_reachable
public import Theorems.Thm_LeanPool_Vizing_PEC_isFree_kempeSwap_of_reachable
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
theorem _root_.solution [Fintype V] [Fintype C] [DecidableRel G.Adj]
    (s : G.Coloring (Fin 2)) (c : PEC G C)
    (hcard : G.maxDegree ≤ Fintype.card C) {x y : V} (hadj : G.Adj x y)
    (hnone : c.col x y = none) :
    ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by
  classical
  obtain ⟨a, ha⟩ := exists_free_of_none c hcard hadj hnone
  obtain ⟨b, hb⟩ := exists_free_of_none c hcard hadj.symm (by rw [c.col_symm]; exact hnone)
  by_cases hay : c.IsFree y a
  · exact ⟨c.setEdge a hadj ha hay, extends_setEdge c a hadj ha hay, by
      simp [setEdge]⟩
  have hab : a ≠ b := fun h => hay (h ▸ hb)
  -- `x` is not in the `a/b` Kempe component of `y`
  have hxy : ¬ (c.kempeGraph a b).Reachable y x := by
    rintro ⟨q⟩
    set p := q.toPath.1.reverse with hpdef
    have hp : p.IsPath := q.toPath.2.reverse
    have hpar := colour_walk (kempeGraph_le c a b) s p
    have hsx : s x ≠ s y := s.valid hadj
    have hodd : p.length % 2 = 1 := by
      have hx := (s x).isLt
      have hy' := (s y).isLt
      have : (s x : ℕ) ≠ (s y : ℕ) := fun h => hsx (Fin.ext h)
      omega
    have hlen : 0 < p.length := by omega
    have := col_snd_of_kempe_path c hb p hp hlen
    simp only [hodd, ↓reduceIte] at this
    exact ha _ this
  set c1 := c.kempeSwap a b y
  have ha1 : c1.IsFree x a := (isFree_kempeSwap_of_not_reachable c a b hxy a).2 ha
  have hay1 : c1.IsFree y a := by
    rw [isFree_kempeSwap_of_reachable c a b (Reachable.refl y) a, Equiv.swap_apply_left]
    exact hb
  refine ⟨c1.setEdge a hadj ha1 hay1, (extends_kempeSwap c a b y).trans
    (extends_setEdge c1 a hadj ha1 hay1), by simp [setEdge]⟩
end Konig
