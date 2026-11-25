-- Prove2me | solution 1 for Konig.colour_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:53.056479+00:00
-- url     : https://prove2.me/submissions/0b90e4f8-5ef6-49f9-a231-6d6172588a02

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
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
theorem _root_.solution {H : SimpleGraph V} (hHG : H ≤ G) (s : G.Coloring (Fin 2)) {u v : V}
    (p : H.Walk u v) : (s v : ℕ) % 2 = ((s u : ℕ) + p.length) % 2 := by
  induction p with
  | nil => simp
  | @cons u w v h p ih =>
    rw [Walk.length_cons, ih]
    have hne : (s u : ℕ) ≠ (s w : ℕ) := fun he => s.valid (hHG h) (Fin.ext he)
    have hu := (s u).isLt
    have hw := (s w).isLt
    omega
end Konig
