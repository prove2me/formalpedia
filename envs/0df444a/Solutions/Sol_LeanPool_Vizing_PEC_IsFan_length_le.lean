-- Prove2me | solution 1 for LeanPool.Vizing.PEC.IsFan.length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:26.769658+00:00
-- url     : https://prove2.me/submissions/3ebc7863-2623-4304-a98b-6259c2dc548e

module
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Definitions.Def_LeanPool_Vizing_Fan
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
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [DecidableEq V] [DecidableEq C]
namespace LeanPool.Vizing.PEC
namespace IsFan
theorem _root_.solution {c : PEC G C} {x y : V} {n : ℕ} {f : ℕ → V} (h : c.IsFan x y n f) :
    n ≤ Fintype.card V := by
  classical
  have hcard : (Finset.range (n + 1)).card ≤ (Finset.univ : Finset V).card := by
    refine Finset.card_le_card_of_injOn f (fun i _ => Finset.mem_univ _) ?_
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact h.inj i (by omega) j (by omega) hij
  simp only [Finset.card_range, Finset.card_univ] at hcard
  omega
end IsFan
end LeanPool.Vizing.PEC
