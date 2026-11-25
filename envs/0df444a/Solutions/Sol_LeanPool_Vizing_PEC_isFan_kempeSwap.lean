-- Prove2me | solution 1 for LeanPool.Vizing.PEC.isFan_kempeSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:30.606142+00:00
-- url     : https://prove2.me/submissions/4975f885-c148-4753-9d36-a90374702f9c

module
public import Definitions.Def_LeanPool_Vizing_Fan
public import Definitions.Def_LeanPool_Vizing_Step
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans
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
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V] [Fintype C]
namespace LeanPool.Vizing.PEC
theorem _root_.solution (c : PEC G C) {x y : V} {n : ℕ} {f : ℕ → V} (hfan : c.IsFan x y n f)
    {a b : C} (ha : c.IsFree x a) (w : V) {m : ℕ} (hm : m ≤ n)
    (hbreak : ∀ i < m, c.col x (f (i + 1)) = some b →
      ((c.kempeGraph a b).Reachable w (f i) ↔ (c.kempeGraph a b).Reachable w x)) :
    (c.kempeSwap a b w).IsFan x y m f := by
  classical
  refine ⟨hfan.start, ?_, fun i hi => hfan.adj i (hi.trans hm),
    fun i hi j hj hij => hfan.inj i (hi.trans hm) j (hj.trans hm) hij, ?_⟩
  · by_cases hxw : (c.kempeGraph a b).Reachable w x
    · rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hxw y, hfan.uncoloured]
      rfl
    · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hxw y]
      exact hfan.uncoloured
  · intro i hi
    obtain ⟨γ, hγ, hγfree⟩ := hfan.step i (hi.trans_le hm)
    have hγa : γ ≠ a := by
      rintro rfl
      exact ha _ hγ
    by_cases hxw : (c.kempeGraph a b).Reachable w x
    · refine ⟨Equiv.swap a b γ, ?_, ?_⟩
      · rw [kempeSwap_col, kempeSwapFun_of_reachable c a b hxw (f (i + 1)), hγ]
        rfl
      · by_cases hiw : (c.kempeGraph a b).Reachable w (f i)
        · rw [isFree_kempeSwap_of_reachable c a b hiw]
          simpa using hγfree
        · have hγb : γ ≠ b := by
            rintro rfl
            exact hiw ((hbreak i hi hγ).2 hxw)
          rw [isFree_kempeSwap_of_not_reachable c a b hiw,
            Equiv.swap_apply_of_ne_of_ne hγa hγb]
          exact hγfree
    · refine ⟨γ, ?_, ?_⟩
      · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c a b hxw (f (i + 1))]
        exact hγ
      · by_cases hiw : (c.kempeGraph a b).Reachable w (f i)
        · have hγb : γ ≠ b := by
            rintro rfl
            exact hxw ((hbreak i hi hγ).1 hiw)
          rw [isFree_kempeSwap_of_reachable c a b hiw,
            Equiv.swap_apply_of_ne_of_ne hγa hγb]
          exact hγfree
        · rw [isFree_kempeSwap_of_not_reachable c a b hiw]
          exact hγfree
end LeanPool.Vizing.PEC
