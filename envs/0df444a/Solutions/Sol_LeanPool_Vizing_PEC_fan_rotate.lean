-- Prove2me | solution 1 for LeanPool.Vizing.PEC.fan_rotate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:01.426811+00:00
-- url     : https://prove2.me/submissions/e9e86b5b-9ca2-4b16-8021-4269ccf89e02

module
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Definitions.Def_LeanPool_Vizing_Fan
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans
public import Theorems.Thm_LeanPool_Vizing_PEC_extends_setEdge
public import Theorems.Thm_LeanPool_Vizing_PEC_isFree_setEdge_of_ne
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col_of_ne_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_of_ne
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V] [DecidableEq C]
namespace LeanPool.Vizing.PEC
theorem _root_.solution (x y : V) (f : ℕ → V) : ∀ (n : ℕ) (c : PEC G C) (b : C), c.IsFan x y n f →
    c.IsFree x b → c.IsFree (f n) b → ∃ c' : PEC G C, Extends c c' ∧ c'.col x y ≠ none := by
  classical
  intro n
  induction n with
  | zero =>
    intro c b hf hbx hbn
    have hy : y = f 0 := hf.start.symm
    subst hy
    refine ⟨c.setEdge b (hf.adj 0 le_rfl) hbx hbn, c.extends_setEdge b (hf.adj 0 le_rfl) hbx hbn,
      ?_⟩
    rw [setEdge_col, updFun_left]
    exact Option.some_ne_none _
  | succ n ih =>
    intro c b hf hbx hbn
    obtain ⟨γ, hγ, hγfree⟩ := hf.step n (Nat.lt_succ_self n)
    have hadj : G.Adj x (f (n + 1)) := hf.adj (n + 1) le_rfl
    have hnex : ∀ i, i ≤ n + 1 → f i ≠ x := fun i hi => (hf.adj i hi).ne'
    have hnelast : ∀ i, i ≤ n → f i ≠ f (n + 1) := by
      intro i hi hcon
      have := hf.inj i (by omega) (n + 1) le_rfl hcon
      omega
    set c1 := c.setEdge b hadj hbx hbn with hc1
    have hcolne : ∀ w u, w ≠ x → w ≠ f (n + 1) → c1.col w u = c.col w u := fun w u hw hw' =>
      c.setEdge_col_of_ne_left b hadj hbx hbn hw hw' u
    have hcolx : ∀ u, u ≠ f (n + 1) → c1.col x u = c.col x u := by
      intro u hu
      rw [hc1, setEdge_col]
      exact updFun_of_ne _ (by
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hu h
        · exact hadj.ne h)
    have hbγ : b ≠ γ := by
      rintro rfl
      exact hbx _ hγ
    -- the fan of length `n` survives the recolouring of the last fan edge
    have hfan1 : c1.IsFan x y n f := by
      refine ⟨hf.start, ?_, fun i hi => hf.adj i (by omega),
        fun i hi j hj hij => hf.inj i (by omega) j (by omega) hij, ?_⟩
      · rw [← hf.start, hcolx (f 0) (hnelast 0 (by omega))]
        rw [hf.start]
        exact hf.uncoloured
      · intro i hi
        obtain ⟨δ, hδ, hδfree⟩ := hf.step i (by omega)
        refine ⟨δ, ?_, ?_⟩
        · rw [hcolx (f (i + 1)) (hnelast (i + 1) (by omega))]
          exact hδ
        · rw [hc1, c.isFree_setEdge_of_ne b hadj hbx hbn (hnex i (by omega))
            (hnelast i (by omega)) δ]
          exact hδfree
    have hγx : c1.IsFree x γ := by
      intro u hu
      by_cases hcase : u = f (n + 1)
      · subst hcase
        rw [hc1, setEdge_col, updFun_left] at hu
        exact hbγ (Option.some_injective _ hu)
      · rw [hcolx u hcase] at hu
        exact hcase (c.col_proper hu hγ)
    have hγn : c1.IsFree (f n) γ := by
      rw [hc1, c.isFree_setEdge_of_ne b hadj hbx hbn (hnex n (by omega))
        (hnelast n le_rfl) γ]
      exact hγfree
    obtain ⟨c', hext, hcol'⟩ := ih c1 γ hfan1 hγx hγn
    exact ⟨c', (c.extends_setEdge b hadj hbx hbn).trans hext, hcol'⟩
end LeanPool.Vizing.PEC
