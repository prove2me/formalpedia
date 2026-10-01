-- Prove2me | solution 1 for JohnsonFlowShop.TwoStage.interchange_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:48:01.574434+00:00
-- url     : https://prove2.me/submissions/771b5d73-1a4f-425f-bd09-d31ba0fd5856

import Definitions.Def_JohnsonFlowShop_TwoStage_F
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open JohnsonFlowShop Shared TwoStage Finset
namespace CJohnson

theorem sum_swap {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (s : Finset ι) (a b : ι) (hab : a ≠ b) :
    (∑ x ∈ s, f (Equiv.swap a b x)) = (∑ x ∈ s, f x) +
      (if a ∈ s then f b-f a else 0) + (if b ∈ s then f a-f b else 0) := by
  have he (x : ι) : f (Equiv.swap a b x) = f x + (if x=a then f b-f a else 0) +
      (if x=b then f a-f b else 0) := by
    by_cases ha : x=a
    · subst x; simp [hab]
    · by_cases hb : x=b
      · subst x; simp [Ne.symm hab]
      · simp [Equiv.swap_apply_of_ne_of_ne ha hb,ha,hb]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp

theorem K_swap_formula {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (a b u : Fin n) (hab : a ≠ b) :
    K A B (σ * Equiv.swap a b) u = K A B σ u +
      (if a ≤ u then A (σ b)-A (σ a) else 0) + (if b ≤ u then A (σ a)-A (σ b) else 0) -
      (if a < u then B (σ b)-B (σ a) else 0) - (if b < u then B (σ a)-B (σ b) else 0) := by
  unfold K
  simp only [Equiv.Perm.mul_apply]
  rw [sum_swap (fun x => A (σ x)) _ a b hab, sum_swap (fun x => B (σ x)) _ a b hab]
  simp only [Finset.mem_Iic,Finset.mem_Iio,Function.comp_apply]
  ring

theorem K_next {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) :
    K A B σ ⟨j+1,hj⟩ = K A B σ ⟨j,by omega⟩ + A (σ ⟨j+1,hj⟩)-B (σ ⟨j,by omega⟩) := by
  have he1 : Finset.Iic (⟨j+1,hj⟩ : Fin n) = insert ⟨j+1,hj⟩ (Finset.Iic ⟨j,by omega⟩) := by
    ext x
    simp only [Finset.mem_Iic,Finset.mem_insert,Fin.ext_iff,Fin.le_iff_val_le_val]
    omega
  have he2 : Finset.Iio (⟨j+1,hj⟩ : Fin n) = insert ⟨j,by omega⟩ (Finset.Iio ⟨j,by omega⟩) := by
    ext x
    simp only [Finset.mem_Iio,Finset.mem_insert,Fin.ext_iff,Fin.lt_iff_val_lt_val]
    omega
  unfold K
  rw [he1,he2,Finset.sum_insert (by simp),Finset.sum_insert (by simp)]
  ring

theorem K_swap_other {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) (u : Fin n) (hua : u ≠ ⟨j,by omega⟩) (hub : u ≠ ⟨j+1,hj⟩) :
    K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) u = K A B σ u := by
  rw [K_swap_formula A B σ _ _ u (by intro h; have := congrArg Fin.val h; simp at this)]
  have hja : u.val ≠ j := by intro he; apply hua; exact Fin.ext he
  have hjb : u.val ≠ j+1 := by intro he; apply hub; exact Fin.ext he
  by_cases h : u.val < j
  · have ha : ¬ (⟨j,by omega⟩ : Fin n) ≤ u := by change ¬j ≤ u.val; omega
    have hb : ¬ (⟨j+1,hj⟩ : Fin n) ≤ u := by change ¬j+1 ≤ u.val; omega
    have ha' : ¬ (⟨j,by omega⟩ : Fin n) < u := by change ¬j < u.val; omega
    have hb' : ¬ (⟨j+1,hj⟩ : Fin n) < u := by change ¬j+1 < u.val; omega
    simp [ha,hb,ha',hb']
  · have ha : (⟨j,by omega⟩ : Fin n) ≤ u := by change j ≤ u.val; omega
    have hb : (⟨j+1,hj⟩ : Fin n) ≤ u := by change j+1 ≤ u.val; omega
    have ha' : (⟨j,by omega⟩ : Fin n) < u := by change j < u.val; omega
    have hb' : (⟨j+1,hj⟩ : Fin n) < u := by change j+1 < u.val; omega
    simp only [ha,hb,ha',hb',if_pos]
    ring

theorem adjacent_max {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) :
    max (K A B σ ⟨j,by omega⟩) (K A B σ ⟨j+1,hj⟩) =
      K A B σ ⟨j,by omega⟩ + A (σ ⟨j+1,hj⟩)-min (A (σ ⟨j+1,hj⟩)) (B (σ ⟨j,by omega⟩)) ∧
    max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) =
      K A B σ ⟨j,by omega⟩ + A (σ ⟨j+1,hj⟩)-min (A (σ ⟨j,by omega⟩)) (B (σ ⟨j+1,hj⟩)) := by
  have hab : (⟨j,by omega⟩ : Fin n) ≠ ⟨j+1,hj⟩ := by intro h; have := congrArg Fin.val h; simp at this
  have ha : (⟨j,by omega⟩ : Fin n) < ⟨j+1,hj⟩ := by simp
  constructor
  · rw [K_next A B σ j hj]
    simp only [max_def,min_def]
    split_ifs <;> linarith
  · rw [K_swap_formula A B σ _ _ _ hab,K_swap_formula A B σ _ _ _ hab]
    simp only [le_refl,ha.le,ha,not_le.mpr ha,not_lt_of_ge ha.le,lt_irrefl,if_pos,if_false]
    rw [K_next A B σ j hj]
    simp only [max_def,min_def]
    split_ifs <;> linarith

theorem interchange_iff {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n) :
    (∀ u : Fin n, u ≠ ⟨j,by omega⟩ → u ≠ ⟨j+1,hj⟩ →
      K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) u = K A B σ u) ∧
    (max (K A B σ ⟨j,by omega⟩) (K A B σ ⟨j+1,hj⟩) <
      max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) ↔
      min (A (σ ⟨j,by omega⟩)) (B (σ ⟨j+1,hj⟩)) < min (A (σ ⟨j+1,hj⟩)) (B (σ ⟨j,by omega⟩))) := by
  refine ⟨K_swap_other A B σ j hj,?_⟩
  rw [(adjacent_max A B σ j hj).1,(adjacent_max A B σ j hj).2]
  exact sub_lt_sub_iff_left _

theorem interchange_F_le {n : ℕ} [NeZero n] (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j+1 < n)
    (hII : min (A (σ ⟨j,by omega⟩)) (B (σ ⟨j+1,hj⟩)) ≤ min (A (σ ⟨j+1,hj⟩)) (B (σ ⟨j,by omega⟩))) :
    F A B σ ≤ F A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) := by
  have hm : max (K A B σ ⟨j,by omega⟩) (K A B σ ⟨j+1,hj⟩) ≤
      max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) := by
    rw [(adjacent_max A B σ j hj).1,(adjacent_max A B σ j hj).2]
    linarith
  have hbound : max (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j,by omega⟩)
        (K A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) ⟨j+1,hj⟩) ≤ F A B (σ * Equiv.swap ⟨j,by omega⟩ ⟨j+1,hj⟩) :=
    max_le (Finset.le_sup' _ (Finset.mem_univ _)) (Finset.le_sup' _ (Finset.mem_univ _))
  apply Finset.sup'_le
  intro u hu
  by_cases ha : u=⟨j,by omega⟩
  · subst u; exact (le_max_left _ _).trans (hm.trans hbound)
  by_cases hb : u=⟨j+1,hj⟩
  · subst u; exact (le_max_right _ _).trans (hm.trans hbound)
  rw [← K_swap_other A B σ j hj u ha hb]
  exact Finset.le_sup' _ (Finset.mem_univ _)

end CJohnson



/-- p. 63, adjacent interchange and (I) ⟺ (II): let `σ'` be `σ` with the items in positions
`j` and `j + 1` interchanged. Then `K'_u = K_u` for every other position `u`, and
`max (K_j, K_{j+1}) < max (K'_j, K'_{j+1})` holds exactly when
`min (A (σ j), B (σ (j+1))) < min (A (σ (j+1)), B (σ j))`. -/
theorem solution {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (hj : j + 1 < n) :
    (∀ u : Fin n, u ≠ ⟨j, by omega⟩ → u ≠ ⟨j + 1, hj⟩ →
        Shared.K A B (σ * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) u = Shared.K A B σ u) ∧
    (max (Shared.K A B σ ⟨j, by omega⟩) (Shared.K A B σ ⟨j + 1, hj⟩) <
        max (Shared.K A B (σ * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) ⟨j, by omega⟩)
            (Shared.K A B (σ * Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩) ⟨j + 1, hj⟩) ↔
      min (A (σ ⟨j, by omega⟩)) (B (σ ⟨j + 1, hj⟩)) <
        min (A (σ ⟨j + 1, hj⟩)) (B (σ ⟨j, by omega⟩))) := by
  exact CJohnson.interchange_iff A B σ j hj


