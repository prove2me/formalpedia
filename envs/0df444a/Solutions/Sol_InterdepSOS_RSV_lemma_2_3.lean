-- Prove2me | solution 1 for InterdepSOS.RSV.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:20:04.783994+00:00
-- url     : https://prove2.me/submissions/9d9e2a8c-1290-400c-a930-f3e2964054ff

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting
set_option autoImplicit false
open InterdepSOS.RSV

theorem l23_aux_BB {n : ℕ} (w : Signal n → ℝ) (d : ℝ) (hd : IsDSOS d w) (A : Finset (Fin n))
    (s y s' : Signal n) (hss' : ∀ j, j ∉ A → s j ≤ s' j) :
    ∀ T : Finset (Fin n), T ⊆ A →
      w (fun j => if j ∈ A then (if j ∈ T then s j + y j else s j) else s' j) -
        w (fun j => if j ∈ A then s j else s' j) ≤
      d * (w (fun j => if j ∈ T then s j + y j else s j) - w s) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    have e1 : (fun j => if j ∈ A then (if j ∈ (∅ : Finset (Fin n)) then s j + y j else s j) else s' j)
        = (fun j => if j ∈ A then s j else s' j) := by
      funext j; simp
    have e2 : (fun j => if j ∈ (∅ : Finset (Fin n)) then s j + y j else s j) = s := by
      funext j; simp
    rw [e1, e2]; simp
  | insert a T haT ih =>
    intro hsub
    have hTA : T ⊆ A := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have haA : a ∈ A := hsub (Finset.mem_insert_self a T)
    have ih' := ih hTA
    set PL : Signal n := fun j => if j ∈ A then (if j ∈ T then s j + y j else s j) else s' j with hPL
    set PR : Signal n := fun j => if j ∈ T then s j + y j else s j with hPR
    have hL1 : (fun j => if j ∈ A then (if j ∈ insert a T then s j + y j else s j) else s' j)
        = Function.update PL a (s a + y a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPL, haA]
      · simp [hPL, Function.update_of_ne hj, hj]
    have hL2 : PL = Function.update PL a (s a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPL, haA, haT]
      · simp [Function.update_of_ne hj]
    have hR1 : (fun j => if j ∈ insert a T then s j + y j else s j)
        = Function.update PR a (s a + y a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPR]
      · simp [hPR, Function.update_of_ne hj, hj]
    have hR2 : PR = Function.update PR a (s a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPR, haT]
      · simp [Function.update_of_ne hj]
    have key := hd a (s a) (y a) PL PR (by
      intro l hl
      by_cases hlA : l ∈ A
      · simp [hPL, hPR, hlA]
      · have : l ∉ T := fun h => hlA (hTA h)
        simp [hPL, hPR, hlA, this, hss' l hlA])
    rw [hL1, hR1]
    rw [← hL2, ← hR2] at key
    linarith

theorem solution {n : ℕ} (w : Signal n → ℝ) (hw : ∀ s, 0 ≤ w s)
    (d : ℝ) (hd : IsDSOS d w) (A : Finset (Fin n))
    (s y s' : Signal n) (hss' : ∀ j, j ∉ A → s j ≤ s' j) :
    w (fun j => if j ∈ A then s j + y j else s' j) -
      w (fun j => if j ∈ A then s j else s' j) ≤
      d * (w (fun j => if j ∈ A then s j + y j else s j) - w s) := by
  have h := l23_aux_BB w d hd A s y s' hss' A (Finset.Subset.refl A)
  have e1 : (fun j => if j ∈ A then (if j ∈ A then s j + y j else s j) else s' j)
      = (fun j => if j ∈ A then s j + y j else s' j) := by
    funext j; by_cases hj : j ∈ A <;> simp [hj]
  rw [e1] at h
  exact h
