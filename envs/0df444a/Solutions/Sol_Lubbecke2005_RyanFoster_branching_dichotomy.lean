-- Prove2me | solution 1 for Lubbecke2005.RyanFoster.branching_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:48:50.761851+00:00
-- url     : https://prove2.me/submissions/ed9f5c82-812a-4e0b-9fd4-dad57308868a

import Mathlib
import Definitions.Def_Lubbecke2005_RyanFoster_SetPartitioning
open Matrix Lubbecke2005.RyanFoster

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : IsZeroOneMatrix A) (lam : Fin n → ℝ) (hint : IsZeroOneVector lam)
    (hfeas : A *ᵥ lam = fun _ => 1) (r s : Fin m) :
    pairCover A lam r s = 0 ∨ pairCover A lam r s = 1 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j => A r j = 1 ∧ A s j = 1 ∧ lam j = 1)
  have hcount : pairCover A lam r s = (S.card : ℝ) := by
    unfold pairCover
    rw [show (S.card : ℝ) = ∑ j : Fin n, if A r j = 1 ∧ A s j = 1 ∧ lam j = 1 then (1 : ℝ) else 0 by
      simp [S]]
    apply Finset.sum_congr rfl
    intro j _
    rcases hA r j with hr | hr <;> rcases hA s j with hs | hs <;>
      rcases hint j with hj | hj <;> simp [hr, hs, hj]
  have hle : pairCover A lam r s ≤ 1 := by
    have hr := congrFun hfeas r
    change (∑ j, A r j * lam j) = 1 at hr
    rw [← hr]
    apply Finset.sum_le_sum
    intro j _
    rcases hA r j with hr | hr <;> rcases hA s j with hs | hs <;>
      rcases hint j with hj | hj <;> simp [hr, hs, hj]
  rw [hcount]
  have hcard : S.card ≤ 1 := by exact_mod_cast (show (S.card : ℝ) ≤ 1 by rwa [← hcount])
  have hc : S.card = 0 ∨ S.card = 1 := by omega
  rcases hc with hc | hc <;> simp [hc]
