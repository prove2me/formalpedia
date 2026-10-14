-- Prove2me | solution 1 for NestedLogitVariants.General.xh_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:19:28.148243+00:00
-- url     : https://prove2.me/submissions/0f765c98-a6ca-488f-9152-634e22ae09a1

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR



namespace NestedLogitVariants.General

theorem xh_nonneg_core {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh) :
    0 ≤ xh := by
  obtain ⟨i0, -⟩ := hsyn
  by_contra hneg
  push_neg at hneg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have := hopt.2 (xh - 1) (fun i => if i = i0 then I.v0 * (xh - 1) else 0) ⟨by
        simp [Finset.sum_ite_eq'], by
        intro i S hS
        rcases hS with ⟨k, hk, -⟩ | ⟨j, -⟩
        · simp at hk
        · exact j.elim0⟩
    linarith
  · set j : Fin n := ⟨0, hn⟩
    have hpos : ∀ i, 0 < yh i := by
      intro i
      have h := hopt.1.2 i {j} (Or.inr ⟨j, rfl⟩)
      have hV : 0 < V I i {j} := by
        simp [V]; linarith [hI.vnp_nonneg i, hI.v_pos i j]
      have hW : 0 < nestWeight I i {j} := Real.rpow_pos_of_pos hV _
      have hR : 0 ≤ R I i {j} := by
        unfold R; apply div_nonneg _ hV.le
        simp; exact mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le
      have : 0 < nestWeight I i {j} * (R I i {j} - xh) := mul_pos hW (by linarith)
      linarith
    have hs : 0 < ∑ i, yh i := Finset.sum_pos (fun i _ => hpos i) ⟨i0, Finset.mem_univ _⟩
    have := hopt.1.1
    have : I.v0 * xh ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hI.v0_nonneg hneg.le
    linarith

end NestedLogitVariants.General

open NestedLogitVariants.General


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh) :
    0 ≤ xh := by
  exact xh_nonneg_core I hI hsyn xh yh hopt
