-- Prove2me | solution 1 for L0BnB.Relax.VB_eq_min_H
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:46:38.437019+00:00
-- url     : https://prove2.me/submissions/3311ab93-2103-4461-b717-eff7ceaaa706

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_H

open L0BnB.Relax in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M) :
    IsLeast (H X y lam0 lam2 M '' {β | ∀ i, |β i| ≤ M}) (VB X y lam0 lam2 M) := by
  set box : Set (Fin p → ℝ) := {β | ∀ i, |β i| ≤ M} with hbox
  set V := {v | ∃ β z : Fin p → ℝ, bigMFeasible M β z ∧ bigMObj X y lam0 lam2 β z = v} with hV
  have hrss : ∀ β, 0 ≤ rss X y β := by
    intro β; unfold rss; positivity
  -- every feasible objective dominates H
  have hdom : ∀ β z, bigMFeasible M β z → H X y lam0 lam2 M β ≤ bigMObj X y lam0 lam2 β z ∧
      β ∈ box := by
    intro β z hf
    refine ⟨?_, fun i => ?_⟩
    · unfold H bigMObj
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have : ∀ i, lam0 / M * |β i| ≤ lam0 * z i := by
        intro i
        obtain ⟨_, _, h3, h4⟩ := hf i
        have : |β i| ≤ M * z i := abs_le.2 ⟨by linarith, h4⟩
        rw [div_mul_eq_mul_div, div_le_iff₀ hM]
        nlinarith
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => this i)
      linarith
    · obtain ⟨_, hz1, h3, h4⟩ := hf i
      exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  -- each β in the box gives a feasible pair with objective H β
  have hach : ∀ β ∈ box, H X y lam0 lam2 M β ∈ V := by
    intro β hβ
    refine ⟨β, fun i => |β i| / M, fun i => ?_, ?_⟩
    · have hb := hβ i
      refine ⟨div_nonneg (abs_nonneg _) hM.le, (div_le_one hM).2 hb, ?_, ?_⟩
      · rw [mul_div_cancel₀ _ hM.ne']; exact neg_le_of_abs_le le_rfl
      · rw [mul_div_cancel₀ _ hM.ne']; exact le_abs_self _
    · unfold H bigMObj
      rw [Finset.sum_add_distrib]
      have hA : ∑ i, lam0 / M * |β i| = lam0 * ∑ i, |β i| / M := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      have hB : ∑ i, lam2 * β i ^ 2 = lam2 * ∑ i, β i ^ 2 := by rw [Finset.mul_sum]
      rw [hA, hB]; ring
  have hbdd : BddBelow V := by
    refine ⟨0, ?_⟩
    rintro v ⟨β, z, hf, rfl⟩
    unfold bigMObj
    have h1 := hrss β
    have h2 : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => (hf i).1)
    have h3 : 0 ≤ ∑ i, β i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    positivity
  -- compactness and continuity
  have hcomp : IsCompact box := by
    have : box = Set.Icc (fun _ => -M) (fun _ => M) := by
      ext β
      simp only [hbox, Set.mem_setOf_eq, Set.mem_Icc, abs_le, Pi.le_def, forall_and]
    rw [this]
    exact isCompact_Icc
  have hne : box.Nonempty := ⟨0, fun i => by simp [hM.le]⟩
  have hcont : Continuous (H X y lam0 lam2 M) := by
    unfold H rss
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  obtain ⟨βs, hβs, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
  have hVB : VB X y lam0 lam2 M = H X y lam0 lam2 M βs := by
    apply le_antisymm
    · exact csInf_le hbdd (hach βs hβs)
    · apply le_csInf ⟨_, hach βs hβs⟩
      rintro v ⟨β, z, hf, rfl⟩
      obtain ⟨hle, hβ⟩ := hdom β z hf
      exact le_trans (isMinOn_iff.1 hmin β hβ) hle
  refine ⟨⟨βs, hβs, hVB.symm⟩, ?_⟩
  rintro v ⟨β, hβ, rfl⟩
  rw [hVB]
  exact isMinOn_iff.1 hmin β hβ
