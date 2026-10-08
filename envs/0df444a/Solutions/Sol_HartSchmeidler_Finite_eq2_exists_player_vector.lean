-- Prove2me | solution 1 for HartSchmeidler.Finite.eq2_exists_player_vector
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:35:09.610973+00:00
-- url     : https://prove2.me/submissions/92b369cd-cd09-4f52-92f1-318e9b53ad05

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HartSchmeidler_Finite_Game

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HsWork

open Finset

/-- A nonnegative array has a probability vector in the kernel of its generator (an invariant
distribution of the associated Markov chain), obtained from a left null vector by taking absolute
values. -/
theorem exists_balance_vector {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    (y : T → T → ℝ) (hy : ∀ r t, 0 ≤ y r t) :
    ∃ x : T → ℝ, AGT.IsLottery x ∧ ∀ r, x r * ∑ t, y r t = ∑ t, x t * y t r := by
  set R : T → ℝ := fun r => ∑ t, y r t with hR
  set c : ℝ := 1 + ∑ r, R r with hc
  have hRnn : ∀ r, 0 ≤ R r := fun r => Finset.sum_nonneg fun t _ => hy r t
  have hRle : ∀ r, R r ≤ ∑ r', R r' := fun r =>
    Finset.single_le_sum (fun r' _ => hRnn r') (Finset.mem_univ r)
  have hcpos : 0 < c := by
    have := Finset.sum_nonneg fun r (_ : r ∈ Finset.univ) => hRnn r
    linarith
  let M : Matrix T T ℝ := Matrix.of fun r t => y r t / c + if r = t then 1 - R r / c else 0
  have hMnn : ∀ r t, 0 ≤ M r t := by
    intro r t
    simp only [M, Matrix.of_apply]
    have h1 : 0 ≤ y r t / c := div_nonneg (hy r t) hcpos.le
    split_ifs
    · have : R r / c ≤ 1 := by rw [div_le_one hcpos]; linarith [hRle r]
      linarith
    · linarith
  have hMrow : ∀ r, ∑ t, M r t = 1 := by
    intro r
    simp only [M, Matrix.of_apply, Finset.sum_add_distrib]
    rw [← Finset.sum_div, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    have : ∑ t, y r t = R r := rfl
    rw [this]; ring
  have hdet : (M - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      obtain ⟨t⟩ := ‹Nonempty T›
      have := congrFun h t
      simp at this
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      ext r
      simp [Matrix.mulVec, dotProduct, hMrow r]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hvM : ∀ t, ∑ r, v r * M r t = v t := by
    intro t
    have h := hv
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at h
    have := congrFun h t
    simpa [Matrix.vecMul, dotProduct] using this
  -- absolute values give an invariant nonnegative vector
  have hineq : ∀ t, |v t| ≤ ∑ r, |v r| * M r t := by
    intro t
    calc |v t| = |∑ r, v r * M r t| := by rw [hvM t]
      _ ≤ ∑ r, |v r * M r t| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r, |v r| * M r t := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [abs_mul, abs_of_nonneg (hMnn r t)]
  have htot : ∑ t, ∑ r, |v r| * M r t = ∑ t, |v t| := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hMrow, mul_one]
  have heq : ∀ t, ∑ r, |v r| * M r t = |v t| := by
    have := (Finset.sum_eq_sum_iff_of_le (fun t _ => hineq t)).1 htot.symm
    exact fun t => (this t (Finset.mem_univ t)).symm
  have hW : 0 < ∑ t, |v t| := by
    obtain ⟨t0, ht0⟩ : ∃ t, v t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    exact lt_of_lt_of_le (abs_pos.2 ht0)
      (Finset.single_le_sum (f := fun t => |v t|) (fun t _ => abs_nonneg _) (Finset.mem_univ t0))
  set W : ℝ := ∑ t, |v t| with hWdef
  refine ⟨fun t => |v t| / W, ⟨fun t => div_nonneg (abs_nonneg _) hW.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div]; exact div_self hW.ne'
  · intro t
    have h1 := heq t
    simp only [M, Matrix.of_apply, mul_add, Finset.sum_add_distrib] at h1
    have h2 : ∑ r, |v r| * (y r t / c) = (∑ r, |v r| * y r t) / c := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun r _ => by ring
    have h3 : ∑ r, |v r| * (if r = t then 1 - R r / c else 0) = |v t| * (1 - R t / c) := by
      simp [Finset.sum_ite_eq]
    rw [h2, h3] at h1
    have h4 : (∑ r, |v r| * y r t) = |v t| * R t := by
      field_simp at h1
      nlinarith
    show |v t| / W * ∑ t', y t t' = ∑ t', |v t'| / W * y t' t
    have h5 : ∑ t', y t t' = R t := rfl
    have h6 : ∑ t', |v t'| / W * y t' t = (∑ t', |v t'| * y t' t) / W := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun t' _ => by ring
    rw [h5, h6, h4]; ring

end HsWork

namespace HsWork

open Finset

theorem eq2_exists_player_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Nonempty (S j)] (h : ι → (∀ j, S j) → ℝ)
    (i : ι) (y : S i → S i → ℝ) (hy : ∀ r t, 0 ≤ y r t)
    (hbal : ∃ x : S i → ℝ, AGT.IsLottery x ∧ ∀ r, x r * ∑ t, y r t = ∑ t, x t * y t r) :
    ∃ x : S i → ℝ, AGT.IsLottery x ∧
      ∀ s : ∀ j, S j,
        ∑ r, x r * ∑ t, y r t *
          (h i (Function.update s i r) - h i (Function.update s i t)) = 0 := by
  obtain ⟨x, hx, hbal⟩ := hbal
  refine ⟨x, hx, fun s => ?_⟩
  set H : S i → ℝ := fun r => h i (Function.update s i r) with hH
  show ∑ r, x r * ∑ t, y r t * (H r - H t) = 0
  have e1 : ∑ r, x r * ∑ t, y r t * (H r - H t) =
      ∑ r, (x r * ∑ t, y r t) * H r - ∑ t, (∑ r, x r * y r t) * H t := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => by ring
  rw [e1]
  have e2 : ∑ r, (x r * ∑ t, y r t) * H r = ∑ t, (∑ r, x r * y r t) * H t := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hbal r]
  rw [e2, sub_self]


end HsWork

open HartSchmeidler.Finite Finset

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Nonempty (S j)] (h : ι → (∀ j, S j) → ℝ)
    (i : ι) (y : S i → S i → ℝ) (hy : ∀ r t, 0 ≤ y r t) :
    ∃ x : S i → ℝ, AGT.IsLottery x ∧
      ∀ s : ∀ j, S j,
        ∑ r, x r * ∑ t, y r t *
          (h i (Function.update s i r) - h i (Function.update s i t)) = 0 :=
  HsWork.eq2_exists_player_vector h i y hy (HsWork.exists_balance_vector y hy)

#print axioms solution
