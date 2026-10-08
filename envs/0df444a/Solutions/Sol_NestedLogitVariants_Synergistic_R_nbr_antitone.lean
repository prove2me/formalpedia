-- Prove2me | solution 1 for NestedLogitVariants.Synergistic.R_nbr_antitone
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:42:29.303182+00:00
-- url     : https://prove2.me/submissions/c89eefdf-c0b5-45d2-91fd-cb601f147716

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Relaxation
import Definitions.Def_NestedLogitVariants_Synergistic_Factor
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NestedLogitVariants.Synergistic

theorem prep_V_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ V I i S :=
  add_nonneg (hI.vnp_nonneg i) (Finset.sum_nonneg fun j _ => (hI.v_pos i j).le)

theorem prep_R_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (S : Finset (Fin n)) : 0 ≤ R I i S :=
  div_nonneg (Finset.sum_nonneg fun j _ =>
    mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le) (prep_V_nonneg I hI i S)

theorem prep_lp4_opt_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ)
    (hopt : LP4Optimal I A xh yh) : 0 ≤ xh := by
  have hfeas : LP4Feasible I A (2 * xh) (fun i => 2 * yh i) := by
    constructor
    · rw [← Finset.mul_sum]
      nlinarith [hopt.1.1]
    · intro i S hS
      have hc := hopt.1.2 i S hS
      have hwr : 0 ≤ nestWeight I i S * R I i S :=
        mul_nonneg (Real.rpow_nonneg (prep_V_nonneg I hI i S) _) (prep_R_nonneg I hI i S)
      nlinarith
  have hm := hopt.2 (2 * xh) (fun i => 2 * yh i) hfeas
  linarith

theorem xh_yh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh) :
    (∀ i, 0 ≤ yh i) ∧ 0 ≤ xh := by
  constructor
  · intro i
    have h := hopt.1.2 i (nbr n 0) ⟨0, Nat.zero_le _, rfl⟩
    simpa [nbr, nestWeight, V, hfc i, Real.zero_rpow (hI.γ_pos i).ne'] using h
  · exact prep_lp4_opt_nonneg I hI _ xh yh hopt

theorem lp7_feasible_lp3 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i) :
    ∀ x (y : ι → ℝ), LP7Feasible I x y → LP3Feasible I x y := by
  intro x y h
  refine ⟨h.1, ?_⟩
  intro i S
  let z : Fin n → ℝ := fun j => if j ∈ S then 1 else 0
  have hz : z ∈ NestedLogitVariants.LP.box n := by
    intro j _
    dsimp [z]
    split_ifs <;> norm_num
  have hbound := h.2 i z hz
  simpa [F8, z, nestWeight, R, V, hfc i, mul_ite, Finset.sum_ite] using hbound

theorem prep_nbr_succ {n k : ℕ} (hk : k < n) :
    nbr n (k + 1) = insert ⟨k, hk⟩ (nbr n k) := by
  ext j
  simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

theorem prep_nbr_weight_pos {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    0 < ∑ j ∈ nbr n k, I.v i j := by
  have hn : 0 < n := hk.trans_le hkn
  have hmem : (⟨0, hn⟩ : Fin n) ∈ nbr n k := by simp [nbr, hk]
  exact (hI.v_pos i ⟨0, hn⟩).trans_le
    (Finset.single_le_sum (fun j _ => (hI.v_pos i j).le) hmem)


end NestedLogitVariants.Synergistic

open NestedLogitVariants.Synergistic

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (i : ι) (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) :
    R I i (nbr n j) ≤ R I i (nbr n (j - 1)) := by
  let k : Fin n := ⟨j - 1, by omega⟩
  have hins : nbr n j = insert k (nbr n (j - 1)) := by
    simpa only [k, Nat.sub_add_cancel (by omega : 1 ≤ j)] using
      prep_nbr_succ (n := n) (k := j - 1) (by omega)
  have hnot : k ∉ nbr n (j - 1) := by simp [nbr, k]
  have hq := prep_nbr_weight_pos I hI i (j - 1) (by omega) (by omega)
  have hq' : 0 < I.v i k + ∑ a ∈ nbr n (j - 1), I.v i a :=
    add_pos (hI.v_pos i k) hq
  have hrw : I.r i k * (∑ a ∈ nbr n (j - 1), I.v i a) ≤
      ∑ a ∈ nbr n (j - 1), I.r i a * I.v i a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have hak : a ≤ k := by
      have hv := (Finset.mem_filter.mp ha).2
      change a.val ≤ j - 1
      omega
    exact mul_le_mul_of_nonneg_right (hI.r_antitone i hak) (hI.v_pos i a).le
  simp only [R, V, hfc i, zero_add, hins, Finset.sum_insert hnot]
  apply (div_le_div_iff₀ hq' hq).mpr
  nlinarith [mul_le_mul_of_nonneg_left hrw (hI.v_pos i k).le]
