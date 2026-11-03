-- Prove2me | solution 1 for HnEpsData.H_n_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:22:33.793209+00:00
-- url     : https://prove2.me/submissions/ec7538fc-a0c0-4004-bae8-5fda5b4671ef

import Mathlib
import Definitions.Def_OAIQ093D001

section
-- module Solutions.OAIQ093_PR.Unitary_HnEps
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The sets `H_n` and their upper bounds

The `HnEpsData` bundle of standing hypotheses, the sets `H_n eps`, and upper bounds on products
of their elements.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


open scoped Pointwise Finset


namespace HnEpsData
variable [h_n_eps_data: HnEpsData]


open scoped Finset
open scoped Pointwise


omit h_n_eps_data in
lemma unitary_shrink {n : ℕ} (a b : Matrix.unitaryGroup (Fin n) ℂ): ‖(a * b).val - 1‖ ≤ ‖a.val - 1‖ + ‖b.val - 1‖ := by
  conv =>
    lhs
    arg 1
    arg 1
    equals (a.val - 1) * b + b =>
      rw [sub_mul]
      simp

  rw [← add_sub]
  grw [norm_add_le]
  rw [CStarRing.norm_mul_coe_unitary]


lemma H_n_upper_bound (data : HnData) (n : ℕ): ‖(theorem_3_8_h_n data (n + 1)).g.val.val - 1‖ ≤ 2 * (H_n_eps data.hd) * ‖(theorem_3_8_h_n data (n)).g.val.val - 1‖ := by
  conv =>
    lhs
    unfold theorem_3_8_h_n
  simp
  have coe_comm_g (a b : data.G): ⁅a.val, b.val⁆ = ⁅a, b⁆.val := by
    rw [commutatorElement_def]
    rw [commutatorElement_def]
    norm_cast

  rw [← coe_comm_g]
  grw [shrinking_conjugators]
  grw [data.S_dist]
  simp

lemma H_n_upper_bound_iter (data : HnData) {a : ℕ} (n : ℕ): ‖(theorem_3_8_h_n data (a + n)).g.val.val - 1‖ ≤ ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ * 2^n * (H_n_eps data.hd)^n  := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [← add_assoc]
    grw [H_n_upper_bound]
    grw [ih]
    abel_nf
    · ring_nf
      rfl
    · simp
      have H_eps_pos := H_n_eps_pos data.hd
      linarith


lemma H_n_single_pow {n : ℕ} {m : ℕ} (data : HnData): ‖((theorem_3_8_h_n data n).g.val^m).val - 1‖ ≤ m * ‖(theorem_3_8_h_n data n).g.val.val - 1‖ := by
  induction m with
  | zero =>
    simp [pow_zero]
  | succ m ih =>
    rw [pow_succ]
    grw [unitary_shrink]
    grw [ih]
    simp
    rw [add_mul]
    simp

lemma H_n_pow_le  {a k : ℕ } {m : ℕ} (a_k_lt : a + k ≤ m)  (pows : Fin m → ℕ) (data : HnData):
  ‖(List.ofFn (fun (i : Fin (k)) => (theorem_3_8_h_n data (a + i)).g^(pows ⟨(a + i), by (have foo := i.isLt; omega)⟩))).prod.val.val - 1‖ ≤ ∑ (i : Fin k), (pows ⟨(a + i), by (have foo := i.isLt; omega)⟩) * ‖(theorem_3_8_h_n data (a + i)).g.val.val - 1‖ := by
  induction k with
  | zero =>
    simp [List.ofFn, List.prod_nil]
  | succ k ih =>
    simp only [ne_eq, List.ofFn_succ']
    simp only [Fin.coe_castSucc, Fin.val_last, List.concat_eq_append, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, Subgroup.val_list_prod,
      List.map_ofFn]

    rw [Subgroup.coe_mul]
    grw [unitary_shrink]
    have prev_le := ih (by linarith)
    grw [prev_le]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_range_succ]
    rw [SubmonoidClass.coe_pow]
    grw [H_n_single_pow]
    simp
    nth_rw 2 [← Finset.sum_attach]


    conv =>
      rhs
      arg 2
      intro x
      equals if h : ↑x < k then ↑(pows ⟨↑(a + x), by omega⟩) * ‖(theorem_3_8_h_n data ↑(a + x)).g.val.val - 1‖ else 0 =>
        have x_lt_m := x.property
        rw [Finset.mem_range] at x_lt_m
        have x_lt_m_succ : x.val < k + 1 := by
          omega
        simp [x_lt_m, Nat.le_of_lt_succ x_lt_m_succ]

    rw [← Finset.sum_attach]


-- Equation 3.16
lemma H_n_prod_le_k {a k : ℕ } {m : ℕ} (a_k_lt : a + k + 1 ≤ m) (c : ℝ) (c_pos : 0 < c) (c_lt : c < 1 / 40) (pows : Fin m → ℕ) (data : HnData)
 (pows_le : ∀ i : Fin m, (pows i) ≤ c * (H_n_eps data.hd)⁻¹) :
  ‖(List.ofFn (fun (i : Fin (k)) => (theorem_3_8_h_n data ((a + 1) + i)).g^(pows ⟨((a + 1) + i), by omega⟩))).prod.val.val - 1‖ ≤ ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ / 10 := by


  grw [H_n_pow_le]
  grw [Finset.sum_le_sum (g := (fun i : Fin (k) => (c * (H_n_eps data.hd)⁻¹) * ‖(theorem_3_8_h_n data ((a + 1) + i)).g.val.val - 1‖))]
  · rw [← Finset.mul_sum]
    grw [Finset.sum_le_sum (g := (fun i : Fin (k) => ‖(theorem_3_8_h_n data (a)).g.val.val - 1‖ * 2^(1 + i.val) * (H_n_eps data.hd)^(1 + i.val)))]
    · have eps_nonneg := H_n_eps_pos data.hd
      simp
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      simp_rw [← mul_pow]
      simp_rw [add_comm]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
      rw [Finset.sum_fin_eq_sum_range]
      rw [Finset.sum_congr (s₁ := Finset.range k) (s₂ := Finset.range k) (g := fun i => (2 * H_n_eps data.hd) ^ i)]

      nth_rw 4 [mul_comm]
      rw [Finset.range_eq_Ico, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      grw [geom_sum_Ico_le_of_lt_one]
      simp
      -- TODO - make this a lemma
      have two_mul_le : 2 * (H_n_eps data.hd) < (1 / 2) := by
        have foo := H_n_eps_lt data.hd
        linarith
      nth_grw 2 [two_mul_le]
      field_simp
      norm_num
      have eps_ne_zero : 0 ≠ (H_n_eps data.hd) := by
        linarith


      ring_nf
      field_simp [eps_ne_zero]

      grw [c_lt]
      ring
      rfl
      · positivity
      · grw [H_n_eps_lt data.hd]
        norm_num
      · rfl
      · intro x hx
        simp at hx
        simp [hx]
    · simp [c_pos]
      have pos := H_n_eps_pos data.hd
      linarith
    -- H_n_upper_bound_iter
    · intro i hi
      rw [add_assoc]
      grw [H_n_upper_bound_iter data]
  · intro i hi
    grw [pows_le]
  · omega

end HnEpsData
end

section
-- module Solutions.OAIQ093_PR.Unitary_HnLowerBound
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A lower bound for powers in `H_n`

The real auxiliary function `f` and the resulting lower bound `H_n_single_pow_lower_bound`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]

omit h_n_eps_data in
lemma norm_sub_swap (n: ℕ) (a b: Matrix (Fin n) (Fin n) ℂ): ‖a - b‖ = ‖b - a‖ := by
  rw [← neg_sub]
  rw [norm_neg]


omit h_n_eps_data in
lemma f_one_eq_zero (a: ℝ): f a 1 = 0 := by
  simp [f]
  ring

omit h_n_eps_data in
lemma f_deriv (a: ℝ) (ha: 0 < 1 + a) (x: ℝ): (deriv (f a)) x = 2*a - (Real.log (1 + a))*(1 + a)^x := by
  unfold f
  simp_rw [← add_sub]
  rw [deriv_const_add]
  rw [← Pi.sub_def]
  rw [deriv_sub]
  · rw [deriv_mul_const]
    · rw [deriv_sub_const, deriv_const_mul]
      · simp
        have deriv_pow := (Real.hasStrictDerivAt_const_rpow (a := 1 + a) ha x).hasDerivAt.deriv
        simp [deriv_pow, mul_comm]
      · simp
    · simp
      apply DifferentiableAt.const_mul
      simp
  · apply DifferentiableAt.mul_const
    simp
    apply DifferentiableAt.const_mul
    simp
  · apply (Real.hasStrictDerivAt_const_rpow _ _).hasDerivAt.differentiableAt
    exact ha


lemma f_deriv_at_one (a: ℝ) (a_pos: 0 < a) (a_lt: a < 1) (ha: 0 < 1 + a): 0 < (deriv (f a) 1) := by
  rw [f_deriv _ ha]
  grw [Real.log_le_sub_one_of_pos]
  · have a_mul_self := mul_lt_of_lt_one_left (a := a) (b := a) (by linarith) (by linarith)
    simp only [add_sub_cancel_left, Real.rpow_one, sub_pos, gt_iff_lt]
    linarith
  simp [ha]


lemma f_deriv_lower (a: ℝ) (ha: 0 < 1 + a) (a_pos: 0 < a) (x: ℝ) (f_zero: (deriv (f a)) x = 0): (Real.log 2) / a ≤ x := by
  have log_plus_le: Real.log (1 + a) ≤ a := by
    grw [Real.log_le_sub_one_of_pos]
    · simp
    · exact ha

  have log_pos : 0 < Real.log (1 + a) := Real.log_pos (by linarith)
  have log_ne : Real.log (1 + a) ≠ 0 := ne_of_gt log_pos

  rw [f_deriv _ ha] at f_zero
  rw [sub_eq_zero] at f_zero
  nth_rw 2 [mul_comm] at f_zero
  replace f_zero := div_eq_of_eq_mul log_ne f_zero
  apply_fun Real.log at f_zero
  rw [Real.log_rpow ha] at f_zero
  replace f_zero := div_eq_of_eq_mul log_ne f_zero
  rw [Real.log_div (mul_ne_zero (by norm_num) a_pos.ne') log_ne,
    Real.log_mul (by norm_num) a_pos.ne'] at f_zero
  rw [← f_zero]

  have log_log_le : Real.log (Real.log (1 + a)) ≤ Real.log a :=
    Real.log_le_log log_pos log_plus_le

  calc Real.log 2 / a
      ≤ Real.log 2 / Real.log (1 + a) :=
        div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) log_pos log_plus_le
    _ ≤ (Real.log 2 + Real.log a - Real.log (Real.log (1 + a))) / Real.log (1 + a) :=
        div_le_div_of_nonneg_right (by linarith) log_pos.le

lemma f_pos_on (a: ℝ) (ha: 0 < 1 + a) (a_pos: 0 < a) (a_lt: a < 1)  (a_lt_log: a < Real.log 2): ∀ x ∈ Set.Ioc 1 (Real.log 2 / a), 0 < f a x := by

  have deriv_nonzero: ∀ x ∈ Set.Ico 1 (Real.log 2 / a), (deriv (f a)) x ≠  0 := by
    intro x hx
    by_contra!
    have x_eq := f_deriv_lower a ha a_pos x this
    have x_lt := hx.right
    linarith

  have one_lt : 1 < Real.log (2) / a := by
    rw [lt_div_iff₀]
    . simp
      exact a_lt_log
    . exact a_pos

  have f_strict := strictMonoOn_of_deriv_pos (f := f a) (D := Set.Icc 1 ((Real.log (2 )) / a)) (by apply convex_Icc) ?_ ?_
  .
    intro x hx
    have f_lt := f_strict.lt_iff_lt (a := 1) (b := x) ?_ ?_
    rw [f_one_eq_zero] at f_lt
    have x_prop := hx.left
    simp [x_prop] at f_lt
    . exact f_lt
    . simp
      linarith
    . simp
      simp at hx
      refine ⟨by linarith, hx.right⟩
  . apply Continuous.continuousOn
    unfold f
    have one_plus: 1 + a ≠ 0 := by linarith
    fun_prop (disch:=assumption)
  .

    intro x hx
    simp at hx

    have deriv_pos: 0 ≤ (deriv (f a)) x := by
      by_contra!
      have foo := ContinuousOn.surjOn_Icc (f := deriv (f a)) (a := x) (b := 1) (s := Set.Ico 1 ((Real.log 2) / a)) ?_ ?_ ?_

      have zero_mem: 0 ∈ (Set.Icc (deriv (f a) x) (deriv (f a) 1)) := by
        simp
        refine ⟨by linarith, ?_⟩
        have my_deriv := f_deriv_at_one a a_pos a_lt ha
        linarith


      unfold Set.SurjOn at foo
      have deriv_zero := foo zero_mem
      rw [Set.mem_image] at deriv_zero
      obtain ⟨y, y_mem, y_deriv⟩ := deriv_zero
      have y_nonzero := deriv_nonzero y y_mem
      . contradiction
      . apply Continuous.continuousOn
        unfold f
        have one_plus: ∀ x: ℝ, 1 + a ≠ 0 := by
          intro x
          linarith
        fun_prop (disch:=assumption)
      . simp
        refine ⟨by linarith, hx.right⟩
      . simp
        exact one_lt

    have not_zero := deriv_nonzero x ?_
    . exact lt_of_le_of_ne deriv_pos (id (Ne.symm not_zero))
    . simp
      refine ⟨by linarith, hx.right⟩


lemma H_n_single_pow_lower_bound {n : ℕ} {m : ℕ} (m_gt: 1 ≤ m) (data : HnData) (m_lt: m < (1/2) / ‖(theorem_3_8_h_n data n).g.val.val - 1‖) : ‖((theorem_3_8_h_n data n).g.val.val^m) - 1‖ ≥ ‖((theorem_3_8_h_n data n).g.val).val - 1‖ := by

  push_cast
  -- TODO: figure out how to get 'SubgroupClass.coe_zpow' to fire for Matrix.unitaryGroup

  conv =>
    lhs
    arg 1
    lhs
    arg 1
    equals (1 + ((theorem_3_8_h_n data n).g.val.val - 1)) =>
      simp

  rw [norm_sub_swap]
  have m_eq: m = (m - 1) + 1 := by
    omega

  rw[add_comm]
  rw [Commute.add_pow (by simp)]
  rw[Finset.sum_range_succ']
  conv =>
    lhs
    arg 1
    rhs
    simp

  nth_rw 1 [m_eq]
  rw [Finset.sum_range_succ']
  simp
  rw [← ge_iff_le]
  rw [← sub_eq_add_neg]
  grw [(norm_sub_norm_le _ _).ge]
  rw [norm_neg]
  --grw [norm_sum_le]


  have nonempty_d: Nonempty (Fin data.d) := by
    have data_pos := data.hd
    exact Fin.pos_iff_nonempty.mp (by linarith)

  have my_pow := Commute.add_pow (y := 1) (x := ‖((theorem_3_8_h_n data n).g.val.val - 1)‖) (n := m - 1 + 1) (by simp)
  rw [Finset.sum_range_succ'] at my_pow
  simp at my_pow
  rw [Finset.sum_range_succ'] at my_pow
  simp at my_pow
  rw [← m_eq] at my_pow
  rw [add_assoc] at my_pow
  apply sub_eq_of_eq_add at my_pow
  norm_cast at my_pow
  rw [← m_eq] at my_pow
  grw [norm_sum_le]

  grw [Finset.sum_le_sum (g := fun i => ‖((theorem_3_8_h_n data n).g.val.val - 1)‖ ^ (i + 1 + 1) * (m.choose (i + 1 + 1)))]
  .
    rw [← my_pow]

    have S_le : (1 + ‖((theorem_3_8_h_n data n).g).val.val - 1‖)^m - ((‖(theorem_3_8_h_n data n).g.val.val - 1‖) * (m : ℝ) + 1) ≤ (m - 1) * ‖(theorem_3_8_h_n data n).g.val.val - 1‖ := by
      by_cases m_eq_one: m = 1
      .
        simp [m_eq_one]
        rw [add_comm]
      .
        have my_bound := f_pos_on ‖((theorem_3_8_h_n data n).g.val.val - 1)‖  ?_ ?_ ?_ ?_ m ?_
        simp [f] at my_bound
        rw [two_mul] at my_bound
        rw [← add_sub] at my_bound
        rw [add_mul] at my_bound
        rw [← add_assoc] at my_bound
        apply sub_left_lt_of_lt_add at my_bound
        rw [← gt_iff_lt] at my_bound
        rw [← ge_iff_le]
        grw [my_bound]
        simp
        ring_nf
        . rfl
        . positivity
        .
          have val_ne := (theorem_3_8_h_n data n).g_dist_nonzero
          positivity
        .
          have val_le := (theorem_3_8_h_n data n).g_dist
          grw [val_le]
          grw [H_n_eps_lt]
          norm_num
        .
          have val_le := (theorem_3_8_h_n data n).g_dist
          grw [val_le]
          grw [H_n_eps_lt]
          norm_num
          linarith [Real.log_two_gt_d9]
        . simp
          refine ⟨by omega, ?_⟩
          grw [← ge_iff_le]
          grw [Real.log_two_gt_d9.gt]
          simp
          grw [m_lt]
          simp
          apply div_le_div₀
          . norm_num
          . norm_num
          . have ne_zero := (theorem_3_8_h_n data n).g_dist_nonzero
            positivity
          . rfl


    rw [add_comm]
    grw [S_le]
    nth_rw 2 [sub_mul]
    rw [mul_comm]
    rw [← mul_comm]
    simp
    have my_smul := norm_smul (m : ℂ) ((theorem_3_8_h_n data n).g.val.val - 1)
    simp at my_smul
    rw [← my_smul]
    conv =>
      rhs
      rhs
      lhs
      arg 1
      equals ((theorem_3_8_h_n data n).g.val.val - 1) * m =>
        rw [Matrix.smul_eq_mul_diagonal]
        rw [← Matrix.diagonal_natCast]

    ring_nf
    rfl

  . intro i hi
    grw [norm_mul_le]
    grw [norm_pow_le]
    nth_rw 2 [Matrix.l2_opNorm_def]
    grw [ContinuousLinearMap.opNorm_le_bound (M := m.choose (i + 1 + 1))]
    . simp
    .
      intro x
      simp
      rw [Matrix.toEuclideanLin_apply]
      simp
      rw [norm_smul]
      simp

  --apply_fun Norm.norm at my_pow


-- TODO: upstream to mathlib
omit h_n_eps_data in
lemma list_ofFn_drop {M: Type*} (a k: ℕ) (f: Fin (k + a) → M): (List.ofFn f).drop a = List.ofFn (fun (i: Fin k) => f ⟨a + i, by omega⟩) := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    rw [List.ofFn_congr (n := (k + a) + 1) (by linarith)]
    simp
    have list_eq := ih (fun i => f i.succ)
    rw [list_eq]
    simp
    funext b
    group

end HnEpsData
end

section
-- module Solutions.OAIQ093_PR.Unitary_Words
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Distinct words in `H_n`

`words_distinct` and the resulting cardinality bound `H_n_ball_S_card` for balls in the word
metric.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
lemma words_distinct {m : ℕ} (k: Fin m) (c : ℝ) (c_pos : 0 < c) (c_lt : c < 1 / 40)
 (data : HnData)
 (pows_i : Fin m → ℕ)
 (pows_j: Fin m → ℕ)
 (pows_i_le : ∀ i : Fin m, (pows_i i) ≤ c * (H_n_eps data.hd)⁻¹)
 (pows_j_le : ∀ i : Fin m, (pows_j i) ≤ c * (H_n_eps data.hd)⁻¹)
 (pows_lt_eq: ∀ j : Fin m, j < k → pows_i j = pows_j j)
 (pows_j_lt_k: (pows_j k) < (pows_i k)):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^(pows_i i))).prod ≠ (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^(pows_j i))).prod := by


  by_contra!

  nth_rw 2 [← List.prod_take_mul_prod_drop (i := k)] at this
  rw [← List.prod_take_mul_prod_drop (i := k)] at this
  -- TODO - generalize this and PR to mathlib
  conv at this =>
    lhs
    lhs
    arg 1
    equals List.take k (List.ofFn fun (i: Fin k) ↦ ((theorem_3_8_h_n data i).g ^ pows_i ⟨i, by omega⟩)) =>
      --clear a_k_lt pows_i_le pows_j_le pows_ne this
      ext i l
      rw [List.getElem?_take]
      rw [List.getElem?_take]
      simp
      by_cases i_lt_k: i < k
      .
        simp [i_lt_k]
        have i_lt_m: i < m := by omega
        simp [i_lt_m]
      . simp [i_lt_k]

  conv at this =>
    rhs
    lhs
    arg 1
    equals List.take k (List.ofFn fun (i: Fin k) ↦ ((theorem_3_8_h_n data i).g ^ pows_j ⟨i, by omega⟩)) =>
      --clear a_k_lt pows_i_le pows_j_le pows_ne this
      ext i l
      rw [List.getElem?_take]
      rw [List.getElem?_take]
      simp
      by_cases i_lt_k: i < k
      .
        simp [i_lt_k]
        have i_lt_m: i < m := by omega
        simp [i_lt_m]
      . simp [i_lt_k]


  conv at this =>
    lhs
    lhs
    arg 1
    arg 2
    arg 1
    intro i
    rw [pows_lt_eq _ (by
      have i_prop := i.is_lt
      exact i_prop
    )]


  rw [mul_right_inj] at this
  nth_rw 2 [List.ofFn_congr (n := m - k + k) (by
    omega
  )] at this
  rw [List.ofFn_congr (n := m - k + k) (by
    omega
  )] at this
  rw [list_ofFn_drop] at this
  rw [list_ofFn_drop] at this
  nth_rw 2 [List.ofFn_congr (n := m - k - 1 + 1) (by
    omega
  )] at this
  rw [List.ofFn_congr (n := m - k - 1 + 1) (by
    omega
  )] at this
  rw [List.ofFn_succ] at this
  rw [List.prod_cons] at this
  rw [List.ofFn_succ] at this
  rw [List.prod_cons] at this
  apply inv_mul_eq_of_eq_mul at this
  rw [← mul_assoc] at this
  simp at this
  rw [← zpow_natCast] at this
  rw [← zpow_natCast] at this
  rw [← zpow_neg] at this
  rw [← zpow_add] at this


  ring_nf at this
  have rhs_le := H_n_prod_le_k (c := c) (m := m) (k := (m - k - 1)) (a := k) (by omega) c_pos c_lt pows_j data pows_j_le
  ring_nf at rhs_le
  rw [← this] at rhs_le


  -- Fin (5)
  -- Fin (5 + 0)
  -- Fin (0 + 5)

  have lhs_ge: ‖((theorem_3_8_h_n data (k)).g ^ (-(pows_j ⟨k, by omega⟩ : ℤ) + (pows_i ⟨k, by omega⟩))).val.val * (List.ofFn fun (i: Fin (m - k - 1)) ↦ (theorem_3_8_h_n data (1 + i + k)).g ^ pows_i ⟨1 + i + k, by omega⟩).prod.val.val - 1‖ ≥ (9 / 10) * ‖(theorem_3_8_h_n data k).g.val.val - 1‖ := by
    have m_minus_k: m - k - 1 + 1 = m - k := by
      omega

    conv =>
      lhs
      arg 1
      equals ((((theorem_3_8_h_n data ↑k).g ^ (-(pows_j k : ℤ) + ↑(pows_i k)))).val.val - 1) * (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (1 + i + k)).g^(pows_i (⟨1 + i + k, by omega⟩) ))).prod + (List.ofFn (fun (i : Fin (m - k - 1)) => (theorem_3_8_h_n data (1 + i + k)).g^(pows_i (⟨1 + i + k, by omega⟩) ))).prod - 1 =>
        rw [sub_mul]
        simp


    have pows_nat: (-((pows_j k) : ℤ) + (pows_i k)) = (((-(pows_j k) : ℤ) + (pows_i k))).toNat := by
      simp
      linarith


    rw [← add_sub]
    grw [(norm_sub_le_norm_add _ _).ge]
    rw [CStarRing.norm_mul_mem_unitary]
    rw [pows_nat]
    rw [zpow_natCast]
    rw [SubmonoidClass.coe_pow]
    rw [SubmonoidClass.coe_pow]
    grw [H_n_single_pow_lower_bound]

    -- TODO : figure out why we can't use 'simp_rw' here
    conv =>
      lhs
      rhs
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      intro i
      simp only [add_comm]
      arg 1
      arg 1
      arg 2
      equals (k.val + 1) + i =>
        group

    conv =>
      lhs
      rhs
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      arg 1
      intro i
      arg 2
      arg 1
      arg 1
      equals (k.val + 1) + i =>
        group

    grw [H_n_prod_le_k (c := c)]
    . linarith
    .
      rw [add_assoc]
      rw [m_minus_k]
      simp
    . exact c_pos
    . exact c_lt
    . exact pows_i_le
    .
      linarith
    .
      conv =>
        lhs
        equals (-((pows_j k) : ℝ) + ((pows_i k) : ℝ)) =>
          rw [add_comm]
          rw [← sub_eq_add_neg]
          rw [add_comm]
          rw [← sub_eq_add_neg]
          simp
          rw [Nat.cast_sub (by linarith)]

      rw [add_comm]
      rw [← sub_eq_add_neg]
      have pow_j_ge: 0 ≤ (pows_j k : ℝ) := by
        positivity
      grw [pows_i_le]
      grw [pow_j_ge.ge]
      simp
      grw [c_lt]
      apply mul_le_mul
      . norm_num
      .
        rw [inv_le_inv₀]
        .
          have my_prop := (theorem_3_8_h_n data k).g_dist
          exact my_prop
        . apply H_n_eps_pos
        . have my_prop := (theorem_3_8_h_n data k).g_dist_nonzero
          positivity
      . simp
        exact (H_n_eps_pos data.hd).le
      . norm_num
      . simp
        have foo := H_n_eps_pos data.hd
        linarith
    . simp [-SubmonoidClass.coe_list_prod]


  rw [ge_iff_le] at lhs_ge

  have one_tenth_lt:  1 / 10 * ‖(theorem_3_8_h_n data ↑k).g.val.val - 1‖ < (9 / 10) * ‖(theorem_3_8_h_n data ↑k).g.val.val - 1‖ := by
    apply mul_lt_mul
    . norm_num
    . simp
    .
      have ne_zero := (theorem_3_8_h_n data ↑k).g_dist_nonzero
      positivity
    . norm_num


  have add_swap (a b : ℕ): 1 + a + b = 1 + b + a := by
    omega

  have add_swap_pows_i (a b: ℕ) (add_lt: 1 + a + b < m): pows_i ⟨1 + a + b, by omega⟩ = pows_i ⟨1 + b + a, by omega⟩ := by
    simp_rw [add_swap]


  grw [lhs_ge] at one_tenth_lt
  ring_nf at one_tenth_lt
  conv at rhs_le =>
    lhs
    arg 1
    lhs
    rhs
    rhs
    rhs
    arg 1
    arg 1
    intro i
    rw [add_swap_pows_i]
    lhs
    rw [add_swap]


  norm_cast at rhs_le
  norm_cast at one_tenth_lt
  grw [rhs_le] at one_tenth_lt
  simp at one_tenth_lt


omit h_n_eps_data in
lemma list_prod_pow {T: Type*} [Group T] (m: ℕ) (elems: Fin m → T) (pows: Fin m → ℕ):
  (List.ofFn (fun (i: Fin m) => (elems i)^(pows i))).prod = (List.ofFn (fun (i : Fin m) => List.replicate (pows i) (elems i))).flatten.prod := by

  induction m with
  | zero =>
    simp
  | succ m ih =>
    have prod_eq := ih (Fin.init elems) (Fin.init pows)
    rw [List.ofFn_succ']
    rw [List.ofFn_succ']
    simp
    simpa [Fin.init] using prod_eq

lemma H_n_pows_mem_ball_G {m : ℕ}
  (data : HnData) (pows : Fin m → ℕ)
  (c: ℝ)
  (pows_le : ∀ i : Fin m, (pows i) ≤ ⌊c * (H_n_eps data.hd)⁻¹⌋₊):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod.val ∈ (data.G.carrier ^ (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹)))) := by

  let replicate_pow (i: Fin m) := List.replicate (pows i) ((theorem_3_8_h_n data i).g)
  let nested_list := List.ofFn (fun (i : Fin (m)) => replicate_pow i)
  let nested_prod := List.prod_flatten (l := nested_list)
  conv at nested_prod =>
    rhs
    equals (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod =>
      simp [nested_list, replicate_pow]
      apply congr (rfl)
      ext i g
      simp


  rw [Set.mem_pow]
  -- We have an upper bound for the list, so pad out the list with '1's to reach the upper bound
  let base_list := (fun (i: Fin (nested_list.flatten.length)) => nested_list.flatten[i])
  let full_list := Fin.append base_list (fun (i: Fin (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) - nested_list.flatten.length)) => 1)

  have len_le_upper: nested_list.flatten.length ≤ (m * (Nat.floor (c * (H_n_eps data.hd)⁻¹))) := by
    simp [nested_list, replicate_pow]
    simp [Fin.sum_ofFn]
    grw [Finset.sum_le_card_nsmul (n := ⌊ (c * (H_n_eps data.hd)⁻¹)⌋₊)]
    . simp
    . intro x _
      apply pows_le


  use (fun i => full_list (i.cast (by omega)))
  .


    conv =>
      lhs
      equals (List.ofFn (fun (i: Fin ((m * (Nat.floor (c * (H_n_eps data.hd)⁻¹))))) => (full_list (i.cast (by omega))))).prod.val =>
        simp
        apply congr (rfl)
        ext i g
        simp


    simp only [full_list, base_list]
    rw [← List.ofFn_congr]
    rw [List.ofFn_fin_append]
    rw [list_prod_pow]
    conv =>
      lhs
      arg 1
      arg 1
      lhs
      equals nested_list.flatten =>
        ext i g
        simp [-List.length_flatten, List.getElem?_eq_some_iff]

    dsimp [nested_list, replicate_pow]
    rw [List.prod_append]
    . simp [-List.prod_flatten]
    . omega


set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
lemma theorem_3_8_h_n_list_prod_eq (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data m).unattach.prod = (theorem_3_8_h_n data m).g := by
  induction m with
  | zero =>
    unfold theorem_3_8_h_n_list
    simp [theorem_3_8_h_n]
  | succ a ih =>
    unfold theorem_3_8_h_n_list
    simp [theorem_3_8_h_n]
    simp [Bracket.bracket]
    rw [ih]
    conv =>
      lhs
      rhs
      rhs
      rhs
      arg 1
      arg 1
      equals List.map Inv.inv (theorem_3_8_h_n_list data a).unattach =>
        ext i g
        simp


    rw [← List.prod_inv_reverse]
    rw [ih]
    group

-- Note - this is (2^(m - 1)) in Vikman, since the list in indexed starting at 1 in the paper
set_option synthInstance.maxHeartbeats 1000000 in
lemma theorem_3_8_h_n_list_length_initial_upper_bound  (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data (m)).length ≤ (3 * (2 ^ (m))) - 2 := by
  induction m with
  | zero =>
    unfold theorem_3_8_h_n_list
    simp
  | succ a ih =>
    unfold theorem_3_8_h_n_list
    -- TODO - can grind somehow solve all of this?
    simp
    grw [ih]
    ring
    rw [Nat.sub_mul]
    ring
    zify
    rw [Nat.cast_sub]
    .
      push_cast
      ring
      rw [Nat.cast_sub]
      . push_cast
        ring
        linarith
      .
        by_cases a_eq_zero: a = 0
        .
          simp [a_eq_zero]
        .
          have a_eq_sub_succ: a = (a - 1) + 1 := by omega
          rw [a_eq_sub_succ]
          rw [Nat.pow_succ]
          rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          apply Nat.le_mul_of_pos_right
          positivity
    .
      rw [← ge_iff_le]
      grw [(Nat.one_le_pow _ _ ?_).ge]
      . norm_num
      . norm_num


-- TODO - figure out how to merge this with 'theorem_3_8_h_n_list_length_initial_upper_bound'
lemma theorem_3_8_h_n_list_length_upper_bound  (data: HnData) (m: ℕ): (theorem_3_8_h_n_list data (m)).length ≤ c' * (2 ^ m) := by
  grw [theorem_3_8_h_n_list_length_initial_upper_bound data m]
  simp [c']


omit h_n_eps_data in
lemma list_concat_unattach {T: Type*} {p: T → Prop} (l: List { x: T // p x}) (a: { x: T // p x}): (l.concat a).unattach = l.unattach.concat a.val := by
  simp


lemma H_n_pows_mem_ball_S {m : ℕ}
  (m_gt: 0 < m) (data : HnData) (pows : Fin m → ℕ)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (pows_le : ∀ i : Fin m, (pows i) ≤ ⌊c * (H_n_eps data.hd)⁻¹⌋₊):
  (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod.val ∈ Subtype.val '' (data.S ^ ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m))) := by

  rw [Set.mem_image]
  simp_rw [Set.mem_pow]
  use (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data i).g^(pows i))).prod


  -- A list with the same product as g_list, but expressed in terms of elements of S
  let g_as_s_list := (List.ofFn (fun (i: Fin m) => List.replicate (pows i) (theorem_3_8_h_n_list data i))).flatten.flatten


  have g_as_list_prod_eq_pow: g_as_s_list.unattach.prod = (List.ofFn (fun (i: Fin m) => (List.replicate (pows i) (theorem_3_8_h_n_list data i)).flatten.unattach.prod)).unattach.prod := by
    dsimp [g_as_s_list]
    clear m_gt
    induction m with
    | zero =>
      simp
    | succ m ih =>
      have prev_prod := ih (Fin.init pows) (by
        intro i
        apply pows_le
      )
      nth_rw 2 [List.ofFn_succ']
      simp only [Fin.init] at prev_prod
      conv =>
        rhs
        pattern List.ofFn _
        arg 1
        intro i
        simp


      rw [List.ofFn_succ']
      conv at prev_prod =>
        rhs
        pattern List.ofFn _
        arg 1
        intro i
        simp


      rw [list_concat_unattach]
      rw [List.prod_concat]
      rw [← prev_prod]
      simp


  have g_list_mem := H_n_pows_mem_ball_G data pows c pows_le
  rw [Set.mem_pow] at g_list_mem
  obtain ⟨g_list, g_list_prod⟩ := g_list_mem


  have lists_prod_eq: g_as_s_list.unattach.prod = (List.ofFn g_list).unattach.prod := by
    rw [g_as_list_prod_eq_pow]
    conv =>
      rhs
      unfold List.unattach
    simp only [List.map_ofFn]
    rw [Function.comp_def]
    rw [g_list_prod]
    simp
    simp_rw [theorem_3_8_h_n_list_prod_eq]
    unfold List.unattach
    simp [Function.comp_def]


  have g_as_s_list_len: g_as_s_list.length ≤ c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m) := by
    simp [g_as_s_list]
    rw [List.sum_ofFn]
    simp
    grw [Finset.sum_le_sum (g := fun i => (pows i) * c' * (2 ^ m))]
    .
      grw [Finset.sum_le_card_nsmul (n := ⌊c * (H_n_eps data.hd)⁻¹⌋₊ * c' * (2^m))]
      .
        simp
        ring
        rfl
      .
        intro i _
        grw [pows_le]
    . intro i _
      grw [theorem_3_8_h_n_list_length_upper_bound]
      ring
      grw [i.isLt]
      simp


  let padded_list := Fin.append (fun (i: Fin (g_as_s_list.length)) => g_as_s_list[i]) (fun (i: Fin (((c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m)) - g_as_s_list.length))) => ⟨1, data.S_one⟩)


  refine ⟨?_, rfl⟩
  .
    use (fun i => padded_list (i.cast (by omega)))
    conv =>
      lhs
      equals (List.ofFn (fun i => padded_list i)).unattach.prod =>
        simp
        apply congr (rfl)
        ext i g
        nth_rw 2 [List.ofFn_congr (n := (c' * ⌊c * (H_n_eps data.hd)⁻¹⌋₊ * m * 2 ^ m))]
        . simp
        . omega


    rw [List.ofFn_fin_append]
    simp
    rw [Subtype.ext_iff]
    rw [lists_prod_eq]
    conv at g_list_prod =>
      lhs
      equals (List.ofFn g_list).unattach.prod =>
        apply congr rfl
        ext i g
        simp
    rw [g_list_prod]


-- In Vikman, this is (1 + ⌊c * (H_n_eps data.hd)⁻¹⌋₊) (since the powers include the upper bound of c*ε ⁻¹)
-- However, the proof works fine with the weaker lower bound ⌊c * (H_n_eps data.hd)⁻¹⌋₊
-- so I'm using that instead (since it avoids the need to deal with different Fin values)
lemma H_n_ball_S_card {m : ℕ}
  (m_gt: 0 < m) (data : HnData)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40):
  (⌊c * (H_n_eps data.hd)⁻¹⌋₊)^m ≤  #(data.S_finite.toFinset ^ ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m))) := by


  let my_set: Finset (Fin m → Fin (⌊c * (H_n_eps data.hd)⁻¹⌋₊)) := Finset.univ
  have my_card := Finset.card_univ (α := (Fin m → Fin (⌊c * (H_n_eps data.hd)⁻¹⌋₊)))
  rw [Fintype.card_pi_const] at my_card
  conv at my_card =>
    rhs
    simp


  rw [← my_card]
  apply Finset.card_le_card_of_injOn (f := fun pows => (List.ofFn (fun (i : Fin (m)) => (theorem_3_8_h_n data (i)).g^((pows i).val))).prod)
  .
    intro pows _
    simp
    -- TODO - modify H_n_pows_mem_ball_S so that this can just be 'apply'
    have my_pows := H_n_pows_mem_ball_S m_gt data (fun i => (pows i).val) c c_pos c_lt ?_
    .
      rw [Set.mem_image] at my_pows
      obtain ⟨g, g_mem, g_eq⟩ := my_pows
      rw [← Subtype.ext_iff] at g_eq
      rw [← g_eq]
      exact g_mem
    . intro i
      simp
  .
    intro pows_i _ pows_j _
    contrapose
    intro pows_neq
    rw [funext_iff] at pows_neq
    simp at pows_neq

    have exists_minimal_k := exists_minimal_of_wellFoundedLT (fun (i: Fin m) => pows_i i ≠ pows_j i) pows_neq
    obtain ⟨k, k_minimal⟩ := exists_minimal_k
    -- TODO - figure out why this pushes a goal of 'False' if we don't use 'generalizing'
    wlog pow_j_lt_i: (pows_j k).val < (pows_i k).val generalizing pows_i pows_j

    .
      conv at k_minimal =>
        arg 1
        intro i
        rw [ne_comm]


      have words_neq := this (pows_j := pows_i) (pows_i := pows_j) (by simp) (by simp) ?_ k_minimal ?_
      .
        rw [eq_comm]
        exact words_neq
      .
        obtain ⟨x, hx⟩ := pows_neq
        use x
        exact fun a ↦ hx (id (Eq.symm a))
      .
        have k_neq := k_minimal.prop
        omega
    .
      simp at k_minimal

      have eps_pos := H_n_eps_pos data.hd

      have prods_neq := words_distinct (m := m) k c c_pos c_lt data (fun i => pows_i i) (fun i => pows_j i) ?_ ?_ ?_ ?_
      . simpa using prods_neq
      .
        intro i
        rw [← Nat.le_floor_iff]
        omega
        positivity
      . intro i
        rw [← Nat.le_floor_iff]
        omega
        positivity
      .
        intro j hk
        have foo := Minimal.not_prop_of_lt k_minimal hk
        simp at foo
        exact congrArg Fin.val foo
      .
        simpa using pow_j_lt_i


end HnEpsData
end

section
-- module Solutions.OAIQ093_PR.Unitary_CentralTrivial
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The centrally trivial case

`H_n_contradiction` and `central_trivial_virtually_abelian`.
-/


open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative


namespace HnEpsData

variable [h_n_eps_data: HnEpsData]

lemma H_n_contradiction_oai (data : HnData)
  (c: ℝ)
  (c_pos: 0 < c)
  (c_lt: c < 1 / 40)
  (c_mul_pos: 1 ≤ c * (H_n_eps data.hd)⁻¹)
  (eps_div_lt: (H_n_eps data.hd) < c / (Real.exp (4 + ↑data.S_poly_deg * Real.log 2) + 1))
  : False := by


  let m: ℕ := max (max (⌈1 + |(↑data.S_poly_deg - Real.log ↑data.S_poly_const)|⌉₊) (1 + ⌈((Real.log ↑data.S_poly_const + ↑data.S_poly_deg * Real.log (↑c' * ↑⌊c * (H_n_eps data.hd)⁻¹⌋₊)) /
    (Real.log ↑⌊c * (H_n_eps data.hd)⁻¹⌋₊ - ↑data.S_poly_deg * Real.log 2 - 4))⌉₊)) (1 + ⌈Real.exp ↑data.S_poly_deg⌉₊)

  have m_gt: 0 < m := by
    simp [m]
  have ne_zero_of_pos (r: ℝ): 0 < r → r ≠ 0 := by
    intro r_pos r_eq
    rw [r_eq] at r_pos
    linarith

  have upper_bound := data.S_poly ( c' * (Nat.floor (c * (H_n_eps data.hd)⁻¹)) * m * (2 ^ m)) (by
    simp [c']
    rw [Nat.one_le_iff_ne_zero]
    apply Nat.mul_ne_zero
    . apply Nat.mul_ne_zero
      . apply Nat.mul_ne_zero
        . simp
        .
          simp
          apply c_mul_pos
      . omega
    . simp
  )
  have lower_bound := H_n_ball_S_card m_gt data c c_pos c_lt
  have ineq := le_trans lower_bound upper_bound
  rify at ineq
  rw [← Real.log_le_log_iff] at ineq
  .
    simp at ineq
    rw [Real.log_mul] at ineq
    .
      simp at ineq
      rw [Real.log_mul] at ineq
      simp at ineq
      rw [mul_add] at ineq
      rw [← add_assoc] at ineq
      rw [← tsub_le_iff_right] at ineq
      rw [add_comm] at ineq
      rw [← mul_assoc] at ineq
      nth_rw 4 [mul_comm] at ineq
      rw [mul_assoc] at ineq
      rw [← mul_sub] at ineq

      have reverse_ineq: swap_le ineq := by
        unfold swap_le

        have log_m_gt:  ↑data.S_poly_deg < Real.log ↑m := by
          rw [← Real.exp_lt_exp]
          rw [Real.exp_log]
          .
            unfold m
            apply Nat.lt_of_ceil_lt
            apply lt_max_of_lt_right
            simp
          . simp
            omega


        rw [Real.log_mul]
        .
          rw [mul_add]
          rw [add_comm]
          rw [← add_assoc]
          nth_grw 2 [log_m_gt]
          rw [← pow_two]
          nth_grw 3 [Real.log_le_rpow_div (ε := (1 / 2))]
          simp
          rw [mul_pow]
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul]
          simp
          norm_num
          rw [← lt_tsub_iff_right]
          rw [← mul_sub]
          rw [← div_lt_iff₀]
          .
            dsimp [m]
            apply Nat.lt_of_ceil_lt
            apply lt_max_of_lt_left
            apply lt_max_of_lt_right
            simp
          .
            simp
            rw [lt_tsub_iff_right]
            rw [← Real.exp_lt_exp]
            rw [Real.exp_log]
            .
              rw [← gt_iff_lt]
              grw [(Nat.sub_one_lt_floor _).gt]
              rw [gt_iff_lt]
              rw [lt_tsub_iff_right]
              field_simp
              rw [lt_div_iff₀']
              rw [← lt_div_iff₀]
              .
                exact eps_div_lt
              . positivity
              . apply H_n_eps_pos
            .
              simp
              rw [Nat.floor_pos]
              exact c_mul_pos
          . simp
          . simp
          . simp
        .
          simp
          refine ⟨by simp [c'], ?_⟩
          exact c_mul_pos
        . simp
          omega

      unfold swap_le at reverse_ineq
      . linarith
      . have m_ne_zero: m ≠ 0 := by
          omega
        simp [c', m_ne_zero]
        exact c_mul_pos

      . simp


    .
      exact Nat.cast_ne_zero.mpr (id (Ne.symm data.S_poly_const_pos))
    .


      apply ne_zero_of_pos
      apply pow_pos
      simp
      apply mul_pos
      .
        simp [c']
        rw [Nat.floor_pos]
        exact c_mul_pos
      . exact Nat.cast_pos'.mpr m_gt
  .
    norm_cast
    apply Nat.pow_pos
    rw [Nat.floor_pos]
    exact c_mul_pos
  .
    apply mul_pos
    . simp
      exact Nat.zero_lt_of_ne_zero (id (Ne.symm data.S_poly_const_pos))
    .
      apply pow_pos
      simp [c']
      apply mul_pos
      . simp
        rw [Nat.floor_pos]
        exact c_mul_pos
      . exact Nat.cast_pos'.mpr m_gt


open scoped Pointwise

-- TODO - figure out why this causes a diamond when we use 'open Classical'


end HnEpsData

-- TODO: upstream to mathlib


-- Helper for theorem 3.8
end

theorem solution : type_of% @HnEpsData.H_n_contradiction_oai := @HnEpsData.H_n_contradiction_oai
