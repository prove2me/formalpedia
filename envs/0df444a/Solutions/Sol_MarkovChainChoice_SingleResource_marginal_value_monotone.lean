-- Prove2me | solution 1 for MarkovChainChoice.SingleResource.marginal_value_monotone
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:15:59.829986+00:00
-- url     : https://prove2.me/submissions/553d679f-9c09-43bf-ac63-a8e2e8d03cc7

import Definitions.Def_MarkovChainChoice_Shared_Balance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Definitions.Def_MarkovChainChoice_SingleResource_ValueFunction
import Mathlib.Algebra.Order.Group.Finset
open Finset Matrix MarkovChainChoice.Shared

private theorem balance_exists_unique {n : ℕ} (M : Model n) (S : Finset (Fin n)) :
    ∃ P R : Fin n → ℝ, IsBalance M S P R ∧ (∀ j, 0 ≤ P j) ∧ (∀ j, 0 ≤ R j) ∧
      ∀ P' R', IsBalance M S P' R' → P' = P ∧ R' = R := by
  classical
  let T : Matrix (Fin n) (Fin n) ℝ := fun j i => if i ∈ S then 0 else M.rho i j
  let A := (1 : Matrix (Fin n) (Fin n) ℝ) - T
  have hdet : A.det ≠ 0 := by
    apply det_ne_zero_of_sum_col_lt_diag
    intro k
    by_cases hk : k ∈ S
    · have he : ∀ j, A j k = if j = k then 1 else 0 := by
        intro j
        change (if j = k then 1 else 0) - (if k ∈ S then 0 else M.rho k j) = _
        simp [hk]
      have hsum : ∑ j ∈ univ.erase k, ‖A j k‖ = 0 := by
        apply sum_eq_zero
        intro j hj
        simp [he,(mem_erase.mp hj).1]
      rw [hsum,he]
      norm_num
    · have hrho : M.rho k k < 1 := (single_le_sum (fun i hi => M.rho_nonneg k i) (mem_univ k)).trans_lt (M.rho_row_lt_one k)
      have he : ∑ j ∈ univ.erase k, ‖A j k‖ = ∑ j ∈ univ.erase k, M.rho k j := by
        apply sum_congr rfl
        intro j hj
        have hjk : j ≠ k := (mem_erase.mp hj).1
        change ‖(if j = k then 1 else 0) - (if k ∈ S then 0 else M.rho k j)‖ = _
        simp [hk,hjk,Real.norm_eq_abs,abs_of_nonneg (M.rho_nonneg k j)]
      rw [he]
      have hd : ‖A k k‖ = 1-M.rho k k := by
        change ‖(if k = k then (1:ℝ) else 0) - (if k ∈ S then 0 else M.rho k k)‖ = _
        simp [hk,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hrho)]
      rw [hd, sum_erase_eq_sub (mem_univ k)]
      linarith [M.rho_row_lt_one k]
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨z,hz⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) M.lam
  have hzeq : ∀ j, z j = M.lam j + ∑ i, (if i ∈ S then 0 else M.rho i j) * z i := by
    intro j
    have h := congrFun hz j
    change ((1 : Matrix (Fin n) (Fin n) ℝ) - T).mulVec z j = M.lam j at h
    rw [Matrix.sub_mulVec,Matrix.one_mulVec] at h
    change z j - ∑ i, (if i ∈ S then 0 else M.rho i j)*z i = M.lam j at h
    linarith
  have hz0 : ∀ j, 0 ≤ z j := by
    by_contra hn
    push_neg at hn
    obtain ⟨j,hj⟩ := hn
    let J := univ.filter (fun i => z i < 0)
    have hjJ : j ∈ J := by simp [J,hj]
    have hlam : 0 < ∑ j ∈ J, M.lam j := sum_pos' (fun i hi => (M.lam_pos i).le) ⟨j,hjJ,M.lam_pos j⟩
    have hflow : ∑ j ∈ J, z j ≤ ∑ j ∈ J, ∑ i, (if i ∈ S then 0 else M.rho i j)*z i := by
      rw [sum_comm]
      calc
        _ = ∑ i, if i ∈ J then z i else 0 := by simp [sum_filter,J]
        _ ≤ _ := by
          apply sum_le_sum
          intro i hi
          have hcoef0 : 0 ≤ ∑ j ∈ J, M.rho i j := sum_nonneg (fun j hj => M.rho_nonneg i j)
          have hcoef1 : ∑ j ∈ J, M.rho i j ≤ 1 :=
            (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j hj hjJ => M.rho_nonneg i j)).trans (M.rho_row_lt_one i).le
          by_cases hiS : i ∈ S
          · simp only [hiS,if_pos,zero_mul,sum_const_zero]
            by_cases hiJ : i ∈ J
            · simp only [if_pos hiJ]
              exact (mem_filter.mp hiJ).2.le
            · simp [hiJ]
          · simp only [if_neg hiS,← sum_mul]
            by_cases hiJ : i ∈ J
            · simp only [if_pos hiJ]
              have hi0 : z i < 0 := (mem_filter.mp hiJ).2
              nlinarith
            · simp only [if_neg hiJ]
              have hi0 : 0 ≤ z i := by simpa [J] using hiJ
              exact mul_nonneg hcoef0 hi0
    have he := sum_congr rfl (fun i (hi : i ∈ J) => hzeq i)
    rw [sum_add_distrib] at he
    linarith
  let P : Fin n → ℝ := fun j => if j ∈ S then z j else 0
  let R : Fin n → ℝ := fun j => if j ∈ S then 0 else z j
  have hPR : ∀ j, P j + R j = z j := by intro j; dsimp [P,R]; split_ifs <;> ring
  have hbal : IsBalance M S P R := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      rw [hPR,hzeq]
      congr 1
      apply sum_congr rfl
      intro i hi
      by_cases hiS : i ∈ S <;> simp [R,hiS]
    · intro j hj; simp [P,hj]
    · intro j hj; simp [R,hj]
  refine ⟨P,R,hbal,?_,?_,?_⟩
  · intro j; dsimp [P]; split_ifs; exact hz0 j; norm_num
  · intro j; dsimp [R]; split_ifs; norm_num; exact hz0 j
  · intro P' R' hbal'
    have hz' : A.mulVec (P'+R') = M.lam := by
      ext j
      rw [show A=1-T from rfl,Matrix.sub_mulVec,Matrix.one_mulVec]
      change P' j+R' j - ∑ i, (if i ∈ S then 0 else M.rho i j)*(P' i+R' i) = M.lam j
      have hsum : (∑ i, (if i ∈ S then 0 else M.rho i j)*(P' i+R' i)) = ∑ i, M.rho i j*R' i := by
        apply sum_congr rfl
        intro i hi
        by_cases hiS : i ∈ S
        · simp [hiS,hbal'.2.2 i hiS]
        · simp [hiS,hbal'.2.1 i hiS]
      rw [hsum]
      linarith [hbal'.1 j]
    have heq : P'+R' = z := (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (hz'.trans hz.symm)
    constructor
    · funext j
      have h := congrFun heq j
      by_cases hj : j ∈ S
      · simpa [P,hj,hbal'.2.2 j hj] using h
      · simp [P,hj,hbal'.2.1 j hj]
    · funext j
      have h := congrFun heq j
      by_cases hj : j ∈ S
      · simp [R,hj,hbal'.2.2 j hj]
      · simpa [R,hj,hbal'.2.1 j hj] using h

private theorem balance_unique {n : ℕ} (M : Model n) (S : Finset (Fin n)) :
    IsBalance M S (purchase M S) (visitNot M S) ∧
    (∀ j, 0 ≤ purchase M S j) ∧ (∀ j, 0 ≤ visitNot M S j) ∧
    ∀ P R : Fin n → ℝ, IsBalance M S P R → P = purchase M S ∧ R = visitNot M S := by
  obtain ⟨P,R,hbal,hP,hR,huniq⟩ := balance_exists_unique M S
  have hchosen : IsBalance M S (purchase M S) (visitNot M S) := by
    unfold purchase visitNot balanceSol
    exact Classical.epsilon_spec (p := fun PR : (Fin n → ℝ) × (Fin n → ℝ) => IsBalance M S PR.1 PR.2) ⟨(P,R),hbal⟩
  obtain ⟨hp,hr⟩ := huniq _ _ hchosen
  rw [hp,hr]
  exact ⟨hbal,hP,hR,huniq⟩

open MarkovChainChoice.SingleResource
private theorem weighted_balance {n : ℕ} (M : Model n) (P R v : Fin n → ℝ)
    (h : ∀ j, P j+R j = M.lam j+∑ i, M.rho i j*R i) :
    (∑ j, M.lam j*v j) = (∑ j, P j*v j) + ∑ i, R i*(v i-∑ j,M.rho i j*v j) := by
  have hflow : (∑ j, (∑ i, M.rho i j*R i)*v j) = ∑ i, R i*(∑ j,M.rho i j*v j) := by
    simp only [sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  have he : (∑ j, P j*v j)+(∑ j,R j*v j) =
      (∑ j,M.lam j*v j)+(∑ j,(∑ i,M.rho i j*R i)*v j) := by
    rw [← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [← add_mul, h j, add_mul]
  rw [hflow] at he
  simp only [mul_sub,sum_sub_distrib]
  linarith


private theorem purchase_sum_le {n : ℕ} (M : Model n) (S : Finset (Fin n))
    (hlam : ∑ j,M.lam j ≤ 1) : (∑ j,purchase M S j) ≤ 1 := by
  have he := weighted_balance M (purchase M S) (visitNot M S) (fun _ => 1) (balance_unique M S).1.1
  simp only [mul_one] at he
  have hz : 0 ≤ ∑ i,visitNot M S i*(1-∑ j,M.rho i j) :=
    sum_nonneg (fun i _ => mul_nonneg ((balance_unique M S).2.2.1 i) (sub_nonneg.mpr (M.rho_row_lt_one i).le))
  linarith

private noncomputable def gain {n : ℕ} (M : Model n) (r : Fin n → ℝ) (d : ℝ) : ℝ :=
  (univ : Finset (Finset (Fin n))).sup' univ_nonempty (fun S => ∑ j,purchase M S j*(r j-d))

private theorem gain_nonneg {n : ℕ} (M : Model n) (r : Fin n → ℝ) (d : ℝ) : 0 ≤ gain M r d := by
  have hempty (j : Fin n) : purchase M ∅ j=0 := (balance_unique M ∅).1.2.1 j (by simp)
  have he := le_sup' (fun S : Finset (Fin n) => ∑ j,purchase M S j*(r j-d)) (mem_univ (∅ : Finset (Fin n)))
  simpa only [gain,hempty,zero_mul,sum_const_zero] using he

private theorem gain_antitone {n : ℕ} (M : Model n) (r : Fin n → ℝ) : Antitone (gain M r) := by
  intro a b hab
  apply sup'_le
  intro S hS
  exact (sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (by linarith) ((balance_unique M S).2.1 j))).trans
    (le_sup' (fun U : Finset (Fin n) => ∑ j,purchase M U j*(r j-a)) hS)

private theorem gain_shift_monotone {n : ℕ} (M : Model n) (r : Fin n → ℝ)
    (hlam : ∑ j,M.lam j ≤ 1) : Monotone (fun d => d+gain M r d) := by
  intro a b hab
  have hbound : gain M r a ≤ gain M r b+(b-a) := by
    apply sup'_le
    intro S hS
    calc
      (∑ j,purchase M S j*(r j-a))
          = (∑ j,purchase M S j*(r j-b))+(∑ j,purchase M S j)*(b-a) := by
        simp only [mul_sub,sum_sub_distrib,← sum_mul];ring
      _ ≤ gain M r b+1*(b-a) := add_le_add
        (le_sup' (fun U : Finset (Fin n) => ∑ j,purchase M U j*(r j-b)) hS)
        (mul_le_mul_of_nonneg_right (purchase_sum_le M S hlam) (sub_nonneg.mpr hab))
      _ = _ := by ring
  linarith

private noncomputable def marginal {n : ℕ} (M : Model n) (r : Fin n → ℝ) (k x : ℕ) : ℝ :=
  valueToGo M r k (x+1)-valueToGo M r k x

private theorem value_zero {n : ℕ} (M : Model n) (r : Fin n → ℝ) (k : ℕ) : valueToGo M r k 0=0 := by
  cases k <;> simp [valueToGo]

private theorem value_step {n : ℕ} (M : Model n) (r : Fin n → ℝ) (k x : ℕ) :
    valueToGo M r (k+1) (x+1)=gain M r (marginal M r k x)+valueToGo M r k (x+1) := by
  rw [valueToGo]
  congr 1
  apply sup'_congr univ_nonempty rfl
  intro S hS
  apply sum_congr rfl
  intro j hj
  dsimp [marginal]
  ring

private theorem marginal_step_zero {n : ℕ} (M : Model n) (r : Fin n → ℝ) (k : ℕ) :
    marginal M r (k+1) 0=marginal M r k 0+gain M r (marginal M r k 0) := by
  unfold marginal
  rw [value_step]
  simp only [value_zero,sub_zero]
  dsimp [marginal]
  rw [value_zero]
  ring

private theorem marginal_step_succ {n : ℕ} (M : Model n) (r : Fin n → ℝ) (k x : ℕ) :
    marginal M r (k+1) (x+1)=marginal M r k (x+1)+gain M r (marginal M r k (x+1))-gain M r (marginal M r k x) := by
  unfold marginal
  rw [value_step,value_step]
  dsimp [marginal]
  ring

private theorem marginal_concave {n : ℕ} (M : Model n) (r : Fin n → ℝ)
    (hlam : ∑ j,M.lam j ≤ 1) : ∀ k x,marginal M r k (x+1) ≤ marginal M r k x := by
  intro k
  induction k with
  | zero => intro x;simp [marginal,valueToGo]
  | succ k ih =>
    intro x
    cases x with
    | zero =>
      rw [marginal_step_succ,marginal_step_zero]
      have h := gain_shift_monotone M r hlam (ih 0)
      have hg := gain_nonneg M r (marginal M r k 0)
      linarith
    | succ x =>
      rw [marginal_step_succ,marginal_step_succ]
      have h := gain_shift_monotone M r hlam (ih (x+1))
      have hg := gain_antitone M r (ih x)
      linarith

private theorem marginal_time {n : ℕ} (M : Model n) (r : Fin n → ℝ)
    (hlam : ∑ j,M.lam j ≤ 1) (k x : ℕ) : marginal M r k x ≤ marginal M r (k+1) x := by
  cases x with
  | zero => rw [marginal_step_zero];linarith [gain_nonneg M r (marginal M r k 0)]
  | succ x =>
    rw [marginal_step_succ]
    have h:=gain_antitone M r (marginal_concave M r hlam k x)
    linarith

private theorem delta_eq_marginal {n : ℕ} (M : Model n) (r : Fin n → ℝ) (T t x : ℕ)
    (hx : 1 ≤ x) : deltaValue M r T t x=marginal M r (T+1-t) (x-1) := by
  unfold deltaValue value marginal
  rw [Nat.sub_add_cancel hx]

theorem solution {n : ℕ} (M : Model n) (r : Fin n → ℝ) (T : ℕ)
    (hlam : ∑ j,M.lam j ≤ 1) :
    (∀ t x,1 ≤ t → t ≤ T+1 → 2 ≤ x → deltaValue M r T t x ≤ deltaValue M r T t (x-1)) ∧
      ∀ t x,1 ≤ t → t ≤ T → 1 ≤ x → deltaValue M r T (t+1) x ≤ deltaValue M r T t x := by
  constructor
  · intro t x ht htT hx
    rw [delta_eq_marginal M r T t x (by omega),delta_eq_marginal M r T t (x-1) (by omega)]
    have he : x-1=(x-1-1)+1 := by omega
    conv_lhs => rw [he]
    exact marginal_concave M r hlam _ _
  · intro t x ht htT hx
    rw [delta_eq_marginal M r T (t+1) x hx,delta_eq_marginal M r T t x hx]
    have he : T+1-t=(T+1-(t+1))+1 := by omega
    rw [he]
    exact marginal_time M r hlam _ _
