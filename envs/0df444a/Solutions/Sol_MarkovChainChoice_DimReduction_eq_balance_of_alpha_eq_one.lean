-- Prove2me | solution 1 for MarkovChainChoice.DimReduction.eq_balance_of_alpha_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:50:57.720168+00:00
-- url     : https://prove2.me/submissions/20fbd411-5826-4e4f-abdb-c7d008d749f6

import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
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

open MarkovChainChoice.DimReduction

private theorem incoming_comparison {n : ℕ} (M : Model n) (d : Fin n → ℝ)
    (hd : ∀ j, 0 < d j → d j ≤ ∑ i,M.rho i j*d i) : ∀ j,d j ≤ 0 := by
  classical
  intro j
  by_contra hj
  have hj0 : 0 < d j := by linarith
  let J := univ.filter (fun i => 0 < d i)
  have hjJ : j ∈ J := by simp [J,hj0]
  have hsum : (∑ j ∈ J,d j) ≤ ∑ j ∈ J,∑ i,M.rho i j*d i :=
    sum_le_sum (fun j hj => hd j (mem_filter.mp hj).2)
  have hupper : (∑ j ∈ J,∑ i,M.rho i j*d i) ≤ ∑ i ∈ J,(∑ j,M.rho i j)*d i := by
    rw [sum_comm]
    calc
      _ ≤ ∑ i, if i ∈ J then (∑ j,M.rho i j)*d i else 0 := by
        apply sum_le_sum
        intro i hi
        rw [← sum_mul]
        have hcoef0 : 0 ≤ ∑ j ∈ J,M.rho i j := sum_nonneg (fun j hj => M.rho_nonneg i j)
        by_cases hiJ : i ∈ J
        · simp only [if_pos hiJ]
          exact mul_le_mul_of_nonneg_right
            (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j hj hjJ => M.rho_nonneg i j))
            (mem_filter.mp hiJ).2.le
        · simp only [if_neg hiJ]
          have hi0 : d i ≤ 0 := by simpa [J] using hiJ
          exact mul_nonpos_of_nonneg_of_nonpos hcoef0 hi0
      _ = _ := by simp [sum_filter,J]
  have hstrict : (∑ i ∈ J,(∑ j,M.rho i j)*d i) < ∑ i ∈ J,d i := by
    apply sum_lt_sum
    · intro i hi
      have hi0 := (mem_filter.mp hi).2
      nlinarith [M.rho_row_lt_one i]
    · refine ⟨j,hjJ,?_⟩
      nlinarith [M.rho_row_lt_one j]
  linarith

private theorem visit_le {n : ℕ} (M : Model n) :
    ∀ p ∈ H M, ∀ j, visitNot M (drSupp p.1) j ≤ p.2 j := by
  classical
  intro p hp j
  let S := drSupp p.1
  have hb := balance_unique M S
  have hd : ∀ i,visitNot M S i-p.2 i ≤ 0 := by
    apply incoming_comparison M
    intro i hi
    have hiS : i ∉ S := by
      intro hiS
      rw [hb.1.2.2 i hiS] at hi
      linarith [hp.2.1 i]
    have hP : purchase M S i=0 := hb.1.2.1 i hiS
    have hx : p.1 i=0 := by
      have hnot : ¬ 0 < p.1 i := by simpa [S,drSupp] using hiS
      linarith [hp.1 i]
    have he1 := hb.1.1 i
    have he2 := hp.2.2 i
    rw [hP,zero_add] at he1
    rw [hx,zero_add] at he2
    simp only [mul_sub,sum_sub_distrib]
    linarith
  exact sub_nonpos.mp (hd j)

private theorem total_mass {n : ℕ} (M : Model n) (P R : Fin n → ℝ)
    (hb : ∀ j,P j+R j=M.lam j+∑ i,M.rho i j*R i) :
    (∑ j, (P j + (1 - (∑ i, M.rho j i)) * R j)) = ∑ j,M.lam j := by
  have he : (∑ j, (P j + R j)) = ∑ j, (M.lam j + ∑ i, M.rho i j * R i) :=
    sum_congr rfl (fun j hj => hb j)
  simp only [sum_add_distrib] at he
  have hflow : (∑ j,∑ i,M.rho i j*R i) = ∑ i,(∑ j,M.rho i j)*R i := by
    rw [sum_comm]
    simp only [sum_mul]
  rw [hflow] at he
  simp only [sub_mul,one_mul,sum_add_distrib,sum_sub_distrib]
  linarith

private theorem H_order_eq {n : ℕ} (M : Model n) (p q : (Fin n → ℝ) × (Fin n → ℝ))
    (hp : p ∈ H M) (hq : q ∈ H M) (hx : ∀ j,q.1 j ≤ p.1 j) (hz : ∀ j,q.2 j ≤ p.2 j) : p=q := by
  have hsum : (∑ j, ((p.1 j - q.1 j) + (1 - (∑ i, M.rho j i)) * (p.2 j - q.2 j)))=0 := by
    have he1 := total_mass M p.1 p.2 hp.2.2
    have he2 := total_mass M q.1 q.2 hq.2.2
    simp only [mul_sub,sum_add_distrib,sum_sub_distrib] at *
    linarith
  have hn : ∀ j,0 ≤ (p.1 j-q.1 j)+(1-∑ i,M.rho j i)*(p.2 j-q.2 j) := by
    intro j
    exact add_nonneg (sub_nonneg.mpr (hx j))
      (mul_nonneg (sub_nonneg.mpr (M.rho_row_lt_one j).le) (sub_nonneg.mpr (hz j)))
  have he := (sum_eq_zero_iff_of_nonneg (fun j hj => hn j)).mp hsum
  have hcoord : ∀ j,p.1 j=q.1 j ∧ p.2 j=q.2 j := by
    intro j
    have heq := he j (mem_univ _)
    have hmul : 0 ≤ (1-∑ i,M.rho j i)*(p.2 j-q.2 j) :=
      mul_nonneg (sub_nonneg.mpr (M.rho_row_lt_one j).le) (sub_nonneg.mpr (hz j))
    have hprod : (1-∑ i,M.rho j i)*(p.2 j-q.2 j)=0 := by linarith [hx j]
    have hz0 : p.2 j-q.2 j=0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (sub_pos.mpr (M.rho_row_lt_one j)))
    constructor <;> linarith
  exact Prod.ext (funext (fun j => (hcoord j).1)) (funext (fun j => (hcoord j).2))

private theorem purchase_pos {n : ℕ} (M : Model n) (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) :
    0 < purchase M S j := by
  have hb := balance_unique M S
  have he := hb.1.1 j
  rw [hb.1.2.2 j hj,add_zero] at he
  have hn : 0 ≤ ∑ i,M.rho i j*visitNot M S i :=
    sum_nonneg (fun i hi => mul_nonneg (M.rho_nonneg i j) (hb.2.2.1 i))
  linarith [M.lam_pos j]

private theorem alpha_le_ratio {n : ℕ} (M : Model n) (x : Fin n → ℝ) (j : Fin n) (hj : j ∈ drSupp x) :
    drAlpha M x ≤ x j/purchase M (drSupp x) j := by
  classical
  have hs : (drSupp x).Nonempty := ⟨j,hj⟩
  simp only [drAlpha,dif_pos hs]
  exact inf'_le _ hj

private theorem purchase_le_of_one_le_alpha {n : ℕ} (M : Model n)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : p ∈ H M) (ha : 1 ≤ drAlpha M p.1) :
    ∀ j,purchase M (drSupp p.1) j ≤ p.1 j := by
  classical
  intro j
  by_cases hj : j ∈ drSupp p.1
  · have hpos := purchase_pos M (drSupp p.1) j hj
    have hratio := alpha_le_ratio M p.1 j hj
    have h := (le_div_iff₀ hpos).mp (ha.trans hratio)
    simpa using h
  · rw [(balance_unique M (drSupp p.1)).1.2.1 j hj]
    exact hp.1 j

theorem solution {n : ℕ} (M : Model n) :
    ∀ p ∈ H M, (drSupp p.1).Nonempty → drAlpha M p.1=1 →
      p=(purchase M (drSupp p.1),visitNot M (drSupp p.1)) := by
  intro p hp hs ha
  have hb := balance_unique M (drSupp p.1)
  exact H_order_eq M p _ hp ⟨hb.2.1,hb.2.2.1,hb.1.1⟩
    (purchase_le_of_one_le_alpha M p hp ha.ge) (visit_le M p hp)
