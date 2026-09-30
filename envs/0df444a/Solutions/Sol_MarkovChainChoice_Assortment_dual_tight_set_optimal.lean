-- Prove2me | solution 1 for MarkovChainChoice.Assortment.dual_tight_set_optimal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:42:55.509183+00:00
-- url     : https://prove2.me/submissions/052feaae-6980-4807-bf20-ee0439711220

import Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms
import Definitions.Def_MarkovChainChoice_Assortment_Model
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
open Finset Matrix MarkovChainChoice.Assortment

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

private theorem dual_tight {n : ℕ} (M : Model n) (r v : Fin n → ℝ)
    (hv : IsDualOptimal M r v) :
    ∀ j, v j = r j ∨ v j = ∑ i, M.rho j i * v i := by
  classical
  intro j
  by_contra h
  push_neg at h
  have hr : r j < v j := lt_of_le_of_ne (hv.1 j).1 h.1.symm
  have hs : (∑ i, M.rho j i * v i) < v j := lt_of_le_of_ne (hv.1 j).2 h.2.symm
  let δ := min (v j-r j) (v j-∑ i, M.rho j i*v i)/2
  have hδ : 0 < δ := div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hδr : δ ≤ v j-r j := by
    have := min_le_left (v j-r j) (v j-∑ i, M.rho j i*v i)
    dsimp [δ] at *
    linarith [lt_min (sub_pos.mpr hr) (sub_pos.mpr hs)]
  have hδs : δ ≤ v j-∑ i, M.rho j i*v i := by
    have := min_le_right (v j-r j) (v j-∑ i, M.rho j i*v i)
    dsimp [δ] at *
    linarith [lt_min (sub_pos.mpr hr) (sub_pos.mpr hs)]
  let w := fun i => if i = j then v i-δ else v i
  have hwle : ∀ i, w i ≤ v i := by intro i; dsimp [w]; split_ifs <;> linarith
  have hw : DualFeasible M r w := by
    intro i
    have hrow : (∑ k, M.rho i k*w k) ≤ ∑ k, M.rho i k*v k :=
      sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hwle k) (M.rho_nonneg i k))
    by_cases hi : i = j
    · subst i
      simp only [w,if_pos rfl]
      constructor <;> linarith
    · simp only [w,if_neg hi]
      exact ⟨(hv.1 i).1,hrow.trans (hv.1 i).2⟩
  have he : (∑ i, M.lam i*w i) = (∑ i, M.lam i*v i) - M.lam j*δ := by
    have ht : ∀ i, M.lam i*w i = M.lam i*v i - if i=j then M.lam j*δ else 0 := by
      intro i
      by_cases hi : i=j
      · subst i; simp [w];ring
      · simp [w,hi]
    simp_rw [ht]
    rw [sum_sub_distrib]
    simp
  have hopt := hv.2 w hw
  rw [he] at hopt
  nlinarith [mul_pos (M.lam_pos j) hδ]

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

private theorem weak_duality {n : ℕ} (M : Model n) (r v P R : Fin n → ℝ)
    (hv : DualFeasible M r v) (hP : ∀ j,0 ≤ P j) (hR : ∀ j,0 ≤ R j)
    (hb : ∀ j,P j+R j=M.lam j+∑ i,M.rho i j*R i) :
    (∑ j,P j*r j) ≤ ∑ j,M.lam j*v j := by
  rw [weighted_balance M P R v hb]
  have hp : (∑ j,P j*r j) ≤ ∑ j,P j*v j :=
    sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hv j).1 (hP j))
  have hz : 0 ≤ ∑ i,R i*(v i-∑ j,M.rho i j*v j) :=
    sum_nonneg (fun i hi => mul_nonneg (hR i) (sub_nonneg.mpr (hv i).2))
  linarith

private theorem tight_value {n : ℕ} (M : Model n) (r v : Fin n → ℝ)
    (hv : IsDualOptimal M r v) :
    revenue M r (univ.filter (fun j => v j=r j)) = ∑ j,M.lam j*v j := by
  classical
  let S := univ.filter (fun j => v j=r j)
  have hb := balance_unique M S
  have ht := dual_tight M r v hv
  have hp : (∑ j,purchase M S j*v j) = ∑ j,purchase M S j*r j := by
    apply sum_congr rfl
    intro j hj
    by_cases hjS : j ∈ S
    · rw [(mem_filter.mp hjS).2]
    · simp [hb.1.2.1 j hjS]
  have hz : (∑ i,visitNot M S i*(v i-∑ j,M.rho i j*v j)) = 0 := by
    apply sum_eq_zero
    intro i hi
    by_cases hiS : i ∈ S
    · rw [hb.1.2.2 i hiS,zero_mul]
    · have hir : v i ≠ r i := by simpa [S] using hiS
      rw [(ht i).resolve_left hir,sub_self,mul_zero]
  rw [weighted_balance M (purchase M S) (visitNot M S) v hb.1.1,hp,hz,add_zero]
  rfl

theorem solution {n : ℕ} (M : Model n) (r v : Fin n → ℝ)
    (hv : IsDualOptimal M r v) :
    IsOptimalAssortment M r (Finset.univ.filter (fun j => v j = r j)) := by
  intro S
  rw [tight_value M r v hv]
  have hb := balance_unique M S
  exact weak_duality M r v _ _ hv.1 hb.2.1 hb.2.2.1 hb.1.1
