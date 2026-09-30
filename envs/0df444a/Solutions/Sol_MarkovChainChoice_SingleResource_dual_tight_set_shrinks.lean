-- Prove2me | solution 1 for MarkovChainChoice.SingleResource.dual_tight_set_shrinks
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:11:18.273642+00:00
-- url     : https://prove2.me/submissions/240e1517-271a-4344-b89a-1110ef4d3282

import Definitions.Def_MarkovChainChoice_SingleResource_Assortment
import Mathlib.Tactic
open Finset MarkovChainChoice.Shared MarkovChainChoice.SingleResource

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

private theorem fixed_le_feasible {n : ℕ} (M : Model n) (r u v : Fin n → ℝ)
    (hu : ∀ j, max (r j) (∑ i,M.rho j i*u i)=u j) (hv : DualFeasible M r v) :
    ∀ j,u j ≤ v j := by
  classical
  intro j
  by_contra hj
  have hjpos : 0 < u j-v j := by linarith
  haveI : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨k,hk,hmax⟩ := exists_max_image univ (fun i => u i-v i) univ_nonempty
  have hpos : 0 < u k-v k := hjpos.trans_le (hmax j (mem_univ _))
  have hr : r k < u k := by linarith [(hv k).1]
  have he : u k=∑ i,M.rho k i*u i := by
    have h := hu k
    rcases le_total (r k) (∑ i,M.rho k i*u i) with ht | ht
    · simpa [max_eq_right ht] using h.symm
    · rw [max_eq_left ht] at h
      linarith
  have hdiff : u k-v k ≤ (∑ i,M.rho k i)*(u k-v k) := by
    calc
      _ ≤ (∑ i,M.rho k i*u i)-(∑ i,M.rho k i*v i) := by rw [← he]; linarith [(hv k).2]
      _ = ∑ i,M.rho k i*(u i-v i) := by simp [mul_sub,sum_sub_distrib]
      _ ≤ ∑ i,M.rho k i*(u k-v k) := sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hmax i hi) (M.rho_nonneg k i))
      _ = _ := by rw [sum_mul]
  nlinarith [M.rho_row_lt_one k]


private theorem optimal_le_feasible {n : ℕ} (M : Model n) (r u v : Fin n → ℝ)
    (hu : IsDualOptimal M r u) (hv : DualFeasible M r v) : ∀ j,u j ≤ v j := by
  apply fixed_le_feasible M r u v _ hv
  intro j
  rcases dual_tight M r u hu j with he | he
  · rw [← he]
    exact max_eq_left (hu.1 j).2
  · rw [← he]
    exact max_eq_right (hu.1 j).1

theorem solution {n : ℕ} (M : Model n) (r : Fin n → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (v0 vη : Fin n → ℝ) (hv0 : IsDualOptimal M r v0)
    (hvη : IsDualOptimal M (fun j => r j - η) vη) :
    Finset.univ.filter (fun j => vη j = r j - η) ⊆
      Finset.univ.filter (fun j => v0 j = r j) := by
  classical
  have hshift : DualFeasible M r (fun j => vη j+η) := by
    intro j
    constructor
    · linarith [(hvη.1 j).1]
    · calc
        (∑ i,M.rho j i*(vη i+η))=(∑ i,M.rho j i*vη i)+(∑ i,M.rho j i)*η := by simp [mul_add,sum_add_distrib,sum_mul]
        _ ≤ vη j+1*η := add_le_add (hvη.1 j).2 (mul_le_mul_of_nonneg_right (M.rho_row_lt_one j).le hη)
        _ = _ := by ring
  intro j hj
  have he := (mem_filter.mp hj).2
  have hle := optimal_le_feasible M r v0 (fun j => vη j+η) hv0 hshift j
  exact mem_filter.mpr ⟨mem_univ _,by linarith [(hv0.1 j).1]⟩
