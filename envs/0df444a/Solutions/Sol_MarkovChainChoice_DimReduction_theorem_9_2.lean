-- Prove2me | solution 2 for MarkovChainChoice.DimReduction.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:19:54.462473+00:00
-- url     : https://prove2.me/submissions/2c0b6a8f-fa4d-4529-ab41-79cbebccaf80

import Mathlib
import Definitions.Def_MarkovChainChoice_DimReduction_Reduced
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Theorems.Thm_MarkovChainChoice_DimReduction_drAlpha_le_one
import Theorems.Thm_MarkovChainChoice_DimReduction_eq_balance_of_supp_empty
import Theorems.Thm_MarkovChainChoice_DimReduction_iterate_invariants
import Theorems.Thm_MarkovChainChoice_DimReduction_lemma_8
import Theorems.Thm_MarkovChainChoice_DimReduction_visitNot_le_of_mem_H

-- carved verbatim out of submission 79a65fc3-6b88-4127-8441-cebd914e000b, lines 523-557

section
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

end

section
open Finset Matrix MarkovChainChoice.Shared
open MarkovChainChoice.DimReduction

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

private theorem iter_succ {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    drIter M x z (k+1)=drNext M (drIter M x z k) := by
  cases k with
  | zero => omega
  | succ k => rfl

private theorem next_of_not_stopped {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ)
    (hp : drIter M x z k ∈ H M) (hn : ¬ drStops M x z k) :
    drNext M (drIter M x z k) ∈ H M ∧
      ∀ j ∈ drS M x z k, (drIter M x z k).1 j/purchase M (drS M x z k) j=drA M x z k →
        drSupp (drNext M (drIter M x z k)).1 ⊆ (drS M x z k).erase j := by
  classical
  have hs : (drS M x z k).Nonempty := nonempty_iff_ne_empty.mpr (fun hs => hn (Or.inl hs))
  have ha : drA M x z k < 1 := lt_of_le_of_ne (MarkovChainChoice.DimReduction.drAlpha_le_one M _ hp hs) (fun ha => hn (Or.inr ha))
  have hmin : ∃ j ∈ drS M x z k,(drIter M x z k).1 j/purchase M (drS M x z k) j=drA M x z k := by
    obtain ⟨j,hj,he⟩ := exists_mem_eq_inf' hs (fun j => (drIter M x z k).1 j/purchase M (drS M x z k) j)
    refine ⟨j,hj,?_⟩
    change _ = drAlpha M (drIter M x z k).1
    rw [drAlpha]
    split_ifs with hh
    · exact he.symm
    · exact False.elim (hh hs)
  obtain ⟨j,hj,hmin⟩ := hmin
  refine ⟨(MarkovChainChoice.DimReduction.lemma_8 M _ hp hs ha j hj hmin).1,?_⟩
  intro i hi hmin
  exact (MarkovChainChoice.DimReduction.lemma_8 M _ hp hs ha i hi hmin).2

private theorem eq_of_alpha_one {n : ℕ} (M : Model n) :
    ∀ p ∈ H M, (drSupp p.1).Nonempty → drAlpha M p.1=1 →
      p=(purchase M (drSupp p.1),visitNot M (drSupp p.1)) := by
  intro p hp hs ha
  have hb := balance_unique M (drSupp p.1)
  exact H_order_eq M p _ hp ⟨hb.2.1,hb.2.2.1,hb.1.1⟩
    (purchase_le_of_one_le_alpha M p hp ha.ge) (MarkovChainChoice.DimReduction.visitNot_le_of_mem_H M p hp)

private theorem support_shrinks {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hp : drIter M x z k ∈ H M) (hn : ¬ drStops M x z k) :
    (drS M x z (k+1)).card < (drS M x z k).card ∧ drS M x z (k+1) ⊆ drS M x z k := by
  classical
  have hs : (drS M x z k).Nonempty := nonempty_iff_ne_empty.mpr (fun hs => hn (Or.inl hs))
  obtain ⟨j,hj,he⟩ := exists_mem_eq_inf' hs (fun j => (drIter M x z k).1 j/purchase M (drS M x z k) j)
  have hmin : (drIter M x z k).1 j/purchase M (drS M x z k) j=drA M x z k := by
    unfold drA drAlpha
    split_ifs with hh
    · exact he.symm
    · exact False.elim (hh hs)
  have hsub : drS M x z (k+1) ⊆ (drS M x z k).erase j := by
    rw [drS,iter_succ M x z k hk]
    exact (next_of_not_stopped M x z k hp hn).2 j hj hmin
  exact ⟨(card_le_card hsub).trans_lt (card_erase_lt_of_mem hj),hsub.trans (erase_subset _ _)⟩

private theorem exists_first_stop {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (hp : (x,z) ∈ H M) :
    ∃ K,1 ≤ K ∧ K ≤ n+1 ∧ drStops M x z K ∧ ∀ k,1 ≤ k → k < K → ¬ drStops M x z k := by
  classical
  have hex : ∃ K,1 ≤ K ∧ K ≤ n+1 ∧ drStops M x z K := by
    by_contra hn
    push_neg at hn
    have hcard : ∀ k,1 ≤ k → k ≤ n+1 → (drS M x z k).card+k ≤ n+1 := by
      intro k hk
      induction k,hk using Nat.le_induction with
      | base =>
        intro hbound
        have hc := card_le_univ (s := drS M x z 1)
        simp only [Fintype.card_fin] at hc
        omega
      | @succ k hk ih =>
        intro hbound
        have hprev := ih (by omega)
        have hkH := (MarkovChainChoice.DimReduction.iterate_invariants M x z hp k hk (fun l hl hlk => hn l hl (by omega))).1
        have hlt := (support_shrinks M x z k hk hkH (hn k hk (by omega))).1
        omega
    have hz := hcard (n+1) (by omega) le_rfl
    have hs : drS M x z (n+1)=∅ := card_eq_zero.mp (by omega)
    exact hn (n+1) (by omega) le_rfl (Or.inl hs)
  let K := Nat.find hex
  have hK := Nat.find_spec hex
  refine ⟨K,hK.1,hK.2.1,hK.2.2,?_⟩
  intro k hk hkK hn
  exact (Nat.find_min hex hkK) ⟨hk,by omega,hn⟩

private theorem stop_eq {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (k : ℕ)
    (hp : drIter M x z k ∈ H M) (hs : drStops M x z k) :
    drA M x z k=1 ∧ drIter M x z k=(purchase M (drS M x z k),visitNot M (drS M x z k)) := by
  rcases hs with hs | ha
  · have ha : drA M x z k=1 := by simp [drA,drAlpha,show drSupp (drIter M x z k).1=∅ from hs]
    refine ⟨ha,?_⟩
    rw [hs]
    exact MarkovChainChoice.DimReduction.eq_balance_of_supp_empty M _ hp hs
  · refine ⟨ha,?_⟩
    by_cases hs : (drS M x z k).Nonempty
    · exact eq_of_alpha_one M _ hp hs ha
    · have he : drS M x z k=∅ := not_nonempty_iff_eq_empty.mp hs
      rw [he]
      exact MarkovChainChoice.DimReduction.eq_balance_of_supp_empty M _ hp he

private theorem partial_decomposition {n : ℕ} (M : Model n) (x z : Fin n → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hrun : ∀ l,1 ≤ l → l < k → ¬ drStops M x z l) :
    (∀ j,x j=(∑ l ∈ Ico 1 k,drGamma M x z l*purchase M (drS M x z l) j)+
      (∏ l ∈ Ico 1 k,(1-drA M x z l))*(drIter M x z k).1 j) ∧
    (∀ j,z j=(∑ l ∈ Ico 1 k,drGamma M x z l*visitNot M (drS M x z l) j)+
      (∏ l ∈ Ico 1 k,(1-drA M x z l))*(drIter M x z k).2 j) ∧
    (∑ l ∈ Ico 1 k,drGamma M x z l)+(∏ l ∈ Ico 1 k,(1-drA M x z l))=1 := by
  induction k,hk using Nat.le_induction with
  | base => simp [drIter]
  | @succ k hk ih =>
    have ih := ih (fun l hl hlk => hrun l hl (by omega))
    have hn := hrun k hk (by omega)
    have ha : 1-drA M x z k ≠ 0 := by
      intro h
      apply hn
      exact Or.inr (by linarith)
    have hstepX (j : Fin n) : (drIter M x z k).1 j = drA M x z k*purchase M (drS M x z k) j+
        (1-drA M x z k)*(drIter M x z (k+1)).1 j := by
      rw [iter_succ M x z k hk]
      change _ = _+(1-drA M x z k)*((_ - _)/(1-drA M x z k))
      field_simp
      simp only [drA,drS]
      ring
    have hstepZ (j : Fin n) : (drIter M x z k).2 j = drA M x z k*visitNot M (drS M x z k) j+
        (1-drA M x z k)*(drIter M x z (k+1)).2 j := by
      rw [iter_succ M x z k hk]
      change _ = _+(1-drA M x z k)*((_ - _)/(1-drA M x z k))
      field_simp
      simp only [drA,drS]
      ring
    simp only [sum_Ico_succ_top hk,prod_Ico_succ_top hk,drGamma]
    refine ⟨?_,?_,?_⟩
    · intro j
      have h := ih.1 j
      rw [hstepX j] at h
      dsimp [drGamma] at h
      nlinarith
    · intro j
      have h := ih.2.1 j
      rw [hstepZ j] at h
      dsimp [drGamma] at h
      nlinarith
    · have h := ih.2.2
      dsimp [drGamma] at h
      nlinarith

theorem solution {n m : ℕ} (M : Model n) (T : ℕ) (c : Fin m → ℝ) (a : Fin m → Fin n → ℝ)
    (r : Fin n → ℝ) (x z : Fin n → ℝ) (hopt : IsReducedOptimal M T c a r x z) :
    (∃ K, 1 ≤ K ∧ K ≤ n + 1 ∧ drStops M x z K ∧ ∀ k, 1 ≤ k → k < K → ¬ drStops M x z k) ∧
    ∀ K, 1 ≤ K → drStops M x z K → (∀ k, 1 ≤ k → k < K → ¬ drStops M x z k) →
      x = ∑ k ∈ Finset.Icc 1 K, drGamma M x z k • purchase M (drS M x z k) ∧
      z = ∑ k ∈ Finset.Icc 1 K, drGamma M x z k • visitNot M (drS M x z k) ∧
      ∑ k ∈ Finset.Icc 1 K, drGamma M x z k = 1 ∧
      ∀ k, 1 ≤ k → k < K → drS M x z (k + 1) ⊆ drS M x z k := by
  have hp : (x,z) ∈ H M := ⟨hopt.1.1,hopt.1.2.1,hopt.1.2.2.2⟩
  refine ⟨exists_first_stop M x z hp,?_⟩
  intro K hK hs hrun
  have hmem := (MarkovChainChoice.DimReduction.iterate_invariants M x z hp K hK hrun).1
  have hstop := stop_eq M x z K hmem hs
  have hpart := partial_decomposition M x z K hK hrun
  have hγ : drGamma M x z K = ∏ l ∈ Ico 1 K,(1-drA M x z l) := by
    simp [drGamma,hstop.1]
  refine ⟨?_,?_,?_,?_⟩
  · funext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← Ico_add_one_right_eq_Icc,sum_Ico_succ_top hK,hγ]
    have h := hpart.1 j
    rw [hstop.2] at h
    exact h
  · funext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← Ico_add_one_right_eq_Icc,sum_Ico_succ_top hK,hγ]
    have h := hpart.2.1 j
    rw [hstop.2] at h
    exact h
  · rw [← Ico_add_one_right_eq_Icc,sum_Ico_succ_top hK,hγ]
    exact hpart.2.2
  · intro k hk hkK
    have hkH := (MarkovChainChoice.DimReduction.iterate_invariants M x z hp k hk (fun l hl hlk => hrun l hl (by omega))).1
    exact (support_shrinks M x z k hk hkH (hrun k hk hkK)).2

end
