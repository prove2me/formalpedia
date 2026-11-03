-- Prove2me | solution 1 for MehtaOnlineAdAllocation.MSVV.eq_5_8
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:50:04.111238+00:00
-- url     : https://prove2.me/submissions/f04d35d6-46e4-4ce8-b439-5c360a77f6cf

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRawRun
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_SmallBids
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_alpha
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_beta

open MehtaOnlineAdAllocation.MSVV

noncomputable section

private def bid0 (t : Fin 9) : ℝ :=
  if t.val = 0 then 1 / 4
  else if t.val = 1 then 1 / 4
  else if t.val = 2 then 1 / 4
  else if t.val = 3 then 1 / 6
  else if t.val = 4 then 1 / 12
  else 0

private def bid1 (t : Fin 9) : ℝ :=
  if t.val = 0 then 0 else 1 / 4

private def inst8 : Instance 2 9 where
  budget := fun _ => 1
  budget_pos := fun _ => one_pos
  bid := fun u t => if u.val = 0 then bid0 t else bid1 t
  bid_nonneg := by
    intro u t
    fin_cases u <;> fin_cases t <;> norm_num [bid0, bid1]

private def sigma8 : Allocation 2 9 :=
  fun t => if t.val = 0 then some 0 else if t.val < 5 then some 1 else none

private def tau8 : Allocation 2 9 :=
  fun t => if t.val < 5 then some 0 else some 1

private lemma spend_eq9 (I : Instance 2 9) (σ : Allocation 2 9) (u : Fin 2) (t : ℕ) :
    spend I σ u t = min (I.budget u)
      (∑ v : Fin 9, if v.val < t ∧ σ v = some u then I.bid u v else 0) := by
  unfold spend assignedBefore
  rw [Finset.sum_filter]

private lemma spend_sigma_0_0 : spend inst8 sigma8 0 0 = 0 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_0_1 : spend inst8 sigma8 0 1 = 1 / 4 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_0_2 : spend inst8 sigma8 0 2 = 1 / 4 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_0_3 : spend inst8 sigma8 0 3 = 1 / 4 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_0_4 : spend inst8 sigma8 0 4 = 1 / 4 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_0_9 : spend inst8 sigma8 0 9 = 1 / 4 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_1_1 : spend inst8 sigma8 1 1 = 0 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_1_2 : spend inst8 sigma8 1 2 = 1 / 4 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_1_3 : spend inst8 sigma8 1 3 = 1 / 2 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_1_4 : spend inst8 sigma8 1 4 = 3 / 4 := by
  rw [spend_eq9]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    inst8, sigma8, bid0, bid1, reduceCtorEq, ite_false]
  norm_num

private lemma spend_sigma_1_5 : spend inst8 sigma8 1 5 = 1 := by
  rw [spend_eq9]
  simp [Fin.sum_univ_succ, inst8, sigma8, bid0, bid1]
  norm_num

private lemma spend_sigma_1_6 : spend inst8 sigma8 1 6 = 1 := by
  rw [spend_eq9]
  simp [Fin.sum_univ_succ, inst8, sigma8, bid0, bid1]
  norm_num

private lemma spend_sigma_1_7 : spend inst8 sigma8 1 7 = 1 := by
  rw [spend_eq9]
  simp [Fin.sum_univ_succ, inst8, sigma8, bid0, bid1]
  norm_num

private lemma spend_sigma_1_8 : spend inst8 sigma8 1 8 = 1 := by
  rw [spend_eq9]
  simp [Fin.sum_univ_succ, inst8, sigma8, bid0, bid1]
  norm_num

private lemma spend_sigma_1_9 : spend inst8 sigma8 1 9 = 1 := by
  rw [spend_eq9]
  simp [Fin.sum_univ_succ, inst8, sigma8, bid0, bid1]
  norm_num

private lemma htau_full : ∀ u : Fin 2, spend inst8 tau8 u 9 = 1 := by
  rw [Fin.forall_fin_two]
  constructor <;> {
    rw [spend_eq9]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      inst8, tau8, bid0, bid1, reduceCtorEq, ite_false]
    norm_num
  }

private lemma hsmall8 : SmallBids inst8 (1 / (2 : ℝ) ^ 2) := by
  intro u t
  fin_cases u <;> fin_cases t <;> norm_num [inst8, bid0, bid1]

private lemma hsigma_run : IsRawRun inst8 sigma8 := by
  intro t
  have hy0 : 0 ≤ Real.exp (-1 / 4) := Real.exp_nonneg (-1 / 4)
  have hy1 : Real.exp (-1 / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  fin_cases t
  · -- t = 0
    change spend inst8 sigma8 0 0 < inst8.budget 0 ∧ ∀ v, rawScore inst8 sigma8 v 0 ≤ rawScore inst8 sigma8 0 0
    refine ⟨by rw [spend_sigma_0_0]; norm_num [inst8], ?_⟩
    rw [Fin.forall_fin_two]
    refine ⟨le_refl _, ?_⟩
    unfold rawScore psi
    have hval : ((0 : Fin 9) : ℕ) = 0 := rfl
    have hbid1 : inst8.bid 1 0 = 0 := rfl
    have hbid0 : inst8.bid 0 0 = 1 / 4 := rfl
    have hbud0 : inst8.budget 0 = 1 := rfl
    rw [hval, hbid1, hbid0, hbud0, spend_sigma_0_0]
    have hexp : Real.exp (0 / 1 - 1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  · -- t = 1
    change spend inst8 sigma8 1 1 < inst8.budget 1 ∧ ∀ v, rawScore inst8 sigma8 v 1 ≤ rawScore inst8 sigma8 1 1
    refine ⟨by rw [spend_sigma_1_1]; norm_num [inst8], ?_⟩
    rw [Fin.forall_fin_two]
    refine ⟨?_, le_refl _⟩
    unfold rawScore psi
    have hval : ((1 : Fin 9) : ℕ) = 1 := rfl
    have hbid0 : inst8.bid 0 1 = 1 / 4 := rfl
    have hbid1 : inst8.bid 1 1 = 1 / 4 := rfl
    have hbud0 : inst8.budget 0 = 1 := rfl
    have hbud1 : inst8.budget 1 = 1 := rfl
    rw [hval, hbid0, hbid1, hbud0, hbud1, spend_sigma_0_1, spend_sigma_1_1]
    have hexp : Real.exp (0 / 1 - 1) ≤ Real.exp ((1 / 4) / 1 - 1) :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith
  · -- t = 2
    change spend inst8 sigma8 1 2 < inst8.budget 1 ∧ ∀ v, rawScore inst8 sigma8 v 2 ≤ rawScore inst8 sigma8 1 2
    refine ⟨by rw [spend_sigma_1_2]; norm_num [inst8], ?_⟩
    rw [Fin.forall_fin_two]
    refine ⟨?_, le_refl _⟩
    unfold rawScore psi
    have hval : ((2 : Fin 9) : ℕ) = 2 := rfl
    have hbid0 : inst8.bid 0 2 = 1 / 4 := rfl
    have hbid1 : inst8.bid 1 2 = 1 / 4 := rfl
    have hbud0 : inst8.budget 0 = 1 := rfl
    have hbud1 : inst8.budget 1 = 1 := rfl
    rw [hval, hbid0, hbid1, hbud0, hbud1, spend_sigma_0_2, spend_sigma_1_2]
  · -- t = 3
    change spend inst8 sigma8 1 3 < inst8.budget 1 ∧ ∀ v, rawScore inst8 sigma8 v 3 ≤ rawScore inst8 sigma8 1 3
    refine ⟨by rw [spend_sigma_1_3]; norm_num [inst8], ?_⟩
    rw [Fin.forall_fin_two]
    refine ⟨?_, le_refl _⟩
    unfold rawScore psi
    have hval : ((3 : Fin 9) : ℕ) = 3 := rfl
    have hbud0 : inst8.budget 0 = 1 := rfl
    have hbud1 : inst8.budget 1 = 1 := rfl
    have hbid0 : inst8.bid 0 3 = 1 / 6 := rfl
    have hbid1 : inst8.bid 1 3 = 1 / 4 := rfl
    rw [hval, hbud0, hbud1, hbid0, hbid1, spend_sigma_0_3, spend_sigma_1_3]
    have hexp3 : Real.exp (1 / 4 / 1 - 1) = Real.exp (-1 / 4) ^ 3 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    have hexp2 : Real.exp (1 / 2 / 1 - 1) = Real.exp (-1 / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    rw [hexp3, hexp2]
    have hid : 1 / 4 * (1 - Real.exp (-1 / 4) ^ 2) - 1 / 6 * (1 - Real.exp (-1 / 4) ^ 3) =
        1 / 12 * (1 - Real.exp (-1 / 4)) ^ 2 * (1 + 2 * Real.exp (-1 / 4)) := by ring
    have hpos : 0 ≤ 1 / 12 * (1 - Real.exp (-1 / 4)) ^ 2 * (1 + 2 * Real.exp (-1 / 4)) := by positivity
    linarith
  · -- t = 4
    change spend inst8 sigma8 1 4 < inst8.budget 1 ∧ ∀ v, rawScore inst8 sigma8 v 4 ≤ rawScore inst8 sigma8 1 4
    refine ⟨by rw [spend_sigma_1_4]; norm_num [inst8], ?_⟩
    rw [Fin.forall_fin_two]
    refine ⟨?_, le_refl _⟩
    unfold rawScore psi
    have hval : ((4 : Fin 9) : ℕ) = 4 := rfl
    have hbud0 : inst8.budget 0 = 1 := rfl
    have hbud1 : inst8.budget 1 = 1 := rfl
    have hbid0 : inst8.bid 0 4 = 1 / 12 := rfl
    have hbid1 : inst8.bid 1 4 = 1 / 4 := rfl
    rw [hval, hbud0, hbud1, hbid0, hbid1, spend_sigma_0_4, spend_sigma_1_4]
    have hexp3 : Real.exp (1 / 4 / 1 - 1) = Real.exp (-1 / 4) ^ 3 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    have hexp1 : Real.exp (3 / 4 / 1 - 1) = Real.exp (-1 / 4) := by
      congr 1; norm_num
    rw [hexp3, hexp1]
    have hid : 1 / 4 * (1 - Real.exp (-1 / 4)) - 1 / 12 * (1 - Real.exp (-1 / 4) ^ 3) =
        1 / 12 * (1 - Real.exp (-1 / 4)) ^ 2 * (2 + Real.exp (-1 / 4)) := by ring
    have hpos : 0 ≤ 1 / 12 * (1 - Real.exp (-1 / 4)) ^ 2 * (2 + Real.exp (-1 / 4)) := by positivity
    linarith
  · -- t = 5
    change ∀ u, rawScore inst8 sigma8 u 5 = 0
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · unfold rawScore; have hbid0 : inst8.bid 0 5 = 0 := rfl; rw [hbid0, zero_mul]
    · unfold rawScore psi
      have hval : ((5 : Fin 9) : ℕ) = 5 := rfl
      have hbud1 : inst8.budget 1 = 1 := rfl
      rw [hval, hbud1, spend_sigma_1_5]; norm_num
  · -- t = 6
    change ∀ u, rawScore inst8 sigma8 u 6 = 0
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · unfold rawScore; have hbid0 : inst8.bid 0 6 = 0 := rfl; rw [hbid0, zero_mul]
    · unfold rawScore psi
      have hval : ((6 : Fin 9) : ℕ) = 6 := rfl
      have hbud1 : inst8.budget 1 = 1 := rfl
      rw [hval, hbud1, spend_sigma_1_6]; norm_num
  · -- t = 7
    change ∀ u, rawScore inst8 sigma8 u 7 = 0
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · unfold rawScore; have hbid0 : inst8.bid 0 7 = 0 := rfl; rw [hbid0, zero_mul]
    · unfold rawScore psi
      have hval : ((7 : Fin 9) : ℕ) = 7 := rfl
      have hbud1 : inst8.budget 1 = 1 := rfl
      rw [hval, hbud1, spend_sigma_1_7]; norm_num
  · -- t = 8
    change ∀ u, rawScore inst8 sigma8 u 8 = 0
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · unfold rawScore; have hbid0 : inst8.bid 0 8 = 0 := rfl; rw [hbid0, zero_mul]
    · unfold rawScore psi
      have hval : ((8 : Fin 9) : ℕ) = 8 := rfl
      have hbud1 : inst8.budget 1 = 1 := rfl
      rw [hval, hbud1, spend_sigma_1_8]; norm_num

private lemma hslab_quarter : AdWordsMSVV.Tradeoff.slabOf 2 (1 / 4 : ℝ) = 1 := by
  unfold AdWordsMSVV.Tradeoff.slabOf
  have hceil : ⌈((2 : ℕ) : ℝ) * (1 / 4)⌉₊ ≤ 1 := Nat.ceil_le.mpr (by norm_num)
  exact max_eq_left hceil

private lemma hslab_one : AdWordsMSVV.Tradeoff.slabOf 2 (1 : ℝ) = 2 := by
  unfold AdWordsMSVV.Tradeoff.slabOf
  have hceil : ⌈((2 : ℕ) : ℝ) * 1⌉₊ = 2 := by
    apply le_antisymm
    · exact Nat.ceil_le.mpr (by norm_num)
    · rw [← Nat.cast_le (α := ℝ)]
      exact le_trans (by norm_num) (Nat.le_ceil _)
  rw [hceil]
  decide

private lemma halpha_1 : alpha 2 (fun u => spend inst8 sigma8 u 9) 1 = 1 := by
  unfold alpha
  have hfilter : Finset.univ.filter (fun u : Fin 2 =>
      AdWordsMSVV.Tradeoff.slabOf 2 (spend inst8 sigma8 u 9) = 1) = {0} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    fin_cases u
    · change AdWordsMSVV.Tradeoff.slabOf 2 (spend inst8 sigma8 0 9) = 1 ↔ (0 : Fin 2) = 0
      rw [spend_sigma_0_9, hslab_quarter]
      simp
    · change AdWordsMSVV.Tradeoff.slabOf 2 (spend inst8 sigma8 1 9) = 1 ↔ (1 : Fin 2) = 0
      rw [spend_sigma_1_9, hslab_one]
      decide
  rw [hfilter]
  norm_num

private lemma hbeta_1 : beta 2 (fun u => spend inst8 sigma8 u 9) 1 = 3 / 4 := by
  unfold beta
  rw [Fin.sum_univ_two]
  dsimp only
  rw [spend_sigma_0_9, spend_sigma_1_9]
  norm_num

end

theorem solution : ¬ (∀ {N M : ℕ} (I : Instance N M)
    (_ : ∀ u, I.budget u = 1) (k : ℕ) (_ : 1 ≤ k)
    (_ : SmallBids I (1 / (k : ℝ) ^ 2))
    (σ : Allocation N M) (_ : IsRawRun I σ)
    (τ : Allocation N M) (_ : ∀ u, spend I τ u M = 1),
    (∑ i ∈ Finset.Icc 1 k,
      psi ((i : ℝ) / (k : ℝ)) * alpha k (fun u => spend I σ u M) i) ≤
    ∑ i ∈ Finset.Icc 1 k,
      psi ((i : ℝ) / (k : ℝ)) * beta k (fun u => spend I σ u M) i) := by
  intro h
  have h1 := h inst8 (fun _ => rfl) 2 (by decide) hsmall8 sigma8 hsigma_run tau8 htau_full
  have hicc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hicc] at h1
  simp only [Finset.mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton] at h1
  have hpsi2 : psi (((2 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 0 := by
    unfold psi
    norm_num
  rw [hpsi2, zero_mul, zero_mul, add_zero, add_zero, halpha_1, hbeta_1] at h1
  have hpsi1_pos : 0 < psi (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) := by
    unfold psi
    have hexp : Real.exp (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) - 1) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  linarith
