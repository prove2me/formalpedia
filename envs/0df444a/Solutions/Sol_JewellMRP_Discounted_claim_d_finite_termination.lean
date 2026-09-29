-- Prove2me | solution 1 for JewellMRP.Discounted.claim_d_finite_termination
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:45:19.02104+00:00
-- url     : https://prove2.me/submissions/fa924f7f-ac78-45fc-a568-4fec43e1f74f

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

open MeasureTheory

lemma aux_cdft_ftilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    (α : ℝ) : 0 ≤ ftilde M z i j α := by
  unfold ftilde
  exact setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)

lemma aux_cdft_ftilde_lt {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    {α : ℝ} (hα : 0 < α) : ftilde M z i j α < 1 := by
  have := M.F_prob z i j
  set μ := M.F z i j with hμ
  have hIoi : μ (Set.Ioi 0) = 1 := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, M.F_Iic_zero, tsub_zero]
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(α * t))) (Set.Ioi 0) μ := by
    refine Integrable.mono' (integrable_const (1:ℝ)) ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(α * t))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have : 0 < t := ht
      nlinarith
  have hint1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioi 0) μ := integrable_const _
  have hpos : 0 < ∫ t in Set.Ioi (0:ℝ), (1 - Real.exp (-(α * t))) ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Set.Ioi (0:ℝ) ⊆ Function.support (fun t : ℝ => 1 - Real.exp (-(α * t)))
          ∩ Set.Ioi 0 := by
        intro t ht
        refine ⟨?_, ht⟩
        have : 0 < t := ht
        simp only [Function.mem_support]
        have : Real.exp (-(α * t)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
        linarith
      calc (0 : ENNReal) < 1 := one_pos
        _ = μ (Set.Ioi 0) := hIoi.symm
        _ ≤ _ := measure_mono hsub
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have : 0 < t := ht
      have : Real.exp (-(α * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      simp only [Pi.zero_apply]
      linarith
    · exact hint1.sub hint
  rw [integral_sub hint1 hint, setIntegral_const, Measure.real, hIoi] at hpos
  simp at hpos
  unfold ftilde
  exact hpos

lemma aux_cdft_q_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (α : ℝ) (z : A) (i j : S) :
    0 ≤ qtilde M α z i j :=
  mul_nonneg (M.p_nonneg _ _ _) (aux_cdft_ftilde_nonneg M z i j α)

lemma aux_cdft_row_lt {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ} (hα : 0 < α) (z : A)
    (i : S) : ∑ j, qtilde M α z i j < 1 := by
  rw [← M.p_sum z i]
  unfold qtilde
  apply Finset.sum_lt_sum
  · intro j _
    exact mul_le_of_le_one_right (M.p_nonneg _ _ _) (aux_cdft_ftilde_lt M z i j hα).le
  · have h : ∑ _j : S, (0:ℝ) < ∑ j, M.p z i j := by simp [M.p_sum z i]
    obtain ⟨j, hj, hjp⟩ := Finset.exists_lt_of_sum_lt h
    exact ⟨j, hj, mul_lt_of_lt_one_right hjp (aux_cdft_ftilde_lt M z i j hα)⟩

lemma aux_cdft_minp {S : Type*} [Fintype S] (Q : S → S → ℝ) (g w : S → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j < 1) (hg : ∀ i, 0 ≤ g i)
    (hw : ∀ i, w i = g i + ∑ j, Q i j * w j) : ∀ i, 0 ≤ w i := by
  intro i
  have : Nonempty S := ⟨i⟩
  obtain ⟨i0, hmin⟩ := Finite.exists_min w
  suffices h : 0 ≤ w i0 from h.trans (hmin i)
  by_contra hneg
  push Not at hneg
  have h1 : ∑ j, Q i0 j * w i0 ≤ ∑ j, Q i0 j * w j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmin j) (hQ i0 j)
  rw [← Finset.sum_mul] at h1
  have h2 := hw i0
  have h3 := hg i0
  have h4 := hrow i0
  nlinarith

lemma aux_cdft_test_sub {S A : Type*} [Fintype S] (M : MRP S A) (α : ℝ) (z : A) (i : S)
    (v w : S → ℝ) : test M α z i v - test M α z i w = ∑ j, qtilde M α z i j * (v j - w j) := by
  unfold test
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

lemma aux_cdft_unique {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ} (hα : 0 < α)
    {d : S → A} {v w : S → ℝ} (hv : SolvesEval M α d v) (hw : SolvesEval M α d w) :
    v = w := by
  have key : ∀ (a b : S → ℝ), SolvesEval M α d a → SolvesEval M α d b → ∀ i, 0 ≤ (a - b) i := by
    intro a b ha hb
    apply aux_cdft_minp (fun i j => qtilde M α (d i) i j) 0 (a - b)
      (fun i j => aux_cdft_q_nonneg M α _ i j) (fun i => aux_cdft_row_lt M hα _ i)
      (fun i => le_refl _)
    intro i
    simp only [Pi.sub_apply, Pi.zero_apply, zero_add]
    rw [ha i, hb i, aux_cdft_test_sub]
  funext i
  have h1 := key v w hv hw i
  have h2 := key w v hw hv i
  simp only [Pi.sub_apply] at h1 h2
  linarith

lemma aux_cdft_step {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) {d d' : S → A} {v v' : S → ℝ} (hv : SolvesEval M α d v)
    (hv' : SolvesEval M α d' v') (himp : IsImprovement M α d v d') :
    v ≤ v' ∧ (d' ≠ d → v ≠ v') := by
  have hge : ∀ i, v i ≤ maxTest M α v i := by
    intro i
    rw [hv i]
    exact Finset.le_sup' (fun z => test M α z i v) (Finset.mem_univ (d i))
  refine ⟨?_, ?_⟩
  · intro i
    have := aux_cdft_minp (fun i j => qtilde M α (d' i) i j)
      (fun i => test M α (d' i) i v - v i) (v' - v)
      (fun i j => aux_cdft_q_nonneg M α _ i j) (fun i => aux_cdft_row_lt M hα _ i)
      (fun i => by rw [(himp i).1]; linarith [hge i]) (by
        intro i
        simp only [Pi.sub_apply]
        have := aux_cdft_test_sub M α (d' i) i v' v
        rw [← hv' i] at this
        linarith) i
    simp only [Pi.sub_apply] at this
    linarith
  · intro hne heq
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have h1 : test M α (d i) i v ≠ maxTest M α v i := fun h => hi ((himp i).2 h)
    apply h1
    rw [← hv i, ← (himp i).1]
    conv_rhs => rw [heq]
    rw [← hv' i, heq]

end JewellMRP.Discounted

open JewellMRP.Discounted
open Filter Topology

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MRP S A) {α : ℝ} (hα : 0 < α) {d : ℕ → S → A} {v : ℕ → S → ℝ}
    (hrun : IsFig1Run M α d v) :
    ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K := by
  by_contra hcon
  push Not at hcon
  set N := Fintype.card (S → A) with hN
  have hmono : Monotone v := monotone_nat_of_le_succ fun k =>
    (aux_cdft_step M hα (hrun k).1 (hrun (k + 1)).1 (hrun k).2).1
  have hne : ∀ a b : ℕ, a < b → b ≤ N → d a ≠ d b := by
    intro a b hab hb heq
    have hsol : SolvesEval M α (d a) (v b) := by rw [heq]; exact (hrun b).1
    have hva : v a = v b := aux_cdft_unique M hα (hrun a).1 hsol
    have h1 : v a ≤ v (a + 1) := hmono (Nat.le_succ a)
    have h2 : v (a + 1) ≤ v b := hmono (by omega)
    have h3 : v a = v (a + 1) := le_antisymm h1 (hva ▸ h2)
    exact (aux_cdft_step M hα (hrun a).1 (hrun (a + 1)).1 (hrun a).2).2 (hcon a (by omega)) h3
  have hinj : Function.Injective (fun a : Fin (N + 1) => d a) := by
    intro a b hab
    simp only at hab
    rcases lt_trichotomy (a : ℕ) b with h | h | h
    · exact absurd hab (hne a b h (by omega))
    · exact Fin.ext h
    · exact absurd hab.symm (hne b a h (by omega))
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at this
  omega
