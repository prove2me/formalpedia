-- Prove2me | solution 1 for JewellMRP.Discounted.claim_b_strict_improvement
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:23:58.734848+00:00
-- url     : https://prove2.me/submissions/0867479e-1009-4c57-b99b-2bd427555fee

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

open MeasureTheory

lemma aux_csi_ftilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    (s : ℝ) : 0 ≤ ftilde M z i j s := by
  unfold ftilde
  exact setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)

lemma aux_csi_ftilde_lt_one {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    {s : ℝ} (hs : 0 < s) : ftilde M z i j s < 1 := by
  have := M.F_prob z i j
  unfold ftilde
  set μ := M.F z i j with hμ
  have hI : μ (Set.Ioi 0) = 1 := by
    have h1 : μ (Set.Iic 0) = 0 := M.F_Iic_zero z i j
    have : (Set.Ioi (0:ℝ)) = (Set.Iic 0)ᶜ := by ext; simp
    rw [this, measure_compl measurableSet_Iic (measure_ne_top _ _), h1, measure_univ]
    simp
  have hint : IntegrableOn (fun t => Real.exp (-(s * t))) (Set.Ioi 0) μ := by
    refine (integrable_const (1:ℝ)).mono' (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht' : (0:ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_le_one_iff]
    nlinarith
  have hint1 : IntegrableOn (fun _ => (1:ℝ)) (Set.Ioi 0) μ := integrable_const _
  have hpos : 0 < ∫ t in Set.Ioi 0, (1 - Real.exp (-(s * t))) ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Set.Ioi (0:ℝ) ⊆ Function.support (fun t => 1 - Real.exp (-(s * t))) ∩ Set.Ioi 0 := by
        intro t ht
        refine ⟨?_, ht⟩
        have ht' : (0:ℝ) < t := ht
        simp only [Function.mem_support]
        have : Real.exp (-(s * t)) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith
        linarith
      have := measure_mono (μ := μ) hsub
      rw [hI] at this
      exact lt_of_lt_of_le (by norm_num) this
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      have ht' : (0:ℝ) < t := ht
      have : Real.exp (-(s * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      simp only [Pi.zero_apply]
      linarith
    · exact hint1.sub hint
  rw [integral_sub hint1 hint, setIntegral_const] at hpos
  have hr : μ.real (Set.Ioi 0) = 1 := by
    rw [measureReal_def, hI]; simp
  rw [hr] at hpos
  simp at hpos
  linarith

lemma aux_csi_qtilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (s : ℝ) (z : A)
    (i j : S) : 0 ≤ qtilde M s z i j :=
  mul_nonneg (M.p_nonneg z i j) (aux_csi_ftilde_nonneg M z i j s)

lemma aux_csi_rowsum_lt_one {S A : Type*} [Fintype S] (M : MRP S A) {s : ℝ} (hs : 0 < s)
    (z : A) (i : S) : ∑ j, qtilde M s z i j < 1 := by
  unfold qtilde
  have hpos : 0 < ∑ j, M.p z i j * (1 - ftilde M z i j s) := by
    obtain ⟨j, hj⟩ : ∃ j, 0 < M.p z i j := by
      by_contra h
      push Not at h
      have : ∑ j, M.p z i j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
      rw [M.p_sum] at this
      linarith
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (M.p_nonneg z i k) (by linarith [aux_csi_ftilde_lt_one M z i k hs])
    · exact ⟨j, Finset.mem_univ _, mul_pos hj (by linarith [aux_csi_ftilde_lt_one M z i j hs])⟩
  have h2 : ∑ j, M.p z i j * (1 - ftilde M z i j s)
      = 1 - ∑ j, M.p z i j * ftilde M z i j s := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, M.p_sum]
  linarith

end JewellMRP.Discounted

open JewellMRP.Discounted

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) {d d' : S → A} {v v' : S → ℝ}
    (hv : SolvesEval M α d v) (hv' : SolvesEval M α d' v')
    (himp : IsImprovement M α d v d') (hne : d' ≠ d) :
    (∀ i, v i ≤ v' i) ∧ ∃ i, v i < v' i := by
  have hkey : ∀ i, v' i - v i = ∑ j, qtilde M α (d' i) i j * (v' j - v j)
      + (test M α (d' i) i v - v i) := by
    intro i
    have h1 := hv' i
    unfold test at h1 ⊢
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have hle : ∀ i, test M α (d i) i v ≤ maxTest M α v i := fun i =>
    Finset.le_sup' (fun z => test M α z i v) (Finset.mem_univ (d i))
  have hgain : ∀ i, 0 ≤ test M α (d' i) i v - v i := by
    intro i
    linarith [hv i, (himp i).1, hle i]
  have hnonneg : ∀ i, v i ≤ v' i := by
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := h
    obtain ⟨i0, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => v' i - v i)
      ⟨k, Finset.mem_univ k⟩
    have hm : v' i0 - v i0 < 0 := lt_of_le_of_lt (hmin k (Finset.mem_univ _)) (by linarith)
    have hsum : (v' i0 - v i0) * ∑ j, qtilde M α (d' i0) i0 j
        ≤ ∑ j, qtilde M α (d' i0) i0 j * (v' j - v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ _))
        (aux_csi_qtilde_nonneg M α _ _ _)
    have hrow := aux_csi_rowsum_lt_one M hα (d' i0) i0
    have h1 := hkey i0
    have h2 := hgain i0
    nlinarith
  refine ⟨hnonneg, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, d' i ≠ d i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine ⟨i, ?_⟩
  have hlt : test M α (d i) i v < maxTest M α v i := by
    rcases lt_or_eq_of_le (hle i) with h | h
    · exact h
    · exact absurd ((himp i).2 h) hi
  have hsum : 0 ≤ ∑ j, qtilde M α (d' i) i j * (v' j - v j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (aux_csi_qtilde_nonneg M α _ _ _)
      (by linarith [hnonneg j]))
  linarith [hkey i, hv i, (himp i).1]
