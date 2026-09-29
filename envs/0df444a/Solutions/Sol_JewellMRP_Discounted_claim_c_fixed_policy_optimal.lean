-- Prove2me | solution 1 for JewellMRP.Discounted.claim_c_fixed_policy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:26:35.42622+00:00
-- url     : https://prove2.me/submissions/f5e086cf-81c7-4a4d-b27b-89ed65abeb79

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

open MeasureTheory

theorem aux_cfp_integrableOn {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => Real.exp (-(α * t))) (Set.Ioi 0) (M.F z i j) := by
  have := M.F_prob z i j
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ ?_)
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_le_one_iff]
    have : 0 < α * t := mul_pos hα ht
    linarith

theorem aux_cfp_ftilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    (α : ℝ) : 0 ≤ ftilde M z i j α := by
  unfold ftilde
  exact setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)

theorem aux_cfp_measure_Ioi {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S) :
    M.F z i j (Set.Ioi 0) = 1 := by
  have := M.F_prob z i j
  rw [← Set.compl_Iic]
  exact (prob_compl_eq_one_iff measurableSet_Iic).mpr (M.F_Iic_zero z i j)

theorem aux_cfp_ftilde_lt_one {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    {α : ℝ} (hα : 0 < α) : ftilde M z i j α < 1 := by
  have := M.F_prob z i j
  have hI := aux_cfp_integrableOn M z i j hα
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) (M.F z i j) :=
    integrable_const _
  have hpos : 0 < ∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(α * t))) ∂(M.F z i j) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Set.Ioi (0 : ℝ) ⊆
          Function.support (fun t : ℝ => 1 - Real.exp (-(α * t))) ∩ Set.Ioi 0 := by
        intro t ht
        refine ⟨?_, ht⟩
        simp only [Function.mem_support]
        have : 0 < α * t := mul_pos hα ht
        have : Real.exp (-(α * t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        linarith
      have := measure_mono (μ := M.F z i j) hsub
      rw [aux_cfp_measure_Ioi] at this
      exact lt_of_lt_of_le one_pos this
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ ?_)
      intro t ht
      have : 0 < α * t := mul_pos hα ht
      have : Real.exp (-(α * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      simp only [Pi.zero_apply]
      linarith
    · exact h1.sub hI
  rw [integral_sub h1 hI, setIntegral_const, measureReal_def, aux_cfp_measure_Ioi] at hpos
  simp only [ENNReal.toReal_one, one_smul] at hpos
  unfold ftilde
  linarith

theorem aux_cfp_rowsum_lt_one {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i : S)
    {α : ℝ} (hα : 0 < α) : ∑ j, qtilde M α z i j < 1 := by
  have hne : (Finset.univ : Finset S).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => ftilde M z i j α) hne
  set c := ftilde M z i j0 α
  have hc : c < 1 := aux_cfp_ftilde_lt_one M z i j0 hα
  calc ∑ j, qtilde M α z i j ≤ ∑ j, M.p z i j * c := by
        apply Finset.sum_le_sum
        intro j _
        unfold qtilde
        exact mul_le_mul_of_nonneg_left (hj0 j (Finset.mem_univ _)) (M.p_nonneg z i j)
    _ = c := by rw [← Finset.sum_mul, M.p_sum, one_mul]
    _ < 1 := hc

end JewellMRP.Discounted

open JewellMRP.Discounted
open Filter Topology

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) {d : S → A} {v : S → ℝ}
    (hv : SolvesEval M α d v) (hfix : IsImprovement M α d v d)
    (e : S → A) (w : S → ℝ) (hw : SolvesEval M α e w) : ∀ i, w i ≤ v i := by
  intro i
  have hne : (Finset.univ : Finset S).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun j => w j - v j) hne
  set m := w k - v k with hm
  -- key inequality at k
  have hvk : test M α (e k) k v ≤ v k := by
    rw [hv k, (hfix k).1]
    exact Finset.le_sup' (fun z => test M α z k v) (Finset.mem_univ (e k))
  have hkey : m ≤ ∑ j, qtilde M α (e k) k j * (w j - v j) := by
    have hwk := hw k
    unfold test at hvk hwk
    have : ∑ j, qtilde M α (e k) k j * (w j - v j)
        = ∑ j, qtilde M α (e k) k j * w j - ∑ j, qtilde M α (e k) k j * v j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hm]
    linarith
  have hle : ∑ j, qtilde M α (e k) k j * (w j - v j) ≤ ∑ j, qtilde M α (e k) k j * m := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left (hk j (Finset.mem_univ _))
    unfold qtilde
    exact mul_nonneg (M.p_nonneg _ _ _) (aux_cfp_ftilde_nonneg M _ _ _ _)
  rw [← Finset.sum_mul] at hle
  have hs := aux_cfp_rowsum_lt_one M (e k) k hα
  have hs0 : 0 ≤ ∑ j, qtilde M α (e k) k j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (M.p_nonneg _ _ _) (aux_cfp_ftilde_nonneg M _ _ _ _))
  have hm0 : m ≤ 0 := by
    by_contra h
    push Not at h
    have : (∑ j, qtilde M α (e k) k j) * m < m := by
      have := mul_lt_mul_of_pos_right hs h
      linarith
    linarith
  have := hk i (Finset.mem_univ _)
  linarith
