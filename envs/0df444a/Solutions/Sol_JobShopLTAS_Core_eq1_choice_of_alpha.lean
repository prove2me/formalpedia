-- Prove2me | solution 1 for JobShopLTAS.Core.eq1_choice_of_alpha
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:19:20.412525+00:00
-- url     : https://prove2.me/submissions/2b5da631-2c59-4461-b65a-64460254d525

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem

open JobShopLTAS.Core

private lemma sum_proc_le_m_mul_Pmax {m n : ℕ} (inst : Instance m n) :
    (∑ o : inst.Op, inst.proc o) ≤ (m : ℝ) * inst.Pmax := by
  have hfib : (∑ o : inst.Op, inst.proc o) = ∑ t : Fin m, inst.load t := by
    unfold Instance.load
    exact (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) inst.proc).symm
  rw [hfib]
  have hle : ∑ t : Fin m, inst.load t ≤ ∑ _t : Fin m, inst.Pmax := by
    apply Finset.sum_le_sum
    intro t _
    exact le_ciSup (Set.finite_range _).bddAbove t
  simpa using hle

private lemma sum_jobLength_eq_sum_proc {m n : ℕ} (inst : Instance m n) :
    (∑ j : Fin n, inst.jobLength j) = ∑ o : inst.Op, inst.proc o := by
  unfold Instance.jobLength Instance.proc
  exact (Fintype.sum_sigma (f := fun o : inst.Op => inst.p o.1 o.2)).symm

private lemma smallJobs_disjoint {m n : ℕ} (inst : Instance m n) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hP : 0 < inst.Pmax) :
    ∀ k₁ k₂ : ℕ, k₁ ≠ k₂ →
      Disjoint (inst.smallJobs ε (ε ^ k₁)) (inst.smallJobs ε (ε ^ k₂)) := by
  have aux : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      Disjoint (inst.smallJobs ε (ε ^ k₁)) (inst.smallJobs ε (ε ^ k₂)) := by
    intro k₁ k₂ hlt
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    rw [Instance.smallJobs, Finset.mem_filter] at hj₁ hj₂
    have hk : k₁ + 1 ≤ k₂ := hlt
    have hpow : ε ^ k₂ ≤ ε ^ (k₁ + 1) :=
      pow_le_pow_of_le_one hε.le hε1.le hk
    have hpow' : ε ^ k₂ * inst.Pmax ≤ (ε ^ k₁ * ε) * inst.Pmax := by
      rw [← pow_succ]
      exact mul_le_mul_of_nonneg_right hpow hP.le
    linarith [hj₁.2.1, hj₂.2.2]
  intro k₁ k₂ hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact aux k₁ k₂ hlt
  · exact (aux k₂ k₁ hgt).symm

theorem solution {m n : ℕ} (inst : Instance m n) (ε : ℝ)
    (hm : 2 ≤ m) (_hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1) (hP : 0 < inst.Pmax) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ ⌈(m : ℝ) / ε⌉₊ ∧
      ∑ j ∈ inst.smallJobs ε (ε ^ k), inst.jobLength j ≤ ε * inst.Pmax := by
  set K := ⌈(m : ℝ) / ε⌉₊
  have hm_pos : (0 : ℝ) < m := by positivity
  have hdiv_pos : 0 < (m : ℝ) / ε := div_pos hm_pos hε
  have hK_pos : 0 < K := Nat.ceil_pos.mpr hdiv_pos
  have hK1 : 1 ≤ K := hK_pos
  set I := Finset.Icc 1 K
  have hI_ne : I.Nonempty := Finset.nonempty_Icc.mpr hK1
  let f : ℕ → ℝ := fun k => ∑ j ∈ inst.smallJobs ε (ε ^ k), inst.jobLength j
  rcases Finset.exists_min_image I f hI_ne with ⟨k₀, hk₀, hmin⟩
  have hk₀_mem := Finset.mem_Icc.mp hk₀
  refine ⟨k₀, hk₀_mem.1, hk₀_mem.2, ?_⟩
  have hsum_I : ∑ k ∈ I, f k ≤ (m : ℝ) * inst.Pmax := by
    have hdisj : (I : Set ℕ).PairwiseDisjoint (fun k => inst.smallJobs ε (ε ^ k)) :=
      fun k₁ _ k₂ _ hne => smallJobs_disjoint inst ε hε hε1 hP k₁ k₂ hne
    have hbi : ∑ k ∈ I, f k = ∑ j ∈ I.biUnion (fun k => inst.smallJobs ε (ε ^ k)), inst.jobLength j :=
      (Finset.sum_biUnion hdisj).symm
    rw [hbi]
    have hjl_nonneg : ∀ j : Fin n, 0 ≤ inst.jobLength j :=
      fun j => Finset.sum_nonneg (fun i _ => inst.p_nonneg j i)
    have hsub : ∑ j ∈ I.biUnion (fun k => inst.smallJobs ε (ε ^ k)), inst.jobLength j ≤
        ∑ j : Fin n, inst.jobLength j :=
      Finset.sum_le_univ_sum_of_nonneg hjl_nonneg
    refine le_trans hsub ?_
    rw [sum_jobLength_eq_sum_proc]
    exact sum_proc_le_m_mul_Pmax inst
  have hcard : I.card = K := by
    simp [I, Nat.card_Icc]
  have hmin_sum : (K : ℝ) * f k₀ ≤ ∑ k ∈ I, f k := by
    have : ∑ _k ∈ I, f k₀ ≤ ∑ k ∈ I, f k := Finset.sum_le_sum (fun k hk => hmin k hk)
    simpa [hcard] using this
  have hK_ge : (m : ℝ) / ε ≤ K := Nat.le_ceil _
  have hm_le : (m : ℝ) ≤ (K : ℝ) * ε := (div_le_iff₀ hε).mp hK_ge
  have hmP_le : (m : ℝ) * inst.Pmax ≤ (K : ℝ) * (ε * inst.Pmax) := by
    calc (m : ℝ) * inst.Pmax ≤ ((K : ℝ) * ε) * inst.Pmax :=
          mul_le_mul_of_nonneg_right hm_le hP.le
      _ = (K : ℝ) * (ε * inst.Pmax) := mul_assoc _ _ _
  have hKf : (K : ℝ) * f k₀ ≤ (K : ℝ) * (ε * inst.Pmax) :=
    le_trans hmin_sum (le_trans hsum_I hmP_le)
  have hK_real_pos : (0 : ℝ) < K := Nat.cast_pos.mpr hK_pos
  exact le_of_mul_le_mul_left hKf hK_real_pos
