-- Prove2me | solution 1 for LearningBasedRO.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:18:38.025678+00:00
-- url     : https://prove2.me/submissions/6729c010-b6b9-42ee-9b2d-de6d09a6049d

import Definitions.Def_LearningBasedRO_Model
import Theorems.Thm_LearningBasedRO_lemma_3_upper_display
import Theorems.Thm_LearningBasedRO_lemma_3_lower_display

open MeasureTheory

open LearningBasedRO in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] (n₂ : ℕ)
    (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (q : ℝ)
    (hq : μ (Set.Iic q) = ENNReal.ofReal (1 - ϵ)) :
    ((iStarSet n₂ ϵ δ).Nonempty →
        ENNReal.ofReal (1 - δ) ≤
          (Measure.pi fun _ : Fin n₂ => μ) {y | q ≤ orderStat y (iStar n₂ ϵ δ)}) ∧
      ((∑ k ∈ Finset.range n₂, binomTerm n₂ ϵ k = 1 - (1 - ϵ) ^ n₂) ∧
        (∑ k ∈ Finset.range n₂, binomTerm n₂ ϵ k < 1 - δ →
          ∀ r : ℕ, 1 ≤ r → r ≤ n₂ →
            (Measure.pi fun _ : Fin n₂ => μ) {y | q ≤ orderStat y r} <
              ENNReal.ofReal (1 - δ))) ∧
      ((iLowerStarSet n₂ ϵ δ).Nonempty →
        ENNReal.ofReal (1 - δ) ≤
          (Measure.pi fun _ : Fin n₂ => μ) {y | orderStat y (iLowerStar n₂ ϵ δ) ≤ q}) ∧
      ((∑ k ∈ Finset.Icc 1 n₂, binomTerm n₂ ϵ k = 1 - ϵ ^ n₂) ∧
        (∑ k ∈ Finset.Icc 1 n₂, binomTerm n₂ ϵ k < 1 - δ →
          ∀ r : ℕ, 1 ≤ r → r ≤ n₂ →
            (Measure.pi fun _ : Fin n₂ => μ) {y | orderStat y r ≤ q} <
              ENNReal.ofReal (1 - δ))) := by
  have _ := hδ0
  have hbinom_nonneg : ∀ k : ℕ, 0 ≤ binomTerm n₂ ϵ k := fun k => by
    unfold binomTerm
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
      (pow_nonneg (by linarith) _)
  have htotal : ∑ k ∈ Finset.range (n₂ + 1), binomTerm n₂ ϵ k = 1 := by
    have hpow : (1 - ϵ + ϵ) ^ n₂ = 1 := by
      rw [sub_add_cancel, one_pow]
    rw [add_pow] at hpow
    rw [← hpow]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold binomTerm
    ring
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · intro hne
    have hmem : iStar n₂ ϵ δ ∈ iStarSet n₂ ϵ δ := Nat.sInf_mem hne
    rcases hmem with ⟨hr1, hrn, hsum⟩
    rw [(lemma_3_upper_display μ ϵ hϵ0 hϵ1 q hq n₂ (iStar n₂ ϵ δ) hr1 hrn).2]
    exact ENNReal.ofReal_le_ofReal hsum
  · have hsplit := Finset.sum_range_succ (fun k => binomTerm n₂ ϵ k) n₂
    have hlast : binomTerm n₂ ϵ n₂ = (1 - ϵ) ^ n₂ := by
      simp [binomTerm]
    linarith [htotal, hsplit, hlast]
  · intro hlt r hr1 hrn
    rw [(lemma_3_upper_display μ ϵ hϵ0 hϵ1 q hq n₂ r hr1 hrn).2]
    have hsub : ∑ k ∈ Finset.range r, binomTerm n₂ ϵ k ≤
        ∑ k ∈ Finset.range n₂, binomTerm n₂ ϵ k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrn)
        (fun k _ _ => hbinom_nonneg k)
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (lt_of_le_of_lt hsub hlt)
  · intro hne
    have hbdd : BddAbove (iLowerStarSet n₂ ϵ δ) := ⟨n₂, fun _ hr => hr.2.1⟩
    have hmem : iLowerStar n₂ ϵ δ ∈ iLowerStarSet n₂ ϵ δ := Nat.sSup_mem hne hbdd
    rcases hmem with ⟨hr1, hrn, hsum⟩
    rw [(lemma_3_lower_display μ ϵ hϵ0 hϵ1 q hq n₂ (iLowerStar n₂ ϵ δ) hr1 hrn).2]
    exact ENNReal.ofReal_le_ofReal hsum
  · have hrange_eq : Finset.range (n₂ + 1) = insert 0 (Finset.Icc 1 n₂) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have h0_not_mem : (0 : ℕ) ∉ Finset.Icc 1 n₂ := by simp
    have hsplit : ∑ k ∈ Finset.range (n₂ + 1), binomTerm n₂ ϵ k =
        binomTerm n₂ ϵ 0 + ∑ k ∈ Finset.Icc 1 n₂, binomTerm n₂ ϵ k := by
      rw [hrange_eq, Finset.sum_insert h0_not_mem]
    have hfirst : binomTerm n₂ ϵ 0 = ϵ ^ n₂ := by
      simp [binomTerm]
    linarith [htotal, hsplit, hfirst]
  · intro hlt r hr1 hrn
    rw [(lemma_3_lower_display μ ϵ hϵ0 hϵ1 q hq n₂ r hr1 hrn).2]
    have hsub : ∑ k ∈ Finset.Icc r n₂, binomTerm n₂ ϵ k ≤
        ∑ k ∈ Finset.Icc 1 n₂, binomTerm n₂ ϵ k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hr1)
        (fun k _ _ => hbinom_nonneg k)
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (lt_of_le_of_lt hsub hlt)
