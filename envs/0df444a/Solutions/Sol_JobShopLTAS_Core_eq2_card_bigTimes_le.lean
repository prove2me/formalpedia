-- Prove2me | solution 1 for JobShopLTAS.Core.eq2_card_bigTimes_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:45:08.394994+00:00
-- url     : https://prove2.me/submissions/32f2a273-7038-46f8-b5ac-bfea1c1679d2

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem
import Definitions.Def_JobShopLTAS_Core_IntervalLP

namespace Aux_JS_eq2
open JobShopLTAS.Core

lemma card_big {m n : ℕ} (inst : Instance m n) (α : ℝ) (hα : 0 < α) (hP : 0 < inst.Pmax) :
    ((inst.bigJobs α).card : ℝ) ≤ (m : ℝ) / α := by
  have htot : ∑ j, inst.jobLength j = ∑ t, inst.load t := by
    unfold Instance.jobLength Instance.load
    rw [Finset.sum_fiberwise Finset.univ inst.mach inst.proc]
    rw [Fintype.sum_sigma]
    rfl
  have hload : ∑ t, inst.load t ≤ m * inst.Pmax := by
    have : ∀ t, inst.load t ≤ inst.Pmax := fun t =>
      le_ciSup (Finite.bddAbove_range _) t
    calc ∑ t, inst.load t ≤ ∑ _t : Fin m, inst.Pmax := Finset.sum_le_sum (fun t _ => this t)
      _ = m * inst.Pmax := by simp
  have hjl : ∀ j, 0 ≤ inst.jobLength j := fun j =>
    Finset.sum_nonneg (fun i _ => inst.p_nonneg j i)
  have hsub : ∑ j ∈ inst.bigJobs α, inst.jobLength j ≤ ∑ j, inst.jobLength j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hjl j)
  have hbig : ((inst.bigJobs α).card : ℝ) * (α * inst.Pmax) ≤
      ∑ j ∈ inst.bigJobs α, inst.jobLength j := by
    have := Finset.card_nsmul_le_sum (inst.bigJobs α) inst.jobLength (α * inst.Pmax)
      (fun j hj => (Finset.mem_filter.mp hj).2)
    rwa [nsmul_eq_mul] at this
  have h1 : ((inst.bigJobs α).card : ℝ) * α * inst.Pmax ≤ m * inst.Pmax := by
    rw [mul_assoc]; linarith
  have h2 : ((inst.bigJobs α).card : ℝ) * α ≤ m := le_of_mul_le_mul_right h1 hP
  rw [le_div_iff₀ hα]
  exact h2

end Aux_JS_eq2

open JobShopLTAS.Core in
theorem solution {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax)
    (σ : inst.Op → ℝ) (hσ : inst.IsBigSchedule ε α σ) :
    ((inst.bigTimes α σ).card : ℝ) ≤ 2 * (inst.maxOps : ℝ) * (inst.bigJobs α).card ∧
      2 * (inst.maxOps : ℝ) * (inst.bigJobs α).card ≤ 2 * (inst.maxOps : ℝ) * m / α := by
  have hα : 0 < α := lt_of_lt_of_le (pow_pos hε _) hα_lo
  refine ⟨?_, ?_⟩
  · set S := Finset.univ.filter (fun o : inst.Op => o.1 ∈ inst.bigJobs α) with hS
    have hSeq : S = (inst.bigJobs α).sigma (fun j => (Finset.univ : Finset (Fin (inst.μ j)))) := by
      ext o
      simp [hS, Finset.mem_sigma]
    have hcardS : S.card ≤ (inst.bigJobs α).card * inst.maxOps := by
      rw [hSeq, Finset.card_sigma]
      have : ∀ j ∈ inst.bigJobs α, (Finset.univ : Finset (Fin (inst.μ j))).card ≤ inst.maxOps := by
        intro j _
        rw [Finset.card_univ, Fintype.card_fin]
        exact Finset.le_sup (f := inst.μ) (Finset.mem_univ j)
      have := Finset.sum_le_card_nsmul (inst.bigJobs α) _ _ this
      rwa [smul_eq_mul] at this
    have hT : (inst.bigTimes α σ).card ≤ 2 * S.card := by
      unfold Instance.bigTimes
      rw [← hS]
      calc _ ≤ (S.image σ).card + (S.image (fun o => σ o + inst.proc o)).card :=
            Finset.card_union_le _ _
        _ ≤ S.card + S.card := add_le_add Finset.card_image_le Finset.card_image_le
        _ = 2 * S.card := by ring
    have : (inst.bigTimes α σ).card ≤ 2 * inst.maxOps * (inst.bigJobs α).card := by
      calc _ ≤ 2 * S.card := hT
        _ ≤ 2 * ((inst.bigJobs α).card * inst.maxOps) := by omega
        _ = 2 * inst.maxOps * (inst.bigJobs α).card := by ring
    exact_mod_cast this
  · have h := Aux_JS_eq2.card_big inst α hα hP
    have hnn : (0:ℝ) ≤ 2 * (inst.maxOps : ℝ) := by positivity
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h hnn
