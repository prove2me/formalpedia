-- Prove2me | solution 1 for JobShopLTAS.Core.card_bigJobs_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:42:42.75883+00:00
-- url     : https://prove2.me/submissions/37bf4fd8-79a8-45a6-897a-2ca34da01380

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem

open JobShopLTAS.Core in
theorem solution {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax) :
    ((inst.bigJobs α).card : ℝ) ≤ (m : ℝ) / α ∧
      (m : ℝ) / α ≤ (m : ℝ) * (ε ^ ⌈(m : ℝ) / ε⌉₊)⁻¹ := by
  have hεK : 0 < ε ^ ⌈(m : ℝ) / ε⌉₊ := pow_pos hε _
  have hα : 0 < α := lt_of_lt_of_le hεK hα_lo
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨?_, ?_⟩
  · have htot : ∑ j, inst.jobLength j = ∑ t, inst.load t := by
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
  · rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hεK hα_lo) hm0
