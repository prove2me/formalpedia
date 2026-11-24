-- Prove2me | solution 1 for GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:46.287736+00:00
-- url     : https://prove2.me/submissions/9bf51f38-c6a8-4ff2-99ce-426a25553c84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfJointEigenvectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.JointEigenvectorsIndependent
namespace GlobalTheory.JointEigenvectorsIndependent
theorem _root_.solution {ι α M : Type} [AddCommGroup M] [Module ℂ M]
    (f : ι → M) (χ : ι → α → ℂ) (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ)
    (hop : ∀ (a : α) (i : ι), (op a : M → M) (f i) = χ i a • f i)
    (hf : ∀ i : ι, f i ≠ (0 : M)) : LinearIndependent ℂ f := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert j s hj ih =>
    intro g hg
    rw [Finset.sum_insert hj] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      obtain ⟨a, ha⟩ : ∃ a, χ i a ≠ χ j a := Function.ne_iff.mp (fun h => hij (hχ h))
      have h1 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ k a) • f k = 0 := by
        have h := congrArg (op a) hg
        rw [map_add, map_sum, map_zero, map_smul, hop, smul_smul] at h
        simpa only [map_smul, hop, smul_smul] using h
      have h2 : (g j * χ j a) • f j + ∑ k ∈ s, (g k * χ j a) • f k = 0 := by
        have h := congrArg (fun x => χ j a • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (χ j a)] using h
      have h3 : ∑ k ∈ s, (g k * (χ k a - χ j a)) • f k = 0 := by
        have h4 : ∑ k ∈ s, (g k * χ k a) • f k = ∑ k ∈ s, (g k * χ j a) • f k :=
          add_left_cancel (h1.trans h2.symm)
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, h4, sub_self]
      have h5 := ih (fun k => g k * (χ k a - χ j a)) h3 i hi
      exact (mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr ha)
    have hsum : ∑ k ∈ s, g k • f k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hsum, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hf _)
    · exact hs i hi
end GlobalTheory.JointEigenvectorsIndependent
