-- Prove2me | solution 1 for HardyFLocal.product_tests_span
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T01:07:21.947439+00:00
-- url     : https://prove2.me/submissions/2d402261-81ed-4c6d-a1a8-d9115875ccb4

import Mathlib
namespace HardyFLocal
open scoped Matrix

end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {D K T R : Type} [Fintype D] [Fintype K] [Fintype T]
    (w : K → T → ℝ) (hw : LinearIndependent ℝ w) (state : R → (D → K) → ℝ)
    (realize : ∀ t : D → T, ∃ s : R, ∀ k, state s k = ∏ d, w (k d) (t d)) :
    Submodule.span ℝ (Set.range state) = ⊤ := by
  classical
  let F := Fintype.linearCombination ℝ w
  have inj : Function.Injective F := fun a b h => funext (Fintype.linearIndependent_iffₛ.mp hw a b h)
  obtain ⟨G,hG⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr inj)
  let d (k : K) (t : T) := G (Pi.single t 1) k
  have dual (j k : K) : ∑ t, d j t * w k t = if j = k then 1 else 0 := by
    have basis (x : T → ℝ) : x = ∑ t, x t • Pi.single t 1 := by
      funext i
      simp [Pi.single_apply]
    have g (x : T → ℝ) : G x j = ∑ t, d j t * x t := by
      conv_lhs => rw [basis x]
      simp [map_smul,d,mul_comm]
    have fb : F (Pi.single k 1) = w k := by simp [F, Fintype.linearCombination_apply,Pi.single_apply]
    have hj := congrFun (LinearMap.congr_fun hG (Pi.single k 1)) j
    rw [LinearMap.comp_apply,fb,g] at hj
    simpa [Pi.single_apply,eq_comm] using hj
  choose s hs using realize
  let W := Submodule.span ℝ (Set.range state)
  have singleMem (j : D → K) : Pi.single j (1 : ℝ) ∈ W := by
    have recon : Pi.single j (1 : ℝ) = ∑ t : D → T, (∏ i, d (j i) (t i)) • state (s t) := by
      ext k
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hs,← Finset.prod_mul_distrib]
      rw [← Fintype.prod_sum (fun (i : D) (t : T) => d (j i) t * w (k i) t)]
      simp only [dual]
      by_cases h : j = k
      · subst k; simp
      · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
        simp [Ne.symm h]
    rw [recon]
    exact W.sum_mem fun _ _ => W.smul_mem _ (Submodule.subset_span (Set.mem_range_self _))
  apply top_unique
  intro a _
  have expansion : a = ∑ k, a k • Pi.single k 1 := by funext k; simp [Pi.single_apply]
  rw [expansion]
  exact W.sum_mem fun k _ => W.smul_mem _ (singleMem k)

