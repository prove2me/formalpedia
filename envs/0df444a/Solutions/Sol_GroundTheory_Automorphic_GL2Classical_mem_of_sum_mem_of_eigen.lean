-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.mem_of_sum_mem_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:18.462923+00:00
-- url     : https://prove2.me/submissions/a20fdd46-c3b9-4abe-a2f7-c3042b20a284

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_WeightOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GL2Classical
variable {E : Type*} [AddCommGroup E] [Module ℂ E] {Rr Ll Jj : Module.End ℂ E}
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution {W : Submodule ℂ E} (hW : ∀ v ∈ W, Jj v ∈ W) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) : ∀ (v : ι → E) (μ : ι → ℂ), (∀ i ∈ s, Jj (v i) = μ i • v i) → Set.InjOn μ s →
      ∑ i ∈ s, v i ∈ W → ∀ i ∈ s, v i ∈ W := by
  induction s using Finset.induction_on with
  | empty => intro v μ _ _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro v μ hv hμ hsum
    rw [Finset.sum_insert ha] at hsum

    have hJs : ∑ i ∈ s, (μ i - μ a) • v i ∈ W := by
      have h1 : Jj (v a + ∑ i ∈ s, v i) - μ a • (v a + ∑ i ∈ s, v i) ∈ W :=
        sub_mem (hW _ hsum) (Submodule.smul_mem _ _ hsum)
      have e : Jj (v a + ∑ i ∈ s, v i) - μ a • (v a + ∑ i ∈ s, v i) = ∑ i ∈ s, (μ i - μ a) • v i := by
        rw [map_add, map_sum, hv a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum]
        rw [Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem hi)]
        simp only [sub_smul, Finset.sum_sub_distrib]
        abel
      rwa [e] at h1
    have hs' := ih (fun i => (μ i - μ a) • v i) μ
      (fun i hi => by rw [map_smul, hv i (Finset.mem_insert_of_mem hi), smul_comm])
      (hμ.mono (Finset.coe_subset.2 (Finset.subset_insert a s))) hJs
    have hvs : ∀ i ∈ s, v i ∈ W := by
      intro i hi
      have hne : μ i - μ a ≠ 0 := sub_ne_zero.2 fun h =>
        ha (hμ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) h ▸ hi)
      have := Submodule.smul_mem W (μ i - μ a)⁻¹ (hs' i hi)
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · have := sub_mem hsum (Submodule.sum_mem W hvs)
      rwa [add_sub_cancel_right] at this
    · exact hvs i hi
end GroundTheory.Automorphic.GL2Classical
