-- Prove2me | solution 1 for GlobalTheory.exists_joint_int_eigenvector_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:25.015808+00:00
-- url     : https://prove2.me/submissions/fd76f650-459f-4c62-94d6-43e2fbe165ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsJointIntEigenvectorOfStable
import Theorems.Thm_GlobalTheory_exists_int_eigenvector_of_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (f : ι → Module.End K V) (hc : ∀ a b, f a * f b = f b * f a)
    (hf : ∀ a, ⨆ n : ℤ, (f a).eigenspace (n : K) = ⊤)
    (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, f a x ∈ W) (hW0 : W ≠ ⊥) :
    ∃ κ : ι → ℤ, ∃ u ∈ W, u ≠ 0 ∧ ∀ a, f a u = (κ a : K) • u := by
  classical
  have key : ∀ s : Finset ι, ∃ U : Submodule K V, U ≤ W ∧ U ≠ ⊥ ∧ (∀ a, ∀ x ∈ U, f a x ∈ U) ∧
      ∃ κ : ι → ℤ, ∀ a ∈ s, ∀ x ∈ U, f a x = (κ a : K) • x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨W, le_rfl, hW0, hW, 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨U, hUW, hU0, hU, κ, hκ⟩ := ih
      obtain ⟨n, u, huU, hu0, hu⟩ := exists_int_eigenvector_of_stable (f a) (hf a) U (hU a) hU0
      refine ⟨U ⊓ (f a).eigenspace (n : K), inf_le_left.trans hUW, ?_, ?_,
        Function.update κ a n, ?_⟩
      · rw [Submodule.ne_bot_iff]
        exact ⟨u, ⟨huU, Module.End.mem_eigenspace_iff.mpr hu⟩, hu0⟩
      · intro b x hx
        refine ⟨hU b x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 := Module.End.mem_eigenspace_iff.mp hx.2
        have h2 := LinearMap.congr_fun (hc a b) x
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb x hx
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [Function.update_self]; exact Module.End.mem_eigenspace_iff.mp hx.2
        · have : b ≠ a := fun h => ha (h ▸ hb)
          rw [Function.update_of_ne this]; exact hκ b hb x hx.1
  obtain ⟨U, hUW, hU0, -, κ, hκ⟩ := key Finset.univ
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨κ, x, hUW hxU, hx0, fun a => hκ a (Finset.mem_univ a) x hxU⟩
end GlobalTheory
