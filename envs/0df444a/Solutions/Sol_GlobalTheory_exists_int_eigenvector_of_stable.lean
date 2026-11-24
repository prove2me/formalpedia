-- Prove2me | solution 1 for GlobalTheory.exists_int_eigenvector_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:33.79236+00:00
-- url     : https://prove2.me/submissions/0260917b-35d7-4ad4-bdfb-e4805efb9cee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsJointIntEigenvectorOfStable

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
theorem _root_.solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : ⨆ n : ℤ, f.eigenspace (n : K) = ⊤)
    (U : Submodule K V) (hU : ∀ x ∈ U, f x ∈ U) (hU0 : U ≠ ⊥) :
    ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
  classical
  have key : ∀ s : Finset ℤ, ∀ x ∈ U, x ≠ 0 → x ∈ (⨆ n ∈ s, f.eigenspace (n : K)) →
      ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx0 hx; simp at hx; exact absurd hx hx0
    | insert a s _ ih =>
      intro x hxU hx0 hx
      by_cases hw : f x - (a : K) • x = 0
      · exact ⟨a, x, hxU, hx0, sub_eq_zero.mp hw⟩
      · refine ih _ (U.sub_mem (hU x hxU) (U.smul_mem _ hxU)) hw ?_
        rw [Finset.iSup_insert, Submodule.mem_sup] at hx
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        rw [Module.End.mem_eigenspace_iff] at hy
        have h1 : f (y + z) - (a : K) • (y + z) = f z - (a : K) • z := by
          rw [map_add, hy, smul_add]; abel
        rw [h1]
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hz)
        have : (⨆ n ∈ s, f.eigenspace (n : K)) ≤ (⨆ n ∈ s, f.eigenspace (n : K)).comap f := by
          refine iSup₂_le fun n hn => ?_
          intro w hw
          rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.mp hw]
          exact Submodule.smul_mem _ _
            (le_iSup₂ (f := fun n (_ : n ∈ s) => f.eigenspace (n : K)) n hn hw)
        exact this hz
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hx : x ∈ ⨆ n : ℤ, f.eigenspace (n : K) := by rw [hf]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  exact key s x hxU hx0 hs
end GlobalTheory
