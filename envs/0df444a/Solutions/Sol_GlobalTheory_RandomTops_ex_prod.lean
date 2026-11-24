-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:19.99988+00:00
-- url     : https://prove2.me/submissions/6472e647-9422-4082-8892-5e71b6ab4d8b

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ex_congr
import Theorems.Thm_GlobalTheory_RandomTops_ex_const
import Theorems.Thm_GlobalTheory_RandomTops_ex_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution {ι : Type*} (J : Finset ι) (A : ι → Finset ℕ) (g : ι → Finset ℕ → ℝ)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) (S : Finset ℕ)
    (hS : ∀ j ∈ J, A j ⊆ S) :
    ex δ S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, ex δ (A j) (g j) := by
  classical
  revert hd S
  induction J using Finset.induction_on with
  | empty => intro _ S _; simp [ex_const]
  | insert j J hj ih =>
    intro hd S hS
    have hdj : ∀ i ∈ J, Disjoint (A i) (A j) := fun i hi =>
      hd i (mem_insert_of_mem hi) j (mem_insert_self j J) (fun h => hj (h ▸ hi))
    have hd' : ∀ i ∈ J, ∀ k ∈ J, i ≠ k → Disjoint (A i) (A k) := fun i hi k hk =>
      hd i (mem_insert_of_mem hi) k (mem_insert_of_mem hk)
    have hS' : ∀ i ∈ J, A i ⊆ S \ A j := by
      intro i hi x hx
      exact mem_sdiff.mpr ⟨hS i (mem_insert_of_mem hi) hx, fun hxj => disjoint_left.mp (hdj i hi) hx hxj⟩
    have e : ∀ T ⊆ S, ∏ i ∈ insert j J, g i (T ∩ A i) =
        g j (T ∩ A j) * ∏ i ∈ J, g i ((T \ A j) ∩ A i) := by
      intro T _
      rw [prod_insert hj]
      congr 1
      refine prod_congr rfl fun i hi => ?_
      congr 1
      ext x
      simp only [mem_inter, mem_sdiff]
      constructor
      · rintro ⟨hxT, hxi⟩
        exact ⟨⟨hxT, fun hxj => disjoint_left.mp (hdj i hi) hxi hxj⟩, hxi⟩
      · rintro ⟨⟨hxT, _⟩, hxi⟩
        exact ⟨hxT, hxi⟩
    rw [ex_congr e, ex_split (hS j (mem_insert_self j J)) (g j) (fun U => ∏ i ∈ J, g i (U ∩ A i)),
      ih hd' (S \ A j) hS', prod_insert hj]
end GlobalTheory.RandomTops
