-- Prove2me | solution 1 for GlobalTheory.weighted_sum_piFinset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:39.66884+00:00
-- url     : https://prove2.me/submissions/e7167554-a688-42da-ab4a-2cc4939bd3f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPiFinsetFinSuccCons
import Theorems.Thm_GlobalTheory_weighted_sum_piFinset_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution : ∀ (ι α K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] (G : (α → K) → Prop) (S S' : Finset α) (w w' : K), (∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) → ∀ F : (ι → α) → K, (∀ (t : ι → α) (i : ι), G (fun a => F (Function.update t i a))) → w ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S), F t = w' ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S'), F t := by
  intro ι α K _ _ _ G S S' w w' h F hF
  let e := Fintype.equivFin ι
  have key : ∀ T : Finset α, ∑ t ∈ Fintype.piFinset (fun _ : ι => T), F t =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin (Fintype.card ι) => T), F (t ∘ e) := by
    intro T
    symm
    refine Finset.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl α)) ?_ ?_
    · intro t
      simp only [Fintype.mem_piFinset, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
        Function.comp, id]
      exact ⟨fun H i => H _, fun H i => by simpa using H (e.symm i)⟩
    · intro t _
      rfl
  rw [key, key]
  refine weighted_sum_piFinset_fin G S S' w w' h _ (fun t => F (t ∘ e)) ?_
  intro t i
  simp only [Function.update_comp_equiv]
  exact hF _ _
end GlobalTheory
