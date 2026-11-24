-- Prove2me | solution 1 for GlobalTheory.SummableProdPi.summable_prod_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:46.152719+00:00
-- url     : https://prove2.me/submissions/3812e207-7c9b-4d94-8e60-3419f47938b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableProdPi
namespace GlobalTheory.SummableProdPi
theorem _root_.solution {J A : Type} [inst : Fintype J] (f : J → A → ℝ)
    (h0 : ∀ (j : J) (a : A), (0 : ℝ) ≤ f j a) (hs : ∀ j : J, Summable (f j)) :
    Summable fun (n : J → A) ↦ ∏ j : J, f j (n j) := by
  classical
  have hnn : ∀ n : J → A, 0 ≤ ∏ j : J, f j (n j) :=
    fun n => Finset.prod_nonneg fun j _ => h0 j (n j)
  refine summable_of_sum_le (c := ∏ j : J, ∑' a, f j a) hnn fun s => ?_
  have hsub : s ⊆ Fintype.piFinset (fun j : J => s.image (fun n : J → A => n j)) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_image_of_mem _ hn
  calc ∑ n ∈ s, ∏ j : J, f j (n j)
      ≤ ∑ n ∈ Fintype.piFinset (fun j : J => s.image (fun n : J → A => n j)),
          ∏ j : J, f j (n j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hnn n
    _ = ∏ j : J, ∑ a ∈ s.image (fun n : J → A => n j), f j a :=
        (Finset.prod_univ_sum (fun j : J => s.image (fun n : J → A => n j)) f).symm
    _ ≤ ∏ j : J, ∑' a, f j a := by
        apply Finset.prod_le_prod
        · intro j _
          exact Finset.sum_nonneg fun a _ => h0 j a
        · intro j _
          exact (hs j).sum_le_tsum _ fun a _ => h0 j a
end GlobalTheory.SummableProdPi
