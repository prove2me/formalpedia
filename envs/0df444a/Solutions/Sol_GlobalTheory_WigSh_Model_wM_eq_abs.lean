-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.wM_eq_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:40.385552+00:00
-- url     : https://prove2.me/submissions/60ba27a3-640c-40bb-ae59-5414bf1d4ac2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Theorems.Thm_GlobalTheory_WigSh_Model_wM_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.Model
namespace GlobalTheory.WigSh.Model
theorem _root_.solution {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) (β : ℝ)
    (u : Fin (n + 1) → ℝ) (ρ : Fin n → ℝ)
    (hu : ∀ j, (L j : ℝ) = u j - (n : ℝ) / 2 - β)
    (hρ : ∀ j, (M j : ℝ) = ρ j - ((n : ℝ) - 1) / 2 - β) (l : Fin (n + 1)) :
    wM L M l = (∏ i, |u l - 1 / 2 - ρ i|) / ∏ i ∈ univ.erase l, |u l - u i| := by
  rw [← abs_of_nonneg (wM_nonneg h l)]
  unfold GlobalTheory.WigSh.wM
  rw [abs_div, Finset.abs_prod, Finset.abs_prod]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_
  · rw [hρ, hu, ← abs_neg]
    congr 1
    ring
  · rw [hu i, hu l, ← abs_neg]
    congr 1
    ring
end GlobalTheory.WigSh.Model
