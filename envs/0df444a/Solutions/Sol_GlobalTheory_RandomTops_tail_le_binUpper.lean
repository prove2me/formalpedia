-- Prove2me | solution 1 for GlobalTheory.RandomTops.tail_le_binUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:02.227998+00:00
-- url     : https://prove2.me/submissions/4b51c934-f308-4e24-817b-2342ae7d9c9b

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_pos
import Theorems.Thm_GlobalTheory_RandomTops_ind_nonneg
import Theorems.Thm_GlobalTheory_RandomTops_ind_le
import Theorems.Thm_GlobalTheory_RandomTops_ex_mono
import Theorems.Thm_GlobalTheory_RandomTops_ex_restrict
import Theorems.Thm_GlobalTheory_RandomTops_tail_eq

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
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ} {G : ℕ} (hA : A.card ≤ G)
    (K : ℕ) : ex δ A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by
  obtain ⟨A', hAA', hA'⟩ := Infinite.exists_superset_card_eq A G hA
  calc ex δ A (fun T => ind (K ≤ #T)) = ex δ A' (fun T => ind (K ≤ #(T ∩ A))) :=
      (ex_restrict hAA' (fun T => ind (K ≤ #T))).symm
    _ ≤ ex δ A' (fun T => ind (K ≤ #T)) := ex_mono h0 h1 fun T _ =>
      ind_le (ind_nonneg _) fun h => (ind_pos (le_trans h (card_le_card inter_subset_left))).ge
    _ = binUpper G δ K := by rw [tail_eq, hA']
end GlobalTheory.RandomTops
