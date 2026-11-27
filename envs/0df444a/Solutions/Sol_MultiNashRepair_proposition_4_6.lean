-- Prove2me | solution 1 for MultiNashRepair.proposition_4_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:00:56.484476+00:00
-- url     : https://prove2.me/submissions/466a11f3-4d65-4ab1-aa24-fa0236ba1497
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_MultiNashRepair_IDRH
import Theorems.Thm_MultiNashRepair_proposition_4_6_iterations
import Theorems.Thm_MultiNashRepair_proposition_4_6_machine

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Utility BoundedGame Table RawProfile encGame encProfile)
open MultiNashRepair

theorem solution (σ : ℚ) (hσ1 : 1 < σ) (hσ2 : (σ : ℝ) < sigmaStar)
    (ctrl : Controls σ) :
    (∃ N0 : ℕ, ∀ (m : ℕ) (n : Fin m → ℕ) (u : Utility n), ctrl.m0 ≤ m → (∀ i, 0 < n i) →
      BoundedGame u → ∀ (k : ℕ) (s : State n), Reach ctrl u k s → k ≤ N0) ∧
    (∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ), ∀ m : ℕ, 1 ≤ m → ∀ G : Table m,
      ∃ x : RawProfile m, x.sizes = G.sizes ∧
        CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
        IDRHOutput ctrl G.utility (x.on G.counts)) :=
  ⟨MultiNashRepair.proposition_4_6_iterations σ hσ1 hσ2 ctrl,
    MultiNashRepair.proposition_4_6_machine σ hσ1 hσ2 ctrl⟩
