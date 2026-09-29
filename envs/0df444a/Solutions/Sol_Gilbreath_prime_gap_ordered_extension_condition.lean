-- Prove2me | solution 1 for Gilbreath.prime_gap_ordered_extension_condition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T00:57:29.513569+00:00
-- url     : https://prove2.me/submissions/76de0cfd-82fb-46c4-ac69-402f36aef0e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_gilbreath_finite_extension
import Theorems.Thm_Gilbreath_extension_interval_criterion
import Theorems.Thm_Gilbreath_prime_gap_extension_fold_characterization

theorem solution (b : ℕ → ℕ)
    (hb : ∀ n, Gilbreath.d 1 (n + 1) = 2 * b n) (n : ℕ)
    (hprefix : ∀ j, j < n → Gilbreath.iterAbsDiff b j 0 ≤ 1) :
    Gilbreath.ExtensionComplete (Gilbreath.extensionBoundary b n) := by
  exact (Gilbreath.extension_interval_criterion _).mp
    (Gilbreath.prime_gap_extension_fold_characterization b hb n hprefix)
