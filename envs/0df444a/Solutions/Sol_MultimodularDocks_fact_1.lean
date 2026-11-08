-- Prove2me | solution 1 for MultimodularDocks.fact_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:11:08.116455+00:00
-- url     : https://prove2.me/submissions/b3648ad3-1440-4816-83a9-b8a5cd2809f6

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

open MultimodularDocks in
theorem solution (f : ℤ → ℤ → ℝ) (hf : IsMultimodular f) (n k : ℤ) (hk : 1 ≤ k)
    (hkn : k + 1 ≤ n) :
    2 * f (n - k) k ≤ f (n - k + 1) (k - 1) + f (n - k - 1) (k + 1) := by
  have h2 := hf.2.1 (n - k) k (by omega) hk
  have h3 := hf.2.2 (n - k) k (by omega) hk
  linarith
