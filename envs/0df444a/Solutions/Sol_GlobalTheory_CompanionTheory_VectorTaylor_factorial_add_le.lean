-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VectorTaylor.factorial_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:22.229439+00:00
-- url     : https://prove2.me/submissions/13e1a692-505a-4f9a-8b1b-959d947e660d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticOrthogonalVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VectorTaylor
open Filter Topology
namespace GlobalTheory.CompanionTheory.VectorTaylor
theorem _root_.solution (k n : ℕ) :
    ((k + n).factorial : ℝ) ≤ 2 ^ (k + n) * k.factorial * n.factorial := by
  have h1 : (k + n).factorial = (k + n).choose n * k.factorial * n.factorial :=
    (Nat.add_choose_mul_factorial_mul_factorial k n).symm
  have h2 : (k + n).choose n ≤ 2 ^ (k + n) := Nat.choose_le_two_pow _ _
  have h3 : (k + n).factorial ≤ 2 ^ (k + n) * k.factorial * n.factorial := by
    rw [h1]
    gcongr
  exact_mod_cast h3
end GlobalTheory.CompanionTheory.VectorTaylor
