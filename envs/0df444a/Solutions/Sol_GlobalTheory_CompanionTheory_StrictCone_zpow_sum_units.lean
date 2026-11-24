-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StrictCone.zpow_sum_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:49:19.715855+00:00
-- url     : https://prove2.me/submissions/631074c3-1d57-457c-ad98-1e278591e4ef

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone
namespace GlobalTheory.CompanionTheory.StrictCone
theorem _root_.solution (Q : ℂˣ) {n : ℕ} (e : Fin n → ℤ) : Q ^ (∑ i, e i) = ∏ i, Q ^ e i := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
end GlobalTheory.CompanionTheory.StrictCone
