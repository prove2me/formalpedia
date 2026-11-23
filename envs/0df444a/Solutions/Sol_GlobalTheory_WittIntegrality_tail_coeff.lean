-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.tail_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:03.1134+00:00
-- url     : https://prove2.me/submissions/07011eb7-cf3f-4df4-9854-f3cecdb62924

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable [CharP C p]
variable [PerfectRing C p]
namespace GlobalTheory.WittIntegrality
theorem _root_.solution (x : WittVector p C) (k : ℕ) : x.coeff (k + 1) = (tail x).coeff k ^ p := by
  simp only [tail, WittVector.coeff_mk, frobeniusEquiv_symm_pow_p]
end GlobalTheory.WittIntegrality
