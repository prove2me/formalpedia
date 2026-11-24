-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.v_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:40:00.025489+00:00
-- url     : https://prove2.me/submissions/805427f9-d784-44d3-a8b0-3634c2f31843

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_v_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) : Valued.v (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [← zpow_natCast, v_zpow hϖ]
end GlobalTheory.InertZeta.RowSpan
