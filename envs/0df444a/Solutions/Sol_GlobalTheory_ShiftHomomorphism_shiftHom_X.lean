-- Prove2me | solution 1 for GlobalTheory.ShiftHomomorphism.shiftHom_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:44.449635+00:00
-- url     : https://prove2.me/submissions/50f91aba-6af5-4904-9eee-e9226548ebb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ShiftHomomorphism
namespace GlobalTheory.ShiftHomomorphism
theorem _root_.solution (D : ℕ) (c : Fin D → ℂ) (i : Fin D) :
    shiftHom D c (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  simp [shiftHom]
end GlobalTheory.ShiftHomomorphism
