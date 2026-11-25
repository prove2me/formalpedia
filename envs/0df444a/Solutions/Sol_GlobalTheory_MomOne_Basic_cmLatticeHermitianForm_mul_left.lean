-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.cmLatticeHermitianForm_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:25.991576+00:00
-- url     : https://prove2.me/submissions/00be9f30-74a3-449d-a47a-c317468fb1f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
open PowerSeries
open scoped ComplexConjugate
variable {q : ℕ} [Fact q.Prime]
open Filter Topology
namespace GlobalTheory.MomOne.Basic
namespace _root_.GlobalTheory.MomOne.Basic
theorem _root_.solution (d : ℕ) (a z w : ℂ) :
    _root_.GlobalTheory.MomOne.h1 d (a * z) w = a * _root_.GlobalTheory.MomOne.h1 d z w := by
  unfold _root_.GlobalTheory.MomOne.h1; ring
end _root_.GlobalTheory.MomOne.Basic
end GlobalTheory.MomOne.Basic
