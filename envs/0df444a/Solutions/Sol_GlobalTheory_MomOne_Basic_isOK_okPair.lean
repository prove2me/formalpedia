-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.isOK_okPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:12.245005+00:00
-- url     : https://prove2.me/submissions/cea7c194-be51-4c32-a9d0-a18157222f87

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
theorem _root_.solution (d : ℕ) (hd : 0 < d) :
    _root_.GlobalTheory.MomOne.IsOK d (_root_.GlobalTheory.MomOne.Basic.okPair d hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨u, v, by simp [_root_.GlobalTheory.MomOne.Basic.okPair]⟩
end _root_.GlobalTheory.MomOne.Basic
end GlobalTheory.MomOne.Basic
