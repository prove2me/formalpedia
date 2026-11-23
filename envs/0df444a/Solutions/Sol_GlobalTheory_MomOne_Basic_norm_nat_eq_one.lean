-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.norm_nat_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:48.288153+00:00
-- url     : https://prove2.me/submissions/ebd25e1b-f03a-4e79-adba-113f0c4e94ac

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
theorem _root_.solution {m : ℕ} (h : Nat.Coprime q m) :
    ‖(m : ℂ_[q])‖ = 1 := by
  have h1 : (m : ℂ_[q]) = (((m : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact h
end _root_.GlobalTheory.MomOne.Basic
end GlobalTheory.MomOne.Basic
