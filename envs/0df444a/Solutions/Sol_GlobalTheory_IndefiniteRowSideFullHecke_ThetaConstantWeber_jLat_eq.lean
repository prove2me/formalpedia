-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.jLat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:15.168918+00:00
-- url     : https://prove2.me/submissions/e11c5754-213a-4435-9152-3bb34ea31f5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Theorems.Thm_P2M_GlobalTheory_latticeCurve_c__6ffa6b5cc0c0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
theorem _root_.solution (τ : ℍ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.jLat τ = 1728 * (_root_.GlobalTheory.periodPairOfTau τ).g₂ ^ 3 /
    ((_root_.GlobalTheory.periodPairOfTau τ).g₂ ^ 3 -
      27 * (_root_.GlobalTheory.periodPairOfTau τ).g₃ ^ 2) := by
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.jLat, WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', _root_.GlobalTheory.latticeCurve_c₄,
    _root_.GlobalTheory.latticeCurve_Δ]
  ring
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
