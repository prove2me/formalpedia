-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.disc_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:10.69525+00:00
-- url     : https://prove2.me/submissions/79487a12-10b3-4d23-8196-cb3938d5039a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber

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
    (_root_.GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (_root_.GlobalTheory.periodPairOfTau τ).g₃ ^ 2
      ≠ 0 := by
  rw [← _root_.GlobalTheory.latticeCurve_Δ]
  exact _root_.GlobalTheory.latticeCurve_Δ_ne_zero _
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
