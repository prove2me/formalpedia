-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.commute_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:34.780727+00:00
-- url     : https://prove2.me/submissions/42c6fe36-a53b-40b9-9f4c-0e6ac50e05f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.LocWeil GlobalTheory.LocWeil.DerComm
variable {S U : Type} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)
variable {β b b'}
variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}
omit [FiniteDimensional ℝ U]
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution {φ : ℝ → U →L[ℝ] U} {Y Z : U →L[ℝ] U} (h : HasDerivAt φ Y 0) (hc : ∀ t, Commute Z (φ t)) :
    Commute Z Y :=
  (h.const_mul Z).unique ((h.mul_const Z).congr_of_eventuallyEq (Eventually.of_forall fun t => hc t))
end GlobalTheory.LocWeil.DerComm
