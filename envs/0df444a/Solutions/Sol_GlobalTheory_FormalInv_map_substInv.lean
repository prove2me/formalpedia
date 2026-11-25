-- Prove2me | solution 1 for GlobalTheory.FormalInv.map_substInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:49.200694+00:00
-- url     : https://prove2.me/submissions/e86644b0-9bce-4d19-997a-48051e80f58d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_eq_substInv_of_right
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply

set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}
namespace GlobalTheory.FormalInv
theorem _root_.solution {S : Type*} [CommRing S] (φ : R →+* S) (hu : ∀ i, constantCoeff (u i) = 0)
    (hA : IsUnit (linearPart u)) :
    (fun i => MvPowerSeries.map φ (substInv u i)) =
      substInv fun i => MvPowerSeries.map φ (u i) := by
  refine eq_substInv_of_right (fun i => by simp [hu i])
    (fun i => by simp [constantCoeff_substInv hu i]) fun i => ?_
  rw [← map_subst (hasSubst_substInv hu), subst_substInv_right hu hA, map_X]
end GlobalTheory.FormalInv
