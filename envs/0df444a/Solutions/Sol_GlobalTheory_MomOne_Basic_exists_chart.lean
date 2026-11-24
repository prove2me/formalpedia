-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:18:44.182882+00:00
-- url     : https://prove2.me/submissions/c624fe6f-7041-433f-bebb-9c379768c8c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Theorems.Thm_GlobalTheory_MomOne_Basic_hasDerivAt_u

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
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution (M : Mdl q) (h : M.Ok) : ∃ ℓ, M.Chart ℓ ∧ hat M.ι ℓ M.u = X := by
  set P := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hP
  have h0 : constantCoeff P = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hP, coeff_map, tay, coeff_mk]
    simp [Mdl.u]
  have h1 : IsUnit (coeff 1 P) := by
    rw [hP, coeff_map, tay, coeff_mk]
    simp [(hasDerivAt_u M h.1).deriv, h.1]
  have e : hat M.ι (P.substInvOfIsUnit h1) M.u = X := subst_substInvOfIsUnit_right P h0 h1
  refine ⟨P.substInvOfIsUnit h1, ⟨h, constantCoeff_substInvOfIsUnit _ _, ?_, ?_⟩, e⟩
  · intro n; rw [e, coeff_X]; split_ifs <;> simp
  · rw [e]; simp
end GlobalTheory.MomOne.Basic
