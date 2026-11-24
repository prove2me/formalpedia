-- Prove2me | solution 1 for GlobalTheory.AnArc.psi_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:41.361728+00:00
-- url     : https://prove2.me/submissions/ee6c2bde-f114-4dc0-ba83-310ad5616541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (μ : A.X) : (A.psi μ : ℂ) ^ 2 = eTwoPi (A.T μ μ) := by
  have h := A.psi_add μ (-μ)
  rw [add_neg_cancel, psi_zero, A.psi_neg, map_neg, Units.val_one] at h
  have h2 := e_add (A.T μ μ) (-A.T μ μ)
  rw [add_neg_cancel, e_zero] at h2
  exact mul_right_cancel₀ (e_ne_zero (-A.T μ μ)) (by rw [← h2, h]; ring)
end GlobalTheory.AnArc
