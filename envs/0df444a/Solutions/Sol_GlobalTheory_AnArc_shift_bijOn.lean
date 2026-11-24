-- Prove2me | solution 1 for GlobalTheory.AnArc.shift_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:42.258304+00:00
-- url     : https://prove2.me/submissions/5e04d7cb-9dbd-4d7b-aa3c-d64e5a1f6de6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_shift_mem_Theta
import Theorems.Thm_GlobalTheory_AnArc_shift_shift
import Theorems.Thm_GlobalTheory_AnArc_shift_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable (k : ℕ) [NeZero k]
namespace GlobalTheory.AnArc
theorem _root_.solution (la : A.La) (α : A.X) :
    Set.BijOn (A.shift k la α) (A.Theta k α) (A.Theta k (α + la.y)) := by
  refine ⟨fun th h => A.shift_mem_Theta h la, (A.shift_injective k la α).injOn, fun th h => ?_⟩
  have h1 := A.shift_mem_Theta h (-la)
  have h2 := A.shift_shift k la (-la) (α + la.y) th
  rw [La.neg_y, add_neg_cancel_right] at h1 h2
  rw [add_neg_cancel, shift_zero] at h2
  refine ⟨_, (A.Theta k α).smul_mem (Complex.exp (-(A.lin (-la) (A.P0 la) / k)))⁻¹ h1, ?_⟩
  rw [map_smul, h2, inv_smul_smul₀ (Complex.exp_ne_zero _)]
end GlobalTheory.AnArc
