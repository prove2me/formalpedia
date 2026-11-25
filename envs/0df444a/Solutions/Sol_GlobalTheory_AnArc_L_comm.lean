-- Prove2me | solution 1 for GlobalTheory.AnArc.L_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:34:29.854441+00:00
-- url     : https://prove2.me/submissions/cb95bb57-10b5-48f5-bd19-9f8d107f1786

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_lin_Pw_sub

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
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (la la' : A.La) (v : A.V) :
    (A.L w la (v + A.Pw w la') + A.L w la' v) - (A.L w la' (v + A.Pw w la) + A.L w la v) =
      -(2 * Real.pi * Complex.I * A.EF la la') := by
  rw [← A.lin_Pw_sub w]; simp only [L, map_add]; ring
end GlobalTheory.AnArc
