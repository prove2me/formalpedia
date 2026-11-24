-- Prove2me | solution 1 for GlobalTheory.AnArc.linear_part_commutator_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:48.228338+00:00
-- url     : https://prove2.me/submissions/bfa9b049-e596-48d9-b6d5-df0d61e43ffe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_lin_Pw_sub
import Theorems.Thm_GlobalTheory_AnArc_Pw_zero

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
theorem _root_.solution (la la' : A.La) :
    A.lin la (A.P0 la') - A.lin la' (A.P0 la) = -(2 * Real.pi * Complex.I * A.EF la la') := by
  rw [← Pw_zero, lin_Pw_sub]
end GlobalTheory.AnArc
