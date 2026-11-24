-- Prove2me | solution 1 for GlobalTheory.AnArc.dualForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:00.118165+00:00
-- url     : https://prove2.me/submissions/8ac18d16-fe75-4d5a-872d-5e396b60b0c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal

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
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
open Classical
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (r r' : A.X →+ ℂ) :
    A.dualForm w r r' = A.coord r ⬝ᵥ ((A.BwMat w)⁻¹.map Complex.ofReal) *ᵥ star (A.coord r') := rfl
end GlobalTheory.AnArc
