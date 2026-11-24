-- Prove2me | solution 1 for GlobalTheory.AnArc.map_eq_sum_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:12.707856+00:00
-- url     : https://prove2.me/submissions/3216d342-c33b-4be4-a01e-e78faeb22540

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
namespace GlobalTheory.AnArc
theorem _root_.solution {M : Type} [Ring M] (f : A.X →+ M) (y : A.X) :
    f y = ∑ i, ((Module.Free.chooseBasis ℤ A.X).repr y i : M) * f (Module.Free.chooseBasis ℤ A.X i) := by
  conv_lhs => rw [← (Module.Free.chooseBasis ℤ A.X).sum_repr y]
  simp only [map_sum, map_zsmul, zsmul_eq_mul]
end GlobalTheory.AnArc
