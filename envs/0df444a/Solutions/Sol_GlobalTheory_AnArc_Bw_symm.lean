-- Prove2me | solution 1 for GlobalTheory.AnArc.Bw_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:18:53.146164+00:00
-- url     : https://prove2.me/submissions/d509c405-957a-474e-b246-fd075e86a73f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_H_re_symm
import Theorems.Thm_GlobalTheory_AnArc_Bw_eq

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
theorem _root_.solution (w : ℂ) (y x : A.X) : A.Bw w y x = A.Bw w x y := by
  rw [Bw_eq, Bw_eq, A.T_symm, A.be_symm, H_re_symm]
end GlobalTheory.AnArc
