-- Prove2me | solution 1 for GlobalTheory.UpperHalfImaginaryForm.imForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:22.050093+00:00
-- url     : https://prove2.me/submissions/040676c6-ff69-4409-9e24-b879698ef648

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpperHalfImaginaryForm
open ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.UpperHalfImaginaryForm
theorem _root_.solution (x y : EuclideanSpace ℂ ι) : imForm x y = (Hf x y).im := rfl
end GlobalTheory.UpperHalfImaginaryForm
