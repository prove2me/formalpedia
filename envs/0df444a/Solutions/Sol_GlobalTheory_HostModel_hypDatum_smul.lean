-- Prove2me | solution 1 for GlobalTheory.HostModel.hypDatum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:11.31711+00:00
-- url     : https://prove2.me/submissions/81e0e596-b83c-48f1-a315-ad00f5703bab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ConjDual
namespace GlobalTheory.HostModel
theorem _root_.solution (H : Host E) (a x : 𝓞 E) (f : ConjDual H) :
    (a • (x, f) : (hypDatum H).La) = (a * x, a • f) := rfl
end GlobalTheory.HostModel
