-- Prove2me | solution 1 for GlobalTheory.HostModel.hypDatum_EF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:49:24.76461+00:00
-- url     : https://prove2.me/submissions/3c089897-ac22-4b40-b29a-38ed32bcf27f

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
theorem _root_.solution (H : Host E) (x y : 𝓞 E) (f g : ConjDual H) :
    (hypDatum H).EF (x, f) (y, g) = toDual H f y - toDual H g x := rfl
end GlobalTheory.HostModel
