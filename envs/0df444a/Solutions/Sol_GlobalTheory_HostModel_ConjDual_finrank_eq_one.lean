-- Prove2me | solution 1 for GlobalTheory.HostModel.ConjDual.finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:25.998568+00:00
-- url     : https://prove2.me/submissions/1c8812cf-f2fd-4019-b1fa-2633f8df6c44

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
namespace ConjDual
theorem _root_.solution (H : Host E) : finrank (𝓞 E) (ConjDual H) = 1 := by
  rw [← finrank_eq_of_injective _ (traceDual_injective H) finrank_int.symm, finrank_self]
end ConjDual
end GlobalTheory.HostModel
