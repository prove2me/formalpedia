-- Prove2me | solution 1 for GlobalTheory.HostModel.hypJ_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:16.056218+00:00
-- url     : https://prove2.me/submissions/709d9ddf-05f4-44d6-a4c0-55a43d49ef9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Theorems.Thm_GlobalTheory_HostModel_hypJ_inl

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
theorem _root_.solution (H : Host E) (x : 𝓞 E) :
    hypJ H (1 ⊗ₜ (0, traceDual H x)) = -(1 ⊗ₜ (x, 0)) := by
  rw [← hypJ_inl, hypJ_hypJ]
end GlobalTheory.HostModel
