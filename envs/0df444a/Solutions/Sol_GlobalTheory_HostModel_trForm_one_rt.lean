-- Prove2me | solution 1 for GlobalTheory.HostModel.trForm_one_rt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:45.650179+00:00
-- url     : https://prove2.me/submissions/e4bbb83f-b875-497b-a939-256b70e3fd71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Theorems.Thm_GlobalTheory_HostModel_trForm_bar_bar

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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HostModel
theorem _root_.solution (H : Host E) : trForm H 1 H.rt = 0 := by
  have h := trForm_bar_bar H 1 H.rt
  rw [map_one, bar_rt, map_neg] at h
  omega
end GlobalTheory.HostModel
