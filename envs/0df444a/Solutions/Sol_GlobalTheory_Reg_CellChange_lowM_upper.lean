-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.lowM_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:11.685947+00:00
-- url     : https://prove2.me/submissions/a53a75d3-5990-46d5-b8f2-aa137179bdcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.CellChange
open Matrix
variable {T S S' : Type} [CommRing S] [CommRing S'] {r : T → ℕ}
namespace GlobalTheory.Reg.CellChange
theorem _root_.solution (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) (i j : Fin (r τ))
    (h : i < j) : lowM x τ i j = 0 := by
  simp [lowM, h.not_gt, h.ne']
end GlobalTheory.Reg.CellChange
