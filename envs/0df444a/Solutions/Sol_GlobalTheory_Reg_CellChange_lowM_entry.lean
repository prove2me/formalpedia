-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.lowM_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:11.00099+00:00
-- url     : https://prove2.me/submissions/57c8bc02-06ad-4a18-8b6c-a7d4665c02ba

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
theorem _root_.solution (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S)
    (v : Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) : lowM x v.1 v.2.1.2 v.2.1.1 = x v := by
  obtain ⟨τ, ⟨i, j⟩, h⟩ := v
  exact dif_pos h
end GlobalTheory.Reg.CellChange
