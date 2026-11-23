-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.lowM_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:58.805799+00:00
-- url     : https://prove2.me/submissions/85936500-57e2-4180-8816-6b2b79989fc7

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
theorem _root_.solution (f : S →+* S') (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) :
    (lowM x τ).map f = lowM (fun v => f (x v)) τ := by
  ext i j
  simp only [lowM, Matrix.map_apply]
  split_ifs <;> simp
end GlobalTheory.Reg.CellChange
