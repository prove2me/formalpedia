-- Prove2me | solution 1 for GlobalTheory.DiffLin.fst_dualLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:03.173998+00:00
-- url     : https://prove2.me/submissions/7292c173-4a19-42e0-bb62-7eb705cec483

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsDiffSumSmulOfIsLieComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.DiffLin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.DiffLin
theorem _root_.solution (t : Fin n → R) (y : JetR R (Fin n) 1) :
    (dualLift t y).fst = jetAug R (Fin n) 1 y :=
  AlgHom.congr_fun (fstD_comp_dualLift t) y
end GlobalTheory.DiffLin
