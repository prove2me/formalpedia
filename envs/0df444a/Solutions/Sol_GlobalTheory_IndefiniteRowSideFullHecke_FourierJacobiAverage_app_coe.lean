-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:37.210386+00:00
-- url     : https://prove2.me/submissions/8d32e229-8948-4345-a3d1-23b775431cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
theorem _root_.solution (l : SB X →ₗ[ℂ] V) (f : SB X) : app l (f : X → ℂ) = l f := by
  rw [app, dif_pos f.2]
end GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
