-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisPositiveAggregationKernel.cellPositive_of_allLeaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:30:53.632713+00:00
-- url     : https://prove2.me/submissions/5ebc0db3-16bc-4f8d-8217-82ed67a58197

import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_reusable_cell_interface
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneContinuity

section
namespace GeneralCK.Certificates.E8TAxisPartitionKernel

open GeneralCK
















theorem locate_leaf {P : Rect → Prop} {tree : Tree} {r : Rect} {s t : ℝ}
    (hall : AllLeaves P tree r) (hpoint : r.Covers s t) :
    ∃ leaf, P leaf ∧ leaf.Covers s t := by
  induction tree generalizing r with
  | leaf => exact ⟨r, hall, hpoint⟩
  | splitS x left right ihl ihr =>
      rcases hall with ⟨hx0, hx1, hl, hr⟩
      by_cases hs : s ≤ (x : ℝ)
      · apply ihl hl
        exact ⟨hpoint.1, hs, hpoint.2.2⟩
      · apply ihr hr
        exact ⟨le_of_not_ge hs, hpoint.2.1, hpoint.2.2⟩
  | splitT x lower upper ihl ihu =>
      rcases hall with ⟨hx0, hx1, hl, hu⟩
      by_cases ht : t ≤ (x : ℝ)
      · apply ihl hl
        exact ⟨hpoint.1, hpoint.2.1, hpoint.2.2.1, ht⟩
      · apply ihu hu
        exact ⟨hpoint.1, hpoint.2.1, le_of_not_ge ht, hpoint.2.2.2⟩










end GeneralCK.Certificates.E8TAxisPartitionKernel
end

section
namespace GeneralCK.Certificates.E8TAxisPositiveAggregationKernel

open E8TAxisPartitionKernel















end GeneralCK.Certificates.E8TAxisPositiveAggregationKernel
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisPositiveAggregationKernel
open E8TAxisPartitionKernel
theorem solution {tree : Tree} {r : Rect}
    (h : AllLeaves CellPositive tree r) : CellPositive r := by
  intro s t hadm hcover
  obtain ⟨leaf, hleaf, hpoint⟩ := locate_leaf h hcover
  exact hleaf s t hadm hpoint
