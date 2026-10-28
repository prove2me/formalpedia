-- Prove2me | solution 1 for MazurProof.N13InfinityLineSpecialRestriction.map_pointIdeal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:28:39.383449+00:00
-- url     : https://prove2.me/submissions/13ad1b84-d739-4f18-9089-584e7c45ddf4

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13InfinityLineSpecialRestriction
open Polynomial
attribute [local instance] MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
theorem solution (P : IntegralInfinityPoint) : Ideal.map N13IntegralInfinityReduction.reduceCoordinate (N13IntegralInfinityPointSpread.pointIdeal P) = N13SpecialDivisorCharts.infinityPointIdeal (N13IntegralInfinityReduction.reduceBase P.1.1) (N13IntegralInfinityReduction.reduceBase P.1.2) := by
  have h1 : N13IntegralInfinityReduction.reduceCoordinate
      (N13IntegralInfinityPointSpread.xClassHom (N13IntegralInfinityPointSpread.pointU P)) =
      N13SpecialInfinityChart.tClass -
        algebraMap _ N13SpecialDivisorCharts.SpecialInfinity
          (C (N13IntegralInfinityReduction.reduceBase P.1.1)) := by
    unfold N13IntegralInfinityReduction.reduceCoordinate N13IntegralInfinityPointSpread.xClassHom
      N13IntegralInfinityPointSpread.pointU N13SpecialInfinityChart.tClass
    rw [AdjoinRoot.map_of]
    simp [N13IntegralInfinityReduction.reducePoly, AdjoinRoot.algebraMap_eq]
  have h2 : N13IntegralInfinityReduction.reduceCoordinate
      (GeneralizedGraphIdealCore.ySubClass N13IntegralInfinityPointSpread.xClassHom
        N13IntegralInfinityPointSpread.yClass (N13IntegralInfinityPointSpread.pointV P)) =
      N13SpecialInfinityChart.vClass -
        algebraMap _ N13SpecialDivisorCharts.SpecialInfinity
          (C (N13IntegralInfinityReduction.reduceBase P.1.2)) := by
    unfold N13IntegralInfinityReduction.reduceCoordinate N13IntegralInfinityPointSpread.xClassHom
      N13IntegralInfinityPointSpread.pointV GeneralizedGraphIdealCore.ySubClass
      N13IntegralInfinityPointSpread.yClass N13IntegralInfinityChart.vClass
      N13SpecialInfinityChart.vClass
    rw [map_sub, AdjoinRoot.map_of, AdjoinRoot.map_root]
    simp [N13IntegralInfinityReduction.reducePoly, AdjoinRoot.algebraMap_eq]
  unfold N13IntegralInfinityPointSpread.pointIdeal GeneralizedGraphIdealCore.graphIdeal
    N13SpecialDivisorCharts.infinityPointIdeal
  rw [Ideal.map_span, Set.image_pair, h1, h2]
