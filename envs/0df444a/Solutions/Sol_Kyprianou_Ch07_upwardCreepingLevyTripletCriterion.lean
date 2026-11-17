-- Prove2me | solution 1 for Kyprianou.Ch07.upwardCreepingLevyTripletCriterion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:33:49.2097+00:00
-- url     : https://prove2.me/submissions/6e48eb8e-dcb3-4313-8a0b-0d1ec60fab2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_boundedVariationDriftUpwardCreeping
import Theorems.Thm_Kyprianou_Ch07_gaussianComponentUpwardCreeping
import Theorems.Thm_Kyprianou_Ch07_infiniteVariationPureJumpCriterionUpwardCreeping
import Theorems.Thm_Kyprianou_Ch07_upwardCreepingRequiresTripletCriterion
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi) :
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    let unboundedPureJump : Prop :=
      sigma2 = 0 ∧ ¬ finiteVariationJumpMass
    let mixedJumpCriterion : Prop :=
      (∫⁻ x : Real in Set.Ioo 0 1,
         (ENNReal.ofReal x * Pi (Set.Ioi x)) /
         (∫⁻ u : Real in Set.Ioo 0 x,
            Pi (Set.Ioo (-1) (-u)) ∂volume) ∂volume) < ⊤
    (0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) 1 ↔
      ((sigma2 = 0 ∧ finiteVariationJumpMass ∧ 0 < canonicalDrift) ∨
       (0 < sigma2) ∨
       (unboundedPureJump ∧ mixedJumpCriterion))) := by
  dsimp only
  constructor
  · exact Kyprianou.Ch07.upwardCreepingRequiresTripletCriterion P X b sigma2 Pi hX hNonCompound hTriplet
  · intro h
    rcases h with hBV | hGaussian | hJump
    · exact Kyprianou.Ch07.boundedVariationDriftUpwardCreeping P X b sigma2 Pi hX hNonCompound hTriplet hBV
    · exact Kyprianou.Ch07.gaussianComponentUpwardCreeping P X b sigma2 Pi hX hNonCompound hTriplet hGaussian
    · exact Kyprianou.Ch07.infiniteVariationPureJumpCriterionUpwardCreeping P X b sigma2 Pi hX hNonCompound hTriplet hJump
