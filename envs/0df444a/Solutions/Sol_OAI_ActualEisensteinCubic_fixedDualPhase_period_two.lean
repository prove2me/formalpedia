-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.fixedDualPhase_period_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:32.812518+00:00
-- url     : https://prove2.me/submissions/d809c34a-3088-400f-a0c9-583d9416ba00

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
namespace RationalQuant
end RationalQuant
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
namespace RationalPrimeExtraction
end RationalPrimeExtraction
open ActualEisensteinCubic ShortDraftLatticeCount
namespace RationalPrimeExtraction
open ActualEisensteinCubic ShortDraftLatticeCount
end RationalPrimeExtraction
namespace OscSpecial
end OscSpecial
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
private theorem breveE_period_div_lam_O (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam) = 1 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz, eisEmbedding_eval]
  exact ConcreteBreveE.breveE_period_coordinates a b
end ActualEisensteinCubic
namespace OscSpecial
open scoped Topology
open Filter
end OscSpecial
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (c y w : O) :
    fixedDualPhase c (y + 2*w) = fixedDualPhase c y := by
  let d : O := -(c * (y*w+w^2))
  have hO : -(c * (y + 2*w)^2) = -(c*y^2) + 4*d := by
    dsimp [d]
    ring
  have h4 : eisEmbedding (4*d) = 4 * eisEmbedding d := by
    simp only [map_mul, map_ofNat]
  have harg :
      eisEmbedding (-(c * (y + 2*w)^2)) / eisLam / (4 : ℂ) =
        eisEmbedding (-(c*y^2)) / eisLam / (4 : ℂ) +
          eisEmbedding d / eisLam := by
    rw [hO, map_add, h4]
    ring
  unfold fixedDualPhase
  rw [harg, AddChar.map_add_eq_mul, breveE_period_div_lam_O, mul_one]
end OAI.ActualEisensteinCubic
