-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_dual_quadratic_real_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:26:24.317216+00:00
-- url     : https://prove2.me/submissions/bf606e0f-0a83-42b8-8fbc-e1351bfdf30f

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_ActualEisensteinCubic_dual_quadratic_trace_coeff
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_real_trace_of_O
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
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
namespace OscSpecial
end OscSpecial
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
private theorem coords_neg_second (z : O) :
    (ActualEisensteinCoordinates.coords (-z)).2 =
      -(ActualEisensteinCoordinates.coords z).2 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hneg : -ActualEisensteinCoordinates.eval a b =
      ActualEisensteinCoordinates.eval (-a) (-b) := by
    simp only [ActualEisensteinCoordinates.eval]
    push_cast
    ring
  rw [hneg, ShortDraftLatticeCount.coords_eval,
    ShortDraftLatticeCount.coords_eval]
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
open scoped Topology
open Filter
end OscSpecial
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  rw [breveE_real_trace_of_O]
  have hneg : (ActualEisensteinCoordinates.coords
      (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2))).2 =
      -((a-b)*k^2+2*a*k*l+b*l^2) := by
    have hp := dual_quadratic_trace_coeff a b k l
    rw [coords_neg_second]
    simpa using congrArg Neg.neg hp
  rw [hneg]
  congr 1
  push_cast
  ring_nf
end OAI.ActualEisensteinCubic
