-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_variable_kernel_eq_dualVarTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:43:43.679039+00:00
-- url     : https://prove2.me/submissions/ea45673a-2090-43ab-ba69-37bc6c587acb

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero
import Theorems.Thm_OAI_ActualEisensteinCubic_dual_gaussian_is_actual_trace_phase
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_OscSpecial_dualGaussian_eq_dualVarTerm
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter
private theorem dualScale_cast (η a b : ℝ) :
    (OscSpecial.dualScale η a b : ℂ) =
      (η : ℂ) * (OscSpecial.q a b : ℂ) /
        (4 * (OscSpecial.r η a b : ℂ)) := by
  dsimp [OscSpecial.dualScale]
  push_cast
  ring
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
end ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
namespace ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftLocal
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
open Filter
open scoped Topology
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have h := (dual_gaussian_is_actual_trace_phase
    a b z.1 z.2 hc η hη).symm.trans
      (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z)
  unfold actualVariableDualKernel
  rw [dualScale_cast]
  exact h
end OAI.ActualEisensteinCubic
