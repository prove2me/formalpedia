-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_separates_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:54:19.1992+00:00
-- url     : https://prove2.me/submissions/b8b5b688-724e-4da4-95c4-ad51ab4edd42

import Mathlib
import Definitions.Def_OAIQ240Bp017

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma planeTest_separates (v : ℂ →ᵇ E) (hv : ∀ g : PlaneTest, planeTestCLM g v=0) : v=0 := by
  have hz := isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := (volume : Measure ℂ))
    (v.continuous.locallyIntegrable.locallyIntegrableOn univ)
    (fun g hg hgc _ => hv ⟨g,hg,hgc⟩)
  have he : EqOn v (fun _ => 0) univ :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' MeasurableSet.univ).mpr hz)
      isOpen_univ v.continuous.continuousOn continuousOn_const
  ext z
  exact he (mem_univ z)

local instance testInst1_r2e8836_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance testInst2_r2e8836_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
lemma jetTest_separates_bp240_oai (u : COne ℂ E) (hu : ∀ g : PlaneTest, jetTestCLM g u=0) : u=0 := by
  have hv : cValue u = 0 := planeTest_separates _ hu
  apply cValue_ext
  intro z
  exact congrArg (fun v : ℂ →ᵇ E => v z) hv

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_separates_bp240_oai.{u_1} := @OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetTest_separates_bp240_oai.{u_1}
