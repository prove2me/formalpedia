-- Prove2me | solution 1 for GlobalTheory.StepData.Model.coords_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:35.277603+00:00
-- url     : https://prove2.me/submissions/dd30e3aa-2d0b-486c-a937-bfc0ff3d8de5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData.Model
theorem _root_.solution {ι ι' Y Y' : Type*} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') : Function.Surjective (F.coords F') := fun w =>
  ⟨F.bas.val * w.submatrix F.ord.symm F'.ord.symm * (F'.bas⁻¹).val, by
    simp only [LatFrame.coords, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]; simp⟩
end GlobalTheory.StepData.Model
