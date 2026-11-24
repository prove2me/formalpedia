-- Prove2me | solution 1 for GlobalTheory.StepData.mem_SB_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:53:36.37987+00:00
-- url     : https://prove2.me/submissions/fd9c3288-41b7-4a01-881d-4a300806bdd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_maxM_zero


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
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
omit [DecidableEq a] [DecidableEq b]
namespace GlobalTheory.StepData
theorem _root_.solution {f : Matrix b a k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, MaxM y → f (x + y) = f x) : f ∈ SB (Matrix b a k) := by
  refine ⟨(IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{x' | MaxM (x' - x)}, ?_, by simpa using maxM_zero,
    fun x' hx' => by rw [← hp x _ hx', add_sub_cancel]⟩,
    HasCompactSupport.intro (SplitFlip.isCompact_intMatrix (k := k) (m := b) (n := a))
      fun x hx => by_contra fun h => hx (hs x h)⟩
  simp only [MaxM, Set.ofPred_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact IsOpen.preimage (f := fun x' : Matrix b a k => (x' - x) i j) (t := {z | valuation k z < 1}) (by fun_prop)
    (by simpa using (valuation k).isOpen_ball 1)
end GlobalTheory.StepData
