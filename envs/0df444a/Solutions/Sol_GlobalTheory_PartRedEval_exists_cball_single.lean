-- Prove2me | solution 1 for GlobalTheory.PartRedEval.exists_cball_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:03.729837+00:00
-- url     : https://prove2.me/submissions/6e527dd1-3cfb-4b0d-b847-dfebf52723c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRedEval
open GlobalTheory.PartRed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
omit [Fintype R] [Fintype Q]
namespace GlobalTheory.PartRedEval
theorem _root_.solution {f : Matrix R Q k → ℂ} (hf : f ∈ SB (Matrix R Q k)) (e : R × Q) :
    ∃ s : kˣ, ∀ t ∈ cball s, ∀ x, f (x + Matrix.single e.1 e.2 t) = f x := by
  have hc : Continuous fun t : k => (Matrix.single e.1 e.2 t : Matrix R Q k) := by
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.single, Matrix.of_apply]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  have h1 : ∀ᶠ t in 𝓝 (0 : k), ∀ x ∈ tsupport f, f (x + Matrix.single e.1 e.2 t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : k × Matrix R Q k => (f (q.2 + Matrix.single e.1 e.2 q.1), f q.2) :=
      (hf.1.comp_continuous (continuous_snd.add (hc.comp continuous_fst))).prodMk
        (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + Matrix.single e.1 e.2 t ∈ tsupport f
  · have := hs (neg_mem_cball ht) _ hx'
    rw [← this, add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
end GlobalTheory.PartRedEval
