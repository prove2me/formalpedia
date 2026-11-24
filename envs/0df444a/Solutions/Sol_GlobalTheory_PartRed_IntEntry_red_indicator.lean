-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.red_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:57.758913+00:00
-- url     : https://prove2.me/submissions/a6ee0324-f746-4067-9d9a-a4b534a45dc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_fill_entry

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
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (A : Set k) (x : Matrix R Q k), red ψ ν w β E I (Set.indicator {t : Matrix R Q k | t e.1 e.2 ∈ A} Φ) x = Set.indicator {z : Matrix R Q k | z e.1 e.2 ∈ A} (red ψ ν w β E I Φ) x := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ A x
  by_cases hx : x e.1 e.2 ∈ A
  · rw [Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ A} from hx)]
    unfold red
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [Set.indicator_of_mem]
    show fillAt β E I x y e.1 e.2 ∈ A
    rwa [fill_entry β E I x y e hI hE]
  · rw [Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ A} from hx)]
    unfold red
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [Set.indicator_of_notMem, zero_mul, Pi.zero_apply]
    show ¬ fillAt β E I x y e.1 e.2 ∈ A
    rwa [fill_entry β E I x y e hI hE]
end GlobalTheory.PartRed.IntEntry
