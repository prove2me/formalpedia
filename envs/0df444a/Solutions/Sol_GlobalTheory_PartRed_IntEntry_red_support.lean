-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.red_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:00.411497+00:00
-- url     : https://prove2.me/submissions/81b0a2e9-5457-4e01-9864-716cb3057f79

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
theorem _root_.solution : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k), red ψ ν w β E I Φ x ≠ 0 → ∃ t, Φ t ≠ 0 ∧ t e.1 e.2 = x e.1 e.2 := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ x hx
  by_contra hne
  refine hx (integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_))
  have : Φ (fillAt β E I x y) = 0 := by
    by_contra h
    exact hne ⟨_, h, fill_entry β E I x y e hI hE⟩
  simp [this]
end GlobalTheory.PartRed.IntEntry
