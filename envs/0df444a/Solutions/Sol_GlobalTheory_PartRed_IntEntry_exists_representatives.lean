-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.exists_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:58.236108+00:00
-- url     : https://prove2.me/submissions/3e854aee-b174-4a0e-a533-d56513450026

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation

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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [Fintype Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → ∀ e : R × Q, ∃ S : Finset k, (∀ a ∈ S, ∀ b ∈ S, a - b ∈ U → a = b) ∧ ∀ t : Matrix R Q k, Φ t ≠ 0 → ∃ a ∈ S, t e.1 e.2 - a ∈ U := by
  intro k _ _ _ _ R Q _ _ Φ hΦ U hU e
  classical
  have hK : IsCompact ((fun t : Matrix R Q k => t e.1 e.2) '' tsupport Φ) := hΦ.2.image (by fun_prop)
  obtain ⟨T, -, hT⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set k))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨T.image fun a : k => (a : k ⧸ U).out, ?_, fun t ht => ?_⟩
  · intro a ha b hb hab
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hb
    have := QuotientAddGroup.eq_iff_sub_mem.mpr hab
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
    rw [this]
  · obtain ⟨a, ha, hta⟩ := Set.mem_iUnion₂.mp (hT ⟨t, subset_tsupport Φ ht, rfl⟩)
    refine ⟨_, Finset.mem_image.mpr ⟨a, ha, rfl⟩, QuotientAddGroup.eq_iff_sub_mem.mp ?_⟩
    rw [QuotientAddGroup.out_eq']
    exact QuotientAddGroup.eq_iff_sub_mem.mpr hta
end GlobalTheory.PartRed.IntEntry
