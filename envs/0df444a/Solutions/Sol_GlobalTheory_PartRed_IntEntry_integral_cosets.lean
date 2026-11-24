-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.integral_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:02.063964+00:00
-- url     : https://prove2.me/submissions/5ea04264-fea1-44e8-ba8b-acdca509ba04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_ind_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_integrable_of_SB
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → IsCompact (U : Set k) → ∀ (S : Finset k), (∀ a ∈ S, ∀ b ∈ S, a - b ∈ U → a = b) → ∀ h : k → ℂ, (∀ s u, u ∈ U → h (s + u) = h s) → (∀ s, h s ≠ 0 → ∃ a ∈ S, s - a ∈ U) → ∫ s, h s ∂ν = ((ν (U : Set k)).toReal : ℂ) * ∑ a ∈ S, h a := by
  intro k _ _ _ _ _ _ ν hν U hUo hUc S hS h hinv hsupp
  haveI := secondCountable k
  haveI := t2Space k
  have he := HaarFactor.integrable_of_SB ν (HaarFactor.ind_mem hUo hUc)
  have hshift : ∀ c : k, ∫ a, (U : Set k).indicator (fun _ => (1 : ℂ)) (a - c) ∂ν = (ν.real (U : Set k) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set k).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  have hT : ∀ s, h s = ∑ a ∈ S, h a * (U : Set k).indicator (fun _ => (1 : ℂ)) (s - a) := by
    intro s
    have hv : ∀ a, s - a ∈ U → h s = h a := fun a ha => by rw [← hinv a _ ha, add_sub_cancel]
    by_cases hs : h s = 0
    · rw [hs]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      by_cases ha : s - a ∈ U
      · rw [← hv a ha, hs, zero_mul]
      · rw [Set.indicator_of_notMem (show s - a ∉ (U : Set k) from ha), mul_zero]
    · obtain ⟨a, ha, hsa⟩ := hsupp s hs
      rw [Finset.sum_eq_single a]
      · rw [Set.indicator_of_mem (show s - a ∈ (U : Set k) from hsa), mul_one, hv a hsa]
      · intro b hb hba
        rw [Set.indicator_of_notMem, mul_zero]
        intro hsb
        have hm := U.sub_mem hsa hsb
        rw [sub_sub_sub_cancel_left] at hm
        exact hba (hS b hb a ha hm)
      · exact fun ha' => absurd ha ha'
  rw [integral_congr_ae (Filter.Eventually.of_forall hT),
    integral_finset_sum _ fun q _ => (he.comp_sub_right _).const_mul _]
  simp only [integral_const_mul, hshift, ← Finset.sum_mul]
  rw [mul_comm]
  rfl
end GlobalTheory.PartRed.IntEntry
