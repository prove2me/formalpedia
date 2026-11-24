-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.exists_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:56.789045+00:00
-- url     : https://prove2.me/submissions/10432ed1-c12e-4b6f-b85a-2ebdfc77434a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_addChar_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
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
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (e : R × Q) (c : k), ∃ U : AddSubgroup k, IsOpen (U : Set k) ∧ IsCompact (U : Set k) ∧ ∀ u ∈ U, ψ (u * c) = 1 ∧ ∀ t, Φ (t + Matrix.single e.1 e.2 u) = Φ t := by
  intro k _ _ _ _ ψ hψ R Q _ _ _ _ Φ hΦ e c
  have hs : Continuous fun u : k => Matrix.single e.1 e.2 u := by
    refine continuous_matrix fun r q => ?_
    simp only [Matrix.single_apply]
    by_cases h : e.1 = r ∧ e.2 = q
    · simp only [if_pos h]; fun_prop
    · simp only [if_neg h]; fun_prop
  have h1 : ∀ᶠ u in 𝓝 (0 : k), ∀ z ∈ tsupport Φ, Φ (z + Matrix.single e.1 e.2 u) = Φ z := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : k × Matrix R Q k => (Φ (q.2 + Matrix.single e.1 e.2 q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add (hs.comp continuous_fst))).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s₀, hs₀⟩ := exists_cball_addChar_eq_one ψ hψ
  have h3 : ∀ᶠ u in 𝓝 (0 : k), ψ (u * c) = 1 := by
    have : (fun u : k => u * c) ⁻¹' cball s₀ ∈ 𝓝 (0 : k) :=
      ((isOpen_cball s₀).preimage (by fun_prop)).mem_nhds (by simp [cball])
    filter_upwards [this] with u hu using hs₀ _ hu
  obtain ⟨s, hUs⟩ := exists_cball_subset (h1.and h3)
  refine ⟨HaarFactor.cballSub s, isOpen_cball s, isCompact_cball s, fun u hu => ⟨(hUs hu).2, fun z => ?_⟩⟩
  by_cases hz : z ∈ tsupport Φ
  · exact (hUs hu).1 z hz
  by_cases hz' : z + Matrix.single e.1 e.2 u ∈ tsupport Φ
  · have := (hUs (neg_mem_cball hu)).1 _ hz'
    rw [add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']
end GlobalTheory.PartRed.IntEntry
