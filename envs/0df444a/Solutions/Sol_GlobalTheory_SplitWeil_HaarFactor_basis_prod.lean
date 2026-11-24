-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.basis_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:08:55.171102+00:00
-- url     : https://prove2.me/submissions/053d5d52-8e98-4b37-ae20-26d253493a40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_coe_boxSub
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution (m₁ m₂ : Type*) [Fintype m₁] [Fintype m₂] :
    ∀ V ∈ 𝓝 (0 : (m₁ → k) × (m₂ → k)), ∃ U : AddSubgroup ((m₁ → k) × (m₂ → k)),
      IsOpen (U : Set ((m₁ → k) × (m₂ → k))) ∧ IsCompact (U : Set ((m₁ → k) × (m₂ → k))) ∧
        (U : Set ((m₁ → k) × (m₂ → k))) ⊆ V := by
  intro V hV
  rw [Prod.zero_eq_mk, nhds_prod_eq, Filter.mem_prod_iff] at hV
  obtain ⟨t₁, h₁, t₂, h₂, hsub⟩ := hV
  obtain ⟨s₁, hs₁⟩ := FourierPi.exists_box_subset h₁
  obtain ⟨s₂, hs₂⟩ := FourierPi.exists_box_subset h₂
  refine ⟨(boxSub m₁ s₁).prod (boxSub m₂ s₂), ?_, ?_, ?_⟩ <;> rw [AddSubgroup.coe_prod, coe_boxSub, coe_boxSub]
  · exact (FourierPi.isOpen_box s₁).prod (FourierPi.isOpen_box s₂)
  · exact (FourierPi.isCompact_box s₁).prod (FourierPi.isCompact_box s₂)
  · exact (Set.prod_mono hs₁ hs₂).trans hsub
end GlobalTheory.SplitWeil.HaarFactor
