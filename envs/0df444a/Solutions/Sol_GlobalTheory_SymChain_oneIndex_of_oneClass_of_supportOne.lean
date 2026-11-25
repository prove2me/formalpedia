-- Prove2me | solution 1 for GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:55.673334+00:00
-- url     : https://prove2.me/submissions/bc9407ae-dde3-45e1-b9e3-c35bf0f21abf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_OneIndexOfOneClassOfSupportOne
import Theorems.Thm_GlobalTheory_SymChain_exists_affPt_of_flat_ne_zero
import Theorems.Thm_GlobalTheory_StepData_Chain_ofType_laws
import Theorems.Thm_GlobalTheory_UnfoldedEntries_flat_ne_zero_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain
namespace GlobalTheory.SymChain
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
      [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t]
      [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c hjc β hβ
  have := hν.1
  obtain ⟨h, rfl, h0⟩ := hβ
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c hjc h h0
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (GlobalTheory.UnfoldedEntries.flat_ne_zero_congr (ψ := S.ψ) (ν := ν) (h₂' := 1) (h₂ := u) (by omega)
    (HL.1 j (c + 1) (by omega)) rfl
    ((DoubleCoset.eq _ _ _ _).2 ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩)).1 h0
  obtain ⟨x₀, e, he⟩ := exists_affPt_of_flat_ne_zero _ _ _ _ _ h1
  obtain ⟨r', hr', w, hw, rfl⟩ := hS j c hjc u hu x₀ e he
  exact (DoubleCoset.eq _ _ _ _).2 ⟨(r * r')⁻¹, inv_mem (mul_mem hr hr'), w⁻¹, inv_mem hw, by group⟩
end GlobalTheory.SymChain
