-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.exists_bd_of_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:06.0697+00:00
-- url     : https://prove2.me/submissions/681bd2db-26a9-429a-8336-5d4de1504612

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
variable {k : Type} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (u : kˣ) :
    ∃ γ : ValueGroupWithZero k, ∀ a : k,
      (∀ t, valuation k t ≤ valuation k (u : k) → ψ (a * t) = 1) → valuation k a ≤ γ := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext y; simp [h y])
  refine ⟨valuation k (y / u), fun a ha => ?_⟩
  by_contra hlt
  push Not at hlt
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hlt
  apply hy
  have := ha (y / a) (by
    rw [map_div₀] at hlt ⊢
    rw [div_lt_iff₀ (by simp [zero_lt_iff])] at hlt
    rw [div_le_iff₀ (by simp [zero_lt_iff, ha0]), mul_comm]
    exact hlt.le)
  rwa [mul_div_cancel₀ _ ha0] at this
end GlobalTheory.RootEx.Supp
