-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:27:23.636271+00:00
-- url     : https://prove2.me/submissions/e255a4dc-3c6f-413d-b94a-93e8e5b4c53f

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_mem_iff_val_le
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_one_lt_q
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_eq_zpow
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_mul_zpow
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_nrm_eq_zpow
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_nrm_le_one_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_nrm_lt_one_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_nrm_le_of_val_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → 1 < q ∧ ϖ ∈ O ∧ (∀ x : F, nrm x ≤ 1 ↔ x ∈ O) ∧ (∀ x : F, nrm x < 1 ↔ ∃ o ∈ O, x = ϖ * o) ∧ (∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) ∧ nrm (x * ϖ ^ (-e)) = 1) ∧ (∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) ∧ (∀ x : F, nrm x = 1 ↔ ValuativeRel.valuation F x = 1) := by
  intro F _ _ _ _ O ϖ nrm q h
  refine ⟨one_lt_q h, (mem_iff_val_le h ϖ).2 (val_pi_lt_one h).le,
    fun x => (nrm_le_one_iff h x).trans (mem_iff_val_le h x).symm,
    fun x => (nrm_lt_one_iff h x).trans (h.lt_one x), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he⟩ := val_eq_zpow h hx
    exact ⟨e, nrm_eq_zpow h he, h.nrm_unit _ (val_mul_zpow h he)⟩
  · intro x y
    rcases le_total (ValuativeRel.valuation F x) (ValuativeRel.valuation F y) with hxy | hxy
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F y :=
        le_trans (Valuation.map_add _ x y) (max_le hxy le_rfl)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_right _ _)
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F x :=
        le_trans (Valuation.map_add _ x y) (max_le le_rfl hxy)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_left _ _)
  · intro x
    constructor
    · intro hn
      have h1 := (nrm_le_one_iff h x).1 hn.le
      have h2 : ¬ ValuativeRel.valuation F x < 1 := fun hlt => by
        have := (nrm_lt_one_iff h x).2 hlt
        linarith
      exact le_antisymm h1 (not_lt.1 h2)
    · exact h.nrm_unit x
end GlobalTheory.CompanionTheory.QL.NormalisedValue
