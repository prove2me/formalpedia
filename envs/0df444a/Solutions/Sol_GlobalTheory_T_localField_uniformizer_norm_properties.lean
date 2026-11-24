-- Prove2me | solution 1 for GlobalTheory.T.localField_uniformizer_norm_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:23.689806+00:00
-- url     : https://prove2.me/submissions/58535aa3-a247-4c7c-adf3-7c0ee10fdb9d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_main


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → 1 < q ∧ ϖ ∈ O ∧ (∀ x : F, nrm x ≤ 1 ↔ x ∈ O) ∧ (∀ x : F, nrm x < 1 ↔ ∃ o ∈ O, x = ϖ * o) ∧ (∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) ∧ nrm (x * ϖ ^ (-e)) = 1) ∧ (∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) ∧ (∀ x : F, nrm x = 1 ↔ ValuativeRel.valuation F x = 1) := by
  first | exact @GlobalTheory.CompanionTheory.QL.NormalisedValue.main | exact GlobalTheory.CompanionTheory.QL.NormalisedValue.main | (intros; apply GlobalTheory.CompanionTheory.QL.NormalisedValue.main <;> assumption)
end _root_.GlobalTheory.T
