-- Prove2me | solution 1 for GlobalTheory.FlowProgramme.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:46.069276+00:00
-- url     : https://prove2.me/submissions/6fbdb3b3-13db-4b47-8e71-dbfb245153f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable
import Theorems.Thm_GlobalTheory_FlowProgramme_duality
import Theorems.Thm_GlobalTheory_FlowProgramme_balanced
import Theorems.Thm_GlobalTheory_FlowProgramme_optimum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme
namespace GlobalTheory.FlowProgramme
theorem _root_.solution :
  (∀ (l d : ℕ) [NeZero d] (X : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ X a) →
    (∀ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) → ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i ≤ ∑ a, X a ∧
      ∀ i₀ : ℕ, ∑ a, ∑ i ∈ Finset.Ico i₀ d, x a i ≤ ((l : ℝ) ^ i₀)⁻¹ * ∑ a, X a) ∧
    (2 ≤ d → (∀ a b, X a ≤ l * X b) → ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧ ((l : ℝ) + 1) * ∑ a, ∑ i ∈ Finset.range d, x a i = ∑ a, X a) ∧
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧ ∀ x' : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x' a i) ∧ (∀ a i, x' a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x' a i + ∑ i ∈ Finset.range d, x' (a - i) i ≤ X a) → ∑ a, ∑ i ∈ Finset.range d, x' a i ≤ ∑ a, ∑ i ∈ Finset.range d, x a i) := by
  intro l d _ X hl hX
  exact ⟨duality l d X hl, balanced l d X hl, optimum l d X hl hX⟩
end GlobalTheory.FlowProgramme
