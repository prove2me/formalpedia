-- Prove2me | solution 1 for GlobalTheory.colValue_mul_of_disjoint_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:43.696809+00:00
-- url     : https://prove2.me/submissions/ecd2d23d-83e7-4905-aa70-f9f532024160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColValueMulOfDisjointColumns
import Theorems.Thm_GlobalTheory_sum_coeff_mul_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (n : ℕ) (mu : Fin n → (ι →₀ ℕ) → k) (T : Finset (Fin n)) (P₁ P₂ : MvPolynomial (ι × Fin n) k), (∀ mo ∈ P₁.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ T) → (∀ mo ∈ P₂.support, ∀ l b, mo (l, b) ≠ 0 → b ∉ T) → ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * ∏ b, mu b (colM mo b) = (∑ mo ∈ P₁.support, P₁.coeff mo * ∏ b ∈ T, mu b (colM mo b)) * ∑ mo ∈ P₂.support, P₂.coeff mo * ∏ b ∈ Tᶜ, mu b (colM mo b) := by
  intro k _ ι _ n mu T P₁ P₂ h₁ h₂
  rw [sum_coeff_mul_weight (fun mo => ∏ b, mu b (colM mo b)) P₁ P₂, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
  have e₁ : ∏ b ∈ T, mu b (colM (m₁ + m₂) b) = ∏ b ∈ T, mu b (colM m₁ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₂ (l, b) = 0 := by
      by_contra h
      exact h₂ m₂ hm₂ l b h hb
    simp [colM, this]
  have e₂ : ∏ b ∈ Tᶜ, mu b (colM (m₁ + m₂) b) = ∏ b ∈ Tᶜ, mu b (colM m₂ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₁ (l, b) = 0 := by
      by_contra h
      exact (Finset.mem_compl.1 hb) (h₁ m₁ hm₁ l b h)
    simp [colM, this]
  rw [← Finset.prod_mul_prod_compl T, e₁, e₂]
  ring
end GlobalTheory
