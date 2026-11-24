-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:10.944725+00:00
-- url     : https://prove2.me/submissions/0e1068fe-ed04-42c6-9fa0-ed692b460462

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_hom_pos
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_mul
import Theorems.Thm_GlobalTheory_Doubling_norm_npow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
variable {K}
variable (K)
variable {δ K χ t}
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h
namespace GlobalTheory.Doubling.IsIwasawa
theorem _root_.solution {Φ : G → ℂ} (hΦ : IndLaw δ χ t Φ) {C : ℝ} (hC : ∀ k ∈ K, ‖Φ k‖ ≤ C) (g : G) :
    ‖Φ g‖ ≤ C * (iwAbs δ K g : ℝ) ^ t.re := by
  obtain ⟨p, k, hk, rfl⟩ := h.1 g
  rw [hΦ, h.iwAbs_mul _ hk, norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_npow (hom_pos δ p), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (by positivity)
end GlobalTheory.Doubling.IsIwasawa
