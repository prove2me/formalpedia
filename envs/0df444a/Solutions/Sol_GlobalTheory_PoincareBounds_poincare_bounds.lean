-- Prove2me | solution 1 for GlobalTheory.PoincareBounds.poincare_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:41.226352+00:00
-- url     : https://prove2.me/submissions/b0eff534-fe9c-4c88-9cbb-c44844b690ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
import Theorems.Thm_GlobalTheory_PoincareBounds_poincareGram_eq
import Theorems.Thm_GlobalTheory_PoincareBounds_pdiag_nonneg
import Theorems.Thm_GlobalTheory_PoincareBounds_norm_mul_tlog_lt
import Theorems.Thm_GlobalTheory_PoincareBounds_half_le_pdiag
import Theorems.Thm_GlobalTheory_PoincareBounds_pdiag_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.PoincareBounds
namespace GlobalTheory.PoincareBounds
theorem _root_.solution : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 → ∀ z ∈ punctured ha ρ,
    (poincareGram a z).PosSemidef ∧ ∀ ξ : Fin n → ℂ, (∀ k, ‖ξ k‖ ≤ 2 * gnorm (poincareGram a z) ξ) ∧
      ∀ i : Fin a, ‖ξ (Fin.castLE ha i)‖ ≤
        2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) * gnorm (poincareGram a z) ξ := by
  intro n a ha ρ hρ z hz
  refine ⟨?_, fun ξ => ⟨fun k => ?_, fun i => ?_⟩⟩
  · rw [poincareGram_eq, posSemidef_diagonal_iff]
    intro k; exact_mod_cast pdiag_nonneg a z k
  · have h1 := pdiag_term_le a z ξ k
    have h2 := half_le_pdiag ha hρ hz k
    have hG := gnorm_nonneg (poincareGram a z) ξ
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * gnorm (poincareGram a z) ξ ^ 2 := by nlinarith
    nlinarith
  · set k := Fin.castLE ha i with hkdef
    have hk : k.val < a := i.2
    have h0 : z k ≠ 0 := hz.2 i
    obtain ⟨hp, -⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have h1 := pdiag_term_le a z ξ k
    have hd : pdiag a z k = 1 / (2 * (‖z k‖ * tlog (z k)) ^ 2) := by
      unfold pdiag; rw [if_pos hk]; ring
    rw [hd] at h1
    set s := ‖z k‖ * tlog (z k)
    set G := gnorm (poincareGram a z) ξ
    have hG : 0 ≤ G := gnorm_nonneg _ _
    have hx := norm_nonneg (ξ k)
    have h3 : ‖ξ k‖ ^ 2 ≤ 2 * s ^ 2 * G ^ 2 := by
      have hs2 : 0 < 2 * s ^ 2 := by positivity
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs2] at h1
      linarith
    nlinarith [mul_nonneg hp.le hG]
end GlobalTheory.PoincareBounds
