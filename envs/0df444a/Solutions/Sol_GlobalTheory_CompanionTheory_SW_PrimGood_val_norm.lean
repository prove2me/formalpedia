-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.val_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:30.843848+00:00
-- url     : https://prove2.me/submissions/570f0963-6780-4fc2-9fec-ff032b35036b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution (hsq : ∀ x : L, w (x - 1) < 1 → IsSquare x) {Δ : L} (hΔ : w Δ = 1)
    (hn : ¬ IsSquare Δ) (a c : L) : w (a ^ 2 - Δ * c ^ 2) = max (w a) (w c) ^ 2 := by
  have ha2 : w (a ^ 2) = w a ^ 2 := map_pow _ _ _
  have hb2 : w (Δ * c ^ 2) = w c ^ 2 := by rw [map_mul, hΔ, one_mul, map_pow]
  rcases lt_trichotomy (w a) (w c) with h | h | h
  · have hlt : w (a ^ 2) < w (Δ * c ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_right hlt, hb2, max_eq_right h.le]
  · rw [← h, max_self]
    by_cases ha : a = 0
    · have hc : c = 0 := by
        rw [ha, map_zero] at h
        exact (Valuation.zero_iff w).1 h.symm
      simp [ha, hc]
    have ha0 : w a ≠ 0 := (Valuation.ne_zero_iff w).2 ha
    have hc : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact ha0 h
    have hle : w (a ^ 2 - Δ * c ^ 2) ≤ w a ^ 2 := by
      refine (w.map_sub _ _).trans (max_le ha2.le ?_)
      rw [hb2, h]
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      apply hn
      have e : Δ * (c / a) ^ 2 - 1 = -((a ^ 2 - Δ * c ^ 2) / a ^ 2) := by
        field_simp; ring
      have hs : IsSquare (Δ * (c / a) ^ 2) := by
        apply hsq
        rw [e, Valuation.map_neg, map_div₀, ha2, div_lt_one₀ (pow_pos (zero_lt_iff.2 ha0) 2)]
        exact hlt
      obtain ⟨r, hr⟩ := hs
      refine ⟨r * a / c, ?_⟩
      have : Δ = (Δ * (c / a) ^ 2) * (a / c) ^ 2 := by field_simp
      rw [this, hr]; ring
    · exact heq
  · have hlt : w (Δ * c ^ 2) < w (a ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_left hlt, ha2, max_eq_left h.le]
end GlobalTheory.CompanionTheory.SW.PrimGood
