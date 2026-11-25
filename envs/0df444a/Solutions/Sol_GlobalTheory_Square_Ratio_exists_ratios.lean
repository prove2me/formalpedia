-- Prove2me | solution 1 for GlobalTheory.Square.Ratio.exists_ratios
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:08.553233+00:00
-- url     : https://prove2.me/submissions/998bca61-dd17-4433-a0bf-7478c8997d86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRatios
import Theorems.Thm_GlobalTheory_Square_Ratio_away
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open GlobalTheory GlobalTheory.Square GlobalTheory.Square.Ratio
open Formalism.DivisionValues.ValuationRepresentative (vw_mul vw_inv)
namespace GlobalTheory.Square.Ratio
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ), (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (e0 h : ℕ), e0 ≤ h → ∀ (L0 L1 : ℤ → ℂ) (zT zTd zψ Ep : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ) (er : ℝ), (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → L0 s ≠ 0 ∧ L1 s ≠ 0) → (∀ s : ℤ, 1 ≤ s → s ≤ h → zT s ≠ 0 ∧ zTd s ≠ 0 ∧ σ₀ (zψ s) * L0 s = σ₀ (zT s) * L1 s ∧ -(n0 s) ≤ ((vw w (zψ s) + gT s : ℤ) : ℝ) ∧ (vw w (zψ s) : ℝ) ≤ (vw w (zTd s) : ℝ) + er) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → IsAwayUnit Qn (Ep s) ∧ L1 s * L0 (1 - s) = σ₀ (Ep s) * (L1 (1 - s) * L0 s)) → ∃ ρ : ℤ → K, (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → ρ s ≠ 0 ∧ σ₀ (ρ s) * L0 s = L1 s) ∧ (∀ s : ℤ, 1 ≤ s → s ≤ h → (vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + |((vw w (zTd s) + gT s : ℤ) : ℝ)| + er ∧ -(vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + n0 s) ∧ (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) := by
  intro K _ _ _ σ₀ w Qn hQ e0 h he L0 L1 zT zTd zψ Ep gT n0 er hL hpos hneg
  have he' : (e0 : ℤ) ≤ h := by exact_mod_cast he
  have key : ∀ s : ℤ, 1 ≤ s → s ≤ h → zψ s ≠ 0 ∧ zψ s / zT s ≠ 0 ∧
      σ₀ (zψ s / zT s) * L0 s = L1 s := by
    intro s h1 h2
    obtain ⟨hT, -, hrel, -, -⟩ := hpos s h1 h2
    obtain ⟨-, hL1⟩ := hL s (by omega) h2
    have hT' : σ₀ (zT s) ≠ 0 := (map_ne_zero σ₀).2 hT
    have hψ : zψ s ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact mul_ne_zero hT' hL1 hrel.symm
    refine ⟨hψ, div_ne_zero hψ hT, ?_⟩
    rw [map_div₀]
    field_simp
    linear_combination hrel
  refine ⟨fun s => if 1 ≤ s then zψ s / zT s else Ep s * (zψ (1 - s) / zT (1 - s)), ?_, ?_, ?_⟩
  · intro s h1 h2
    by_cases hs : 1 ≤ s
    · simp only [hs, if_true]
      exact (key s hs h2).2
    · simp only [hs, if_false]
      obtain ⟨hu, hrel⟩ := hneg s h1 (by omega)
      obtain ⟨-, hne, hk⟩ := key (1 - s) (by omega) (by omega)
      refine ⟨mul_ne_zero (away hQ hu).1 hne, ?_⟩
      have hL0 := (hL (1 - s) (by omega) (by omega)).1
      apply mul_right_cancel₀ hL0
      rw [hrel, map_mul, ← hk]
      ring
  · intro s h1 h2
    simp only [h1, if_true]
    obtain ⟨hT, -, -, hb1, hb2⟩ := hpos s h1 h2
    have hψ := (key s h1 h2).1
    have hv : vw w (zψ s / zT s) = vw w (zψ s) - vw w (zT s) := by
      rw [div_eq_mul_inv, vw_mul w _ _ hψ (inv_ne_zero hT), vw_inv]; ring
    rw [hv]
    have a1 := le_abs_self ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a2 := neg_abs_le ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a3 := le_abs_self ((vw w (zTd s) + gT s : ℤ) : ℝ)
    generalize |((vw w (zT s) + gT s : ℤ) : ℝ)| = A at *
    generalize |((vw w (zTd s) + gT s : ℤ) : ℝ)| = B at *
    push_cast at *
    constructor <;> linarith
  · intro s h1 h2
    have hs : ¬ 1 ≤ s := by omega
    have hs' : 1 ≤ 1 - s := by omega
    simp only [hs, hs', if_true, if_false]
    obtain ⟨hu, -⟩ := hneg s h1 h2
    obtain ⟨hE, hv⟩ := away hQ hu
    rw [vw_mul w _ _ hE (key (1 - s) hs' (by omega)).2.1, hv, zero_add]
end GlobalTheory.Square.Ratio
