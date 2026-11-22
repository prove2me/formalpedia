-- Prove2me | solution 1 for MasulloRH.compensated_resolvent_defect_low_high_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T08:28:29.28562+00:00
-- url     : https://prove2.me/submissions/e3995e3b-09a9-4552-bfab-3f0d31ac78ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloAudit_trace_formula_rational_source_form
import Theorems.Thm_MasulloAudit_geometric_side_eq_formal_lhs
import Theorems.Thm_MasulloAudit_trace_formula_rational_fixed_window_iff
import Theorems.Thm_MasulloRH_realTraceIntegrand_integrable
import Theorems.Thm_MasulloRH_low_height_trace_zero_set_empty
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option autoImplicit false
open MasulloRH MeasureTheory Set
open scoped Topology

theorem solution
    (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    ∃ F : Set (ZetaZerosInTraceStrip (1 / 2)),
      F.Finite ∧
      (∀ ρ, |ρ.val.im| ^ 2 < 36 → ρ ∈ F) ∧
      ∃ fLow fHigh : ZetaZerosInTraceStrip (1 / 2) → ℝ,
        (∀ ρ, 0 ≤ fLow ρ) ∧
        (∀ ρ, 0 ≤ fHigh ρ) ∧
        (∀ ρ, ρ ∉ F → fLow ρ = 0) ∧
        (∀ ρ, ρ ∈ F → fHigh ρ = 0) ∧
        Summable fLow ∧ Summable fHigh ∧
        (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re =
          (∑' ρ, fLow ρ) + ∑' ρ, fHigh ρ := by
  have hformula : ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
    intro φ hφ
    have : ∀ p : Nat.Primes, Fact (p : ℕ).Prime := fun p => ⟨p.2⟩
    let inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p] := fun p => borel ℚ_[p]
    have hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p] := fun p => ⟨rfl⟩
    let μ : ∀ p : Nat.Primes, Measure ℚ_[p] := fun p => Measure.addHaar
    have hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure := fun p => by
      dsimp only [μ]; infer_instance
    obtain ⟨-, -, -, -, hpp, hgeom⟩ :=
      MasulloAudit.geometric_side_eq_formal_lhs φ hφ inst μ
    obtain ⟨-, -, -, hz, hsrc⟩ :=
      MasulloAudit.trace_formula_rational_source_form α hα φ hφ inst μ
    refine ⟨MasulloRH.realTraceIntegrand_integrable φ hφ, hpp, hz, ?_⟩
    rw [← hgeom]
    exact hsrc
  have hzeros : ∀ ρ : ZetaZerosInTraceStrip (1 / 2),
      |(ρ : ℂ).re - 1 / 2| < α :=
    (MasulloAudit.trace_formula_rational_fixed_window_iff α hα).mp hformula
  let e : ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip (1 / 2) := {
    toFun := fun ρ => ⟨ρ.val, ρ.property.1, ρ.property.2.1, ρ.property.2.2.1,
      (abs_lt.mpr ⟨by linarith [ρ.property.2.1], by linarith [ρ.property.2.2.1]⟩)⟩
    invFun := fun ρ => ⟨ρ.val, ρ.property.1, ρ.property.2.1, ρ.property.2.2.1,
      hzeros ρ⟩
    left_inv := by intro ρ; exact Subtype.ext rfl
    right_inv := by intro ρ; exact Subtype.ext rfl
  }
  have hspectral : regularizedSpectral α (3 : ℂ) =
      regularizedSpectral (1 / 2) (3 : ℂ) := by
    unfold regularizedSpectral
    calc
      (∑' ρ : ZetaZerosInTraceStrip α, zeroResolventTerm α (3 : ℂ) ρ) =
          ∑' ρ : ZetaZerosInTraceStrip α,
            zeroResolventTerm (1 / 2) (3 : ℂ) (e ρ) := by
              apply tsum_congr
              intro ρ
              rfl
      _ = ∑' ρ : ZetaZerosInTraceStrip (1 / 2),
            zeroResolventTerm (1 / 2) (3 : ℂ) ρ := e.tsum_eq _
  have hrhs : regularizedTraceRHS α (3 : ℂ) =
      regularizedTraceRHS (1 / 2) (3 : ℂ) := by
    simp only [regularizedTraceRHS, hspectral]
  refine ⟨∅, Set.finite_empty, ?_, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ hheight
    have hmem : ρ ∈ ({ρ : ZetaZerosInTraceStrip (1 / 2) |
        |ρ.val.im| ^ 2 < 36} : Set _) := hheight
    rw [MasulloRH.low_height_trace_zero_set_empty] at hmem
    exact hmem
  · intro ρ; exact le_refl 0
  · intro ρ; exact le_refl 0
  · intro ρ hρ; rfl
  · intro ρ hρ; rfl
  · exact summable_zero
  · exact summable_zero
  · simp [hrhs]
