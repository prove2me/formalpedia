-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchrSys.pair_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:10.460372+00:00
-- url     : https://prove2.me/submissions/39336582-1ae6-4e4e-bd89-796e35422b6e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchrSys
variable {R : Type} [TopologicalSpace R] {κ : Type}
namespace GlobalTheory.CompanionTheory.SchrSys
theorem _root_.solution (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (hμ' : @Measure.IsOpenPosMeasure _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) : 0 < (pair μ φ φ).re := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h3 : HasCompactSupport (φ : (κ → R) → ℂ) := φ.2.2
  have e : pair μ φ φ = ((∫ x, ‖(φ : (κ → R) → ℂ) x‖ * ‖(φ : (κ → R) → ℂ) x‖ ∂μ : ℝ) : ℂ) := by
    unfold pair
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    simp [sq]
  rw [e, Complex.ofReal_re]
  obtain ⟨x, hx⟩ : ∃ x, (φ : (κ → R) → ℂ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (Subtype.ext (funext h))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) (h1.norm.mul h1.norm)
    (HasCompactSupport.mul_left (f := fun x => ‖(φ : (κ → R) → ℂ) x‖) h3.norm)
    (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  have := norm_pos_iff.2 hx
  exact (mul_pos this this).ne'
end GlobalTheory.CompanionTheory.SchrSys
