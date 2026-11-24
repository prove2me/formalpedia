-- Prove2me | solution 1 for GlobalTheory.schr_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:44.363102+00:00
-- url     : https://prove2.me/submissions/6b6ee995-adc0-40cf-9818-ecf87ceecf57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergInnerPreserving
import Theorems.Thm_GlobalTheory_norm_addChar_nonarch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory
open ValuativeRel
namespace GlobalTheory
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  intro k _ _ _ _ _ ψ0 hψ κ _ μ hμ w φ φ'
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have h1 : ∀ s : k, ψ0 s * (starRingEnd ℂ) (ψ0 s) = 1 := fun s => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar_nonarch ψ0 hψ s]; simp
  have h2 : (fun y => GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y)) =
      fun y => φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1)) := by
    funext y
    simp only [GlobalTheory.WeilM.schr, map_mul]
    have := h1 (y ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2))
    linear_combination (φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1))) * this
  rw [h2]
  exact integral_add_right_eq_self (fun y => φ y * (starRingEnd ℂ) (φ' y)) w.1
end GlobalTheory
