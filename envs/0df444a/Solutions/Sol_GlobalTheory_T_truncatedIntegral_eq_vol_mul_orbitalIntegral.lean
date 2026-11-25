-- Prove2me | solution 1 for GlobalTheory.T.truncatedIntegral_eq_vol_mul_orbitalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:51.702262+00:00
-- url     : https://prove2.me/submissions/e0d3765f-3577-409a-b09d-9b86ad241486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedIntegralEqVolMulOrbitalIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedIntegralEqVolMulOrbitalIntegralStatement
import Theorems.Thm_GlobalTheory_JR_truncated_integral_eq_vol_mul_orbL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) → ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (y₀ : A.L), IsUnit y₀ → ∀ (D : AddSubgroup A.K), IsOpen (D : Set A.K) → IsCompact (D : Set A.K) → ∀ φ : A.L → ℂ, IsTest φ → (∀ b ∈ D, ∃ s s' : A.K, s ∈ A.OK ∧ s' ∈ A.OK ∧ s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse ((x : A.K) * A.NL y₀) * b ∧ ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y) → ∫ y, φ y * Set.indicator (D : Set A.K) (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - (x : A.K) * A.NL y₀) ∂(m.μL x) = ((m.μK D).toReal : ℂ) * A.orbL m.ν φ y₀ := by
  first | exact @GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL | exact GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL | (intros; apply GlobalTheory.JR.truncated_integral_eq_vol_mul_orbL <;> assumption)
end _root_.GlobalTheory.T
