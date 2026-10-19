-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.circlePolynomial_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:40:53.613152+00:00
-- url     : https://prove2.me/submissions/adcba23f-1eb7-4d19-9df3-00c63d144c1d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/MinimizingFamily.lean:L94-L116
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.circlePolynomial_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LittlewoodFiniteFlatness
import Definitions.Def_OAI_Analysis_Littlewood_MinimizingFamily

-- ---- from OAI.Analysis.Littlewood.MinimizingFamily ----
namespace OAI

/-! A minimizing family with vanishing second error moment. -/
noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

/- An all-length upper-flatness bound for real-sign polynomials. -/
variable (hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
  ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N)

/-- Exact finite Parseval, obtained from finite orthonormal Fourier sums. -/
lemma circlePolynomial_energy {N : ℕ} (ε : Fin N → ℝ) :
    (∫ t : UnitAddCircle, ‖circlePolynomial ε t‖ ^ 2 ∂μ) = ∑ k, (ε k) ^ 2 := by
  classical
  have hi : Function.Injective (fun k : Fin N => (k : ℤ)) := by
    intro i j h
    apply Fin.ext
    change (i.val : ℤ) = (j.val : ℤ) at h
    exact_mod_cast h
  have ho := (orthonormal_fourier (T := (1 : ℝ))).comp
    (fun k : Fin N => (k : ℤ)) hi
  have he := ho.inner_sum (fun k => (ε k : ℂ)) (fun k => (ε k : ℂ)) Finset.univ
  have hmap : ContinuousMap.toLp 2 μ ℂ (circlePolynomial ε) =
      ∑ k : Fin N, (ε k : ℂ) • fourierLp 2 (k : ℤ) := by
    simp [circlePolynomial, fourierLp, μ]
  change inner ℂ (∑ k : Fin N, (ε k : ℂ) • fourierLp 2 (k : ℤ))
    (∑ k : Fin N, (ε k : ℂ) • fourierLp 2 (k : ℤ)) = _ at he
  rw [← hmap, ContinuousMap.inner_toLp] at he
  have hc : (∫ t : UnitAddCircle, ((‖circlePolynomial ε t‖ ^ 2 : ℝ) : ℂ) ∂μ) =
      ((∑ k : Fin N, (ε k) ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two] using he
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.circlePolynomial_energy := @_root_.OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.circlePolynomial_energy
