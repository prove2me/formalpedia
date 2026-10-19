-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.normalized_error_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:42:42.851858+00:00
-- url     : https://prove2.me/submissions/628ceb0f-894f-46f1-bd7c-a6ad849d3a14

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/MinimizingFamily.lean:L162-L200
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.normalized_error_sq_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LittlewoodFiniteFlatness
import Definitions.Def_OAI_Analysis_Littlewood_MinimizingFamily
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewoodFiniteFlatness_circlePolynomial_energy

-- ---- from OAI.Analysis.Littlewood.MinimizingFamily ----
namespace OAI

/-! A minimizing family with vanishing second error moment. -/
noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

lemma signVector_signing {N : ℕ} (b : Fin N → Bool) : IsRealSigning (signVector b) := by
  intro k
  cases h : b k <;> simp [signVector, boolSign, h]

lemma chosenSigns_signing (N : ℕ) : IsRealSigning (chosenSigns N) :=
  signVector_signing _

/- An all-length upper-flatness bound for real-sign polynomials. -/
variable (hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
  ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N)

lemma signing_energy {N : ℕ} (ε : Fin N → ℝ) (hε : IsRealSigning ε) :
    (∫ t : UnitAddCircle, ‖circlePolynomial ε t‖ ^ 2 ∂μ) = (N : ℝ) := by
  rw [circlePolynomial_energy]
  have hs : ∀ k, (ε k) ^ 2 = (1 : ℝ) := by
    intro k
    rcases hε k with h | h <;> simp [h]
  simp [hs]

lemma normalized_nonneg (N : ℕ) (t : UnitAddCircle) : 0 ≤ normalized N t :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

lemma normalized_continuous (N : ℕ) : Continuous (normalized N) :=
  (circlePolynomial (chosenSigns N)).continuous.norm.div_const _

lemma normalized_energy {N : ℕ} (hN : 1 ≤ N) :
    (∫ t : UnitAddCircle, normalized N t ^ 2 ∂μ) = 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp_rw [normalized, div_pow]
  rw [integral_div, signing_energy _ (chosenSigns_signing N), Real.sq_sqrt hNr.le]
  exact div_self hNr.ne'

lemma continuous_integrable (f : UnitAddCircle → ℝ) (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Elementary second-error-moment estimate; no p-dependent signing is used. -/
lemma normalized_error_sq_bound {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    (hb : ∀ t, normalized N t ≤ 1 + η) :
    (∫ t : UnitAddCircle, (normalized N t - 1) ^ 2 ∂μ) ≤ 2 * η := by
  let f := normalized N
  have hf : Continuous f := normalized_continuous N
  have hi := continuous_integrable f hf
  have hi2 := continuous_integrable (fun t => f t ^ 2) (hf.pow 2)
  have hE : (∫ t, f t ^ 2 ∂μ) = 1 := normalized_energy hN
  have hmul : (∫ t, f t ^ 2 ∂μ) ≤ (1 + η) * ∫ t, f t ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hi2 (hi.const_mul _)
    intro t
    have hp := normalized_nonneg N t
    have ht := hb t
    change f t ≤ 1 + η at ht
    change 0 ≤ f t at hp
    nlinarith
  rw [hE] at hmul
  have hmean : 1 / (1 + η) ≤ ∫ t, f t ∂μ :=
    (div_le_iff₀ (by linarith : 0 < 1 + η)).2 (by nlinarith [hmul])
  have hrec : 1 - η ≤ 1 / (1 + η) :=
    (le_div_iff₀ (by linarith : 0 < 1 + η)).2 (by nlinarith [sq_nonneg η])
  have hid : (∫ t, (f t - 1) ^ 2 ∂μ) = 2 - 2 * ∫ t, f t ∂μ := by
    calc
      _ = ∫ t, (f t ^ 2 - 2 * f t) + 1 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = 2 - 2 * ∫ t, f t ∂μ := by
        rw [integral_add (f := fun t => f t ^ 2 - 2 * f t) (g := fun _ => (1 : ℝ))
          (hi2.sub (hi.const_mul 2)) (integrable_const 1),
          integral_sub (f := fun t => f t ^ 2) (g := fun t => 2 * f t)
            hi2 (hi.const_mul 2), integral_const_mul, hE]
        simp
        ring
  change (∫ t, (f t - 1) ^ 2 ∂μ) ≤ 2 * η
  rw [hid]
  linarith

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.normalized_error_sq_bound := @_root_.OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.normalized_error_sq_bound
