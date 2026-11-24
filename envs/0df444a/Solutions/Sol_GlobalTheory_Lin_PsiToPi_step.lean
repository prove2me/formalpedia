-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:52:58.609229+00:00
-- url     : https://prove2.me/submissions/c44793e9-a678-4113-a73f-099c6401f0cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_integral_main
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_core
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_psi_sub_wt
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_main_bounds
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_abs_emain_le
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_cnt_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (P : ℕ → Prop) {θ : ℤ} {β δ φ B ρ s : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hδ : 0 < δ)
    (hδβ : δ ≤ 1 - β) (hB : 3 ≤ B) (hφ : 0 ≤ φ) (hφB : φ ≤ B) (hρ : 0 ≤ ρ) (hs : 64 * B ≤ δ * s)
    (h : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - mainPsi θ β u| ≤ ρ * mainPsi θ β u) :
    0 ≤ Emain θ β (s ^ 16) ∧
      |φ * cnt P (s ^ 16) - Emain θ β (s ^ 16)| ≤ (3 * ρ + 4 / s) * Emain θ β (s ^ 16) := by
  have hs0 : 0 < s := by
    by_contra hc
    nlinarith
  have hsB : 64 * B ≤ s := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  have hls : 1 ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le hs0]; linarith [Real.exp_one_lt_d9]
  have hY : s ≤ s ^ 8 := le_self_pow₀ hs1 (by norm_num)
  have hYX : s ^ 8 ≤ s ^ 16 := pow_le_pow_right₀ hs1 (by norm_num)
  have hlY : 4 ≤ Real.log (s ^ 8) := by rw [Real.log_pow]; push_cast; linarith
  have hm : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16), δ * u ≤ mainPsi θ β u ∧ mainPsi θ β u ≤ 3 * u := fun u hu =>
    main_bounds hθ hβ hδ hδβ (by linarith [hu.1]) (hlY.trans (Real.log_le_log (by positivity) hu.1))
  have h' : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      |φ * (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k) - mainPsi θ β u| ≤ (ρ + 1 / s) * mainPsi θ β u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have k1 := psi_sub_wt P (u := u) (by linarith [hu.1])
    obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ u = r ^ 4 :=
      ⟨√(√u), by positivity, by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity), Real.sq_sqrt hu0.le]⟩
    have hsr : s ^ 2 ≤ r := by
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hr0.le
      rw [← hr, ← pow_mul]; exact hu.1
    have k2 : √u = r ^ 2 := by
      rw [hr, show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have k3 : Real.log u ≤ 4 * r := by
      rw [hr, Real.log_pow]; push_cast; linarith [Real.log_le_sub_one_of_pos hr0]
    have k4 : 2 * √u * Real.log u ≤ 8 * r ^ 3 := by
      rw [k2]
      have := mul_le_mul_of_nonneg_left k3 (show 0 ≤ 2 * r ^ 2 by positivity)
      linarith
    have k5 : B * (8 * r ^ 3) ≤ 1 / s * (δ * u) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs0, hr]
      have a1 : 8 * B * s ≤ δ * r := by nlinarith
      have := mul_le_mul_of_nonneg_left a1 (show 0 ≤ r ^ 3 by positivity)
      linarith
    have k6 : 1 / s * (δ * u) ≤ 1 / s * mainPsi θ β u := mul_le_mul_of_nonneg_left (hm u hu).1 (by positivity)
    have k7 : |φ * ((∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k)| ≤ B * (8 * r ^ 3) := by
      rw [abs_mul, abs_of_nonneg hφ]
      exact mul_le_mul hφB (k1.trans k4) (abs_nonneg _) (by linarith)
    have k8 := abs_le.1 (h u hu)
    rw [abs_le] at k7 ⊢
    constructor <;> linarith [k7.1, k7.2, k8.1, k8.2]
  have hc := core P θ (φ := φ) (by linarith : 0 < β) (by linarith) hYX h'
  have hI : 0 ≤ ∫ t in s ^ 8..s ^ 16, 1 / (t * Real.log t ^ 2) * mainPsi θ β t :=
    intervalIntegral.integral_nonneg hYX fun t ht => by
      have : 0 < t := by linarith [ht.1]
      exact mul_nonneg (by positivity) (le_trans (by positivity) (hm t ht).1)
  rw [integral_main θ (by linarith) (by linarith) hYX] at hI
  have e1 := abs_le.1 (abs_emain_le (u := s ^ 8) hθ hβ (by linarith) (by linarith))
  have e2 : mainPsi θ β (s ^ 8) / Real.log (s ^ 8) ≤ s ^ 8 := by
    rw [div_le_iff₀ (by linarith)]
    have := (hm _ ⟨le_rfl, hYX⟩).2
    nlinarith
  have e3 : 8 * s ^ 14 ≤ mainPsi θ β (s ^ 16) / Real.log (s ^ 16) := by
    rw [le_div_iff₀ (Real.log_pos (by linarith)), Real.log_pow]
    have a1 := (hm _ ⟨hYX, le_rfl⟩).1
    have a2 : Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hs0]
    have a3 := mul_le_mul_of_nonneg_left a2 (show 0 ≤ s ^ 14 by positivity)
    have a4 := mul_le_mul_of_nonneg_left (show 128 ≤ δ * s by linarith) (show 0 ≤ s ^ 15 by positivity)
    push_cast
    nlinarith
  have e4 : s ^ 8 ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have e5 : s ^ 10 ≤ s ^ 14 := pow_le_pow_right₀ hs1 (by norm_num)
  have e6 : 4 * s ^ 10 ≤ Emain θ β (s ^ 16) := by linarith [e1.1]
  have hY0 : 0 < s ^ 8 := by positivity
  refine ⟨by linarith, ?_⟩
  have e7 : (ρ + 1 / s) * (Emain θ β (s ^ 16) - Emain θ β (s ^ 8) + 2 * (mainPsi θ β (s ^ 8) / Real.log (s ^ 8))) ≤
      (ρ + 1 / s) * (3 * Emain θ β (s ^ 16)) := mul_le_mul_of_nonneg_left (by linarith [e1.1]) (by positivity)
  obtain ⟨c1, c2⟩ := cnt_bounds P hY0.le
  have e8 : φ * cnt P (s ^ 8) ≤ B * s ^ 8 := mul_le_mul hφB c2 c1 (by linarith)
  have e9 : 0 ≤ φ * cnt P (s ^ 8) := mul_nonneg hφ c1
  have e10 : B * s ^ 8 + 3 * s ^ 8 ≤ 1 / s * Emain θ β (s ^ 16) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left (show B + 3 ≤ s by linarith) (show 0 ≤ s ^ 9 by positivity)
    have : 0 < s ^ 10 := by positivity
    nlinarith
  have e11 := abs_le.1 (hc.trans e7)
  have e12 : 0 ≤ B * s ^ 8 := by positivity
  rw [abs_le, show 4 / s = 4 * (1 / s) by ring]
  constructor <;> linarith [e11.1, e11.2, e1.1, e1.2]
end GlobalTheory.Lin.PsiToPi
