-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmTangent.tendsto_pow_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:17:03.497031+00:00
-- url     : https://prove2.me/submissions/b63d3379-b29e-4c5b-af14-43a33c19469a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
import Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_norm_pow_sub_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmTangent
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A] [CompleteSpace A]
namespace GlobalTheory.CompanionTheory.SmTangent
theorem _root_.solution (h1 : ‖(1 : A)‖ ≤ 1) (γ : ℝ → A) (Y : A) (h0 : γ 0 = 1)
    (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp (t • Y))) := by
  set E : ℝ → A := fun s => NormedSpace.exp (s • Y) with hE
  have hE0 : E 0 = 1 := by simp [hE]
  have hEd : HasDerivAt E Y 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
    simpa using this
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  obtain ⟨M1, hM1⟩ := hd.isBigO_sub.bound
  obtain ⟨M2, hM2⟩ := hEd.isBigO_sub.bound
  set M : ℝ := max (max M1 M2) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  set c : ℝ := M * |t| with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ (f : ℝ → A) (M' : ℝ), M' ≤ M → f 0 = 1 →
      (∀ᶠ s in 𝓝 (0 : ℝ), ‖f s - f 0‖ ≤ M' * ‖s - 0‖) →
      ∀ᶠ k : ℕ in atTop, ‖f (t / k)‖ ≤ 1 + c / k := by
    intro f M' hM' hf hb
    filter_upwards [hs.eventually hb, eventually_gt_atTop 0] with k hk hk0
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [hf] at hk
    have e : f (t / k) = 1 + (f (t / k) - 1) := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add h1 (hk.trans ?_))
    have : ‖t / (k : ℝ) - 0‖ = |t| / k := by
      simp [abs_div]
    rw [this, hc, mul_div_assoc]
    gcongr
  have ha := hbound γ M1 ((le_max_left _ _).trans (le_max_left _ _)) h0 hM1
  have hb := hbound E M2 ((le_max_right _ _).trans (le_max_left _ _)) hE0 hM2
  have hpow : ∀ k : ℕ, 0 < k → (1 + c / k) ^ k ≤ Real.exp c := by
    intro k hk
    have hk' : (k : ℝ) ≠ 0 := by positivity
    calc (1 + c / k) ^ k ≤ (Real.exp (c / k)) ^ k := by
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp c := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hD : HasDerivAt (fun s => γ s - E s) 0 0 := by
    have := hd.sub hEd
    rw [sub_self] at this
    exact this
  have hlo : (fun s => γ s - E s) =o[𝓝 0] (fun s : ℝ => s) := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 hD
    simpa [h0, hE0] using this
  have hK : Tendsto (fun k : ℕ => Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (k : ℝ) * ‖γ (t / k) - E (t / k)‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hp : 0 < |t| + 1 := by positivity
      have hcε : 0 < ε / (|t| + 1) := by positivity
      filter_upwards [(hlo.comp_tendsto hs).def hcε, eventually_gt_atTop 0] with k hk hk0
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
      simp only [Function.comp] at hk
      have e : ‖t / (k : ℝ)‖ = |t| / k := by simp [abs_div]
      rw [e] at hk
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      calc (k : ℝ) * ‖γ (t / k) - E (t / k)‖ ≤ k * (ε / (|t| + 1) * (|t| / k)) := by gcongr
        _ = ε * (|t| / (|t| + 1)) := by field_simp
        _ < ε * 1 := by
          gcongr
          rw [div_lt_one hp]
          linarith
        _ = ε := mul_one _
    simpa using this.const_mul (Real.exp c)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [ha, hb, eventually_gt_atTop 0] with k hak hbk hk0
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hC : 1 ≤ 1 + c / k := by
    have : 0 ≤ c / k := by positivity
    linarith
  have hEk : NormedSpace.exp (t • Y) = E (t / k) ^ k := by
    simp only [hE]
    letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  rw [hEk]
  refine (norm_pow_sub_pow_le h1 hC hak hbk k).trans ?_
  have := hpow k hk0
  have hn : 0 ≤ ‖γ (t / k) - E (t / k)‖ := norm_nonneg _
  calc (k : ℝ) * (1 + c / k) ^ k * ‖γ (t / k) - E (t / k)‖
      ≤ k * Real.exp c * ‖γ (t / k) - E (t / k)‖ := by gcongr
    _ = Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖) := by ring
end GlobalTheory.CompanionTheory.SmTangent
