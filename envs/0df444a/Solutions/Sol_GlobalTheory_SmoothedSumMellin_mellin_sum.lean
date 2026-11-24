-- Prove2me | solution 1 for GlobalTheory.SmoothedSumMellin.mellin_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:06:43.297354+00:00
-- url     : https://prove2.me/submissions/c11997a0-cfe4-4c7e-86a6-b7519a1fec1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
import Theorems.Thm_GlobalTheory_SmoothedSumMellin_integral_norm_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology
open GlobalTheory GlobalTheory.SmoothedSumMellin
namespace GlobalTheory.SmoothedSumMellin
theorem _root_.solution {ι : Type} [Countable ι] {a : ι → ℂ} {N : ι → ℝ} {wt : ℝ → ℂ} {s : ℂ}
    (hw : MellinConvergent wt s) (hN : ∀ i, a i ≠ 0 → 1 ≤ N i)
    (hsum : Summable fun i => ‖a i‖ * N i ^ (-s.re)) :
    mellin (fun t : ℝ => ∑' i, a i * wt (t * N i)) s
      = mellin wt s * ∑' i, a i * (N i : ℂ) ^ (-s) := by
  have hI : ∀ i, a i ≠ 0 → 0 < N i := fun i hi => by linarith [hN i hi]
  set I := ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ with hIdef
  set G : ι → ℝ → ℂ := fun i t => (t : ℂ) ^ (s - 1) • (a i * wt (t * N i)) with hG
  have hGint : ∀ i, Integrable (G i) (volume.restrict (Ioi 0)) := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have hc : MellinConvergent (fun t => wt (t * N i)) s := by
        have := (MellinConvergent.comp_mul_left (f := wt) (s := s) (hI i hai)).2 hw
        simpa only [mul_comm] using this
      exact hc.const_smul (a i)
  have hGnorm : ∀ i, ∫ t in Ioi (0 : ℝ), ‖G i t‖ = ‖a i‖ * N i ^ (-s.re) * I := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have h1 : ∀ t, ‖G i t‖ = ‖a i‖ * ‖(t : ℂ) ^ (s - 1) • wt (t * N i)‖ := fun t => by
        simp only [hG, _root_.norm_smul, norm_mul]
        ring
      simp_rw [h1]
      rw [integral_const_mul, integral_norm_comp wt s (hI i hai)]
      ring
  have hsumG : Summable fun i => ∫ t in Ioi (0 : ℝ), ‖G i t‖ := by
    simp_rw [hGnorm]
    exact hsum.mul_right I
  have key := integral_tsum_of_summable_integral_norm hGint hsumG
  have hM : mellin (fun t : ℝ => ∑' i, a i * wt (t * N i)) s = ∫ t in Ioi (0 : ℝ), ∑' i, G i t := by
    rw [mellin]
    congr 1
    funext t
    simp only [hG, smul_eq_mul]
    rw [tsum_mul_left]
  have hGi : ∀ i, ∫ t in Ioi (0 : ℝ), G i t = a i * (N i : ℂ) ^ (-s) * mellin wt s := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have h1 : ∫ t in Ioi (0 : ℝ), G i t = a i * mellin (fun t => wt (t * N i)) s := by
        rw [mellin, ← integral_const_mul]
        congr 1
        funext t
        simp only [hG, smul_eq_mul]
        ring
      rw [h1, mellin_comp_mul_right wt s (hI i hai), smul_eq_mul, mul_assoc]
  rw [hM, ← key]
  simp_rw [hGi]
  rw [tsum_mul_right, mul_comm]
end GlobalTheory.SmoothedSumMellin
