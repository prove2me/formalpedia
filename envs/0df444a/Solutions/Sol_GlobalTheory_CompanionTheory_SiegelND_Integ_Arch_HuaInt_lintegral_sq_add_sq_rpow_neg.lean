-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:38:53.240002+00:00
-- url     : https://prove2.me/submissions/8e64febd-0660-45aa-9f1b-4dd9b90fd076

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralPowerLineScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
