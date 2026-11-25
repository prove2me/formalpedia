-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.gauss_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:36.435192+00:00
-- url     : https://prove2.me/submissions/99e3e0da-cfdd-4045-8d2a-415008785b92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
namespace GlobalTheory.HCXi.ConeOne
theorem _root_.solution {X : Type*} [MeasurableSpace X] (m : Measure X) (q : X → ℝ) (hq : Measurable q) (h0 : ∀ v, 0 ≤ q v)
    (d : ℕ) (hh : ∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ v, f (s * q v) ∂m) = ENNReal.ofReal (s ^ (-(d : ℝ))) * ∫⁻ v, f (q v) ∂m)
    (hfin : m {v | q v ≤ 1} < ∞) : (∫⁻ v, ENNReal.ofReal (Real.exp (-q v)) ∂m) ≠ ∞ := by
  set f : ℝ → ℝ≥0∞ := (Set.Iic (1 : ℝ)).indicator 1 with hf
  have hfm : Measurable f := measurable_const.indicator measurableSet_Iic
  have hM : (∫⁻ v, f (q v) ∂m) = m {v | q v ≤ 1} := by
    rw [← lintegral_indicator_one (measurableSet_le hq measurable_const)]
    rfl
  have hle : ∀ v, ENNReal.ofReal (Real.exp (-q v)) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v) := by
    intro v
    refine le_trans ?_ (ENNReal.le_tsum ⌊q v⌋₊)
    have h1 : ((⌊q v⌋₊ : ℝ) + 1)⁻¹ * q v ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity), mul_one]
      exact (Nat.lt_floor_add_one _).le
    rw [hf, Set.indicator_of_mem (show _ ∈ Set.Iic (1 : ℝ) from h1), Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg (Nat.floor_le (h0 v))))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun v => ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v)) m :=
    fun n => ((hfm.comp (hq.const_mul _)).const_mul _).aemeasurable
  rw [lintegral_tsum hmeas]
  have hterm : ∀ n : ℕ, (∫⁻ v, ENNReal.ofReal (Real.exp (-(n : ℝ))) * f (((n : ℝ) + 1)⁻¹ * q v) ∂m) =
      ENNReal.ofReal (Real.exp (-(n : ℝ)) * ((n : ℝ) + 1) ^ d) * m {v | q v ≤ 1} := by
    intro n
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hh _ (by positivity) f hfm, hM, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow, inv_inv]
  simp only [hterm]
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_ne_top ?_ hfin.ne
  have hsum : Summable fun n : ℕ => Real.exp (-(n : ℝ)) * ((n : ℝ) + 1) ^ d := by
    have h1 := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul d (r := 1) one_pos)
    refine (h1.mul_left (Real.exp 1)).congr fun n => ?_
    push_cast
    rw [mul_left_comm, ← Real.exp_add, mul_comm]
    congr 2
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  exact ENNReal.ofReal_ne_top
end GlobalTheory.HCXi.ConeOne
