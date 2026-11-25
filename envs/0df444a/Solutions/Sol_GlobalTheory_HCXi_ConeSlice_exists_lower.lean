-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.exists_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:05.853487+00:00
-- url     : https://prove2.me/submissions/8c3ea7dd-3d25-4d0b-813f-c96360ee8150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeSlice
namespace GlobalTheory.HCXi.ConeSlice
theorem _root_.solution {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * sqLen v ≤ sqLen (g *ᵥ v) := by
  set L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (Matrix.toLin' g⁻¹)
  refine ⟨((n * ‖L‖ ^ 2) + 1)⁻¹, by positivity, fun v => ?_⟩
  have h0 : ∀ u : Fin n → ℂ, 0 ≤ sqLen u := fun u =>
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h1 : ∀ u : Fin n → ℂ, sqLen u ≤ n * ‖u‖ ^ 2 := fun u => by
    calc sqLen u ≤ ∑ _i : Fin n, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [Complex.normSq_eq_norm_sq]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2
      _ = _ := by simp
  have h2 : ∀ u : Fin n → ℂ, ‖u‖ ^ 2 ≤ sqLen u := fun u => by
    have : ‖u‖ ≤ Real.sqrt (sqLen u) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      apply Real.le_sqrt_of_sq_le
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (f := fun i => Complex.normSq (u i))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    calc ‖u‖ ^ 2 ≤ Real.sqrt (sqLen u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (h0 u)
  have h3 : L (g *ᵥ v) = v := by
    simp [L, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g (Ne.isUnit hg)]
  have h4 : ‖v‖ ≤ ‖L‖ * ‖g *ᵥ v‖ := by
    conv_lhs => rw [← h3]
    exact L.le_opNorm _
  have h5 : ‖v‖ ^ 2 ≤ ‖L‖ ^ 2 * sqLen (g *ᵥ v) := by
    calc ‖v‖ ^ 2 ≤ (‖L‖ * ‖g *ᵥ v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h4 2
      _ = ‖L‖ ^ 2 * ‖g *ᵥ v‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h2 _) (by positivity)
  rw [inv_mul_le_iff₀ (by positivity)]
  have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg (α := ℝ) n)
  have := h1 v
  have := h0 (g *ᵥ v)
  nlinarith
end GlobalTheory.HCXi.ConeSlice
