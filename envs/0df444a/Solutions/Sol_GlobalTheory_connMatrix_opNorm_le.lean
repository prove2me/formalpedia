-- Prove2me | solution 1 for GlobalTheory.connMatrix_opNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:01.310994+00:00
-- url     : https://prove2.me/submissions/25646546-cc02-4d0b-83ef-bf334a3a4c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLe
import Theorems.Thm_GlobalTheory_ConnPointwise_opNorm_one_le_of_entry
import Theorems.Thm_GlobalTheory_ConnPointwise_inv_entry_le
import Theorems.Thm_GlobalTheory_ConnPointwise_entry_le_of_mulVec
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory
open GlobalTheory.ConnPointwise
namespace GlobalTheory
theorem _root_.solution : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  intro g a Y Bs Dm s t c K W hc hK hW hY ht hB hD
  obtain ⟨hdet, hinv⟩ := inv_entry_le Y hc hY
  have hmapinv : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply inv_eq_left_inv
    show (Y⁻¹).map Complex.ofRealHom * Y.map Complex.ofRealHom = 1
    rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBe : ∀ i j k, |(Y⁻¹ * Bs i) j k| ≤ W / t i := fun i j k => by
    have := entry_le_of_mulVec _ hW (hB i) j k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (ht i)] at this
    rw [le_div_iff₀ (ht i), mul_comm]; exact this
  have hE0 : 0 ≤ (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := by
    have : 0 ≤ ∑ i, ‖s i‖ / t i := Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (ht i).le
    positivity
  refine opNorm_one_le_of_entry _ hE0 fun j k => ?_
  rw [hmapinv]
  have hexp : ((Y⁻¹).map Complex.ofReal * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) j k
      = (1 / (2 * Complex.I)) * (∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)) := by
    simp only [mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, map_apply, smul_eq_mul, ofReal_sum,
      ofReal_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, norm_mul]
  have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1 := by simp; norm_num
  have hA : ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ g * K / c := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l, ‖((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ ∑ _l : Fin g, 1 / c * K :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hinv j l) (hD l k) (norm_nonneg _) (by positivity)
      _ = g * K / c := by simp; ring
  have hBs : ‖∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖ ≤ W * ∑ i, ‖s i‖ / t i := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s i‖ * |(Y⁻¹ * Bs i) j k| ≤ ‖s i‖ * (W / t i) :=
          mul_le_mul_of_nonneg_left (hBe i j k) (norm_nonneg _)
      _ = W * (‖s i‖ / t i) := by ring
  calc ‖(1 / (2 * Complex.I) : ℂ)‖ * ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖
      ≤ 1 * ((g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i) :=
        mul_le_mul hhalf ((norm_add_le _ _).trans (add_le_add hA hBs)) (norm_nonneg _) zero_le_one
    _ = (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := one_mul _
end GlobalTheory
