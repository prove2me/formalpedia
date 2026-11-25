-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.exists_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:54:18.771346+00:00
-- url     : https://prove2.me/submissions/c3b16cf3-98aa-43ca-910d-97029662ad19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_mul
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_one
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_dvd
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_sub
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_conj
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_inv_smul
import Theorems.Thm_GlobalTheory_SW_ShortStep_exists_span
import Theorems.Thm_GlobalTheory_SW_RowExt_exists_right_inv
import Theorems.Thm_GlobalTheory_SW_exists_nearly_primitive
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution (m D b : ℕ) (hD : 0 < D) (hb : 0 < b) : ∃ D' : ℕ, 0 < D' ∧
    ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) E) (V w : Matrix (Fin 1) (Fin n) E), n = m + 2 →
    Gᴴ = G → G.det ≠ 0 → Den D G → Den D G⁻¹ → IntM V → Den b w → V * G * Vᴴ = 0 →
    V * G * wᴴ = 1 → w * G * Vᴴ = 1 → w * G * wᴴ = 0 →
    ∃ (B : Matrix (Fin m) (Fin n) E) (S : Matrix (Fin n) (Fin m) E), IntM B ∧ V * S = 0 ∧
      B * S = 1 ∧ B * G * Vᴴ = 0 ∧ S * B = 1 - G * wᴴ * V - G * Vᴴ * w ∧
      (B * G * Bᴴ).det ≠ 0 ∧ Den D' (B * G * Bᴴ) ∧ Den D' (B * G * Bᴴ)⁻¹ := by
  obtain ⟨c, C, hc, hprim⟩ := exists_nearly_primitive E m
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨D * b * c * D * (D * b * c), by positivity,
    fun n G V w hn hG h0 hD1 hD2 hVi hw h1 h2 h3 h4 => ?_⟩
  obtain ⟨B₀, S₀, hB₀, hli, hBF, hSB⟩ := exists_span (E := E) (m := m) (by simpa using hn)
    (fromRows V w) (fromCols (G * wᴴ) (G * Vᴴ)) (by
      rw [fromRows_mul_fromCols]
      simp only [← Matrix.mul_assoc, h1, h2, h3, h4, fromBlocks_one])
  rw [fromCols_mul_fromRows, ← sub_sub] at hSB
  obtain ⟨a, ha, -, hBi, hpr⟩ := hprim _ B₀ hB₀ hli
  have hBF' : a * B₀ * fromCols (G * wᴴ) (G * Vᴴ) = 0 := by
    rw [Matrix.mul_assoc, hBF, Matrix.mul_zero]
  have hli' : LinearIndependent E fun i => (a * B₀) i := by
    refine Matrix.vecMul_injective_iff.1 fun x y e => ?_
    refine Matrix.vecMul_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det a).2 ha.isUnit) ?_
    refine Matrix.vecMul_injective_iff.2 hli ?_
    simpa [vecMul_vecMul] using e
  have hSB' : S₀ * a⁻¹ * (a * B₀) = 1 - G * wᴴ * V - G * Vᴴ * w := by
    rw [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ ha.isUnit, hSB]
  generalize a * B₀ = B at hBi hpr hBF' hli' hSB'
  generalize S₀ * a⁻¹ = S at hSB'
  obtain ⟨X, hX, hBX⟩ := RowExt.exists_right_inv (c : E) B hBi hli' hpr
  rw [mul_fromCols, ← fromCols_zero] at hBF'
  obtain ⟨e1, e2⟩ := (fromCols_ext_iff _ _ _ _).1 hBF'
  obtain ⟨P, hP⟩ : ∃ P, P = 1 - G * wᴴ * V - G * Vᴴ * w := ⟨_, rfl⟩
  have hPd : Den (D * b) P := by
    rw [hP]
    refine den_sub (den_sub (den_dvd (den_one fun i j => ?_) (one_dvd _)) ?_) ?_
    · rw [Matrix.one_apply]; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · simpa using den_mul (den_mul hD1 (den_conj hw)) (den_one hVi)
    · simpa using den_mul (den_mul hD1 (den_conj (den_one hVi))) hw
  have hBP : B * P = B := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc B (G * wᴴ),
      ← Matrix.mul_assoc B (G * Vᴴ), e1, e2]; simp
  have hVP : V * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, h1, h2]; simp
  have hPG : G * Pᴴ = P * G := by
    simp [hP, conjTranspose_mul, hG, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, sub_right_comm]
  rw [← hP] at hSB'
  have hS : S = (c : E)⁻¹ • (P * X) := by
    rw [← hSB', Matrix.mul_assoc, hBX]; simp [smul_smul, hc0]
  have hSd : Den (D * b * c) S := by
    have := den_inv_smul hc (den_mul hPd (den_one hX))
    rwa [mul_one, ← hS] at this
  have hBS : B * S = 1 := by
    rw [hS, Matrix.mul_smul, ← Matrix.mul_assoc, hBP, hBX]; simp [smul_smul, hc0]
  have hinv : B * G * Bᴴ * (Sᴴ * G⁻¹ * S) = 1 := by
    have : B * G * Bᴴ * (Sᴴ * G⁻¹ * S) = B * (G * (S * B)ᴴ) * G⁻¹ * S := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hSB', hPG, ← Matrix.mul_assoc, hBP, mul_nonsing_inv_cancel_right _ _ h0.isUnit, hBS]
  refine ⟨B, S, hBi, ?_, hBS, by rw [Matrix.mul_assoc, e2], by rw [hSB', hP],
    (isUnit_det_of_right_inverse hinv).ne_zero, ?_, ?_⟩
  · rw [hS, Matrix.mul_smul, ← Matrix.mul_assoc, hVP]; simp
  · exact den_dvd (den_mul (den_mul (den_one hBi) hD1) (den_conj (den_one hBi)))
      ⟨b * c * D * (D * b * c), by ring⟩
  · rw [inv_eq_right_inv hinv]
    exact den_mul (den_mul (den_conj hSd) hD2) hSd
end GlobalTheory.SW.ShortStep
