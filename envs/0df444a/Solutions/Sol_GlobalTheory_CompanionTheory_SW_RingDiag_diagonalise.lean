-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:48.703395+00:00
-- url     : https://prove2.me/submissions/3871ad02-366e-4097-baa3-85a1f1080e87

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinatePolynomialsFormMemKernelDifferential
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_det_bd
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_cT_bd
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_diagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_det_uni
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_schur_step
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_det_cT
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_cT_congr_herm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_corner
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_unimodular
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SemilocalColumn_exists_invertible_first_column

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ

set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RingDiag
open HeckeCharacterZeroLocus.SiegelWeilU
variable {A : Type} [CommRing A] {m : ℕ}
namespace GlobalTheory.CompanionTheory.SW.RingDiag
theorem _root_.solution : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by
  intro A _ _ σ hσ H m
  induction m with
  | zero =>
    intro J _ _
    exact ⟨1, Fin.elim0, by simp, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ m ih =>
    intro J hJ hdet
    obtain ⟨x, hx⟩ := H m J hJ hdet
    obtain ⟨b, hb⟩ := hx.exists_left_inv
    obtain ⟨g₀, hg₀, hcol⟩ := GlobalTheory.CompanionTheory.SW.SemilocalColumn.exists_invertible_first_column A m x (unimodular σ J x b hb)
    set K := cT σ g₀ * J * g₀ with hKdef
    have hK : ∀ i j, σ (K j i) = K i j := cT_congr_herm σ hσ J g₀ hJ
    have hcorner : K 0 0 = hform σ J x x := corner σ J g₀ x hcol
    have hbK : b * K 0 0 = 1 := by rw [hcorner]; exact hb
    have hβ : IsUnit (K 0 0) := by rw [hcorner]; exact hx
    have hσβ : σ (K 0 0) = K 0 0 := hK 0 0
    have hσb : σ b = b := by
      have h1 : σ b * K 0 0 = 1 := by
        have := congrArg σ hbK
        rwa [map_mul, hσβ, map_one] at this
      calc σ b = σ b * (K 0 0 * b) := by rw [mul_comm (K 0 0), hbK, mul_one]
        _ = (σ b * K 0 0) * b := by ring
        _ = b := by rw [h1, one_mul]
    set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
    have hstep := schur_step σ K hK b hbK hσb
    have hKdet : IsUnit K.det := by
      rw [hKdef, Matrix.det_mul, Matrix.det_mul, det_cT]
      exact ((hg₀.map σ).mul hdet).mul hg₀
    have hJ₁det : IsUnit (schur K b).det := by
      have h2 : (K 0 0) * (schur K b).det = K.det := by
        rw [← det_bd, ← hstep, Matrix.det_mul, Matrix.det_mul, det_cT, det_uni]; simp
      rw [← h2] at hKdet
      exact isUnit_of_mul_isUnit_right hKdet
    have hJ₁ : ∀ i j, σ (schur K b j i) = schur K b i j := by
      intro i j
      simp only [schur, map_sub, map_mul, hσb, hK]
      ring
    obtain ⟨g₁, d₁, hg₁, hd₁, hdiag⟩ := ih (schur K b) hJ₁ hJ₁det
    refine ⟨g₀ * uni r * bd 1 g₁, Fin.cons (K 0 0) d₁, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, det_uni, det_bd]
      simpa using hg₀.mul hg₁
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simpa using ⟨hβ, hσβ⟩
      · simpa using hd₁ i'
    · have e : cT σ (g₀ * uni r * bd 1 g₁) * J * (g₀ * uni r * bd 1 g₁) =
          cT σ (bd 1 g₁) * (cT σ (uni r) * K * uni r) * bd 1 g₁ := by
        rw [hKdef, cT_mul, cT_mul]
        simp only [Matrix.mul_assoc]
      rw [e, hstep, cT_bd, bd_mul, bd_mul, hdiag, map_one, one_mul, mul_one, bd_diagonal]
end GlobalTheory.CompanionTheory.SW.RingDiag
