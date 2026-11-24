-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RingDiag.schur_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:07.961809+00:00
-- url     : https://prove2.me/submissions/dd4b9a6e-1bc1-4d78-ab44-44a2f0461156

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinatePolynomialsFormMemKernelDifferential
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_mul_uni
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_cT_uni_mul
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
theorem _root_.solution (σ : A →+* A) (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hK : ∀ i j, σ (K j i) = K i j) (b : A) (hb : b * K 0 0 = 1) (hσb : σ b = b) :
    cT σ (uni fun j => -(b * K 0 j.succ)) * K * (uni fun j => -(b * K 0 j.succ)) =
      bd (K 0 0) (schur K b) := by
  set r : Fin m → A := fun j => -(b * K 0 j.succ) with hr
  have hσr : ∀ i, σ (r i) = -(b * K i.succ 0) := by
    intro i; simp [hr, hσb, hK]
  have hzero : ∀ j : Fin m, K 0 j.succ + K 0 0 * r j = 0 := by
    intro j
    have : K 0 0 * r j = -((b * K 0 0) * K 0 j.succ) := by simp only [hr]; ring
    rw [this, hb]; ring
  rw [Matrix.mul_assoc]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [(cT_uni_mul σ _ r 0).1, (mul_uni K r 0).1]; simp
  · rw [(cT_uni_mul σ _ r _).1, (mul_uni K r 0).2, hzero]; simp
  · rw [(cT_uni_mul σ _ r 0).2, (mul_uni K r _).1, (mul_uni K r 0).1, hσr]
    simp only [bd_succ_zero]
    have : b * K i'.succ 0 * K 0 0 = (b * K 0 0) * K i'.succ 0 := by ring
    rw [neg_mul, this, hb]; ring
  · rw [(cT_uni_mul σ _ r _).2, (mul_uni K r _).2, (mul_uni K r 0).2, hzero, hσr]
    simp only [bd_succ_succ, schur, hr]; ring
end GlobalTheory.CompanionTheory.SW.RingDiag
