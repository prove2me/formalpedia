-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.exists_blockGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:57:19.755886+00:00
-- url     : https://prove2.me/submissions/685175d5-5a29-4ad7-adc4-78272b8b5efd

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_blockOne_right_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_coe_blockGL
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_eq_blockOne_of_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) {s : K} (hs : IsUnit s)
    {h : GL (Fin (M + 1)) K} (hm : h ∈ UJ σ (blockOne s J))
    (h00 : (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) 0 0 = 1)
    (hi0 : ∀ i : Fin M, (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) i.succ 0 = 0) :
    ∃ g : GL (Fin M) K, blockGL g = h := by
  set A := (h : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hA
  set B := ((h⁻¹ : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) with hB
  have hAB : A * B = 1 := by rw [hA, hB]; exact Units.mul_inv h
  have hBA : B * A = 1 := by rw [hA, hB]; exact Units.inv_mul h
  have eA := eq_blockOne_of_col σ J hs (h := A) hm h00 hi0
  have hcol : ∀ a, (B * A) a 0 = B a 0 := by
    intro a
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [h00, hi0]
  have hB00 : B 0 0 = 1 := by rw [← hcol, hBA]; simp
  have hBi0 : ∀ i : Fin M, B i.succ 0 = 0 := by
    intro i
    rw [← hcol, hBA]
    simp [Matrix.one_apply, Fin.succ_ne_zero]
  have eB := eq_blockOne_of_col σ J hs (h := B) ((UJ σ (blockOne s J)).inv_mem hm) hB00 hBi0
  have e1 : A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ = 1 := by
    apply blockOne_right_injective (a := (1 : K)) (b := 1)
    rw [← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hAB, one_mul, blockOne_one]
  have e2 : B.submatrix Fin.succ Fin.succ * A.submatrix Fin.succ Fin.succ = 1 := by
    apply blockOne_right_injective (a := (1 : K)) (b := 1)
    rw [← one_mul (1 : K), ← blockOne_mul, ← eA, ← eB, hBA, one_mul, blockOne_one]
  refine ⟨⟨A.submatrix Fin.succ Fin.succ, B.submatrix Fin.succ Fin.succ, e1, e2⟩, ?_⟩
  apply Units.ext
  rw [coe_blockGL]
  exact eA.symm
end GlobalTheory.CompanionTheory.SW.StabFirst
