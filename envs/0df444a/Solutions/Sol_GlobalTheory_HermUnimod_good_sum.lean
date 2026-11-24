-- Prove2me | solution 1 for GlobalTheory.HermUnimod.good_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:03:05.566832+00:00
-- url     : https://prove2.me/submissions/8fb17ead-91da-4228-97c5-2da0b15935bd

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
import Theorems.Thm_GlobalTheory_HermUnimod_intg_mul
import Theorems.Thm_GlobalTheory_HermUnimod_intg_conjT
import Theorems.Thm_GlobalTheory_HermUnimod_intg_one
import Theorems.Thm_GlobalTheory_HermUnimod_intg_fromBlocks
import Theorems.Thm_GlobalTheory_HermUnimod_intg_sub
import Theorems.Thm_GlobalTheory_HermUnimod_intg_neg
import Theorems.Thm_GlobalTheory_HermUnimod_intg_zero
import Theorems.Thm_GlobalTheory_HermUnimod_schur_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
namespace GlobalTheory.HermUnimod
theorem _root_.solution (hs : ∀ y : E, ‖star y‖ = ‖y‖) {m : Type} [Fintype m] [DecidableEq m] (H : Good m E)
    (G : Matrix (m ⊕ Unit) (m ⊕ Unit) E) (hG : G.IsHermitian) (hGi : ∀ i j, ‖G i j‖ ≤ 1)
    (hGd : ‖G.det‖ = 1) (hk : G (Sum.inr ()) (Sum.inr ()) = 1) :
    ∃ h : Matrix (m ⊕ Unit) (m ⊕ Unit) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  have hD : G.toBlocks₂₂ = 1 := by
    ext ⟨⟩ ⟨⟩
    simp [toBlocks₂₂, hk]
  have hG' : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₁ 1 := by
    rw [← hD, fromBlocks_toBlocks]
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  have hh := hG
  rw [hG', isHermitian_fromBlocks_iff] at hh
  obtain ⟨hA, hBC, -, -⟩ := hh
  rw [← hBC] at hG'
  have hAi : Intg A := fun i j => hGi _ _
  have hBi : Intg B := fun i j => hGi _ _
  have hA'i : Intg (A - B * Bᴴ) := intg_sub hAi (intg_mul hBi (intg_conjT hs hBi))
  have hA'h : (A - B * Bᴴ).IsHermitian := hA.sub (isHermitian_mul_conjTranspose_self B)
  have hA'd : ‖(A - B * Bᴴ).det‖ = 1 := by
    rw [← det_fromBlocks_one₂₂, ← hG']
    exact hGd
  obtain ⟨h', hi', hd', hh'⟩ := H _ hA'h hA'i hA'd
  refine ⟨fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1, ?_, ?_, ?_⟩
  · exact intg_mul (intg_fromBlocks intg_one intg_zero (intg_neg (intg_conjT hs hBi)) intg_one)
      (intg_fromBlocks hi' intg_zero intg_zero intg_one)
  · rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
    simp [hd']
  · rw [conjTranspose_mul, hG']
    calc (fromBlocks h' 0 0 1)ᴴ * (fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          (fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1)
        = (fromBlocks h' 0 0 1)ᴴ * ((fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          fromBlocks 1 0 (-Bᴴ) 1) * fromBlocks h' 0 0 1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [schur_conj]
        simp [fromBlocks_conjTranspose, fromBlocks_multiply, hh']
end GlobalTheory.HermUnimod
