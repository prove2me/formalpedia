-- Prove2me | solution 1 for GlobalTheory.WeilM.det_siegel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:32.004807+00:00
-- url     : https://prove2.me/submissions/c33e3af2-8dd7-4fa7-b745-581510f4237b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Theorems.Thm_GlobalTheory_WeilM_ugFst_val
import Theorems.Thm_GlobalTheory_WeilM_ug_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution {JB : Matrix β β (R × R)} (hB : IsHerm (swapA R) JB) (p : UG (swapA R) (dbl JB))
    (t : Matrix β β (R × R))
    (h : ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R)) * (diagCols β : Matrix (β ⊕ β) β (R × R)) =
      (diagCols β : Matrix (β ⊕ β) β (R × R)) * t) :
    (ugFst _ p).val * (diagCols β : Matrix (β ⊕ β) β R) = (diagCols β : Matrix (β ⊕ β) β R) * cmp₁ t ∧
      (ugFst _ p).val.det * (cmp₂ t).det = (cmp₁ t).det := by
  have hD1 : (diagCols β : Matrix (β ⊕ β) β (R × R)).map (RingHom.fst R R) = diagCols β := by
    rw [diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have hD2 : (diagCols β : Matrix (β ⊕ β) β (R × R)).map (RingHom.snd R R) = diagCols β := by
    rw [diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 := congrArg (fun M => M.map (RingHom.fst R R)) h
  have h2 := congrArg (fun M => M.map (RingHom.snd R R)) h
  simp only [Matrix.map_mul] at h1 h2
  rw [hD1] at h1
  rw [hD2] at h2
  have e1 : (ugFst _ p).val * diagCols β = diagCols β * cmp₁ t := by rw [ugFst_val]; exact h1
  have e2 : cmp₂ ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R)) * diagCols β = diagCols β * cmp₂ t := h2
  refine ⟨e1, ?_⟩
  obtain ⟨a, b, c, d, hP⟩ : ∃ a b c d, (ugFst (dbl JB) p).val = fromBlocks a b c d :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks _).symm⟩

  have hdc : (diagCols β : Matrix (β ⊕ β) β R) = Matrix.fromRows 1 1 := rfl
  have e1' : fromBlocks a b c d * (Matrix.fromRows 1 1 : Matrix (β ⊕ β) β R) = Matrix.fromRows 1 1 * cmp₁ t := by
    rw [← hP, ← hdc]; exact e1
  rw [Matrix.fromBlocks_mul_fromRows] at e1'
  obtain ⟨ha, hc⟩ := Matrix.fromRows_inj (e1'.trans (Matrix.fromRows_mul (1 : Matrix β β R) 1 (cmp₁ t)))
  simp only [Matrix.mul_one, Matrix.one_mul] at ha hc

  have hS : fromBlocks a b c d * fromBlocks (1 : Matrix β β R) 0 1 1 =
      fromBlocks (1 : Matrix β β R) 0 1 1 * fromBlocks (cmp₁ t) b 0 (d - b) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul, zero_add]
    rw [ha, hc, add_sub_cancel]
  have hdetP : (ugFst (dbl JB) p).val.det = (cmp₁ t).det * (d - b).det := by
    have hd := congrArg Matrix.det hS
    simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, one_mul,
      Matrix.det_fromBlocks_zero₂₁] at hd
    rw [hP, hd]

  have rel := ug_rel p
  have hK : (ugFst (dbl JB) p).valᵀ * (cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R)) * cmp₂ t = cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R) := by
    calc (ugFst (dbl JB) p).valᵀ * (cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R)) * cmp₂ t
        = (ugFst (dbl JB) p).valᵀ * cmp₁ (dbl JB) * ((diagCols β : Matrix (β ⊕ β) β R) * cmp₂ t) := by simp only [Matrix.mul_assoc]
      _ = (ugFst (dbl JB) p).valᵀ * cmp₁ (dbl JB) * (cmp₂ ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R)) * (diagCols β : Matrix (β ⊕ β) β R)) := congrArg (_ * ·) e2.symm
      _ = ((ugFst (dbl JB) p).valᵀ * cmp₁ (dbl JB) * cmp₂ ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R))) * (diagCols β : Matrix (β ⊕ β) β R) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [rel]
  have hDB : cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R) = fromRows (cmp₁ JB) (-cmp₁ JB) := by
    have hb : cmp₁ (dbl JB) = fromBlocks (cmp₁ JB) 0 0 (-cmp₁ JB) := by
      ext (i | i) (j | j) <;> simp [dbl]
    rw [hb, hdc, Matrix.fromBlocks_mul_fromRows]
    simp
  rw [hDB, hP, Matrix.fromBlocks_transpose, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul] at hK
  obtain ⟨-, hK2⟩ := Matrix.fromRows_inj hK
  have hY : (d - b)ᵀ * cmp₁ JB * cmp₂ t = cmp₁ JB := by
    calc (d - b)ᵀ * cmp₁ JB * cmp₂ t = -((bᵀ * cmp₁ JB + dᵀ * -cmp₁ JB) * cmp₂ t) := by
          rw [Matrix.transpose_sub]; noncomm_ring
      _ = cmp₁ JB := by rw [hK2, neg_neg]
  have hdetY : (d - b).det * (cmp₂ t).det = 1 := by
    have hd := congrArg Matrix.det hY
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
    refine hB.isUnit_cmp₁.mul_left_cancel ?_
    rw [mul_one]
    calc (cmp₁ JB).det * ((d - b).det * (cmp₂ t).det) = (d - b).det * (cmp₁ JB).det * (cmp₂ t).det := by ring
      _ = _ := hd
  rw [hdetP, mul_assoc, hdetY, mul_one]
end GlobalTheory.WeilM
