-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.unip_iff_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:14:12.665569+00:00
-- url     : https://prove2.me/submissions/2a1fa75d-751c-4a08-80d3-7a63119981e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

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
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (M : Matrix (n ⊕ n) (n ⊕ n) B) :
    ((M - 1) * Matrix.fromRows (1 : Matrix n n B) (1 : Matrix n n B) = 0 ∧
      Matrix.fromCols (1 : Matrix n n B) (-1 : Matrix n n B) * (M - 1) = 0) ↔
      ∃ X, M = blk X := by
  constructor
  · rintro ⟨h1, h2⟩
    have hM : M - 1 = fromBlocks (M - 1).toBlocks₁₁ (M - 1).toBlocks₁₂ (M - 1).toBlocks₂₁ (M - 1).toBlocks₂₂ :=
      (fromBlocks_toBlocks (M - 1)).symm
    set a := (M - 1).toBlocks₁₁
    set b := (M - 1).toBlocks₁₂
    set c := (M - 1).toBlocks₂₁
    set d := (M - 1).toBlocks₂₂
    rw [hM, fromBlocks_mul_fromRows] at h1
    rw [hM, fromCols_mul_fromBlocks] at h2
    have e1 := congrArg Matrix.toRows₁ h1
    have e2 := congrArg Matrix.toRows₂ h1
    have e3 := congrArg Matrix.toCols₁ h2
    have e4 := congrArg Matrix.toCols₂ h2
    have z1 : toRows₁ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z2 : toRows₂ (0 : Matrix (n ⊕ n) n B) = 0 := by ext; rfl
    have z3 : toCols₁ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    have z4 : toCols₂ (0 : Matrix n (n ⊕ n) B) = 0 := by ext; rfl
    simp only [toRows₁_fromRows, toRows₂_fromRows, toCols₁_fromCols, toCols₂_fromCols, Matrix.mul_one,
      Matrix.one_mul, Matrix.neg_mul, z1, z2, z3, z4] at e1 e2 e3 e4
    have hb : b = -a := eq_neg_of_add_eq_zero_right e1
    have hc : c = a := (sub_eq_zero.1 (by simpa [sub_eq_add_neg] using e3)).symm
    have hd : d = -a := by rw [← hc]; exact eq_neg_of_add_eq_zero_right e2
    refine ⟨a, ?_⟩
    have : M = 1 + (M - 1) := by abel
    rw [this, hM, hb, hc, hd, blk, ← fromBlocks_one, fromBlocks_add]
    simp [sub_eq_add_neg]
  · rintro ⟨X, rfl⟩
    have e : blk X - 1 = fromBlocks X (-X) X (-X) := by
      rw [blk, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
      congr 1 <;> abel
    rw [e, fromBlocks_mul_fromRows, fromCols_mul_fromBlocks]
    constructor <;> ext i j <;> (try rcases i with i | i) <;> (try rcases j with j | j) <;>
      simp [Matrix.fromRows, Matrix.fromCols, Sum.elim_inl, Sum.elim_inr] <;> rfl
end GlobalTheory.EisBL.NilAlg
