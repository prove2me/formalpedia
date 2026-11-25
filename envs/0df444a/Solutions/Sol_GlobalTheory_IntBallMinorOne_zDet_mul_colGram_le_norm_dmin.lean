-- Prove2me | solution 1 for GlobalTheory.IntBallMinorOne.zDet_mul_colGram_le_norm_dmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:46.404329+00:00
-- url     : https://prove2.me/submissions/79f1e501-f901-483f-9a0d-e7a81c8ef32c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
import Theorems.Thm_GlobalTheory_IntBallMinorOne_schur_bound
import Theorems.Thm_GlobalTheory_IntBallMinorOne_lowMat_diag
import Theorems.Thm_GlobalTheory_IntBallMinorOne_lowMat_upper
import Theorems.Thm_GlobalTheory_IntBallMinorOne_mat_nFrame
import Theorems.Thm_GlobalTheory_IntBallMinorOne_gram_mul_right
import Theorems.Thm_GlobalTheory_IntBallMinorOne_eR_inl
import Theorems.Thm_GlobalTheory_IntBallMinorOne_eR_inr
import Theorems.Thm_GlobalTheory_IntBallMinorOne_eC_inl
import Theorems.Thm_GlobalTheory_IntBallMinorOne_eC_inr
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ExhaustionFrames_zDet_pos
import Theorems.Thm_GlobalTheory_IntBall_nmat_eq_lowMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IntBallMinorOne.eR_inl
attribute [local simp] GlobalTheory.IntBallMinorOne.eR_inr
attribute [local simp] GlobalTheory.IntBallMinorOne.eC_inl
attribute [local simp] GlobalTheory.IntBallMinorOne.eC_inr

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBallMinorOne
namespace GlobalTheory.IntBallMinorOne
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 = 1 →
    ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)),
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.castSucc ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  intro E _ _ _ r X hp x0 z hz τ k
  have hr : 1 ≤ r := by have := k.isLt; omega
  have hk : (k : ℕ) + 1 ≤ r := by have := k.isLt; omega
  set w := zOf X z τ with hw
  set L : Matrix (Fin r) (Fin r) ℂ := lowMat w with hL
  set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hD
  have hgram : gram τ.1 X.Gm (mat (point X x0 z) τ) = Lᵀ * D * L.map (starRingEnd ℂ) := by
    have : mat (point X x0 z) τ = mat x0.1 τ * mat (nFrame X z) τ := rfl
    rw [this, gram_mul_right, x0.2 τ, mat_nFrame X hp]
  set f : Fin 1 ⊕ Fin k → Fin r := fun j => Fin.castLE hk (eC k j) with hf
  set A : Matrix (Fin 1 ⊕ Fin (r - 1)) (Fin 1 ⊕ Fin k) ℂ := L.submatrix (eR r hr) f with hA
  set D' : Matrix (Fin 1 ⊕ Fin (r - 1)) (Fin 1 ⊕ Fin (r - 1)) ℂ := D.submatrix (eR r hr) (eR r hr) with hD'
  have hdmin : dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩ = (Aᵀ * D' * A.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [hgram, ← Matrix.det_submatrix_equiv_self (eC k), Matrix.submatrix_submatrix]
    congr 1
    rw [Matrix.submatrix_mul _ _ _ (eR r hr) _ (eR r hr).bijective,
      Matrix.submatrix_mul _ _ _ (eR r hr) _ (eR r hr).bijective, hA, hD', Matrix.transpose_submatrix,
      Matrix.submatrix_map]
    rfl
  set Zm : Matrix (Fin (r - 1)) (Fin 1) ℂ := fun i _ => A (Sum.inr i) (Sum.inl 0) with hZm
  set Nm : Matrix (Fin (r - 1)) (Fin k) ℂ := fun i j => A (Sum.inr i) (Sum.inr j) with hNm
  have hAb : A = Matrix.fromBlocks 1 0 Zm Nm := by
    ext (i | i) (j | j)
    · have h : eR r hr (Sum.inl i) = f (Sum.inl j) := Fin.ext (by simp [hf, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j])
      simp only [Matrix.fromBlocks_apply₁₁, hA, Matrix.submatrix_apply]
      rw [h, hL, lowMat_diag, Subsingleton.elim i j, Matrix.one_apply_eq]
    · have h : eR r hr (Sum.inl i) < f (Sum.inr j) := Fin.lt_def.2 (by simp [hf, Fin.fin_one_eq_zero i])
      simp only [Matrix.fromBlocks_apply₁₂, hA, Matrix.submatrix_apply, Matrix.zero_apply]
      rw [hL, lowMat_upper w h]
    · rw [Fin.fin_one_eq_zero j]; rfl
    · rfl
  have hDb : D' = Matrix.fromBlocks 1 0 0 (-1) := by
    ext (i | i) (j | j) <;>
      simp [hD', hD, Matrix.diagonal_apply, sgn, hp, Matrix.one_apply, (eR r hr).injective.eq_iff] <;>
      split_ifs <;> simp
  have hT : Aᵀ * D' * A.map (starRingEnd ℂ) = (Aᴴ * D' * A)ᵀ := by
    have h1 : D'ᵀ = D' := by rw [hDb, Matrix.fromBlocks_transpose]; simp
    have h2 : (Aᴴ)ᵀ = A.map (starRingEnd ℂ) := by ext i j; simp
    rw [Matrix.transpose_mul, Matrix.transpose_mul, h1, h2, Matrix.mul_assoc]
  have hzD : zDet X z τ = (1 - Zmᴴ * Zm).det.re := by
    unfold zDet
    haveI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by show 0 < X.p0; omega⟩
        uniq := fun b => Subtype.ext (Fin.ext (by
          have h1 : ((b : Fin r) : ℕ) < X.p0 := b.2
          show ((b : Fin r) : ℕ) = 0
          omega)) }
    rw [Matrix.det_unique, Matrix.det_fin_one]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hmem : ∀ i : Fin (r - 1), X.p0 ≤ (i : ℕ) + 1 := fun i => by omega
    let eqv : Fin (r - 1) ≃ {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { toFun := fun i => ⟨⟨(i : ℕ) + 1, by omega⟩, hmem i⟩
        invFun := fun a => ⟨(a.1 : ℕ) - 1, by have := a.1.2; omega⟩
        left_inv := fun i => Fin.ext (by simp)
        right_inv := fun a => Subtype.ext (Fin.ext (by
          have h1 : X.p0 ≤ ((a : Fin r) : ℕ) := a.2
          show ((a : Fin r) : ℕ) - 1 + 1 = (a : Fin r)
          omega)) }
    have key : ∀ i : Fin (r - 1), Zm i 0 = zBlock X z τ ⟨⟨(i : ℕ) + 1, by omega⟩, hmem i⟩ default := by
      intro i
      simp only [hZm, hA, Matrix.submatrix_apply, hL, zBlock, Matrix.of_apply]
      rw [← congrFun (congrFun (nmat_eq_lowMat X z τ) _) _, Matrix.of_apply]
      congr 1
      · exact Fin.ext (by simp; omega)
      · have h1 : (((default : {b : Fin r // (b : ℕ) < X.p0}) : Fin r) : ℕ) < X.p0 :=
          (default : {b : Fin r // (b : ℕ) < X.p0}).2
        exact Fin.ext (by simp [hf]; omega)
    congr 2
    exact (Fintype.sum_equiv eqv _ _ fun i => by rw [key i]; rfl).symm
  have hcG : colGram (blkW X.p0 (zOf X z τ)) k.castSucc = ‖(Nmᴴ * Nm).det‖ := by
    unfold colGram lminor
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.conjTranspose_submatrix]
    have hN : (blkW X.p0 (zOf X z τ)).submatrix id (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc k).isLt)) = Nm := by
      ext i j
      simp only [Matrix.submatrix_apply, blkW, hp, if_true, hNm, hA, hL, id]
      congr 1
      · exact Fin.ext (by simp; omega)
      · exact Fin.ext (by simp [hf]; omega)
    rw [hN]
  rw [hdmin, hT, Matrix.det_transpose, hzD, hcG, hAb, hDb]
  apply schur_bound
  rw [← hzD]
  exact zDet_pos X hz τ
end GlobalTheory.IntBallMinorOne
