-- Prove2me | solution 1 for GlobalTheory.IntBall.MinorLast.finiteRing_sq_sub_mul_sq_eq_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:44.833087+00:00
-- url     : https://prove2.me/submissions/94156234-30c8-47e4-b88a-d1ca14bb2f43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundLast
import Theorems.Thm_GlobalTheory_IntBall_MinorLast_det_sub_bound
import Theorems.Thm_GlobalTheory_IntBall_MinorLast_gram_mul
import Theorems.Thm_GlobalTheory_IntBall_MinorLast_entry_tdm
import Theorems.Thm_GlobalTheory_IntBall_MinorLast_n_top
import Theorems.Thm_GlobalTheory_IntBall_MinorLast_n_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.MinorLast
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ}
namespace GlobalTheory.IntBall.MinorLast
theorem _root_.solution (X : Data E (p + 1)) (hp : X.p0 = p) (x0 : Base X) (z : V (nd X)) (τ : X.Ψ)
    (k : Fin p) :
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  set w := zOf X z τ with hw
  let N : Matrix (Fin p) (Fin ((k : ℕ) + 1)) ℂ := fun i a => lowMat w i.castSucc (Fin.castSucc ⟨a, by omega⟩)
  let q : Fin p → ℂ := fun c => lowMat w (Fin.last p) c.castSucc
  have hA : colGram (blkW X.p0 w) k.succ = ‖(Nᴴ * N).det‖ := by
    have hB : blkW X.p0 w = fun (i j : Fin (p + 1 - 1)) => lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩ := by
      funext i j
      unfold blkW
      split_ifs with h
      · have hi : (i : ℕ) = 0 := by omega
        have hj : (j : ℕ) = 0 := by omega
        simp [lowMat, hi, hj, Fin.ext_iff]
      · rfl
    rw [hB]
    rfl
  have hZ : zDet X z τ = 1 - ∑ c, ‖q c‖ ^ 2 := by
    unfold zDet
    rw [Matrix.det_one_sub_mul_comm]
    letI hU : Unique {a : Fin (p + 1) // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨Fin.last p, by simp [hp]⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp; omega)) }
    rw [Matrix.det_unique]
    let e : Fin p ≃ {b : Fin (p + 1) // (b : ℕ) < X.p0} :=
      { toFun := fun c => ⟨c.castSucc, by simp [hp]⟩
        invFun := fun b => ⟨b.1, by have := b.2; omega⟩
        left_inv := fun c => rfl
        right_inv := fun b => rfl }
    have hs : ∑ b : {b : Fin (p + 1) // (b : ℕ) < X.p0},
        zBlock X z τ default b * star (zBlock X z τ default b) = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Fintype.sum_equiv e (fun c => zBlock X z τ default (e c) * star (zBlock X z τ default (e c)))
        _ (fun _ => rfl)]
      push_cast
      refine Finset.sum_congr rfl fun c _ => ?_
      change q c * star (q c) = _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hs]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  have hD : dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩ =
      (Nᴴ * N - Matrix.vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det := by
    have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (point X x0 z) τ) =
        (mat (nFrame X z) τ)ᵀ * Matrix.diagonal (fun a : Fin (p + 1) => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          (mat (nFrame X z) τ).map (starRingEnd ℂ) := by
      rw [show mat (point X x0 z) τ = mat x0.1 τ * mat (nFrame X z) τ from rfl, gram_mul, x0.2 τ]
    unfold dmin lminor
    rw [hg, ← Matrix.det_transpose (Nᴴ * N - _)]
    congr 1
    ext a b
    have hc : ∀ a : Fin ((k : ℕ) + 1), (Fin.castLE (by omega) a : Fin (p + 1)) =
        Fin.castSucc (⟨a, by omega⟩ : Fin p) := fun a => Fin.ext rfl
    rw [Matrix.submatrix_apply, hc, hc, entry_tdm, Fin.sum_univ_castSucc]
    simp only [n_top X hp, n_last X hp, Fin.val_castSucc, Fin.val_last, sgn, hp, Fin.is_lt, if_true,
      lt_irrefl, if_false, Matrix.transpose_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply, N, q, ← hw]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_one, Complex.ofReal_neg,
      mul_one, Complex.star_def]
    rw [sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · ring
  rw [hA, hZ, hD]
  exact det_sub_bound N q
end GlobalTheory.IntBall.MinorLast
