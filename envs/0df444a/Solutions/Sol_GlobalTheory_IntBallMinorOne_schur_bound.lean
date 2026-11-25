-- Prove2me | solution 1 for GlobalTheory.IntBallMinorOne.schur_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:40:54.586562+00:00
-- url     : https://prove2.me/submissions/b4fd5d2c-fc53-4d3a-adf1-75a959c823b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
import Theorems.Thm_GlobalTheory_IntBallMinorOne_norm_det_le_add_rankOne

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
open GlobalTheory GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.IntBallMinorOne
theorem _root_.solution {m k : ℕ} (Z : Matrix (Fin m) (Fin 1) ℂ) (N : Matrix (Fin m) (Fin k) ℂ)
    (hd : 0 < (1 - Zᴴ * Z).det.re) :
    (1 - Zᴴ * Z).det.re * ‖(Nᴴ * N).det‖ ≤
      ‖((fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N)ᴴ *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 (-1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N).det‖ := by
  set d : Matrix (Fin 1) (Fin 1) ℂ := 1 - Zᴴ * Z with hdd
  have hprod : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N)ᴴ *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 (-1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N =
      fromBlocks d (-(Zᴴ * N)) (-(Nᴴ * Z)) (-(Nᴴ * N)) := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hdd, sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg]
  have hdet : d.det = d 0 0 := Matrix.det_fin_one d
  have hherm : d.IsHermitian := Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self Z)
  have him : (d 0 0).im = 0 := by
    have := hherm.apply 0 0
    have h2 : (starRingEnd ℂ) (d 0 0) = d 0 0 := this
    exact Complex.conj_eq_iff_im.1 h2
  set δ : ℝ := d.det.re with hδ
  have hreal : d.det = (δ : ℂ) := by
    apply Complex.ext
    · simp [hδ]
    · simp [hdet, him]
  have hne : d.det ≠ 0 := by
    rw [hreal]; exact_mod_cast hd.ne'
  haveI : Invertible d := Matrix.invertibleOfIsUnitDet d (isUnit_iff_ne_zero.2 hne)
  have hinvd : ⅟d = (((δ : ℂ))⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.inv_def, Matrix.adjugate_fin_one, hreal]
    rw [← hdet, hreal]
  rw [hprod, det_fromBlocks₁₁]
  set v : Fin k → ℂ := fun j => (Nᴴ * Z) j 0 with hv
  have hs : ∀ j, (Zᴴ * N) 0 j = star (v j) := by
    intro j
    simp only [hv, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hcr : Nᴴ * Z * (Zᴴ * N) = replicateCol (Fin 1) v * replicateRow (Fin 1) (star v) := by
    ext i j
    rw [Matrix.mul_apply (M := Nᴴ * Z), Fin.sum_univ_one, hs j, Matrix.mul_apply (M := replicateCol (Fin 1) v),
      Fin.sum_univ_one]
    rfl
  have hrk : -(Nᴴ * N) - -(Nᴴ * Z) * ⅟d * -(Zᴴ * N) =
      -((Nᴴ * N) + ((δ⁻¹ : ℝ) : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v))) := by
    rw [hinvd, ← hcr]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    push_cast
    module
  rw [hrk, Matrix.det_neg, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hreal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  gcongr
  exact norm_det_le_add_rankOne _ (Matrix.posSemidef_conjTranspose_mul_self N) v _
    (inv_nonneg.2 hd.le)
end GlobalTheory.IntBallMinorOne
