-- Prove2me | solution 1 for GlobalTheory.IntBall.MinorLast.det_sub_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:50:46.532383+00:00
-- url     : https://prove2.me/submissions/f1c53443-f36d-49ed-9778-dd33a83f284d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundLast

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
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.IntBall.MinorLast
theorem _root_.solution {p m : ℕ} (N : Matrix (Fin p) (Fin m) ℂ) (q : Fin p → ℂ) :
    (1 - ∑ c, ‖q c‖ ^ 2) * ‖(Nᴴ * N).det‖ ≤
      ‖(Nᴴ * N - vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det‖ := by
  set A := Nᴴ * N with hAdef
  set u := q ᵥ* N with hu
  by_cases hA : A.det = 0
  · rw [hA]; simp
  have hU : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hsplit : A - vecMulVec (star u) u = A + replicateCol Unit (-star u) * replicateRow Unit u := by
    ext i j
    simp [vecMulVec, replicateCol, replicateRow, Matrix.mul_apply, sub_eq_add_neg]
  have key : (A - vecMulVec (star u) u).det = A.det * (1 - u ⬝ᵥ A⁻¹ *ᵥ star u) := by
    rw [hsplit, Matrix.det_add_mul _ _ hU]
    congr 1
    rw [Matrix.det_unique]
    simp [Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec, sub_eq_add_neg,
      Finset.mul_sum]
    simp only [Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  set P := N * A⁻¹ * Nᴴ with hPdef
  have hs : u ⬝ᵥ A⁻¹ *ᵥ star u = q ⬝ᵥ P *ᵥ star q := by
    rw [hu, Matrix.star_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hAh : Aᴴ = A := by rw [hAdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPh : Pᴴ = P := by
    rw [hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hAh, Matrix.mul_assoc]
  have hPP : P * P = P := by
    have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hU
    calc P * P = N * (A⁻¹ * (Nᴴ * N) * A⁻¹) * Nᴴ := by simp only [hPdef, Matrix.mul_assoc]
      _ = P := by rw [← hAdef, h1, Matrix.one_mul, hPdef, Matrix.mul_assoc]
  have hQ : (1 - P) = (1 - P)ᴴ * (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hPP]
    simp
  have hpsd : (1 - P).PosSemidef := by rw [hQ]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have ht := hpsd.dotProduct_mulVec_nonneg (star q)
  rw [star_star, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at ht
  have hqq : q ⬝ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_sum,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have ha := (Matrix.posSemidef_conjTranspose_mul_self N).det_nonneg
  rw [← hAdef] at ha
  rw [key, hs]
  set a := A.det
  set t := q ⬝ᵥ star q - q ⬝ᵥ P *ᵥ star q with htdef
  have hsq : q ⬝ᵥ P *ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - t := by rw [htdef, hqq]; ring
  rw [hsq]
  obtain ⟨ha1, ha2⟩ := Complex.nonneg_iff.1 ha
  obtain ⟨ht1, ht2⟩ := Complex.nonneg_iff.1 ht
  have hae : a = (a.re : ℂ) := Complex.ext rfl (by simp [← ha2])
  have hte : t = (t.re : ℂ) := Complex.ext rfl (by simp [← ht2])
  rw [hae, hte, Complex.norm_real, Real.norm_of_nonneg ha1]
  rw [show (a.re : ℂ) * (1 - (((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - (t.re : ℂ))) = ((a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real]
  calc (1 - ∑ c, ‖q c‖ ^ 2) * a.re ≤ a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) := by nlinarith
    _ ≤ _ := Real.le_norm_self _
end GlobalTheory.IntBall.MinorLast
