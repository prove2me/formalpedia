-- Prove2me | solution 1 for LogLogJam.physical_history_likelihood
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:52.42449+00:00
-- url     : https://prove2.me/submissions/4a4c5912-a221-4ff0-b133-75ca7ec9bbaf

import Definitions.Def_LogLogJam_GaussProtocol

open Matrix LogLogJam
open scoped ComplexOrder

private theorem outcome_posDef (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    (VsqK lam θ k + Matrix.of W).PosDef := by
  have hrot : (rot θ).det = 1 := by
    simp [rot, det_fin_two, ← sq, Real.cos_sq_add_sin_sq]
  have hU : IsUnit (rot θ) := (isUnit_iff_isUnit_det _).mpr (by simp [hrot])
  have hdiag : (diagonal ![lam, lam⁻¹]).PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i <;> simp <;> positivity
  have hV : (Vsq lam θ).PosDef := by
    have h := hdiag.mul_mul_conjTranspose_same (B := rot θ)
      (vecMul_injective_of_isUnit hU)
    have heq : diagonal ![lam, lam⁻¹] = !![lam,0;0,lam⁻¹] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    simpa [Vsq, heq, conjTranspose_eq_transpose_of_trivial] using h
  apply PosDef.add_posSemidef (hV.kronecker (PosDef.one : (1 : Matrix (Fin k) (Fin k) ℝ).PosDef))
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hW.1
  · intro v
    have h := (Complex.nonneg_iff.mp (hW.2.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im, Complex.re_sum] using h

set_option maxHeartbeats 700000

private theorem rot_period (s : ℝ) : rot (s+Real.pi) = - rot s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot]

private theorem vsq_period (lam s : ℝ) : Vsq lam (s+Real.pi) = Vsq lam s := by
  simp [Vsq,rot_period]

private theorem rot_diff (i j : Fin 2) : ContDiff ℝ 1 (fun s => rot s i j) := by
  fin_cases i <;> fin_cases j <;> simp [rot] <;> fun_prop

private theorem entries_det_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} (h : ∀ i j, ContDiff ℝ 1 (fun s => A s i j)) :
    ContDiff ℝ 1 (fun s => (A s).det) := by
  simp only [Matrix.det_apply']
  fun_prop (disch := assumption)

private theorem round_diff (lam : ℝ) (hlam : 1 < lam) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) (y : Q k → ℝ) :
    ContDiff ℝ 1 (fun s => outDens k (VsqK lam s k + Matrix.of W) y) := by
  let D (s : ℝ) := VsqK lam s k + Matrix.of W
  have hD (i j : Q k) : ContDiff ℝ 1 (fun s => D s i j) := by
    simp only [D, VsqK, Vsq, Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply]
    apply ContDiff.add _ contDiff_const
    apply ContDiff.mul _ contDiff_const
    apply ContDiff.sum
    intro b _
    apply ContDiff.mul _ (rot_diff j.1 b)
    apply ContDiff.sum
    exact fun a _ => (rot_diff i.1 a).mul contDiff_const
  have hdet := entries_det_diff hD
  have hpos (s : ℝ) : 0 < (D s).det := (outcome_posDef lam s hlam k W hW).det_pos
  have hadj (i j : Q k) : ContDiff ℝ 1 (fun s => (D s).adjugate i j) := by
    simp only [Matrix.adjugate_apply]
    apply entries_det_diff
    intro a b
    by_cases h : a = j
    · simp [Matrix.updateRow_apply,h]; exact contDiff_const
    · simpa [Matrix.updateRow_apply,h] using hD a b
  have hi (i j : Q k) : ContDiff ℝ 1 (fun s => (D s)⁻¹ i j) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact (hdet.inv (fun s => (hpos s).ne')).mul (hadj i j)
  change ContDiff ℝ 1 (fun s => Real.exp (-(y ⬝ᵥ ((D s)⁻¹ *ᵥ y))) /
      (Real.pi ^ k * Real.sqrt (D s).det))
  apply ContDiff.div
  · simp only [dotProduct, Matrix.mulVec]
    apply ContDiff.exp
    apply ContDiff.neg
    apply ContDiff.sum
    intro i _
    apply contDiff_const.mul
    exact ContDiff.sum (fun j _ => (hi i j).mul contDiff_const)
  · exact contDiff_const.mul (hdet.sqrt (fun s => (hpos s).ne'))
  · intro s
    exact mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (Real.sqrt_pos.mpr (hpos s)).ne'

theorem solution {t : ℕ} (lam : ℝ) (hlam : 1 < lam) (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) :
    (∀ s, 0 < histDens lam s H) ∧
    (∀ s, histDens lam (s+Real.pi) H = histDens lam s H) ∧
    ContDiff ℝ 1 (fun s => histDens lam s H) := by
  refine ⟨fun s => Finset.prod_pos (fun i _ => ?_), fun s => ?_, ?_⟩
  · have hp := (outcome_posDef lam s hlam (H i).1 (H i).2.1 (hH i)).det_pos
    unfold obsDens outDens
    positivity
  · simp only [histDens,obsDens,VsqK,vsq_period]
  · unfold histDens
    exact contDiff_prod (fun i _ => round_diff lam hlam (H i).1 (H i).2.1 (hH i) (H i).2.2)
