-- Prove2me | solution 1 for LogLogJam.heterodyne_fisher_exact
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:56:12.556512+00:00
-- url     : https://prove2.me/submissions/c5a4cff8-456c-4919-899d-f3210014b216

import Theorems.Thm_LogLogJam_gaussian_covariance_fisher
open Matrix LogLogJam
open scoped ENNReal Kronecker ComplexOrder MatrixOrder
set_option maxHeartbeats 750000

private theorem outcome_posDef (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ) :
    (VsqK lam θ k + 1).PosDef := by
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
  exact PosSemidef.one

private noncomputable def velocity (lam θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (lam-lam⁻¹) • (rot θ * !![0,1;1,0] * (rot θ)ᵀ)

private theorem velocity_deriv (lam θ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => Vsq lam t i j) (velocity lam θ i j) θ := by
  fin_cases i <;> fin_cases j
  all_goals
    simp [Vsq, velocity, rot, vecMul, dotProduct, Fin.sum_univ_two]
    apply HasDerivAt.congr_deriv (f := _) (f' := deriv _ θ)
    · apply DifferentiableAt.hasDerivAt
      fun_prop
    · simp (disch := fun_prop) [deriv_fun_mul, deriv_fun_add]
      ring

private theorem rotation_orthogonal (t : ℝ) :
    (rot t)ᵀ * rot t = 1 ∧ rot t * (rot t)ᵀ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j
  all_goals simp [rot, Matrix.mul_apply, Fin.sum_univ_two, ← sq,
    Real.cos_sq_add_sin_sq, Real.sin_sq_add_cos_sq] <;> ring

private theorem single_mode (lam t : ℝ) (hlam : 1 < lam) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℝ, (Vsq lam t + 1) * B = velocity lam t ∧
      B * B = (4 * energy lam - 2) • 1 := by
  let R := rot t
  let C (M : Matrix (Fin 2) (Fin 2) ℝ) := R * M * Rᵀ
  obtain ⟨hleft, hright⟩ := rotation_orthogonal t
  change Rᵀ * R = 1 at hleft
  change R * Rᵀ = 1 at hright
  have c_one : C 1 = 1 := by simpa [C] using hright
  have c_mul (A B) : C A * C B = C (A * B) := by
    calc
      _ = R * A * (Rᵀ * R) * B * Rᵀ := by simp only [C, mul_assoc]
      _ = _ := by simp only [hleft, mul_one, C, mul_assoc]
  have c_smul (x : ℝ) (A) : C (x • A) = x • C A := by
    simp only [C, Matrix.mul_smul, Matrix.smul_mul]
  let B : Matrix (Fin 2) (Fin 2) ℝ := !![0,(lam-1)/lam;lam-1,0]
  refine ⟨C B, ?_, ?_⟩
  · have cov : Vsq lam t + 1 = C (!![lam,0;0,lam⁻¹] + 1) := by
      change C _ + 1 = _
      simpa only [C, mul_add, add_mul] using congrArg (C !![lam,0;0,lam⁻¹] + ·) c_one.symm
    rw [cov, c_mul]
    change C _ = (lam-lam⁻¹) • C !![0,1;1,0]
    rw [← c_smul]
    congr 1
    ext i j; fin_cases i <;> fin_cases j
    all_goals simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  · rw [c_mul, ← c_one, ← c_smul]
    congr 1
    ext i j; fin_cases i <;> fin_cases j
    all_goals simp [B, energy, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem solution (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (θ : ℝ) :
    measFisher lam k (fun i j => (1 : Matrix (Q k) (Q k) ℝ) i j) θ =
      ENNReal.ofReal ((k : ℝ) * (4 * energy lam - 2)) := by
  let I := (1 : Matrix (Fin k) (Fin k) ℝ)
  let D := fun t => VsqK lam t k + 1
  let H := velocity lam θ ⊗ₖ I
  have hD (t) : (D t).PosDef := outcome_posDef lam t hlam k
  have hd (i j : Q k) : HasDerivAt (fun t => D t i j) (H i j) θ :=
    ((velocity_deriv lam θ i.1 j.1).mul_const (I i.2 j.2)).add_const _
  change fisherInfo MeasureTheory.volume (fun t y => outDens k (D t) y) θ = _
  rw [gaussian_covariance_fisher k D H θ hD hd]
  obtain ⟨B, hB, hsq⟩ := single_mode lam θ hlam
  have hfac : D θ = (Vsq lam θ + 1) ⊗ₖ I := by
    simp only [D, I, add_kronecker, one_kronecker_one]
    rfl
  have hb : D θ * (B ⊗ₖ I) = H := by
    rw [hfac, ← mul_kronecker_mul, hB]
    simp only [I, H, one_mul]
  have hi : (D θ)⁻¹ * H = B ⊗ₖ I := by
    rw [← hb, nonsing_inv_mul_cancel_left _ _ ((isUnit_iff_isUnit_det _).mp (hD θ).isUnit)]
  rw [hi, ← mul_kronecker_mul, hsq, trace_kronecker]
  simp only [I, one_mul, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  congr 1
  push_cast
  ring
