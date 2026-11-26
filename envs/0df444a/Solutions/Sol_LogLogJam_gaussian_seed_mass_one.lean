-- Prove2me | solution 1 for LogLogJam.gaussian_seed_mass_one
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:24:50.921801+00:00
-- url     : https://prove2.me/submissions/d4378e08-f85d-4e1e-a6a0-eb24aa01838c

import Theorems.Thm_DeepLearningTheory_gaussian_integral_normalization
import Definitions.Def_LogLogJam_IsCov

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

open MeasureTheory DeepLearningTheory
open scoped ENNReal

private theorem fin_gaussian_mass (n : ℕ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef) :
    ∫ z : Fin n → ℝ, Real.exp (-(z ⬝ᵥ (D⁻¹ *ᵥ z))) = Real.sqrt (Real.pi ^ n * D.det) := by
  have hhalf : (((1/2 : ℝ) • D)⁻¹) = (2 : ℝ) • D⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hD.isUnit)]
    norm_num
  have hform (z : Fin n → ℝ) : gaussQuadForm ((1/2 : ℝ) • D) z = 2 * (z ⬝ᵥ (D⁻¹ *ᵥ z)) := by
    simp only [gaussQuadForm, hhalf, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h := gaussian_integral_normalization ((1/2 : ℝ) • D) (hD.smul (by norm_num))
  simp_rw [hform] at h
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with z
    congr 1; ring
  · congr 1
    rw [Matrix.det_smul, Fintype.card_fin, ← mul_assoc, ← mul_pow]
    congr 2
    ring

theorem solution (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    ∫⁻ y, ENNReal.ofReal (outDens k (VsqK lam θ k + Matrix.of W) y) = 1 := by
  let D := VsqK lam θ k + Matrix.of W
  have hD : D.PosDef := outcome_posDef lam θ hlam k W hW
  have hdet : 0 < D.det := hD.det_pos
  let e : Fin (2*k) ≃ Q k := finProdFinEquiv.symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : Q k => ℝ) e
  have hg (z : Fin (2*k) → ℝ) : g z ∘ e = z := by
    funext j; exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Q k => ℝ) e z j
  have hq (z : Fin (2*k) → ℝ) : g z ⬝ᵥ (D⁻¹ *ᵥ g z) = z ⬝ᵥ ((D.submatrix e e)⁻¹ *ᵥ z) := by
    have hv : z ∘ e.symm = g z := by
      funext j
      obtain ⟨i,rfl⟩ := e.surjective j
      simpa [Function.comp_def] using (congrFun (hg z) i).symm
    rw [← comp_equiv_dotProduct_comp_equiv (g z) (D⁻¹ *ᵥ g z) e, hg,
      inv_submatrix_equiv, submatrix_mulVec_equiv, hv]
  have hnorm : ∫ y : Q k → ℝ, Real.exp (-(y ⬝ᵥ (D⁻¹ *ᵥ y))) =
      Real.pi ^ k * Real.sqrt D.det := by
    rw [← (volume_measurePreserving_piCongrLeft (fun _ : Q k => ℝ) e).integral_comp'
      (fun y => Real.exp (-(y ⬝ᵥ (D⁻¹ *ᵥ y))))]
    change (∫ z, Real.exp (-(g z ⬝ᵥ (D⁻¹ *ᵥ g z)))) = _
    simp_rw [hq]
    rw [fin_gaussian_mass _ _ (hD.submatrix e.injective), det_submatrix_equiv_self,
      Real.sqrt_mul (by positivity), mul_comm 2 k, pow_mul, Real.sqrt_sq (by positivity)]
  have hnormpos : 0 < Real.pi ^ k * Real.sqrt D.det := by positivity
  have hI : ∫ y, outDens k D y = 1 := by
    simp only [outDens, integral_div, hnorm, div_self hnormpos.ne']
  have hi : Integrable (outDens k D) := by
    by_contra hn
    rw [integral_undef hn] at hI
    norm_num at hI
  change (∫⁻ y, ENNReal.ofReal (outDens k D y)) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · simp [hI]
  · filter_upwards with y
    unfold outDens; positivity
