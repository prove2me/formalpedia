-- Prove2me | solution 1 for LogLogJam.seed_fisher_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:52.178508+00:00
-- url     : https://prove2.me/submissions/1588889d-1b74-4547-95a6-63535ff48729

import Theorems.Thm_LogLogJam_gaussian_covariance_fisher

open Matrix LogLogJam
open scoped ComplexOrder MatrixOrder Kronecker

private theorem trace_pos_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hc, star_eq_conjTranspose, trace_mul_cycle']
  simpa only [← mul_assoc] using (hA.mul_mul_conjTranspose_same C).trace_nonneg

private theorem trace_bound_of_order_interval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D H : Matrix ι ι ℝ) (b : ℝ) (hD : D.PosDef) (hp : (b • D + H).PosSemidef)
    (hm : (b • D - H).PosSemidef) :
    ((D⁻¹ * H) * (D⁻¹ * H)).trace ≤ b^2 * Fintype.card ι := by
  have hiD := (isUnit_iff_isUnit_det _).mp hD.isUnit
  have hp' : (D⁻¹ * (b • D + H) * D⁻¹).PosSemidef := by
    simpa only [hD.isHermitian.inv.eq] using hp.mul_mul_conjTranspose_same D⁻¹
  have h := trace_pos_product hp' hm
  have hId : (D⁻¹ * (b • D + H) * D⁻¹) * (b • D - H) =
      b^2 • (1 : Matrix ι ι ℝ) - (D⁻¹ * H) * (D⁻¹ * H) := by
    calc
      _ = (D⁻¹ * (b • D + H)) * (D⁻¹ * (b • D - H)) := by simp [mul_assoc]
      _ = _ := by
        rw [mul_add, mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hiD]
        simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          one_mul, mul_one, sq]
        abel
  rw [hId, trace_sub, trace_smul, trace_one, smul_eq_mul] at h
  linarith

private theorem squeezing_direction (lam θ : ℝ) (hL : 1 < lam) (x : ℝ) (hx : x^2=1) :
    ((lam-lam⁻¹) • Vsq lam θ + (lam-lam⁻¹) •
      (rot θ * !![0,x;x,0] * (rot θ)ᵀ)).PosSemidef := by
  have hl : 0 < lam := by linarith
  have hb : 0 ≤ lam-lam⁻¹ := by
    have h := (inv_le_one₀ hl).2 hL.le
    linarith
  have hb0 : (!![lam,x;x,lam⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    apply posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · apply IsHermitian.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
    · intro v
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      apply (mul_nonneg_iff_of_pos_left hl).mp
      nlinarith [sq_nonneg (lam*v 0+x*v 1), inv_mul_cancel₀ hl.ne',
        show x^2*(v 1)^2=(v 1)^2 by rw [hx,one_mul],
        show lam*(lam⁻¹ * v 1 ^ 2)=v 1 ^2 by field_simp]
  have hp := (hb0.mul_mul_conjTranspose_same (rot θ)).smul hb
  have matEq : (!![lam,0;0,lam⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) + !![0,x;x,0] = !![lam,x;x,lam⁻¹] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [← matEq, mul_add, add_mul, smul_add, conjTranspose_eq_transpose_of_trivial] at hp
  exact hp

private theorem real_seed_psd (k : ℕ) (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) : (Matrix.of W).PosSemidef := by
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hW.1
  · intro v
    have h := (Complex.nonneg_iff.mp (hW.2.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im, Complex.re_sum] using h

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
  exact real_seed_psd k W hW

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

open scoped ENNReal

theorem solution (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    measFisher lam k W θ ≤ ENNReal.ofReal ((4 * energy lam)^2) * (k : ℝ≥0∞) := by
  let b := lam-lam⁻¹
  let H := velocity lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  let D (t : ℝ) := VsqK lam t k + Matrix.of W
  have hL : 0 < lam := by linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith [(inv_le_one₀ hL).2 hlam.le]
  have hD (t) : (D t).PosDef := outcome_posDef lam t hlam k W hW
  have hd (i j : Q k) : HasDerivAt (fun t => D t i j) (H i j) θ :=
    ((velocity_deriv lam θ i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)).add_const _
  have hfi := gaussian_covariance_fisher k D H θ hD hd
  change fisherInfo MeasureTheory.volume (fun t y => outDens k (D t) y) θ ≤ _
  rw [hfi, ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hI := (PosSemidef.one : (1 : Matrix (Fin k) (Fin k) ℝ).PosSemidef)
  have hWb := (real_seed_psd k W hW).smul hb
  have hpbase : (b • Vsq lam θ + velocity lam θ).PosSemidef :=
    squeezing_direction lam θ hlam 1 (by norm_num)
  have hmbase : (b • Vsq lam θ - velocity lam θ).PosSemidef := by
    have h := squeezing_direction lam θ hlam (-1) (by norm_num)
    have hneg : (!![0,-1;-1,0] : Matrix (Fin 2) (Fin 2) ℝ) = - !![0,1;1,0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    simpa only [b, velocity, hneg, mul_neg, neg_mul, smul_neg, sub_eq_add_neg] using h
  have hp : (b • D θ + H).PosSemidef := by
    have heq : b • D θ + H = ((b • Vsq lam θ + velocity lam θ) ⊗ₖ
        (1 : Matrix (Fin k) (Fin k) ℝ)) + b • Matrix.of W := by
      ext i j
      simp [D,H,VsqK, Matrix.kroneckerMap_apply, Matrix.kronecker_apply, smul_eq_mul]
      ring
    rw [heq]
    exact (hpbase.kronecker hI).add hWb
  have hm : (b • D θ - H).PosSemidef := by
    have heq : b • D θ - H = ((b • Vsq lam θ - velocity lam θ) ⊗ₖ
        (1 : Matrix (Fin k) (Fin k) ℝ)) + b • Matrix.of W := by
      ext i j
      simp [D,H,VsqK, Matrix.kroneckerMap_apply, Matrix.kronecker_apply, smul_eq_mul]
      ring
    rw [heq]
    exact (hmbase.kronecker hI).add hWb
  have htrace := trace_bound_of_order_interval (D θ) H b (hD θ) hp hm
  simp only [Q, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at htrace
  have hc : b ≤ 4 * energy lam := by dsimp [b, energy]; linarith [inv_pos.mpr hL]
  have hk : b^2 * (k : ℝ) ≤ (4 * energy lam)^2 * (k : ℝ) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hc 2) (Nat.cast_nonneg k)
  linarith
