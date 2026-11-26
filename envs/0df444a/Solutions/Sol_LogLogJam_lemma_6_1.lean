-- Prove2me | solution 1 for LogLogJam.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:48:05.882666+00:00
-- url     : https://prove2.me/submissions/97c2b839-94af-4a72-bcc0-ec17484e2d34

import Theorems.Thm_LogLogJam_sharp_angular_trace_integral
import Theorems.Thm_LogLogJam_gaussian_covariance_fisher
open Matrix MeasureTheory LogLogJam
open scoped Kronecker ENNReal ComplexOrder MatrixOrder
set_option maxHeartbeats 650000
private theorem trace_pos_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨C, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hc, star_eq_conjTranspose, trace_mul_cycle']
  simpa only [← mul_assoc] using (hA.mul_mul_conjTranspose_same C).trace_nonneg

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

private theorem cov_cont (l : ℝ) (k : ℕ) : Continuous (fun θ => VsqK l θ k) := by
  apply continuous_pi
  rintro ⟨a,i⟩
  apply continuous_pi
  rintro ⟨b,j⟩
  fin_cases a <;> fin_cases b
  all_goals simp [VsqK, Vsq, rot, Matrix.kroneckerMap_apply]
  all_goals fun_prop

private theorem vacuum (k : ℕ) (W : Q k → Q k → ℝ) (θ : ℝ) : measFisher 1 k W θ = 0 := by
  have hv (u : ℝ) : Vsq 1 u = 1 := by
    ext i j; fin_cases i <;> fin_cases j
    all_goals simp [Vsq,rot,vecMul,dotProduct,Fin.sum_univ_two, ← sq,Real.cos_sq_add_sin_sq,Real.sin_sq_add_cos_sq] <;> ring
  simp [measFisher,VsqK,hv,fisherInfo,deriv_const]

theorem solution (lam : ℝ) (hlam : 1 ≤ lam) (k : ℕ) (hk : 1 ≤ k) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    (∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ ≤
        ENNReal.ofReal (k * Real.pi * (4 * energy lam - 2))) ∧
      (1 < lam → (∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ =
        ENNReal.ofReal (k * Real.pi * (4 * energy lam - 2)) ↔ (Matrix.of W).det = 1)) ∧
      (lam = 1 → ∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ =
        ENNReal.ofReal (k * Real.pi * (4 * energy lam - 2))) := by
  rcases hlam.eq_or_lt with e|hl
  · subst lam
    norm_num [vacuum,energy]
  let D := fun θ => VsqK lam θ k + Matrix.of W
  let H := fun θ => velocity lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  let g := fun θ => (((D θ)⁻¹ * H θ) * ((D θ)⁻¹ * H θ)).trace / 2
  have hd (θ) : (D θ).PosDef := outcome_posDef lam θ hl k W hW
  have heval (θ) : measFisher lam k W θ = ENNReal.ofReal (g θ) := by
    apply gaussian_covariance_fisher k D (H θ) θ hd
    intro i j
    exact ((velocity_deriv lam θ i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)).add_const _
  have hs (θ) : (H θ).IsHermitian := by
    apply IsHermitian.ext
    intro i j
    have hsym : (fun t => D t j i) = fun t => D t i j := funext fun t => by
      simpa [conjTranspose_eq_transpose_of_trivial] using (hd t).isHermitian.apply i j
    have hder (i j : Q k) : HasDerivAt (fun t => D t i j) (H θ i j) θ :=
      ((velocity_deriv lam θ i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)).add_const _
    simpa [conjTranspose_eq_transpose_of_trivial] using (hder j i).unique (hsym ▸ hder i j)
  have hnn (θ) : 0 ≤ g θ := by
    have hbase := (hd θ).inv.posSemidef
    have hprod := hbase.mul_mul_conjTranspose_same (H θ)
    rw [(hs θ).eq] at hprod
    have htr := trace_pos_product hbase hprod
    dsimp [g]; apply div_nonneg _ (by norm_num); simpa [mul_assoc] using htr
  have hD : Continuous D := (cov_cont lam k).add continuous_const
  have hInv : Continuous (fun t => (D t)⁻¹) := continuous_iff_continuousAt.mpr fun t =>
    (continuousAt_matrix_inv (A := D t) (by simpa [Ring.inverse_eq_inv] using (continuousAt_inv₀ (hd t).det_pos.ne'))).comp hD.continuousAt
  have hH : Continuous H := by
    apply continuous_pi; rintro ⟨i,a⟩; apply continuous_pi; rintro ⟨j,b⟩
    fin_cases i <;> fin_cases j <;> simp [H,velocity,rot,Matrix.kroneckerMap_apply] <;> fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  let I := ∫ θ in Set.Ico 0 Real.pi, g θ
  have hI : 0 ≤ I := integral_nonneg hnn
  have hx : (∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ) = ENNReal.ofReal I := by
    simp_rw [heval]; exact (ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self) (ae_of_all _ hnn)).symm
  obtain ⟨hi, he⟩ := sharp_angular_trace_integral lam hl k hk W hW
  change I ≤ _ at hi; change (I = _ ↔ _) at he
  rw [hx]
  refine ⟨ENNReal.ofReal_le_ofReal hi, fun _ => ⟨fun eq => he.mp ?_,fun e => congrArg ENNReal.ofReal (he.mpr e)⟩, fun e => (hl.ne' e).elim⟩
  have h := congrArg ENNReal.toReal eq; simpa [ENNReal.toReal_ofReal hI, ENNReal.toReal_ofReal (hI.trans hi)] using h
