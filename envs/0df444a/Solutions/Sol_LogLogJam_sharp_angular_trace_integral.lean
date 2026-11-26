-- Prove2me | solution 1 for LogLogJam.sharp_angular_trace_integral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:52:23.637631+00:00
-- url     : https://prove2.me/submissions/72d9f8f3-501e-445b-acd5-07a07ef892da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LogLogJam_sharp_angular_curvature_integral
open MeasureTheory Matrix LogLogJam Filter
open scoped ENNReal Kronecker ComplexOrder MatrixOrder Topology
set_option maxHeartbeats 950000
open MeasureTheory Matrix

open scoped Matrix.Norms.Operator in
private theorem curveInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ℝ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (θ : ℝ)
    (hu : IsUnit (D θ)) (hd : ∀ i j, HasDerivAt (fun t => D t i j) (H i j) θ) :
    ∀ i j, HasDerivAt (fun t => (D t)⁻¹ i j) ((-(D θ)⁻¹ * H * (D θ)⁻¹) i j) θ := by
  have h : HasDerivAt D H θ := hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hd i))
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [hu.unit_spec] at hi
  have hi' := hi.comp_hasDerivAt θ h
  intro i j
  have hv := hasDerivAt_pi.mp (hasDerivAt_pi.mp hi' i) j
  simpa only [Function.comp_def, _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    coe_units_inv, hu.unit_spec, nonsing_inv_eq_ringInverse, neg_mul] using hv

open scoped Matrix.Norms.Operator in
private theorem periodic_trace_energy {n : Type} [Fintype n] [DecidableEq n]
    (D H A : ℝ → Matrix n n ℝ)
    (hd : ∀ t i j, HasDerivAt (fun s => D s i j) (H t i j) t)
    (hh : ∀ t i j, HasDerivAt (fun s => H s i j) (A t i j) t)
    (hu : ∀ t, IsUnit (D t)) (hc : Continuous A)
    (hD : D Real.pi = D 0) (hH : H Real.pi = H 0) :
    (∫ t in Set.Ico 0 Real.pi, (((D t)⁻¹ * H t) * ((D t)⁻¹ * H t)).trace / 2) =
      ∫ t in Set.Ico 0 Real.pi, ((D t)⁻¹ * A t).trace / 2 := by
  let I := fun t => (D t)⁻¹
  have di (t : ℝ) : HasDerivAt I (-I t * H t * I t) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr (curveInverse D (H t) t (hu t) (hd t) i)
  have dh (t : ℝ) : HasDerivAt H (A t) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr (hh t i)
  let L := fun t => ((I t * H t) * (I t * H t)).trace / 2
  let R := fun t => (I t * A t).trace / 2
  have ci : Continuous I := continuous_iff_continuousAt.mpr fun t => (di t).continuousAt
  have ch : Continuous H := continuous_iff_continuousAt.mpr fun t => (dh t).continuousAt
  have cl : Continuous L := ((ci.mul ch).mul (ci.mul ch)).matrix_trace.div_const 2
  have cr : Continuous R := (ci.mul hc).matrix_trace.div_const 2
  have derivTrace (t : ℝ) : HasDerivAt (fun s => (I s * H s).trace / 2) (R t - L t) t := by
    have dp := (di t).mul (dh t)
    have dtr : HasDerivAt (fun s => (I s * H s).trace)
        (((-I t * H t * I t) * H t + I t * A t).trace) t := by
      apply HasDerivAt.fun_sum
      intro i _
      exact hasDerivAt_pi.mp (hasDerivAt_pi.mp dp i) i
    have e : R t - L t = (((-I t * H t * I t) * H t + I t * A t).trace / 2) := by
      simp only [R, L, Matrix.trace_add, neg_mul, Matrix.trace_neg, mul_assoc]
      ring
    rw [e]
    exact dtr.div_const 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := Real.pi)
    (fun t _ => derivTrace t) ((cr.sub cl).intervalIntegrable _ _)
  change (∫ t in (0 : ℝ)..Real.pi, R t - L t) =
    (((D Real.pi)⁻¹ * H Real.pi).trace / 2) - (((D 0)⁻¹ * H 0).trace / 2) at h
  rw [intervalIntegral.integral_sub (cr.intervalIntegrable _ _) (cl.intervalIntegrable _ _),
    hD, hH, sub_self, sub_eq_zero] at h
  change (∫ t in Set.Ico 0 Real.pi, L t) = ∫ t in Set.Ico 0 Real.pi, R t
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ico_eq_integral_Ioc] using h.symm

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

private noncomputable def accel (l θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2*(l-l⁻¹)) • (rot θ * !![-1,0;0,1] * (rot θ)ᵀ)
private theorem acc_deriv (l θ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => velocity l t i j) (accel l θ i j) θ := by
  fin_cases i <;> fin_cases j
  all_goals
    simp [velocity,accel,rot,vecMul,dotProduct,Fin.sum_univ_two]
    apply HasDerivAt.congr_deriv (f := _) (f' := deriv _ θ)
    · apply DifferentiableAt.hasDerivAt; fun_prop
    · simp (disch := fun_prop) [deriv_fun_mul, deriv_fun_add]; ring

theorem solution (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (hk : 1 ≤ k)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    let D := fun θ => VsqK lam θ k + Matrix.of W
    let H := fun θ : ℝ => ((lam-lam⁻¹) • (rot θ * !![0,1;1,0] * (rot θ)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let I := ∫ θ in Set.Ico 0 Real.pi, (((D θ)⁻¹ * H θ) * ((D θ)⁻¹ * H θ)).trace / 2
    I ≤ k * Real.pi * (4 * energy lam - 2) ∧
      (I = k * Real.pi * (4 * energy lam - 2) ↔ (Matrix.of W).det = 1) := by
  let D := fun θ => VsqK lam θ k + Matrix.of W
  let H := fun θ => velocity lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  let A := fun θ => accel lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  have hd (t) (i j : Q k) : HasDerivAt (fun s => D s i j) (H t i j) t :=
    ((velocity_deriv lam t i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)).add_const _
  have hh (t) (i j : Q k) : HasDerivAt (fun s => H s i j) (A t i j) t :=
    (acc_deriv lam t i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)
  have hc : Continuous A := by
    apply continuous_pi; rintro ⟨i,a⟩; apply continuous_pi; rintro ⟨j,b⟩
    fin_cases i <;> fin_cases j <;> simp [A,accel,rot,Matrix.kroneckerMap_apply] <;> fun_prop
  have hD : D Real.pi = D 0 := by
    ext ⟨i,a⟩ ⟨j,b⟩; fin_cases i <;> fin_cases j <;> simp [D,VsqK,Vsq,rot,Matrix.kroneckerMap_apply,vecMul,dotProduct,Fin.sum_univ_two]
  have hH : H Real.pi = H 0 := by
    ext ⟨i,a⟩ ⟨j,b⟩; fin_cases i <;> fin_cases j <;> simp [H,velocity,rot,Matrix.kroneckerMap_apply,vecMul,dotProduct,Fin.sum_univ_two]
  have h := periodic_trace_energy D H A hd hh (fun t => (outcome_posDef lam t hlam k W hW).isUnit) hc hD hH
  change (∫ t in Set.Ico 0 Real.pi, (((D t)⁻¹ * H t) * ((D t)⁻¹ * H t)).trace / 2) ≤ _ ∧ ((∫ t in Set.Ico 0 Real.pi, (((D t)⁻¹ * H t) * ((D t)⁻¹ * H t)).trace / 2) = _ ↔ _)
  rw [h]; exact sharp_angular_curvature_integral lam hlam k hk W hW
