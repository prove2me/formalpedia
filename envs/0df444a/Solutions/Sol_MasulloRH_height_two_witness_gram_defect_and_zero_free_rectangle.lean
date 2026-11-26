-- Prove2me | solution 1 for MasulloRH.height_two_witness_gram_defect_and_zero_free_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T14:32:31.156015+00:00
-- url     : https://prove2.me/submissions/8ba5fb10-51cd-4ba9-b822-be6241d4bc67

import Theorems.Thm_MasulloRH_height_two_energy_bound_from_central_interval
import Theorems.Thm_MasulloRH_scalar_curvature_endpoint_bound
import Theorems.Thm_MasulloRH_height_two_surrogate_truncation_bound
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Theorems.Thm_MasulloRH_height_two_curvature_row_of_interval_check
import Theorems.Thm_MasulloRH_height_two_central_interval_checks
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation MasulloRH.HeightTwoCurvature
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

private theorem smooth_surrogate (j : ℕ) : ContDiff ℝ 2 (surrogate j) := by
  have hs (b : Bool) : ContDiff ℝ 2 (thetaSix b) := by
    cases b <;> unfold thetaSix factor arg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  unfold surrogate
  fun_prop (disch := aesop)

private theorem central_cap_total : (∑ j ∈ Finset.range 816, cap (144+j)) = 1285944 := by
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 4000000 in
  decide +kernel

private theorem tightEnergy :
    Integrable (fun x : ℝ => Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2) ∧
    energy (3/4) (11/48) (residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts) ≤ 200929077/20000000000 := by
  let w (x : ℝ) := Real.exp (2*(3/4)*x + 2*(11/48)*|x|)
  let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts
  let F (x : ℝ) := w x * ‖R x‖^2
  obtain ⟨hint, ht⟩ := MasulloRH.height_two_energy_bound_from_central_interval
  refine ⟨hint, ?_⟩
  change energy (3/4) (11/48) R ≤ (∫ x : ℝ in Icc (-23/8) (7/2), F x) +
    13/800000000 + 1/10000000000 at ht
  have hstep (j : ℕ) : edge (j+1) - edge j = 1/128 := by
    simp [edge]
    ring
  have hw (x y : ℝ) (hxy : x ≤ y) : w x ≤ Real.exp (3/2*y + 11/24*|y|) := by
    apply Real.exp_le_exp.mpr
    have h := abs_add_le (x-y) y
    rw [sub_add_cancel, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    linarith
  have hcell (j : ℕ) (hj : 144 ≤ j) (hjR : j < 960) (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) :
      F x ≤ (cap j : ℝ)/1000000 := by
    have h := List.all_eq_true.mp MasulloRH.height_two_central_interval_checks
      (j-144) (List.mem_range.mpr (by omega))
    have checked : MasulloRH.InteriorEvaluator.passes j = true := by
      simpa only [show 144+(j-144) = j by omega] using h
    obtain ⟨A,M,E,hM,hl,hr,hb,hc⟩ := MasulloRH.height_two_curvature_row_of_interval_check j checked
    have hs := smooth_surrogate j
    have hp := MasulloRH.scalar_curvature_endpoint_bound (surrogate j) (deriv (surrogate j))
      (deriv (deriv (surrogate j))) (edge j) (edge (j+1)) M A hM
      (fun u => (hs.differentiable (by decide) u).hasDerivAt)
      (fun u => (hs.differentiable_deriv_two u).hasDerivAt)
      (fun u hu => (hb u hu).1) hl hr x hx
    rw [hstep] at hp
    have hst := (MasulloRH.height_two_surrogate_truncation_bound j x).trans (hb x hx).2
    have hnorm : ‖R x‖ ≤ A + M/131072 + E := by
      have tri := norm_add_le (R x - (surrogate j x : ℂ)) (surrogate j x : ℂ)
      rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at tri
      change ‖R x - (surrogate j x : ℂ)‖ ≤ E at hst
      linarith
    apply le_trans _ hc
    apply (mul_le_mul_of_nonneg_right (hw x _ hx.2) (sq_nonneg _)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (Real.exp_pos _).le
  let e (j : ℕ) := edge (144+j)
  have h0 : e 0 = -23/8 := by norm_num [e,edge]
  have hJ : e 816 = 7/2 := by norm_num [e,edge]
  have hi : Integrable F := hint
  have hmain : (∫ x : ℝ in Icc (e 0) (e 816), F x) ≤
      ∑ j ∈ Finset.range 816, (1/128:ℝ) * ((cap (144+j) : ℝ)/1000000) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by rw [h0,hJ]; norm_num)]
    rw [← intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hi.intervalIntegrable)]
    apply Finset.sum_le_sum
    intro j hj
    have h : j < 816 := Finset.mem_range.mp hj
    have hs : e (j+1)-e j = 1/128 := by simpa only [e,Nat.add_assoc] using hstep (144+j)
    calc
      (∫ x in e j..e (j+1), F x) ≤ ∫ _ in e j..e (j+1), (cap (144+j):ℝ)/1000000 := by
        apply intervalIntegral.integral_mono_on (by linarith : e j ≤ e (j+1)) hi.intervalIntegrable intervalIntegrable_const
        intro x hx
        apply hcell (144+j) (by omega) (by omega) x
        simpa only [e,Nat.add_assoc] using hx
      _ = _ := by rw [intervalIntegral.integral_const,hs]; simp
  rw [h0,hJ] at hmain
  have hcast : (∑ j ∈ Finset.range 816, (cap (144+j) : ℝ)) = 1285944 := by
    exact_mod_cast central_cap_total
  have hin : (∑ j ∈ Finset.range 816, (1/128 : ℝ) * ((cap (144+j) : ℝ)/1000000)) =
      (1285944:ℝ)/128000000 := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hcast]
    norm_num
  rw [hin] at hmain
  change energy (3/4) (11/48) R ≤ 200929077/20000000000
  linarith

private noncomputable def realQuad {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * v j * A i j

private theorem shiftQuad {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (t : ℝ) (v : Fin (m+1) → ℝ) :
    realQuad (A - Matrix.single 0 0 t) v = realQuad A v - (v 0)^2*t := by
  have hs : realQuad (Matrix.single 0 0 t) v = (v 0)^2*t := by
    have hzero (i : Fin m) : (0 : Fin (m+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp [realQuad,Fin.sum_univ_succ,Matrix.single_apply,pow_two,hzero]
  rw [←hs]
  simp only [realQuad,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem solution :
    let u : Fin 12 → ℝ → ℂ := Fin.cons (pulse 2) (fun i x => theta (x - HeightTwoWitness.shifts i))
    let K : Matrix (Fin 12) (Fin 12) ℝ := fun i j =>
      (∫ x : ℝ, (Real.exp (3/2*x + 11/24*|x|) : ℂ) * conj (u i x) * u j x).re
    let v : Fin 12 → ℝ := Fin.cons 1 (fun i => -(HeightTwoWitness.coeffsQ i : ℝ))
    energy (3/4) (11/48) (residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts)
        ≤ 200929077/20000000000 ∧
      (∑ i, (v i)^2) = 5930379/10000 ∧
      (∑ i, ∑ j, v i * v j * (K - Matrix.single (0 : Fin 12) 0 (1/96 : ℝ) : Matrix (Fin 12) (Fin 12) ℝ) i j) ≤ -(22212769/60000000000) ∧
      ∀ s : ℂ, 43/80 ≤ s.re → s.re ≤ 77/80 → |s.im| ≤ 2 → riemannZeta s ≠ 0 := by
  let u : Fin 12 → ℝ → ℂ := Fin.cons (pulse 2) (fun i x => theta (x - HeightTwoWitness.shifts i))
  let G : Matrix (Fin 12) (Fin 12) ℂ := fun i j =>
    ∫ x : ℝ, (Real.exp (3/2*x+11/24*|x|) : ℂ)*conj (u i x)*u j x
  let K : Matrix (Fin 12) (Fin 12) ℝ := fun i j => (G i j).re
  let v : Fin 12 → ℝ := Fin.cons 1 (fun i => -(HeightTwoWitness.coeffsQ i : ℝ))
  let d : Fin 12 → ℂ := Fin.cons 1 (fun i => -HeightTwoWitness.coeffs i)
  have hd (i : Fin 12) : d i = (v i : ℂ) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [d,v]
    · simp [d,v,HeightTwoWitness.coeffs]
  have hv0 : v 0 = 1 := rfl
  have cert := MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1 11 2
    (3/4) (11/48) (1/60) HeightTwoWitness.coeffs HeightTwoWitness.shifts
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hi := cert.2.2.1
  change energy (3/4) (11/48) _ = (∑ i, ∑ j, conj (d i)*d j*
    ∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(11/48)*|x|) : ℂ)*conj (u i x)*u j x).re at hi
  norm_num only [show (2*(3/4):ℝ) = 3/2 by norm_num,show (2*(11/48):ℝ) = 11/24 by norm_num] at hi
  change energy (3/4) (11/48) _ = (∑ i, ∑ j, conj (d i)*d j*G i j).re at hi
  simp only [hd,Complex.conj_ofReal,←Complex.ofReal_mul,Complex.re_sum,Complex.re_ofReal_mul] at hi
  have hE := tightEnergy.2
  refine ⟨hE,?_,?_,?_⟩
  · have hq : (∑ i : Fin 11, (HeightTwoWitness.coeffsQ i)^2) = (5920379/10000:ℚ) := by decide +kernel
    have hh : (∑ i : Fin 11, (HeightTwoWitness.coeffsQ i:ℝ)^2) = 5920379/10000 := by
      have h := congrArg (fun q : ℚ => (q:ℝ)) hq
      push_cast at h
      exact h
    change (∑ i : Fin (11+1), (v i)^2) = _
    rw [Fin.sum_univ_succ]; simp [v,hh]; norm_num
  · change realQuad (K - Matrix.single 0 0 (1/96)) v ≤ _
    rw [shiftQuad, hv0, one_pow, one_mul]
    change energy (3/4) (11/48) _ = realQuad K v at hi
    rw [←hi]; linarith
  · intro s hl hu him hz
    have hin : |s.re-3/4| ≤ 11/48-1/60 := abs_le.mpr ⟨by linarith,by linarith⟩
    have bad := cert.2.2.2 s hin him hz
    have hq : (29/48 : ℚ) ≤ (MasulloRH.CentralInterval.expPoint (-1/2)).1 := by decide +kernel
    have hx := (MasulloRH.central_interval_arithmetic_sound.exp_ok
      (MasulloRH.central_interval_arithmetic_sound.point_ok (-1/2))).1
    change ((MasulloRH.CentralInterval.expPoint (-1/2)).1:ℝ) ≤ Real.exp ((-1/2:ℚ):ℝ) at hx
    have hlower : ((29/48:ℚ):ℝ) ≤ Real.exp ((-1/2:ℚ):ℝ) := (Rat.cast_le.mpr hq).trans hx
    push_cast at hlower
    linarith
