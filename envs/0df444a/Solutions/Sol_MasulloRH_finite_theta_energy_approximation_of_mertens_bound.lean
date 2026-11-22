-- Prove2me | solution 1 for MasulloRH.finite_theta_energy_approximation_of_mertens_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:24:53.543458+00:00
-- url     : https://prove2.me/submissions/802b95b6-8b03-4234-a1ce-53388805d216

import Theorems.Thm_MasulloRH_theta_translate_density_of_mertens_bound
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Theorems.Thm_MasulloAudit_window_mellin_evaluation_bounded

set_option autoImplicit false
open Set MeasureTheory Filter Asymptotics
open scoped Topology ENNReal BigOperators
open MasulloRH.GaussianApproximation

/-
The widened-window estimate below is adapted from marozols' ACCEPTED submission
4bdbae60-2c51-4a6c-98af-6e656970db1f for
MasulloRH.theta_translate_density_of_mertens_bound (16054a29-40cd-4795-8087-001dbb739caa),
specifically MasulloCyclic.weighted_energy_le and rational_energy_approx.
This file exposes their pulse/Mertens consequence through proved public statements.
It is not an independent new proof of theta-translate density.
-/

private theorem thetaEnergy_window_gap_bound (c b A B x : ℝ) :
    Real.exp (c*x+b*|x|) ≤
      Real.exp (-min (c-b-A) (B-(c+b))*|x|) *
        max (Real.exp (A*x)) (Real.exp (B*x)) := by
  let k := min (c-b-A) (B-(c+b))
  change _ ≤ Real.exp (-k*|x|)*max (Real.exp (A*x)) (Real.exp (B*x))
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    calc
      _ ≤ Real.exp (-k*x) * Real.exp (B*x) := by
        rw [←Real.exp_add,Real.exp_le_exp]
        have h : k ≤ B-(c+b) := min_le_right _ _
        nlinarith only [mul_le_mul_of_nonneg_right h hx]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right ..) (Real.exp_nonneg _)
  · have hnx := le_of_not_ge hx
    rw [abs_of_nonpos hnx]
    calc
      _ ≤ Real.exp (-k*(-x)) * Real.exp (A*x) := by
        rw [←Real.exp_add,Real.exp_le_exp]
        have h : k ≤ c-b-A := min_le_left _ _
        nlinarith only [mul_le_mul_of_nonpos_right h hnx]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left ..) (Real.exp_nonneg _)

private theorem thetaEnergy_weighted_energy_le_of_integrable
    (f : ℝ → ℂ) (c b A B ε : ℝ)
    (hI : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2))
    (hL : A < c-b) (hR : c+b < B)
    (hbound : ∀ x, max (Real.exp (A*x)) (Real.exp (B*x))*‖f x‖ ≤ ε) :
    energy c b f ≤ ε^2 / min (c-b-A) (B-(c+b)) := by
  let k := min (c-b-A) (B-(c+b))
  have hk : 0 < k := lt_min (sub_pos.mpr hL) (sub_pos.mpr hR)
  obtain ⟨hK,hKI,_,_⟩ := MasulloAudit.window_mellin_evaluation_bounded k hk 0 (by simpa using hk)
  simp only [Complex.zero_re,mul_zero,zero_mul,zero_sub,sub_zero,add_zero] at hK hKI
  let E (x : ℝ) := Real.exp (2*c*x+2*b*|x|)*‖f x‖^2
  let K (x : ℝ) := ε^2*Real.exp (-(2*k*|x|))
  have hK' : Integrable K := hK.const_mul _
  have hE (x : ℝ) : E x ≤ K x := by
    have he : Real.exp (c*x+b*|x|)*‖f x‖ ≤ Real.exp (-k*|x|)*ε := by
      calc
        _ ≤ (Real.exp (-k*|x|)*max (Real.exp (A*x)) (Real.exp (B*x)))*‖f x‖ :=
          mul_le_mul_of_nonneg_right (thetaEnergy_window_gap_bound _ _ _ _ _) (norm_nonneg _)
        _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hbound x) (Real.exp_nonneg _)
    have hp := pow_le_pow_left₀ (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) he 2
    simp only [mul_pow,←Real.exp_nat_mul,Nat.cast_ofNat] at hp
    convert! hp using 1 <;> dsimp [E,K] <;> ring_nf
  refine (integral_mono hI hK' hE).trans_eq ?_
  change (∫ x, ε^2*Real.exp (-(2*k*|x|))) = ε^2/k
  rw [integral_const_mul,hKI]
  field_simp
  ring

/-- A Mertens exponent strictly below a closed window gives rational finite theta
approximations of every Gaussian pulse with arbitrarily small window energy. -/
theorem solution
    (β c b T ε : ℝ) (hβ : 0 ≤ β) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hleft : β < c-b) (hright : c+b < 1)
    (hM : (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℂ)) =O[atTop]
      (fun n : ℕ => (n:ℝ)^β)) (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let r := residual T (fun i => ((a i).1 : ℂ)+((a i).2 : ℂ)*Complex.I)
        (fun i => (y i : ℝ))
      Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖r x‖^2) ∧
        energy c b r < ε := by
  let A : ℝ := (β+(c-b))/2
  let B : ℝ := (1+(c+b))/2
  have hA : A < c-b := by dsimp [A]; linarith
  have hB : c+b < B := by dsimp [B]; linarith
  have hβA : β < A := by dsimp [A]; linarith
  have hAB : A ≤ B := by dsimp [A,B]; linarith
  have hB1 : B < 1 := by dsimp [B]; linarith
  let c' : ℝ := (A+B)/2
  let b' : ℝ := (B-A)/2
  have hb' : 0 ≤ b' := by dsimp [b']; linarith
  have hc'left : c'-b' = A := by dsimp [c',b']; ring
  have hc'right : c'+b' = B := by dsimp [c',b']; ring
  let k : ℝ := min (c-b-A) (B-(c+b))
  have hk : 0 < k := lt_min (sub_pos.mpr hA) (sub_pos.mpr hB)
  let ρ : ℝ := Real.sqrt (ε*k/2)
  have hρ : 0 < ρ := by dsimp [ρ]; exact Real.sqrt_pos.mpr (by positivity)
  have hDensity := MasulloRH.theta_translate_density_of_mertens_bound.1 β c' b' hβ hb'
    (by simpa only [hc'left] using hβA) (by simpa only [hc'right] using hB1) hM
  obtain ⟨m,a,y,happrox⟩ := hDensity.2.1 T hT ρ hρ
  let aC : Fin m → ℂ := fun i => ((a i).1 : ℂ)+((a i).2 : ℂ)*Complex.I
  let yR : Fin m → ℝ := fun i => (y i : ℝ)
  let r : ℝ → ℂ := residual T aC yR
  have hI : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖r x‖^2) :=
    (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1 m T c b 1 aC yR
      hT (by norm_num) (lt_of_le_of_lt hβ hleft) hright).1
  have hbound : ∀ x, max (Real.exp (A*x)) (Real.exp (B*x))*‖r x‖ ≤ ρ := by
    intro x
    simpa only [hc'left,hc'right,r,MasulloRH.GaussianApproximation.residual,aC,yR] using happrox x
  have he := thetaEnergy_weighted_energy_le_of_integrable r c b A B ρ hI hA hB hbound
  refine ⟨m,a,y,hI,he.trans_lt ?_⟩
  change ρ^2/k < ε
  rw [div_lt_iff₀ hk, show ρ^2 = ε*k/2 from Real.sq_sqrt (by positivity)]
  nlinarith [mul_pos hε hk]

