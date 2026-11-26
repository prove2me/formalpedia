-- Prove2me | solution 1 for MasulloRH.height_two_curvature_tail_rows
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:30:39.159789+00:00
-- url     : https://prove2.me/submissions/2ee35582-a03e-497b-b617-0257288630ec

import Theorems.Thm_MasulloRH_height_two_surrogate_truncation_bound
import Theorems.Thm_MasulloRH_height_two_theta_six_tail_derivative_bounds
import Theorems.Thm_MasulloRH_second_deriv_finite_translated_sum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH MasulloRH.HeightTwoCurvature MasulloRH.GaussianApproximation Set

private noncomputable def pulseR (x : ℝ) := 3/Real.sqrt Real.pi * Real.exp (-9*x^2)

private theorem pulse_bounds (x : ℝ) (hx : x ∈ Icc (-4:ℝ) 4)
    (hs : x ≤ -23/8 ∨ 7/2 ≤ x) :
    |pulseR x| ≤ 1/10000000 ∧ |deriv (deriv pulseR) x| ≤ 1/10 := by
  have hsq : 64 ≤ 9*x^2 := by
    rcases hs with h|h
    · nlinarith [sq_nonneg (x+23/8)]
    · nlinarith [sq_nonneg (x-7/2)]
  have hlow : 1 ≤ Real.sqrt Real.pi :=
    (by norm_num : (1:ℝ) ≤ Real.sqrt 1).trans (Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three]))
  have hf : 3/Real.sqrt Real.pi ≤ 3 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hd : Real.exp (-9*x^2) ≤ 1/(2:ℝ)^64 := by
    apply (Real.exp_le_exp.mpr (show -9*x^2 ≤ -64 by linarith)).trans
    rw [Real.exp_neg, ←one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    simpa using (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 64).trans_eq (Real.exp_nat_mul 1 64).symm
  have hp : |pulseR x| ≤ 3/(2:ℝ)^64 := by
    rw [abs_of_nonneg (show 0 ≤ pulseR x by unfold pulseR; positivity)]
    exact (mul_le_mul hf hd (Real.exp_pos _).le (by norm_num)).trans_eq (by ring)
  have dp (u : ℝ) : HasDerivAt pulseR ((-18*u)*pulseR u) u := by
    have d : HasDerivAt (fun y : ℝ => -9*y^2) (-18*u) u := by
      apply (((hasDerivAt_id u).pow 2).const_mul (-9)).congr_deriv
      simp; ring
    have h := d.exp.const_mul (3/Real.sqrt Real.pi)
    apply h.congr_deriv
    unfold pulseR
    ring
  have d2 : deriv (deriv pulseR) x = (324*x^2-18)*pulseR x := by
    rw [show deriv pulseR = fun y => (-18*y)*pulseR y from funext fun u => (dp u).deriv]
    have h := ((hasDerivAt_id x).const_mul (-18)).mul (dp x)
    calc
      _ = (-18*1)*pulseR x + (-18*x)*((-18*x)*pulseR x) := h.deriv
      _ = _ := by ring
  refine ⟨hp.trans (by norm_num),?_⟩
  rw [d2,abs_mul]
  have hquad : |324*x^2-18| ≤ 5202 := by
    obtain ⟨hl,hr⟩ := hx
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg x],by nlinarith [mul_nonneg (show 0 ≤ x+4 by linarith) (show 0 ≤ 4-x by linarith)]⟩
  exact (mul_le_mul hquad hp (abs_nonneg _) (by norm_num)).trans (by norm_num)

private theorem positive_cap : ∀ j : Fin 1024, 1 ≤ cap j.val := by
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 4000000 in
  decide +kernel

theorem solution (j : ℕ) (hj : j < 1024) (hs : j < 144 ∨ 960 ≤ j) :
    (∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000) ∧
      ∀ x ∈ Icc (edge j) (edge (j+1)), Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
        ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2 ≤ 1/100000000 := by
  have hshift (i : Fin 11) : -(3:ℝ)/8 ≤ HeightTwoWitness.shifts i ∧
      HeightTwoWitness.shifts i ≤ 19/8 := by
    fin_cases i <;> norm_num [HeightTwoWitness.shifts,HeightTwoWitness.shiftsQ,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
  let c (i : Fin 11) := (HeightTwoWitness.coeffsQ i : ℝ)
  have hc (i : Fin 11) : |c i| ≤ 15 := by
    fin_cases i <;> norm_num [c,HeightTwoWitness.coeffsQ,Matrix.cons_val_zero,Matrix.cons_val_succ]
  have he : edge j ≤ edge (j+1) := by simp [edge]; linarith
  have hd : (edgeQ j:ℝ) = edge j := by simp [edgeQ,edge]
  have hg (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) :
      x ∈ Icc (-4:ℝ) 4 ∧ (x ≤ -23/8 ∨ 7/2 ≤ x) := by
    obtain ⟨hl,hr⟩ := hx
    simp only [edge,Nat.cast_add,Nat.cast_one] at hl hr
    have hj' : (j:ℝ)+1 ≤ 1024 := by exact_mod_cast hj
    refine ⟨⟨by linarith [Nat.cast_nonneg (α:=ℝ) j],by linarith⟩,?_⟩
    rcases hs with h|h
    · have h' : (j:ℝ)+1 ≤ 144 := by exact_mod_cast h
      left; linarith
    · have h' : (960:ℝ) ≤ j := by exact_mod_cast h
      right; linarith
  let f (i : Fin 11) := thetaSix (reflected j i)
  have hf (i : Fin 11) : ContDiff ℝ 2 (f i) := by
    dsimp only [f]
    cases reflected j i <;> unfold thetaSix factor arg <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
  let T := fun u => ∑ i, c i*f i (u-HeightTwoWitness.shifts i)
  have hsf : ContDiff ℝ 2 T := by
    dsimp only [T]
    fun_prop (disch := aesop)
  have hpf : ContDiff ℝ 2 pulseR := by unfold pulseR; fun_prop
  have hTheta (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) (i : Fin 11) :
      |f i (x-HeightTwoWitness.shifts i)| ≤ 1/200000000 ∧
      |deriv (deriv (f i)) (x-HeightTwoWitness.shifts i)| ≤ 1/200 ∧
      thetaTail (reflected j i) (x-HeightTwoWitness.shifts i) ≤ 1/1000000000 := by
    apply MasulloRH.height_two_theta_six_tail_derivative_bounds
    rcases hs with h|h
    · have h' : (j:ℝ)+1 ≤ 144 := by exact_mod_cast h
      have heR : edge (j+1) ≤ -23/8 := by simp [edge]; linarith
      have hz : x-HeightTwoWitness.shifts i ≤ -5/2 := by linarith [hx.2,(hshift i).1]
      have hfl : edgeQ j-HeightTwoWitness.shiftsQ i < -1 := by
        have hh : (edgeQ j:ℝ) - (HeightTwoWitness.shiftsQ i:ℝ) < -1 := by
          rw [hd]; change edge j-HeightTwoWitness.shifts i < -1; linarith [hx.1]
        exact_mod_cast hh
      exact Or.inl ⟨by simp [reflected,hfl],hz⟩
    · have h' : (960:ℝ) ≤ j := by exact_mod_cast h
      have heL : 7/2 ≤ edge j := by unfold edge; linarith
      have hz : 9/8 ≤ edge j-HeightTwoWitness.shifts i := by linarith [(hshift i).2]
      have hfl : ¬ edgeQ j-HeightTwoWitness.shiftsQ i < -1 := by
        have hh : (-1:ℝ) ≤ (edgeQ j:ℝ) - (HeightTwoWitness.shiftsQ i:ℝ) := by
          rw [hd]; change -1 ≤ edge j-HeightTwoWitness.shifts i; linarith
        exact not_lt.mpr (by exact_mod_cast hh)
      exact Or.inr ⟨by simp [reflected,hfl],by linarith [hx.1]⟩
  have agg (g : Fin 11 → ℝ) (B : ℝ) (hg' : ∀ i, |g i| ≤ B) : |∑ i, c i*g i| ≤ 165*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin 11, 15*B := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul (hc i) (hg' i) (abs_nonneg _) (by norm_num)
      _ = _ := by simp; ring
  have hsval (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) : |surrogate j x| ≤ 1/1000000 := by
    obtain ⟨hdx,hsx⟩ := hg x hx
    have hp := (pulse_bounds x hdx hsx).1
    have ht := agg _ _ (fun i => (hTheta x hx i).1)
    change |pulseR x-T x| ≤ _
    apply (abs_sub _ _).trans
    change |pulseR x| + |∑ i, c i*f i (x-HeightTwoWitness.shifts i)| ≤ _
    linarith
  have htail (x : ℝ) (hx : x ∈ Icc (edge j) (edge (j+1))) : tail j x ≤ 165/1000000000 := by
    unfold tail
    calc
      _ ≤ ∑ _i : Fin 11, 15*(1/1000000000:ℝ) := Finset.sum_le_sum fun i _ =>
        (mul_le_mul_of_nonneg_left (hTheta x hx i).2.2 (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hc i) (by norm_num))
      _ = _ := by norm_num
  have weightBound (x : ℝ) (hx : x ∈ Icc (-4:ℝ) 4) :
      Real.exp (3/2*x+11/24*|x|) ≤ (3:ℝ)^8 := by
    have ha := abs_le.mpr hx
    apply (Real.exp_le_exp.mpr (show 3/2*x+11/24*|x| ≤ 8 by linarith [hx.2])).trans
    simpa using (Real.exp_nat_mul 1 8).trans_le (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 8)
  refine ⟨?_,?_⟩
  · refine ⟨1/1000000,1,1/1000000,by norm_num,hsval _ (left_mem_Icc.mpr he),hsval _ (right_mem_Icc.mpr he),?_,?_⟩
    · intro x hx
      obtain ⟨hdx,hsx⟩ := hg x hx
      have hp := (pulse_bounds x hdx hsx).2
      have ht := agg _ _ (fun i => (hTheta x hx i).2.1)
      have hdiff : deriv (surrogate j) = fun y => deriv pulseR y-deriv T y := by
        funext y
        exact deriv_fun_sub (hpf.differentiable (by decide) y) (hsf.differentiable (by decide) y)
      constructor
      · rw [hdiff,deriv_fun_sub (hpf.differentiable_deriv_two x) (hsf.differentiable_deriv_two x)]
        apply (abs_sub _ _).trans
        have hT : deriv (deriv T) x = _ :=
          MasulloRH.second_deriv_finite_translated_sum f c HeightTwoWitness.shifts hf x
        rw [hT]
        linarith
      · exact (htail x hx).trans (by norm_num)
    · obtain ⟨hw,_⟩ := hg _ (right_mem_Icc.mpr he)
      have hw8 := weightBound _ hw
      have hcap : (1:ℝ) ≤ cap j := by exact_mod_cast positive_cap ⟨j,hj⟩
      apply (mul_le_mul_of_nonneg_right hw8 (sq_nonneg _)).trans
      linarith
  · intro x hx
    let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x
    have hdiff : ‖R - (surrogate j x : ℂ)‖ ≤ 165/1000000000 :=
      (MasulloRH.height_two_surrogate_truncation_bound j x).trans (htail x hx)
    have hnorm : ‖R‖ ≤ 1/1000000 + 165/1000000000 := by
      have tri := norm_add_le (R-(surrogate j x:ℂ)) (surrogate j x:ℂ)
      rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs] at tri
      linarith [hsval x hx]
    change Real.exp _ * ‖R‖^2 ≤ _
    have hw : Real.exp (2*(3/4)*x+2*(11/48)*|x|) ≤ (3:ℝ)^8 := by
      convert weightBound x (hg x hx).1 using 2; ring
    exact (mul_le_mul hw (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (sq_nonneg _) (by norm_num)).trans (by norm_num)
