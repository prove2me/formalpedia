-- Prove2me | solution 1 for MasulloRH.height_two_curvature_row_of_interval_check
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T14:07:09.533032+00:00
-- url     : https://prove2.me/submissions/5ef05153-1862-4522-b0a4-4ff684a7f213

import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Theorems.Thm_MasulloRH_central_theta_interval_sound
import Theorems.Thm_MasulloRH_second_deriv_finite_translated_sum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH MasulloRH.CentralInterval MasulloRH.InteriorEvaluator MasulloRH.HeightTwoCurvature Set
private abbrev ok := MasulloRH.central_interval_arithmetic_sound
private noncomputable def pulseR (x : ℝ) := 3/Real.sqrt Real.pi * Real.exp (-9*x^2)

private theorem pulse_eval {a : Box} {x : ℝ} (hx : Covers a x) :
    Covers (pulseV a) (pulseR x) ∧ Covers (pulseD a) (deriv (deriv pulseR) x) := by
  have hpos := Real.sqrt_pos.mpr Real.pi_pos
  have hl : (1692568750643/1000000000000:ℝ) ≤ 3/Real.sqrt Real.pi := by
    apply (le_div_iff₀ hpos).2
    have h : Real.sqrt Real.pi ≤ 3/(1692568750643/1000000000000:ℝ) :=
      (Real.sqrt_le_left (by norm_num)).2 (Real.pi_lt_d20.le.trans (by norm_num))
    linarith
  have hu : 3/Real.sqrt Real.pi ≤ (1692568750644/1000000000000:ℝ) := by
    apply (div_le_iff₀ hpos).2
    have h : 3/(1692568750644/1000000000000:ℝ) ≤ Real.sqrt Real.pi :=
      Real.le_sqrt_of_sq_le ((by norm_num : (3/(1692568750644/1000000000000:ℝ))^2 ≤ 3.14159265358979323846).trans Real.pi_gt_d20.le)
    linarith
  have hfac : Covers pulseFactor (3/Real.sqrt Real.pi) := by
    dsimp [Covers,pulseFactor]; push_cast; exact ⟨hl,hu⟩
  have hp : Covers (pulseV a) (pulseR x) := by
    simpa [pulseV,pulseR] using ok.mul_ok hfac (ok.exp_ok (ok.mul_ok (ok.point_ok (-9)) (ok.sq_ok hx)))
  have dp (u : ℝ) : HasDerivAt pulseR ((-18*u)*pulseR u) u := by
    have d : HasDerivAt (fun y : ℝ => -9*y^2) (-18*u) u := by
      apply (((hasDerivAt_id u).pow 2).const_mul (-9)).congr_deriv
      simp; ring
    apply (d.exp.const_mul (3/Real.sqrt Real.pi)).congr_deriv
    unfold pulseR; ring
  have d2 : deriv (deriv pulseR) x = (324*x^2-18)*pulseR x := by
    rw [show deriv pulseR = fun y => (-18*y)*pulseR y from funext fun u => (dp u).deriv]
    have h := ((hasDerivAt_id x).const_mul (-18)).mul (dp x)
    calc
      _ = (-18*1)*pulseR x + (-18*x)*((-18*x)*pulseR x) := h.deriv
      _ = _ := by ring
  refine ⟨hp,?_⟩
  rw [d2]
  simpa [pulseD] using ok.mul_ok (ok.sub_ok (ok.mul_ok (ok.point_ok 324) (ok.sq_ok hx)) (ok.point_ok 18)) hp

private theorem theta_eval (j : ℕ) (i : Fin 11) {a : Box} {x : ℝ} (hx : Covers a x) :
    let b := reflected j i
    let z := x-HeightTwoWitness.shifts i
    let d := shifted j i a
    Covers (thetaV d) (thetaSix b z) ∧ Covers (thetaD b d) (deriv (deriv (thetaSix b)) z) ∧
      (0 < tailDen d → thetaTail b z ≤ (tailU d:ℝ)) :=
  MasulloRH.central_theta_interval_sound _ _ _ (ok.sub_ok hx (ok.point_ok _))

private theorem svalue (j : ℕ) {a : Box} {x : ℝ} (hx : Covers a x) :
    Covers (surrogateV j a) (surrogate j x) := by
  apply ok.sub_ok (pulse_eval hx).1
  apply ok.sum_ok
  intro i
  exact ok.mul_ok (ok.point_ok _) (theta_eval j i hx).1

private theorem scurv (j : ℕ) {a : Box} {x : ℝ} (hx : Covers a x) :
    Covers (surrogateD j a) (deriv (deriv (surrogate j)) x) := by
  let c (i : Fin 11) := (HeightTwoWitness.coeffsQ i : ℝ)
  let f (i : Fin 11) := thetaSix (reflected j i)
  let T := fun u => ∑ i, c i*f i (u-HeightTwoWitness.shifts i)
  have hf (i : Fin 11) : ContDiff ℝ 2 (f i) := by
    dsimp only [f]
    cases reflected j i <;> unfold thetaSix factor arg <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
  have hsf : ContDiff ℝ 2 T := by dsimp only [T]; fun_prop (disch := aesop)
  have hpf : ContDiff ℝ 2 pulseR := by unfold pulseR; fun_prop
  have hdiff : deriv (surrogate j) = fun y => deriv pulseR y-deriv T y := by
    funext y
    exact deriv_fun_sub (hpf.differentiable (by decide) y) (hsf.differentiable (by decide) y)
  rw [hdiff,deriv_fun_sub (hpf.differentiable_deriv_two x) (hsf.differentiable_deriv_two x),
    show deriv (deriv T) x = _ from MasulloRH.second_deriv_finite_translated_sum f c HeightTwoWitness.shifts hf x]
  apply ok.sub_ok (pulse_eval hx).2
  apply ok.sum_ok
  intro i
  exact ok.mul_ok (ok.point_ok _) (theta_eval j i hx).2.1

theorem solution (j : ℕ) (h : passes j = true) :
    ∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000 := by
  have hed (k : ℕ) : (edgeQ k:ℝ) = edge k := by simp [edgeQ,edge]
  obtain ⟨hden,hm,hcap⟩ := of_decide_eq_true h
  have leftE (k : ℕ) : Covers (point (edgeQ k)) (edge k) := by rw [←hed]; exact ok.point_ok _
  have hL := (ok.abs_ok (svalue j (leftE j))).2
  have hR := (ok.abs_ok (svalue j (leftE (j+1)))).2
  refine ⟨(endBound j:ℝ),(curvBound j:ℝ),(tailSum j (cell j):ℝ),by exact_mod_cast hm,?_,?_,?_,?_⟩
  · exact hL.trans (Rat.cast_le.mpr (le_max_left ..))
  · exact hR.trans (Rat.cast_le.mpr (le_max_right ..))
  · intro x hx
    have ha : Covers (cell j) x := by simpa [Covers,cell,hed] using hx
    refine ⟨(ok.abs_ok (scurv j ha)).2,?_⟩
    unfold tail tailSum
    push_cast
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ((theta_eval j i ha).2.2 (hden i)) (abs_nonneg _)
  · let w := 3/2*edgeQ (j+1)+11/24*|edgeQ (j+1)|
    have heq : (w:ℝ) = 3/2*edge (j+1)+11/24*|edge (j+1)| := by dsimp [w]; push_cast; rw [hed]
    have hw := (ok.exp_ok (ok.point_ok w)).2
    change Real.exp (w:ℝ) ≤ (weightCap j:ℝ) at hw
    rw [heq] at hw
    apply (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans
    have hwide : (energyCap j:ℝ) ≤ (((cap j:ℚ)/1000000:ℚ):ℝ) := Rat.cast_le.mpr hcap
    unfold energyCap at hwide
    push_cast at hwide
    exact hwide
