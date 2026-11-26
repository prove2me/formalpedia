-- Prove2me | solution 1 for MasulloRH.central_theta_interval_sound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T14:06:34.840615+00:00
-- url     : https://prove2.me/submissions/9e3eacc1-b904-4fbe-a0b1-c66bd71a86a8

import Definitions.Def_MasulloRH_InteriorEvaluator
import Theorems.Thm_MasulloRH_central_interval_arithmetic_sound
import Theorems.Thm_MasulloRH_second_deriv_finite_translated_sum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH.CentralInterval MasulloRH.InteriorEvaluator MasulloRH.HeightTwoCurvature
private abbrev ok := MasulloRH.central_interval_arithmetic_sound

private def rho (b : Bool) : ℝ := if b then -1 else 0
private def rate (b : Bool) : ℝ := if b then -2 else 2
private noncomputable def mass (b : Bool) (h : ℝ) := (if b then Real.pi/16 else Real.pi)*h^2
private noncomputable def atom (b : Bool) (h z : ℝ) := Real.exp (rho b*z - mass b h*Real.exp (rate b*z))
private def signs (i : Fin 3) : ℝ := ![1,-3,2] i
private def modes (i : Fin 3) : ℝ := ![1,2,4] i
private def coeff (b : Bool) (i : Fin 6 × Fin 3) := (if b then 1 else 2)*signs i.2
private def scaleMode (i : Fin 6 × Fin 3) : ℝ := ((i.1.val:ℝ)+1)*modes i.2

private theorem exponent (b : Bool) (h z : ℝ) :
    mass b h * Real.exp (rate b*z) = Real.pi*(h*Real.exp (arg b z))^2 := by
  cases b
  · simp only [mass,rate,arg,Bool.false_eq_true,↓reduceIte]
    rw [show 2*z = z+z by ring,Real.exp_add]; ring
  · simp only [mass,rate,arg,↓reduceIte]
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<4),
      show (-2:ℝ)*z = -z + -z by ring, Real.exp_add]; ring

private theorem atom_form (b : Bool) (h z : ℝ) :
    atom b h z = (if b then Real.exp (-z) else 1) * Real.exp (-Real.pi*(h*Real.exp (arg b z))^2) := by
  unfold atom
  rw [exponent, sub_eq_add_neg, Real.exp_add, ← neg_mul]
  cases b <;> simp [rho]

private theorem theta_form (b : Bool) (z : ℝ) :
    thetaSix b z = ∑ i : Fin 6 × Fin 3, coeff b i * atom b (scaleMode i) z := by
  unfold thetaSix
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Fin.sum_univ_three]
  simp only [coeff,scaleMode,signs,modes,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,atom_form]
  cases b <;> simp only [factor,Bool.false_eq_true,↓reduceIte]
    <;> ring_nf


private theorem second_atom (C r b z : ℝ) :
    let v := fun x : ℝ => C*Real.exp (b*x)
    let f := fun x : ℝ => Real.exp (r*x-v x)
    deriv (deriv f) z = ((r-b*v z)^2-b^2*v z)*f z := by
  let v (x : ℝ) := C * Real.exp (b*x)
  let f (x : ℝ) := Real.exp (r*x-v x)
  have dv (x : ℝ) : HasDerivAt v (b*v x) x := by
    have h := (((hasDerivAt_id x).const_mul b).exp).const_mul C
    change HasDerivAt (fun y => C*Real.exp (b*y)) (b*v x) x
    simpa only [v, id_eq, mul_one, mul_left_comm, mul_comm, mul_assoc] using h
  have df (x : ℝ) : HasDerivAt f ((r-b*v x)*f x) x := by
    have h := (((hasDerivAt_id x).const_mul r).sub (dv x)).exp
    change HasDerivAt (fun y => Real.exp (r*y-v y)) ((r-b*v x)*f x) x
    simpa only [f, id_eq, Pi.sub_apply, mul_one, mul_comm] using h
  have ddf : deriv (deriv f) z = ((r-b*v z)^2-b^2*v z)*f z := by
    rw [show deriv f = fun x => (r-b*v x)*f x from funext fun x => (df x).deriv]
    have h := (((dv z).const_mul b).const_sub r).mul (df z)
    calc
      _ = -(b*(b*v z))*f z + (r-b*v z)*((r-b*v z)*f z) := h.deriv
      _ = _ := by ring
  exact ddf

private noncomputable def U (b : Bool) (z : ℝ) := (if b then Real.pi/16 else Real.pi)*Real.exp (rate b*z)
private noncomputable def P (b : Bool) (z : ℝ) := if b then Real.exp (-z) else 2
private noncomputable def poly (b : Bool) (v : ℝ) := 4*(v-(if b then 1 else 1/2))^2-(if b then 3 else 1)

private theorem Ueq (b : Bool) (z : ℝ) : U b z = Real.pi*(Real.exp (arg b z))^2 := by
  simpa [mass,U] using exponent b 1 z
private theorem index_eq (i : Index) : (powerIndex i:ℝ) = (scaleMode i)^2 := by
  obtain ⟨k,t⟩ := i
  fin_cases t <;> norm_num [powerIndex,scaleNat,scaleMode,modes,Matrix.cons_val_zero,Matrix.cons_val_succ]
private theorem sign_eq (i : Index) : (signQ i:ℝ) = signs i.2 := by
  obtain ⟨k,t⟩ := i
  fin_cases t <;> norm_num [signQ,signs,Matrix.cons_val_zero,Matrix.cons_val_succ]
private theorem parameter (b : Bool) (i : Index) (z : ℝ) :
    mass b (scaleMode i)*Real.exp (rate b*z) = (powerIndex i:ℝ)*U b z := by
  rw [index_eq]; dsimp [mass,U]; ring
private theorem term_eq (b : Bool) (i : Index) (z : ℝ) :
    coeff b i*atom b (scaleMode i) z =
    (signQ i:ℝ)*(P b z*(Real.exp (-U b z))^(powerIndex i)) := by
  rw [sign_eq, ←Real.exp_nat_mul]
  unfold atom
  rw [parameter, sub_eq_add_neg, Real.exp_add,←mul_neg]
  cases b <;> simp [coeff,P,rho]
  ring
private theorem atom_curvature (b : Bool) (i : Index) (z : ℝ) :
    deriv (deriv (atom b (scaleMode i))) z = poly b ((powerIndex i:ℝ)*U b z)*atom b (scaleMode i) z := by
  have h := second_atom (mass b (scaleMode i)) (rho b) (rate b) z
  change deriv (deriv (atom b (scaleMode i))) z =
    ((rho b-rate b*(mass b (scaleMode i)*Real.exp (rate b*z)))^2 -
      rate b^2*(mass b (scaleMode i)*Real.exp (rate b*z)))*atom b (scaleMode i) z at h
  rw [parameter] at h
  rw [h]
  congr 1
  cases b <;> simp [rho,rate,poly] <;> ring

private theorem param_sound (b : Bool) {a : Box} {z : ℝ} (h : Covers a z) :
    Covers (params b a).u (U b z) ∧ Covers (params b a).q (Real.exp (-U b z)) ∧
      Covers (params b a).pref (P b z) := by
  have piOK : Covers piB Real.pi := by
    constructor
    · exact (by norm_num [piB] : ((piB.1:ℚ):ℝ) ≤ 3.14159265358979323846).trans Real.pi_gt_d20.le
    · exact Real.pi_lt_d20.le.trans (by norm_num [piB])
  have hu : Covers (params b a).u (U b z) := by
    cases b
    · simpa [params,U,rate] using ok.mul_ok piOK (ok.exp_ok (ok.mul_ok (ok.point_ok 2) h))
    · simpa [params,U,rate,div_eq_mul_inv] using
        ok.mul_ok (ok.mul_ok piOK (ok.point_ok (1/16))) (ok.exp_ok (ok.mul_ok (ok.point_ok (-2)) h))
  refine ⟨hu,ok.exp_ok (ok.neg_ok hu),?_⟩
  cases b
  · simpa [params,P] using ok.point_ok 2
  · exact ok.exp_ok (ok.neg_ok h)

private theorem poly_ok (b : Bool) {a : Box} {v : ℝ} (hv : Covers a v) :
    Covers (curvaturePoly b a) (poly b v) := by
  cases b
  · simpa [curvaturePoly,poly] using
      ok.sub_ok (ok.mul_ok (ok.point_ok 4) (ok.sq_ok (ok.sub_ok hv (ok.point_ok (1/2))))) (ok.point_ok 1)
  · simpa [curvaturePoly,poly] using
      ok.sub_ok (ok.mul_ok (ok.point_ok 4) (ok.sq_ok (ok.sub_ok hv (ok.point_ok 1)))) (ok.point_ok 3)

theorem solution (b : Bool) (a : Box) (z : ℝ) (hz : Covers a z) :
    let d := params b a
    Covers (thetaV d) (thetaSix b z) ∧ Covers (thetaD b d) (deriv (deriv (thetaSix b)) z) ∧
      (0 < tailDen d → thetaTail b z ≤ (tailU d:ℝ)) := by
  let d := params b a
  let q := Real.exp (-U b z)
  obtain ⟨hu,hq,hp⟩ := param_sound b hz
  have ht (i : Index) : Covers (term d i) (P b z*q^powerIndex i) :=
    ok.mul_ok hp (ok.pow_ok hq _)
  have hd2 : deriv (deriv (thetaSix b)) z =
      ∑ i : Index, coeff b i*deriv (deriv (atom b (scaleMode i))) z := by
    let F (i : Index) := atom b (scaleMode i)
    have smooth (i : Index) : ContDiff ℝ 2 (F i) := by
      change ContDiff ℝ 2 (fun x => Real.exp (rho b*x - mass b (scaleMode i)*Real.exp (rate b*x)))
      fun_prop
    have heq : thetaSix b = fun x => ∑ i : Index, coeff b i*F i (x-0) := by
      funext x; simpa [F] using theta_form b x
    rw [heq, MasulloRH.second_deriv_finite_translated_sum F _ (fun _ => 0) smooth, sub_zero]
  refine ⟨?_,?_,?_⟩
  · rw [theta_form]
    apply ok.sum_ok
    intro i
    rw [term_eq]
    exact ok.mul_ok (ok.point_ok _) (ht i)
  · rw [hd2]
    apply ok.sum_ok
    intro i
    rw [atom_curvature,show coeff b i*(poly b ((powerIndex i:ℝ)*U b z)*atom b (scaleMode i) z) =
        poly b ((powerIndex i:ℝ)*U b z)*(coeff b i*atom b (scaleMode i) z) by ring,term_eq]
    rw [show poly b ((powerIndex i:ℝ)*U b z)*((signQ i:ℝ)*(P b z*q^(powerIndex i))) =
          (signQ i:ℝ)*(poly b ((powerIndex i:ℝ)*U b z)*(P b z*q^(powerIndex i))) by ring]
    exact ok.mul_ok (ok.point_ok _) (ok.mul_ok
      (poly_ok b (by simpa using ok.mul_ok (ok.point_ok (powerIndex i)) hu)) (ht i))
  · intro hden
    have hQ (n : ℕ) : q^n = Real.exp ((-Real.pi*(Real.exp (arg b z))^2) * (n:ℝ)) := by
      dsimp only [q]; rw [←Real.exp_nat_mul,Ueq]; congr 1; ring
    have he : thetaTail b z = 6*P b z*q^49/(1-q^15) := by
      rw [hQ 49,hQ 15]
      cases b <;> simp [thetaTail,factor,P] <;> ring
    have h49 := (ok.pow_ok hq 49).2
    have h15 := (ok.pow_ok hq 15).2
    have hn : (0:ℝ) ≤ P b z := by
      cases b <;> simp [P]
      positivity
    have hqp : 0 ≤ q := (Real.exp_pos _).le
    have hden' : 0 < 1-((powB d.q 15).2:ℝ) := by exact_mod_cast hden
    have hlow : 1-((powB d.q 15).2:ℝ) ≤ 1-q^15 := by linarith
    have hpos : 0 ≤ 6*P b z*q^49 := by positivity
    have hnum : 6*P b z*q^49 ≤ 6*(d.pref.2:ℝ)*(↑(powB d.q 49).2:ℝ) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp.2 (by norm_num)) h49
        (pow_nonneg hqp _) (mul_nonneg (by norm_num) (hn.trans hp.2))
    rw [he]
    change _ ≤ (tailU d:ℝ)
    unfold tailU tailDen
    push_cast
    exact (div_le_div_of_nonneg_left hpos hden' hlow).trans (div_le_div_of_nonneg_right hnum hden'.le)
