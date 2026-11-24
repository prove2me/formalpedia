-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_fifth_euler_gaussian_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:26:55.568232+00:00
-- url     : https://prove2.me/submissions/9005796a-c52a-4233-a10d-df8c46bc0520

import Theorems.Thm_GrothendieckLB_Supplement_cq_fifth_price_integral_expansion
import Theorems.Thm_GrothendieckLB_Supplement_cq_price_partial_gaussian_bound
import Definitions.Def_GrothendieckLB_Supplement_cqPriceMajorant
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels


open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice
open scoped ComplexConjugate
namespace CQPriceSymmetry
private def parity (p : RationalPoly) (n : ℕ) := p.terms.all (fun t => decide (t.1%2=n%2))=true
private instance (p : RationalPoly) (n : ℕ) : Decidable (parity p n) := inferInstanceAs (Decidable (_ = _))
theorem tableParity : parity rho 1 ∧ terms.all (fun t => decide (parity t.polynomial (t.parameterOrder+t.spatialOrder)))=true :=
  by decide +kernel

private theorem sign_eq {i j : ℕ} (h : i%2=j%2) : (-1:ℂ)^i=(-1:ℂ)^j := by
  have red (k : ℕ) : (-1:ℂ)^k=(-1:ℂ)^(k%2) := by
    conv_lhs => rw [← Nat.mod_add_div k 2,pow_add,pow_mul]; norm_num
  rw [red i,red j,h]

private theorem negList (ts : List (ℕ×ℤ)) (z : ℂ) (n : ℕ) (hp : ∀ t∈ts,t.1%2=n%2) :
    (ts.map (fun t => (t.2:ℂ)*(-z)^t.1)).sum =
    (-1:ℂ)^n*(ts.map (fun t => (t.2:ℂ)*z^t.1)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons,List.sum_cons,mul_add]
    rw [ih (fun u hu => hp u (by simp [hu])),show -z=(-1:ℂ)*z by ring,mul_pow, sign_eq (hp t (by simp))]
    ring

theorem negEval (p : RationalPoly) (z : ℂ) (n : ℕ) (h : parity p n) :
    eval p (-z)=(-1:ℂ)^n*eval p z := by
  simp only [eval, negList _ _ n (fun t ht => of_decide_eq_true (List.all_eq_true.mp h t ht)),
    mul_div_assoc]
theorem conjEval (p : RationalPoly) (z : ℂ) : eval p (conj z)=conj (eval p z) := by
  simp [eval,map_list_sum,List.map_map,Function.comp_def]

private theorem sigma_neg (z : ℂ) : sigma (-z)=sigma z := by
  simp [sigma,negEval rho z 1 tableParity.1]
private theorem sigma_conj (z : ℂ) : sigma (conj z)=sigma z := by simp [sigma,conjEval]

theorem majorant_neg (z : ℂ) : majorant (-z)=majorant z := by
  unfold majorant
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have h := of_decide_eq_true (List.all_eq_true.mp tableParity.2 t ht)
  rw [negEval _ _ _ h,sigma_neg,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]

theorem majorant_conj (z : ℂ) : majorant (conj z)=majorant z := by
  simp [majorant,conjEval,sigma_conj]

private theorem point_eq (r s : ℝ) : circleMap 0 r (2*Real.arctan (s^2))=point r s := by
  have h : 0<1+s^4 := by positivity
  have hs := (Real.sqrt_pos.mpr h).ne'
  apply Complex.ext
  · rw [circleMap_zero_re,Real.cos_two_mul,Real.cos_arctan,show (s^2)^2=s^4 by ring]
    change r*(2*(1/Real.sqrt (1+s^4))^2-1)=r*((1-s^4)/(1+s^4))
    rw [div_pow,Real.sq_sqrt h.le]
    field_simp [h.ne'];ring
  · rw [circleMap_zero_im,Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan,show (s^2)^2=s^4 by ring]
    change r*(2*(s^2/Real.sqrt (1+s^4))*(1/Real.sqrt (1+s^4)))=r*(2*s^2/(1+s^4))
    field_simp [hs,h.ne']
    rw [Real.sq_sqrt h.le]

theorem reflected (r s θ : ℝ) (hθ : let a:=2*Real.arctan (s^2)
    θ=a ∨ θ=Real.pi-a ∨ θ=Real.pi+a ∨ θ=2*Real.pi-a) :
    majorant (circleMap 0 r θ)=majorant (point r s) := by
  rw [← point_eq]
  let a := 2*Real.arctan (s^2)
  change θ=a ∨ θ=Real.pi-a ∨ θ=Real.pi+a ∨ θ=2*Real.pi-a at hθ
  rcases hθ with h|h|h|h
  · rw [h]
  · have eq : circleMap 0 r (Real.pi-a) = -(conj (circleMap 0 r a)) := by
      apply Complex.ext <;> simp [circleMap_zero_re,circleMap_zero_im,Real.cos_sub,Real.sin_sub]
    rw [h,eq,majorant_neg,majorant_conj]
  · have eq : circleMap 0 r (Real.pi+a) = -(circleMap 0 r a) := by
      apply Complex.ext <;> simp [circleMap_zero_re,circleMap_zero_im,Real.cos_add,Real.sin_add]
    rw [h,eq,majorant_neg]
  · have eq : circleMap 0 r (2*Real.pi-a) = conj (circleMap 0 r a) := by
      apply Complex.ext <;> simp [circleMap_zero_re,circleMap_zero_im,Real.cos_sub,Real.sin_sub]
    rw [h,eq,majorant_conj]
end CQPriceSymmetry


open GrothendieckLB.Supplement.CQPrice
namespace CQPriceSymmetry
theorem sum_bound (z : ℂ) (ts : List Term) (C : ℝ)
    (h : ∀ t∈ts, ‖partialTerm z t.parameterOrder t.spatialOrder‖ ≤ C*momentBound t (sigma z)) :
    ‖(ts.map (fun t => eval t.polynomial z * partialTerm z t.parameterOrder t.spatialOrder)).sum‖ ≤
      C*(ts.map (fun t => ‖eval t.polynomial z‖*momentBound t (sigma z))).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons,List.sum_cons,mul_add]
    apply (norm_add_le _ _).trans
    apply add_le_add _ (ih fun u hu => h u (by simp [hu]))
    rw [norm_mul,mul_left_comm]
    exact mul_le_mul_of_nonneg_left (h t (by simp)) (norm_nonneg _)
end CQPriceSymmetry

open GrothendieckLB.Supplement

theorem solution (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t| < 1 → F (t : ℂ) = (cqCorr 0.136419125 0.34101124 0.05276111 t : ℂ))
    (r s θ : ℝ) (hr : (99999 : ℝ) / 100000 ≤ r) (hr₁ : r < 1) (hs : s ∈ Set.Icc 0 1)
    (hθ : let a := 2 * Real.arctan (s^2)
          θ = a ∨ θ = Real.pi-a ∨ θ = Real.pi+a ∨ θ = 2*Real.pi-a) :
    ‖(((fun g : ℂ → ℂ => fun w : ℂ => w * deriv g w)^[5]) F) (circleMap 0 r θ)‖ ≤
      (2/Real.sqrt ‖1-(circleMap 0 r θ)^2‖) * CQPrice.majorant (CQPrice.point r s) := by
  have hr0 : 0 ≤ r := by linarith
  have hz : ‖circleMap 0 r θ‖ < 1 := by rwa [norm_circleMap_zero,abs_of_nonneg hr0]
  rw [cq_fifth_price_integral_expansion F hF hreal _ hz,← CQPriceSymmetry.reflected r s θ hθ]
  exact CQPriceSymmetry.sum_bound _ CQPrice.terms _ (cq_price_partial_gaussian_bound _ hz)
