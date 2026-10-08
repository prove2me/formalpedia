-- Prove2me | solution 1 for Helfgott.rankin_single_finite_prime_product_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:31:33.102011+00:00
-- url     : https://prove2.me/submissions/3a033dd8-f953-4f9e-a6f0-e2921ea7b2f3

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Group

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma natural_power_geometric_series (σ : ℝ) (hσ : 0<σ) (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun k : ℕ => ‖((p^k : ℕ) : ℝ)^(-σ)‖) ∧
      (∑' k : ℕ,((p^k : ℕ) : ℝ)^(-σ))=(1-(p : ℝ)^(-σ))⁻¹ := by
  have hpR : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ)≤p := by positivity
  have he : (fun k : ℕ => ((p^k : ℕ) : ℝ)^(-σ))=(fun k => ((p : ℝ)^(-σ))^k) := by
    funext k
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hp0 k (-σ),mul_comm,Real.rpow_mul_natCast hp0]
  have hr : ‖(p : ℝ)^(-σ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp0 _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  constructor
  · apply (summable_geometric_of_norm_lt_one hr).congr
    intro k
    rw [←congrFun he k,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  · rw [he]
    exact tsum_geometric_of_norm_lt_one hr

theorem prime_supported_dirichlet_series (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
  let g : ℕ→ℝ := fun n => (n : ℝ)^(-σ)
  have hg1 : g 1=1 := by simp [g]
  have hmul : ∀ {m n},Nat.Coprime m n → g (m*n)=g m*g n := by
    intro m n hmn
    dsimp [g]
    rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hg1 hmul (fun {p} hp => (natural_power_geometric_series σ hσ p hp).1) q.primeFactors
  have hfilter : q.primeFactors.filter Nat.Prime=q.primeFactors := by
    exact Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hvalue : (∏ p∈q.primeFactors with Nat.Prime p,∑' k : ℕ,g (p^k))=
      ∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
    rw [hfilter]
    exact Finset.prod_congr rfl (fun p hp => (natural_power_geometric_series σ hσ p (Nat.prime_of_mem_primeFactors hp)).2)
  have hmem (n : ℕ) : n∈Nat.factoredNumbers q.primeFactors ↔
      n≠0 ∧ (∀ p∈n.primeFactors,p∣q) := by
    rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
    constructor
    · rintro ⟨hn0,hsub⟩
      exact ⟨hn0,fun p hp => Nat.dvd_of_mem_primeFactors (hsub hp)⟩
    · rintro ⟨hn0,hall⟩
      exact ⟨hn0,fun p hp => Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,hall p hp,by omega⟩⟩
  have he : (Nat.factoredNumbers q.primeFactors).indicator g=
      (fun n : ℕ => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0) := by
    funext n
    rw [Set.indicator_apply]
    by_cases hn : n∈Nat.factoredNumbers q.primeFactors
    · rw [if_pos hn,if_pos ((hmem n).mp hn)]
    · rw [if_neg hn,if_neg (fun hh => hn ((hmem n).mpr hh))]
  constructor
  · rw [←he]
    exact summable_subtype_iff_indicator.mp h.1.of_norm
  · rw [←he,←_root_.tsum_subtype]
    exact h.2.tsum_eq.trans hvalue

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real Filter
open scoped BigOperators Topology Classical
namespace Helfgott

theorem real_zeta_euler_hasProd (σ : ℝ) (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes => (1-(p : ℝ)^(-σ))⁻¹)
      (∑' n : ℕ,(n : ℝ)^(-σ)) := by
  let g : ℕ → ℝ := fun n => (n : ℝ)^(-σ)
  have hg1 : g 1=1 := by simp [g]
  have hg0 : g 0=0 := by simp [g,Real.zero_rpow (by linarith : -σ ≠ 0)]
  have hmul : ∀ {m n},Nat.Coprime m n → g (m*n)=g m*g n := by
    intro m n _
    dsimp [g]
    rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have hsum : Summable (fun n : ℕ => ‖g n‖) := by
    simpa only [g,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  have h := EulerProduct.eulerProduct_hasProd hg1 hmul hsum hg0
  have he : (fun p : Nat.Primes => ∑' k : ℕ,g (p^k))=
      (fun p : Nat.Primes => (1-(p : ℝ)^(-σ))⁻¹) := by
    funext p
    exact (natural_power_geometric_series σ (by linarith) p p.property).2
  rw [he] at h
  exact h

lemma real_zeta_sum_pos (σ : ℝ) (hσ : 1 < σ) :
    0 < ∑' n : ℕ,(n : ℝ)^(-σ) := by
  have hsum := Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  have h := hsum.sum_le_tsum {1} (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))
  norm_num at h
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Helfgott

theorem rankin_single_euler_factor_upper (x y : ℝ) (hx : 0<x) (hxy : x≤y)
    (hy : y<1) (hysq : y^2≤x) :
    1+x*y/((1+x)*(1-y))≤(1-x^3)/((1-x*y)*(1-x*y^2)) := by
  have hy0 : 0≤y := hx.le.trans hxy
  have hx1 : x<1 := hxy.trans_lt hy
  have hxylt : x*y<x := by simpa only [mul_one] using mul_lt_mul_of_pos_left hy hx
  have hxy1 : x*y<1 := hxylt.trans hx1
  have hy2 : y^2<1 := by nlinarith
  have hxysq1 : x*y^2<1 := (show x*y^2<x by simpa only [mul_one] using mul_lt_mul_of_pos_left hy2 hx).trans hx1
  have hden1 : 0<(1+x)*(1-y) := mul_pos (by linarith) (by linarith)
  have hden2 : 0<(1-x*y)*(1-x*y^2) := mul_pos (by linarith) (by linarith)
  have hfactor : (1+x-y)*(1-x*y)*(1-x*y^2)-(1+x)*(1-y)*(1-x^3)=
      (x-y)*(y^2-x)*(x*y-x-1)*x := by ring
  have hneg : x*y-x-1≤0 := by nlinarith
  have hprod : (x-y)*(y^2-x)*(x*y-x-1)*x≤0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hneg) hx.le
  have he : 1+x*y/((1+x)*(1-y))=(1+x-y)/((1+x)*(1-y)) := by
    field_simp [ne_of_gt (by linarith : (0:ℝ)<1+x),ne_of_gt (by linarith : (0:ℝ)<1-y)] <;> ring
  rw [he]
  apply (div_le_div_iff₀ hden1 hden2).mpr
  nlinarith [hfactor,hprod]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Real
namespace Helfgott

theorem rankin_single_prime_factor_upper (p s : ℝ) (hp : 1<p) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    1+p^(-s-1)/((1+p^(-1:ℝ))*(1-p^(-s)))≤
      (1-p^(-3:ℝ))/((1-p^(-s-1))*(1-p^(-2*s-1))) := by
  have hp0 : 0<p := by linarith
  have hx : 0<p^(-1:ℝ) := Real.rpow_pos_of_pos hp0 _
  have hxy : p^(-1:ℝ)≤p^(-s) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hy : p^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hysq : (p^(-s))^2≤p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have h := rankin_single_euler_factor_upper (p^(-1:ℝ)) (p^(-s)) hx hxy hy hysq
  have he1 : p^(-1:ℝ)*p^(-s)=p^(-s-1) := by
    rw [←Real.rpow_add hp0]
    congr 1
    ring
  have he2 : p^(-1:ℝ)*(p^(-s))^2=p^(-2*s-1) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2,←Real.rpow_add hp0]
    congr 1
    ring
  have he3 : (p^(-1:ℝ))^3=p^(-3:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-1) 3]
    norm_num
  simpa only [he1,he2,he3] using h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Finset Nat Real Filter
open scoped BigOperators Topology Classical
namespace Helfgott

lemma rankin_single_comparison_hasProd (s : ℝ) (hs : 1/2 ≤ s) :
    HasProd (fun p : Nat.Primes => (1-(p : ℝ)^(-3:ℝ))/
      ((1-(p : ℝ)^(-s-1))*(1-(p : ℝ)^(-2*s-1))))
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1))/
        (∑' n : ℕ,(n : ℝ)^(-3:ℝ))) := by
  have h3 := (real_zeta_euler_hasProd 3 (by norm_num)).inv₀ (ne_of_gt (real_zeta_sum_pos 3 (by norm_num)))
  have h1 := real_zeta_euler_hasProd (s+1) (by linarith)
  have h2 := real_zeta_euler_hasProd (2*s+1) (by linarith)
  have h := h3.mul (h1.mul h2)
  have he1 : (fun n : ℕ => (n : ℝ)^(-(s+1)))=(fun n : ℕ => (n : ℝ)^(-s-1)) := by funext n;congr 1;ring
  have he2 : (fun n : ℕ => (n : ℝ)^(-(2*s+1)))=(fun n : ℕ => (n : ℝ)^(-2*s-1)) := by funext n;congr 1;ring
  rw [he1,he2] at h
  have hv : (∑' n : ℕ,(n : ℝ)^(-3:ℝ))⁻¹*((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1))) =
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
    rw [div_eq_mul_inv];ring
  rw [hv] at h
  apply h.congr_fun
  intro p
  have e1 : -(s+1)=-s-1 := by ring
  have e2 : -(2*s+1)=-2*s-1 := by ring
  simp only [inv_inv,e1,e2,div_eq_mul_inv,mul_inv_rev]
  ring

theorem rankin_single_finite_prime_product_upper_complete (P : Finset Nat.Primes) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∏ p∈P,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := by
  let f : Nat.Primes → ℝ := fun p => 1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)))
  let g : Nat.Primes → ℝ := fun p => (1-(p : ℝ)^(-3:ℝ))/((1-(p : ℝ)^(-s-1))*(1-(p : ℝ)^(-2*s-1)))
  have hf1 (p : Nat.Primes) : 1 ≤ f p := by
    have hp : (1:ℝ)<p := by exact_mod_cast p.property.one_lt
    have hp0 : (0:ℝ)<p := by linarith
    have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    dsimp [f]
    have hd : 0<(1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s)) :=
      mul_pos (by linarith [Real.rpow_pos_of_pos hp0 (-1)]) (by linarith)
    exact le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg hp0.le _) hd.le)
  have hfg (p : Nat.Primes) : f p ≤ g p :=
    rankin_single_prime_factor_upper (p : ℝ) s (by exact_mod_cast p.property.one_lt) hs0 hs1
  have hg1 (p : Nat.Primes) : 1 ≤ g p := (hf1 p).trans (hfg p)
  have hP : (∏ p∈P,f p) ≤ ∏ p∈P,g p := Finset.prod_le_prod (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hf1 p)) (fun p _ => hfg p)
  apply hP.trans
  apply ge_of_tendsto (rankin_single_comparison_hasProd s hs0)
  exact Filter.eventually_atTop.mpr ⟨P,fun T hPT => Finset.prod_le_prod_of_subset_of_one_le hPT
    (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hg1 p)) (fun p _ _ => hg1 p)⟩

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (P : Finset Nat.Primes) (s : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) :
    (∏ p∈P,(1+(p : ℝ)^(-s-1)/((1+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-s))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-1))*(∑' n : ℕ,(n : ℝ)^(-2*s-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ)) := Helfgott.rankin_single_finite_prime_product_upper_complete P s hs0 hs1

#print axioms solution
