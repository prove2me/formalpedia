-- Prove2me | solution 2 for GrothendieckConstant.grothendieckConst_le_cubic_quintic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:55:17.213018+00:00
-- url     : https://prove2.me/submissions/8fa37895-aec6-43da-bfdd-70658793a3d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_hermite_expansion
import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib
import Theorems.Thm_GrothendieckLB_Supplement_theorem_5_1
import Theorems.Thm_GrothendieckLB_Supplement_grothendieck_bound_of_rounded_correlation
import Theorems.Thm_GrothendieckLB_Supplement_cq_rounded_matrix_objective
import Theorems.Thm_GrothendieckLB_Supplement_cq_coefficient_estimates_at_251
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential
open GrothendieckLB GrothendieckLB.Supplement Polynomial Real Filter FormalMultilinearSeries
open MeasureTheory
open scoped Topology
namespace CubicTaylor
set_option maxHeartbeats 500000

private theorem rho_dvd (u v : ℝ) : X ∣ cqRhoPoly u v := by
  apply X_dvd_iff.mpr
  simp [cqRhoPoly,coeff_mul_X_pow',coeff_X_pow]

private theorem rho_coeff (u v : ℝ) (a j : ℕ) : |((cqRhoPoly u v)^a).coeff j| ≤ 1 := by
  let ρ := cqRhoPoly u v
  let D : ℝ := 1+u^2+v^2
  have hD : 0 < D := by dsimp [D]; positivity
  change |(ρ^a).coeff j| ≤ 1
  induction a generalizing j with
  | zero => simp [Polynomial.coeff_one]; split <;> norm_num
  | succ a ih =>
    let s (k : ℕ) := if k ≤ j then (ρ^a).coeff (j-k) else 0
    have hb (k : ℕ) : |s k| ≤ 1 := by unfold s; split <;> simp_all
    have hs : ρ^(a+1) = C (1/D) * ((ρ^a * X^1) - C (u^2) * (ρ^a * X^3) + C (v^2) * (ρ^a * X^5)) := by
      rw [pow_succ]
      change ρ^a * (C (1/D) * (X-C (u^2)*X^3+C (v^2)*X^5)) = _
      ring
    rw [hs,coeff_C_mul,coeff_add,coeff_sub,coeff_C_mul,coeff_C_mul]
    simp only [coeff_mul_X_pow']
    change |1/D*(s 1-u^2*s 3+v^2*s 5)| ≤ 1
    rw [abs_mul,abs_of_pos (one_div_pos.mpr hD),one_div,mul_comm,←div_eq_mul_inv,div_le_iff₀ hD,one_mul]
    calc _ ≤ |s 1-u^2*s 3|+|v^2*s 5| := abs_add_le _ _
         _ ≤ (|s 1|+|u^2*s 3|)+|v^2*s 5| := add_le_add_left (abs_sub _ _) _
         _ ≤ D := by
           simp only [abs_mul,abs_of_nonneg (sq_nonneg u),abs_of_nonneg (sq_nonneg v)]
           dsimp only [D]
           nlinarith only [hb 1,mul_nonneg (sq_nonneg u) (sub_nonneg.mpr (hb 3)),mul_nonneg (sq_nonneg v) (sub_nonneg.mpr (hb 5))]

private noncomputable def q (η u v : ℝ) (p : ℕ × ℕ) : ℝ[X] :=
  C (Real.pi/2*(-1:ℝ)^p.2*(cqA η u v p.1 p.2)^2) * ((cqRhoPoly u v)^p.1*X^p.2)

private theorem q_zero (η u v : ℝ) (p : ℕ × ℕ) {m : ℕ} (hm : m < p.1+p.2) :
    (q η u v p).coeff m = 0 := by
  apply (X_pow_dvd_iff (n:=p.1+p.2)).mp _ m hm
  obtain ⟨Q,hQ⟩ := rho_dvd u v
  refine ⟨C (Real.pi/2*(-1:ℝ)^p.2*(cqA η u v p.1 p.2)^2)*Q^p.1,?_⟩
  rw [q,hQ,mul_pow,pow_add]
  ring

private theorem q_bound (η u v : ℝ) (p : ℕ × ℕ) (m : ℕ) : |(q η u v p).coeff m| ≤ Real.pi/2 := by
  have hA := (cq_gaussian_hermite_expansion η u v).2 p.1 p.2
  simp only [q,coeff_C_mul,coeff_mul_X_pow',abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)]
  split
  · apply mul_le_of_le_one_right (by positivity) (rho_coeff u v _ _) |>.trans
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg _) hA)
  · simp; positivity

private def box (m : ℕ) := Finset.range (m+1) ×ˢ Finset.range (m+1)

private theorem outside {p : ℕ × ℕ} {m : ℕ} (hp : p ∉ box m) : m < p.1+p.2 := by
  by_contra! h
  exact hp (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩)

private noncomputable def coef (η u v : ℝ) (m : ℕ) : ℝ := ∑ p ∈ box m, (q η u v p).coeff m

private theorem row_bound (η u v : ℝ) (m : ℕ) :
    (∑ p ∈ box m, |(q η u v p).coeff m|) ≤ (Real.pi/2)*(((m:ℝ)+1)^2) := by
  calc _ ≤ ∑ _p ∈ box m, (Real.pi/2) := Finset.sum_le_sum (fun p _ => q_bound η u v p m)
       _ = _ := by simp [box,Finset.card_product,nsmul_eq_mul,pow_two]; ring

private theorem eval_row (η u v t : ℝ) (p : ℕ × ℕ) :
    HasSum (fun m : ℕ => (q η u v p).coeff m*t^m)
      (Real.pi/2*(cqA η u v p.1 p.2)^2*((cqRhoPoly u v).eval t)^p.1*(-t)^p.2) := by
  have z (n : ℕ) (hn : n ∉ (q η u v p).support) : (q η u v p).coeff n*t^n=0 :=
    by rw [Polynomial.notMem_support_iff.mp hn,zero_mul]
  have hs : HasSum (fun n => (q η u v p).coeff n*t^n) (∑ n ∈ (q η u v p).support,(q η u v p).coeff n*t^n) := hasSum_sum_of_ne_finset_zero z
  rw [show (∑ n ∈ (q η u v p).support, (q η u v p).coeff n*t^n) = (q η u v p).eval t from (eval_eq_sum (p:=q η u v p) (x:=t)).symm] at hs
  have he : (q η u v p).eval t = Real.pi/2*(cqA η u v p.1 p.2)^2*((cqRhoPoly u v).eval t)^p.1*(-t)^p.2 := by
    simp only [q,eval_mul,eval_C,eval_pow,eval_X]
    rw [show -t=(-1)*t by ring,mul_pow]
    ring
  exact he ▸ hs

private theorem coefficient_hasSum (η u v t : ℝ) (ht : |t| < 1) :
    HasSum (fun m => coef η u v m*t^m) (cqCorr η u v t) := by
  let F (z : ℕ × (ℕ × ℕ)) := (q η u v z.2).coeff z.1*t^z.1
  have hz (m : ℕ) (p : ℕ × ℕ) (hp : p ∉ box m) : F (m,p)=0 := by simp [F,q_zero η u v p (outside hp)]
  have hb (m : ℕ) : (∑' p : ℕ × ℕ, |F (m,p)|) ≤ (Real.pi/2)*(((m:ℝ)+1)^2)*|t|^m := by
    rw [tsum_eq_sum (s:=box m) (fun p hp => by simp [hz m p hp])]
    simp only [F,abs_mul,abs_pow,← Finset.sum_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (row_bound η u v m) (by positivity)
  have htn : ‖|t|‖ < 1 := by simpa only [Real.norm_eq_abs,abs_abs] using ht
  have geom (k : ℕ) : Summable (fun m : ℕ => (m:ℝ)^k*|t|^m) := summable_pow_mul_geometric_of_norm_lt_one k htn
  have hg : Summable (fun m : ℕ => (Real.pi/2)*(((m:ℝ)+1)^2)*|t|^m) := by
    apply (((geom 2).add ((geom 1).mul_left 2)).add (geom 0) |>.mul_left (Real.pi/2)).congr
    intro m
    change (Real.pi/2)*(((m:ℝ)^2*|t|^m+2*((m:ℝ)^1*|t|^m))+(m:ℝ)^0*|t|^m)=_
    ring
  have habs : Summable (fun z => |F z|) := by
    apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    refine ⟨fun m => summable_of_ne_finset_zero (s:=box m) (fun p hp => by simp [hz m p hp]),?_⟩
    exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) hb hg
  have hs : Summable F := habs.of_norm
  have hrow (m : ℕ) : HasSum (fun p => F (m,p)) (coef η u v m*t^m) := by
    simpa only [F,coef,Finset.sum_mul] using hasSum_sum_of_ne_finset_zero (hz m)
  have hcol := (hs.prod_symm.hasSum).prod_fiberwise (fun p => eval_row η u v t p)
  have hspec := (cq_gaussian_hermite_expansion η u v).1 t ht
  have htgt := hcol.unique hspec
  have htotal : (∑' p, F p)=cqCorr η u v t := by
    calc _ = ∑' p : (ℕ × ℕ) × ℕ, F p.swap := ((Equiv.prodComm (ℕ × ℕ) ℕ).tsum_eq F).symm
         _ = _ := htgt
  exact htotal ▸ hs.hasSum.prod_fiberwise hrow

private theorem coefficient_taylor (η u v : ℝ) (m : ℕ) : taylorCoeff m (cqCorr η u v) = coef η u v m := by
  let c := coef η u v
  let H := cqCorr η u v
  have hseries : HasFPowerSeriesAt H (ofScalars ℝ c) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    have hn : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
    filter_upwards [hn] with t ht
    simpa only [c,H,coeff_ofScalars,zero_add,smul_eq_mul,mul_comm] using coefficient_hasSum η u v t ht
  have hc := hseries.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hseries
  have h := congrArg (fun P : FormalMultilinearSeries ℝ ℝ ℝ => P.coeff m) hc
  simpa only [coeff_ofScalars,taylorCoeff,c,H] using h

private theorem full_taylor (η u v t : ℝ) (ht : |t| < 1) :
    HasSum (fun n => taylorCoeff n (cqCorr η u v)*t^n) (cqCorr η u v t) := by
  simpa only [coefficient_taylor] using coefficient_hasSum η u v t ht

end CubicTaylor

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement

namespace CubeLocalOdd
open Filter MeasureTheory
open scoped Topology
private theorem unit_near {x : ℝ} (hx : |x| < 1) : ∀ᶠ y in 𝓝 x, |y| < 1 :=
  (isOpen_lt continuous_abs continuous_const).mem_nhds hx

private theorem allowable_odd {ρ : ℝ → ℝ} (hρ : IsAllowableCorr ρ)
    {t : ℝ} (ht : |t| < 1) : ρ (-t) = -ρ t := by
  obtain ⟨c, hev, _, _, heq⟩ := hρ
  rw [heq (-t) (by simpa using ht), heq t ht, ← tsum_neg]
  apply tsum_congr
  intro n
  rcases Nat.even_or_odd n with he | ho
  · simp [hev n he]
  · rw [ho.neg_pow, mul_neg]

private theorem normalized_corr_odd {k : ℕ} (S : LimitingScheme k) {t : ℝ} (ht : |t| < 1) :
    S.corr (-t) = -S.corr t := by
  let P (t : ℝ) (x y : Fin k → ℝ) := ∏ i : Fin k,
    GrothendieckConstant.gaussianPairDensity 1 (S.ρ i t) (fun _ => x i) (fun _ => y i)
  have hP (x y : Fin k → ℝ) : P (-t) x (-y) = P t x y := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [allowable_odd (S.ρ_allowable i) ht]
    simp only [GrothendieckConstant.gaussianPairDensity, Fin.prod_univ_one, Pi.neg_apply]
    ring_nf
  have hint (x : Fin k → ℝ) :
      (∫ y, S.f x * S.g y * P (-t) x y) = -(∫ y, S.f x * S.g y * P t x y) := by
    calc
      _ = ∫ y, S.f x * S.g (-y) * P (-t) x (-y) :=
        (integral_neg_eq_self (fun y => S.f x * S.g y * P (-t) x y) volume).symm
      _ = ∫ y, -(S.f x * S.g y * P t x y) := by
        apply integral_congr_ae
        filter_upwards [S.g_odd] with y hy
        rw [hy, hP]
        ring
      _ = _ := integral_neg _
  change Real.pi / 2 * (∫ x, ∫ y, S.f x * S.g y * P (-t) x y) =
    -(Real.pi / 2 * (∫ x, ∫ y, S.f x * S.g y * P t x y))
  simp only [hint, integral_neg, mul_neg]


end CubeLocalOdd

set_option maxHeartbeats 800000 in
private theorem compare_cubic_quintic_constant :
    Real.pi / (2 * 0.881545409) ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  have hsqrt : Real.sqrt 2 ≤ 1.414213563 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hexp : (2.414213563 : ℝ) ≤ Real.exp 0.8813736 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 11, (0.8813736 : ℝ) ^ j / j.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 11
  have hlog : Real.log (1 + Real.sqrt 2) ≤ 0.8813736 := by
    apply (Real.log_le_iff_le_exp (by positivity)).2
    linarith only [hsqrt, hexp]
  have hlog_pos : 0 < Real.log (1 + Real.sqrt 2) := by
    apply Real.log_pos
    have h := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hdiv : Real.pi / (2 * 0.8813736) ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith only [hlog])
  calc
    Real.pi / (2 * 0.881545409) ≤ Real.pi / (2 * 0.8813736) - 3.47 * 10 ^ (-4 : ℤ) := by
      norm_num [div_eq_mul_inv] <;> linarith only [Real.pi_gt_d2]
    _ ≤ _ := sub_le_sub_right hdiv _

theorem solution :
    grothendieckConst ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let a (j : ℕ) := |taylorCoeff (2 * j + 3) H|
  obtain ⟨S, hS⟩ := exists_limitingScheme_cqCorr 0.136419125 0.34101124 0.05276111
  change S.corr = H at hS
  obtain ⟨hlinear, hhead, htail_sum, htail⟩ := cq_coefficient_estimates_at_251
  change 0.881573822049 ≤ taylorCoeff 1 H at hlinear
  change (∑ j ∈ Finset.range 125, a j) ≤ 0.000011328860 at hhead
  have hshift (j : ℕ) : a (j + 125) = |taylorCoeff (2 * j + 253) H| := by
    dsimp only [a]
    rw [show 2 * (j + 125) + 3 = 2 * j + 253 by omega]
  have hsum : Summable a := by
    apply (summable_nat_add_iff (f := a) 125).1
    simpa only [hshift] using htail_sum
  have hsqrt : (14.443 / 0.000004575864 : ℝ) ≤ Real.sqrt (10 * (251 : ℝ) ^ 5) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have htail_num : 14.443 / Real.sqrt (10 * (251 : ℝ) ^ 5) ≤ 0.000004575864 := by
    apply (div_le_iff₀ (by positivity)).2
    simpa only [mul_comm] using
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.000004575864)).mp hsqrt
  have hmass : (∑' j, a j) ≤ 0.000015904724 := by
    rw [← hsum.sum_add_tsum_nat_add 125]
    have htail' : (∑' j : ℕ, a (j + 125)) ≤ 0.000004575864 := by
      simpa only [hshift] using htail.trans htail_num
    linarith only [hhead, htail']
  have hgap : 0.881545409 + (∑' j, a j) < taylorCoeff 1 H := by
    linarith only [hmass, hlinear]
  refine le_trans ?_ compare_cubic_quintic_constant
  let b (n : ℕ) := taylorCoeff n H
  have hinv := CubeLocalOdd.normalized_corr_odd S (t:=0) (by norm_num)
  rw [hS,neg_zero] at hinv
  have h0 : b 0=0 := by
    have h : H 0=0 := by linarith only [hinv]
    simp [b,taylorCoeff,h]
  have heven (j : ℕ) : b (2*j+2)=0 := (theorem_5_1 _ _ _).2.2 _ (by omega) ⟨j+1,by omega⟩
  have he : HasSum (fun j : ℕ => |b (2*j+2)|) 0 := by simp [heven]
  have ho : HasSum (fun j : ℕ => |b ((2*j+1)+2)|) (∑' j, a j) := by
    simpa only [b,a,Nat.add_assoc] using hsum.hasSum
  have hall : HasSum (fun n : ℕ => |b (n+2)|) (∑' j,a j) := by
    simpa only [zero_add] using (HasSum.even_add_odd (f:=fun n => |b (n+2)|) he ho)
  apply grothendieck_bound_of_rounded_correlation H b 0.881545409 (by norm_num)
    (fun t ht => CubicTaylor.full_taylor _ _ _ t ht) h0 hall.summable
  · rw [hall.tsum_eq]
    exact hgap.le
  · exact cq_rounded_matrix_objective _ _ _
