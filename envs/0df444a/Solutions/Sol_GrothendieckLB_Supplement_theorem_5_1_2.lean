-- Prove2me | solution 2 for GrothendieckLB.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:36:42.682122+00:00
-- url     : https://prove2.me/submissions/be3ceb53-bbd0-4eb5-b718-3fd076ba57a9

import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_hermite_expansion
import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib
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
    (∑ p ∈ box m, |(q η u v p).coeff m|) ≤ (Real.pi/2)*4^m := by
  have hn : ((m+1:ℕ):ℝ) ≤ 2^m := by exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=m))
  calc _ ≤ ∑ _p ∈ box m, (Real.pi/2) := Finset.sum_le_sum (fun p _ => q_bound η u v p m)
       _ = (((m+1:ℕ):ℝ)*((m+1:ℕ):ℝ))*(Real.pi/2) := by simp [box,Finset.card_product,nsmul_eq_mul]
       _ ≤ (2^m*2^m)*(Real.pi/2) := by gcongr
       _ = _ := by rw [←mul_pow]; norm_num; ring

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

private theorem coefficient_hasSum (η u v t : ℝ) (ht : |t| < 1/4) :
    HasSum (fun m => coef η u v m*t^m) (cqCorr η u v t) := by
  let F (z : ℕ × (ℕ × ℕ)) := (q η u v z.2).coeff z.1*t^z.1
  have hz (m : ℕ) (p : ℕ × ℕ) (hp : p ∉ box m) : F (m,p)=0 := by simp [F,q_zero η u v p (outside hp)]
  have hb (m : ℕ) : (∑' p : ℕ × ℕ, |F (m,p)|) ≤ Real.pi/2*(4*|t|)^m := by
    rw [tsum_eq_sum (s:=box m) (fun p hp => by simp [hz m p hp])]
    simp only [F,abs_mul,abs_pow,← Finset.sum_mul,mul_pow]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (row_bound η u v m) (by positivity)
  have habs : Summable (fun z => |F z|) := by
    apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    refine ⟨fun m => summable_of_ne_finset_zero (s:=box m) (fun p hp => by simp [hz m p hp]),?_⟩
    exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => abs_nonneg _)) hb
      ((summable_geometric_of_lt_one (show 0 ≤ 4*|t| by positivity) (by linarith only [ht] : 4*|t|<1)).mul_left (Real.pi/2))
  have hs : Summable F := habs.of_norm
  have hrow (m : ℕ) : HasSum (fun p => F (m,p)) (coef η u v m*t^m) := by
    simpa only [F,coef,Finset.sum_mul] using hasSum_sum_of_ne_finset_zero (hz m)
  have hcol := (hs.prod_symm.hasSum).prod_fiberwise (fun p => eval_row η u v t p)
  have hspec := (cq_gaussian_hermite_expansion η u v).1 t (by linarith only [ht])
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
    have hn : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1/4 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
    filter_upwards [hn] with t ht
    simpa only [c,H,coeff_ofScalars,zero_add,smul_eq_mul,mul_comm] using coefficient_hasSum η u v t ht
  have hc := hseries.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hseries
  have h := congrArg (fun P : FormalMultilinearSeries ℝ ℝ ℝ => P.coeff m) hc
  simpa only [coeff_ofScalars,taylorCoeff,c,H] using h

private theorem coef_formula (η u v : ℝ) (m : ℕ) :
    coef η u v m = Real.pi/2 * ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
      (-1:ℝ)^b*(cqA η u v a b)^2*((cqRhoPoly u v)^a).coeff (m-b) := by
  rw [coef,box,Finset.sum_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  calc _ = ∑ b ∈ Finset.range (m+1-a), (q η u v (a,b)).coeff m := by
           symm
           apply Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _))
           intro b hb hn
           apply q_zero
           simp only [Finset.mem_range] at ha hn
           dsimp
           omega
       _ = _ := by
           apply Finset.sum_congr rfl
           intro b hb
           have h := Finset.mem_range.mp hb
           have hab : b ≤ m := by omega
           simp only [q,coeff_C_mul,coeff_mul_X_pow',if_pos hab]
           ring

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

end CubicTaylor

open CubicTaylor in
theorem solution (η s₃ s₅ : ℝ) :
    (∀ t : ℝ, |t| < 1 →
      HasSum (fun p : ℕ × ℕ => Real.pi / 2 * (cqA η s₃ s₅ p.1 p.2) ^ 2 *
          ((cqRhoPoly s₃ s₅).eval t) ^ p.1 * (-t) ^ p.2) (cqCorr η s₃ s₅ t)) ∧
    (∀ m : ℕ, 1 ≤ m → taylorCoeff m (cqCorr η s₃ s₅) =
      Real.pi / 2 * ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1 - a),
        (-1 : ℝ) ^ b * (cqA η s₃ s₅ a b) ^ 2 * ((cqRhoPoly s₃ s₅) ^ a).coeff (m - b)) ∧
    (∀ m : ℕ, 1 ≤ m → Even m → taylorCoeff m (cqCorr η s₃ s₅) = 0) := by
  refine ⟨(cq_gaussian_hermite_expansion η s₃ s₅).1,fun m _ => (coefficient_taylor η s₃ s₅ m).trans (coef_formula η s₃ s₅ m),?_⟩
  obtain ⟨S,hS⟩ := exists_limitingScheme_cqCorr η s₃ s₅
  rw [←hS]
  have ho : (fun t : ℝ => S.corr (-t)) =ᶠ[𝓝 0] (fun t => -S.corr t) :=
    (unit_near (by norm_num : |(0:ℝ)| < 1)).mono fun t ht => normalized_corr_odd S ht
  intro n _ hn
  have h := ho.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg,neg_zero,hn.neg_one_pow,one_smul,iteratedDeriv_fun_neg] at h
  have hz : iteratedDeriv n S.corr 0=0 := by linarith only [h]
  simp [taylorCoeff,hz]
