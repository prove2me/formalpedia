-- Prove2me | solution 1 for GrothendieckLB.Supplement.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:34:14.886142+00:00
-- url     : https://prove2.me/submissions/b27d0233-5506-4b91-bace-a43eccfccab6

import Theorems.Thm_GrothendieckLB_Supplement_cq_mehler_expansion
import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement Filter MeasureTheory Polynomial
open scoped Topology
set_option maxHeartbeats 1000000
namespace CQCoefficient

private noncomputable def factor (u v : ℝ) (z : ℂ) : ℂ :=
  (1 - (u:ℂ)^2*z^2 + (v:ℂ)^2*z^4)/((1+u^2+v^2:ℝ):ℂ)
private noncomputable def realFactor (u v t : ℝ) := (1-u^2*t^2+v^2*t^4)/(1+u^2+v^2)

private lemma factor_real (u v t : ℝ) : factor u v (t : ℂ) = (realFactor u v t : ℂ) := by
  simp [factor,realFactor]
private lemma factor_eval (u v t : ℝ) : (cqRhoPoly u v).eval t = t * realFactor u v t := by
  simp [cqRhoPoly,realFactor]
  ring
private lemma factor_bound (u v : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖factor u v z‖ ≤ 1 := by
  let V := 1+u^2+v^2
  have hv : (0:ℝ)<V := by unfold V; positivity
  have h1 := norm_sub_le (1:ℂ) ((u:ℂ)^2*z^2)
  have h2 := norm_add_le (1-(u:ℂ)^2*z^2) ((v:ℂ)^2*z^4)
  rw [factor,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv,div_le_iff₀ hv,one_mul]
  simp only [norm_one,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs, sq_abs] at h1 h2
  nlinarith only [h1,h2,mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hz (n:=2)) (sq_nonneg u),
    mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hz (n:=4)) (sq_nonneg v)]

private lemma polynomial_jet (P : ℝ[X]) (m : ℕ) :
    iteratedDeriv m (fun t => P.eval t) 0 / (m.factorial : ℝ) = P.coeff m := by
  have hi (k : ℕ) : iteratedDeriv k (fun t => P.eval t) = fun t => (derivative^[k] P).eval t := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
      funext t
      exact Polynomial.deriv _
  rw [hi]
  change (derivative^[m] P).eval 0 / _ = _
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp [Nat.descFactorial_self, Nat.factorial_ne_zero]

private lemma vanish_factor (m : ℕ) {G : ℝ → ℝ} (hg : AnalyticAt ℝ G 0) :
    iteratedDeriv m (fun t => t^(m+1)*G t) 0 = 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hg.contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  have h : i ≠ m+1 := Nat.ne_of_lt (Finset.mem_range.mp hi)
  have hz : iteratedDeriv i (fun t : ℝ => t^(m+1)) 0 = 0 := by
    rw [iteratedDeriv_fun_pow_zero, if_neg h, Nat.cast_zero]
  rw [hz]
  simp

private lemma extract (η u v : ℝ) (m : ℕ) : taylorCoeff m (cqCorr η u v) =
    Real.pi/2 * ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
      (-1:ℝ)^b * (cqA η u v a b)^2 * ((cqRhoPoly u v)^a).coeff (m-b) := by
  classical
  obtain ⟨ha,hs⟩ := cq_mehler_expansion η u v
  let c (p : ℕ×ℕ) := Real.pi/2 * (cqA η u v p.1 p.2)^2 * (-1:ℝ)^p.2
  have hc (p : ℕ×ℕ) : |c p| ≤ Real.pi/2 := by
    have hab := ha p.1 p.2
    simp only [c,abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,
      abs_of_pos (by positivity : (0:ℝ)<Real.pi/2)]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg _) hab)
  let T := ((Finset.range (m+1)) ×ˢ (Finset.range (m+1))).filter (fun p : ℕ×ℕ => p.1+p.2 ≤ m)
  have hnot (p : {q : ℕ×ℕ // q ∉ T}) : m+1 ≤ p.1.1+p.1.2 := by
    by_contra! h
    apply p.2
    simp only [T,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
    omega
  let P : ℝ[X] := ∑ p ∈ T, C (c p) * ((cqRhoPoly u v)^p.1 * X^p.2)
  let tail (p : {q : ℕ×ℕ // q ∉ T}) (z : ℂ) := (c p.1 : ℂ) * factor u v z ^ p.1.1 * z^(p.1.1+p.1.2-(m+1))
  let G (z : ℂ) := ∑' p, tail p z
  let R (t : ℝ) := ∑' p : {q : ℕ×ℕ // q ∉ T}, c p.1 * realFactor u v t ^ p.1.1 * t^(p.1.1+p.1.2-(m+1))
  have hcast (t : ℝ) : G (t : ℂ) = (R t : ℂ) := by
    dsimp only [G,R]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro p
    simp [tail,factor_real]
  let M := Real.pi/2*2^(m+1)
  have hgeo := summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have hprod : Summable (fun p : ℕ×ℕ => (1/2:ℝ)^p.1 * (1/2:ℝ)^p.2) :=
    hgeo.mul_of_nonneg hgeo (fun _ => by positivity) (fun _ => by positivity)
  have hG : DifferentiableOn ℂ G (Metric.ball 0 (1/2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (F := tail) ((hprod.subtype (fun q => q ∉ T)).mul_left M) ?_ Metric.isOpen_ball ?_
    · intro p
      dsimp only [tail,factor]
      fun_prop
    · intro p z hz
      have hz' : ‖z‖ ≤ (1/2:ℝ) := (show ‖z‖ < (1/2:ℝ) by simpa using hz).le
      have hq := factor_bound u v (hz'.trans (by norm_num))
      have he : (1/2:ℝ)^p.1.1 * (1/2:ℝ)^p.1.2 = (1/2:ℝ)^(p.1.1+p.1.2-(m+1)) * (1/2:ℝ)^(m+1) := by
        rw [← pow_add,← pow_add,Nat.sub_add_cancel (hnot p)]
      have hone : (2:ℝ)^(m+1) * (1/2:ℝ)^(m+1) = 1 := by rw [←mul_pow]; norm_num
      simp only [tail,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      calc
        _ ≤ (Real.pi/2 * 1)*(1/2:ℝ)^(p.1.1+p.1.2-(m+1)) := by
          exact mul_le_mul (mul_le_mul (hc _) (pow_le_one₀ (norm_nonneg _) hq)
            (by positivity) (by positivity)) (pow_le_pow_left₀ (norm_nonneg z) hz' _) (by positivity) (by positivity)
        _ = _ := by
          change _ = (Real.pi/2*2^(m+1))*((1/2:ℝ)^p.1.1 * (1/2:ℝ)^p.1.2)
          rw [he]
          linear_combination -(Real.pi/2)*(1/2:ℝ)^(p.1.1+p.1.2-(m+1))*hone
  have hR : AnalyticAt ℝ R 0 := by
    have hg : AnalyticAt ℂ G ((0:ℝ):ℂ) := hG.analyticOnNhd Metric.isOpen_ball _ (by norm_num)
    apply hg.re_ofReal.congr
    exact .of_forall fun t => by simp [hcast]
  have heq : cqCorr η u v =ᶠ[𝓝 0] (fun t => P.eval t + t^(m+1) * R t) := by
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
    filter_upwards [hnear] with t ht
    have hsum : HasSum (fun p : ℕ×ℕ => c p * (cqRhoPoly u v).eval t ^ p.1 * t^p.2) (cqCorr η u v t) := by
      apply (hs t ht).congr_fun
      intro p
      rw [show -t = (-1:ℝ)*t by ring,mul_pow]
      dsimp only [c]
      ring
    rw [←hsum.tsum_eq,← hsum.summable.sum_add_tsum_subtype_compl T]
    congr 1
    · simp [P,eval_finsetSum, mul_assoc]
    · dsimp only [R]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      rw [factor_eval,mul_pow]
      have he : t^p.1.1*t^p.1.2 = t^(m+1) * t^(p.1.1+p.1.2-(m+1)) := by
        rw [← pow_add,← pow_add]; congr 1; have := hnot p; omega
      linear_combination c p.1 * (realFactor u v t)^p.1.1 * he
  have hjet := heq.iteratedDeriv_eq m
  have hpoly : ContDiffAt ℝ m (fun t : ℝ => P.eval t) 0 :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) P 0 (Set.mem_univ 0)).contDiffAt
  have hrem : ContDiffAt ℝ m (fun t : ℝ => t^(m+1)*R t) 0 :=
    ((by fun_prop : AnalyticAt ℝ (fun t : ℝ => t^(m+1)) 0).mul hR).contDiffAt
  rw [iteratedDeriv_fun_add hpoly hrem, vanish_factor m hR, add_zero] at hjet
  rw [taylorCoeff,hjet,polynomial_jet]
  simp only [P,finset_sum_coeff,coeff_C_mul,coeff_mul_X_pow',T,Finset.sum_filter,Finset.sum_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha'
  have ha' := Finset.mem_range.mp ha'
  have hcoeff (s : Prop) [Decidable s] (A : ℝ[X]) :
      (if s then A else 0).coeff m = if s then A.coeff m else 0 := by
    split <;> simp_all
  simp only [hcoeff,coeff_C_mul,coeff_mul_X_pow']
  rw [Finset.mul_sum, ← Finset.sum_filter]
  have hset : (Finset.range (m+1)).filter (fun b => a+b ≤ m) = Finset.range (m+1-a) := by
    ext b; simp; omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := Finset.mem_range.mp hb
  rw [if_pos (show b ≤ m by omega)]
  dsimp only [c]
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


end CQCoefficient
open CQCoefficient

theorem solution (η s₃ s₅ : ℝ) :
    (∀ t : ℝ, |t| < 1 →
      HasSum (fun p : ℕ × ℕ => Real.pi / 2 * (cqA η s₃ s₅ p.1 p.2) ^ 2 *
          ((cqRhoPoly s₃ s₅).eval t) ^ p.1 * (-t) ^ p.2) (cqCorr η s₃ s₅ t)) ∧
    (∀ m : ℕ, 1 ≤ m → taylorCoeff m (cqCorr η s₃ s₅) =
      Real.pi / 2 * ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1 - a),
        (-1 : ℝ) ^ b * (cqA η s₃ s₅ a b) ^ 2 * ((cqRhoPoly s₃ s₅) ^ a).coeff (m - b)) ∧
    (∀ m : ℕ, 1 ≤ m → Even m → taylorCoeff m (cqCorr η s₃ s₅) = 0)  := by
  obtain ⟨S,hS⟩ := exists_limitingScheme_cqCorr η s₃ s₅
  refine ⟨(cq_mehler_expansion η s₃ s₅).2, fun m _ => extract η s₃ s₅ m, ?_⟩
  intro m hm he
  rw [← hS]
  have hodd : (fun t : ℝ => S.corr (-t)) =ᶠ[𝓝 0] (fun t => -S.corr t) :=
    (unit_near (by norm_num : |(0:ℝ)|<1)).mono fun _ ht => normalized_corr_odd S ht
  have h := hodd.iteratedDeriv_eq m
  rw [iteratedDeriv_comp_neg,neg_zero,he.neg_one_pow,one_smul,iteratedDeriv_fun_neg] at h
  have hz : iteratedDeriv m S.corr 0 = 0 := by linarith
  simp [taylorCoeff,hz]
