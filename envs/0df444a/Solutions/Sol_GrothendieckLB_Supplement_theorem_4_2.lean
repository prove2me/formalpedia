-- Prove2me | solution 1 for GrothendieckLB.Supplement.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:06:06.731263+00:00
-- url     : https://prove2.me/submissions/fb3ca4c2-491b-42b0-9f22-c47e71a9940e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_theorem_2_4
import Theorems.Thm_GrothendieckLB_Supplement_theorem_3_7
import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Theorems.Thm_GrothendieckLB_Supplement_cq_coefficient_estimates_at_251
import Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_bound_of_coefficient_gap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Real.Pi.Bounds

open Filter MeasureTheory GrothendieckLB GrothendieckLB.Supplement
open scoped Topology

/- The oddness, real Taylor expansion and finite-tail arguments below adapt the
   public Prove2Me submissions e5be45ba-30d4-4759-b81c-18c40f16b01e and
   642af0cb-1bb9-49c5-b115-570b132bc2d7 (Apache 2.0). -/

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

private theorem real_taylor_on_disk (H : ℝ → ℝ) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t| < 1 → F t = (H t : ℂ)) :
    AnalyticAt ℝ H 0 ∧
      ∀ t : ℝ, |t| < 1 → H t = ∑' n, taylorCoeff n H * t^n := by
  have hmem {x : ℝ} (hx : |x| < 1) : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, Real.norm_eq_abs] using hx
  have hiter (n : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv n F) (Metric.ball 0 1) := by
    induction n with
    | zero => simpa using hF.analyticOnNhd Metric.isOpen_ball
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hjets (n : ℕ) : ∀ t : ℝ, |t| < 1 →
      iteratedDeriv n H t = (iteratedDeriv n F (t : ℂ)).re := by
    induction n with
    | zero => intro t ht; simp [hreal t ht]
    | succ n ih =>
      intro t ht
      have hlocal : iteratedDeriv n H =ᶠ[𝓝 t] fun y : ℝ => (iteratedDeriv n F (y : ℂ)).re :=
        (unit_near ht).mono fun y hy => ih y hy
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact hlocal.deriv_eq.trans ((hiter n _ (hmem ht)).differentiableAt.hasDerivAt.real_of_complex.deriv)
  have hzero : |(0 : ℝ)| < 1 := by norm_num
  constructor
  · have hf0 : AnalyticAt ℂ F ((0 : ℝ) : ℂ) := (hF.analyticOnNhd Metric.isOpen_ball) _ (hmem hzero)
    apply hf0.re_ofReal.congr
    filter_upwards [unit_near hzero] with t ht
    simp [hreal t ht]
  · intro t ht
    have hc := Complex.hasSum_taylorSeries_on_ball hF (hmem ht)
    have hr := RCLike.hasSum_re ℂ hc
    rw [hreal t ht] at hr
    have hs : HasSum (fun n : ℕ => taylorCoeff n H * t^n) (H t) := by
      apply hr.congr_fun
      intro n
      rw [taylorCoeff, hjets n 0 hzero]
      change ((iteratedDeriv n F (0 : ℂ)).re / n.factorial) * t^n =
        (((n.factorial : ℂ)⁻¹) * (((t : ℂ) - 0)^n * iteratedDeriv n F 0)).re
      simp only [sub_zero, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
        Complex.re_ofReal_mul]
      ring
    exact hs.tsum_eq.symm

private theorem inverse_certificate {k : ℕ} (S : LimitingScheme k)
    (γ : ℝ) (hγ : 0 < γ)
    (hsum : Summable (fun j : ℕ => |taylorCoeff (2*j+3) S.corr|))
    (hgap : γ + (∑' j : ℕ, |taylorCoeff (2*j+3) S.corr|) < taylorCoeff 1 S.corr) :
    (∃ G : ℝ → ℝ, IsLocalInverseBranch S.corr G) ∧
    (∀ G : ℝ → ℝ, IsLocalInverseBranch S.corr G →
      Summable (fun n : ℕ => |taylorCoeff (n+1) G| * γ^(n+1)) ∧
      ∑' n : ℕ, |taylorCoeff (n+1) G| * γ^(n+1) < 1) := by
  let b (n : ℕ) := taylorCoeff n S.corr
  have hodd : (fun t : ℝ => S.corr (-t)) =ᶠ[𝓝 0] (fun t => -S.corr t) :=
    (unit_near (by norm_num : |(0 : ℝ)| < 1)).mono fun _ ht => normalized_corr_odd S ht
  have h0 : S.corr 0 = 0 := by
    have h := hodd.eq_of_nhds
    change S.corr (-0) = -S.corr 0 at h
    rw [neg_zero] at h
    linarith
  have heven (n : ℕ) (hn : Even n) : b n = 0 := by
    have h := hodd.iteratedDeriv_eq n
    rw [iteratedDeriv_comp_neg, neg_zero, hn.neg_one_pow, one_smul, iteratedDeriv_fun_neg] at h
    have he : iteratedDeriv n S.corr 0 = 0 := by linarith
    simp [b, taylorCoeff, he]
  have htail : HasSum (fun n : ℕ => |b (n+2)|) (∑' j : ℕ, |b (2*j+3)|) := by
    have he : HasSum (fun j : ℕ => |b (2*j+2)|) 0 := by
      have hz (j : ℕ) : b (2*j+2) = 0 := heven _ ⟨j+1, by omega⟩
      simp [hz]
    have ho : HasSum (fun j : ℕ => |b ((2*j+1)+2)|) (∑' j : ℕ, |b (2*j+3)|) := by
      simpa only [Nat.add_assoc] using hsum.hasSum
    simpa only [zero_add] using (HasSum.even_add_odd (f := fun n => |b (n+2)|) he ho)
  have hall : Summable (fun n : ℕ => |b n|) := (summable_nat_add_iff 2).1 htail.summable
  have hgap' : γ + (∑' n : ℕ, |b (n+2)|) < b 1 := by rwa [htail.tsum_eq]
  have hb : 0 < b 1 := lt_trans (add_pos_of_pos_of_nonneg hγ (tsum_nonneg fun _ => abs_nonneg _)) hgap'
  have hder : 0 < deriv S.corr 0 := by simpa [b, taylorCoeff, iteratedDeriv_one] using hb
  obtain ⟨F, hF, hreal, _⟩ := theorem_3_7 S
  obtain ⟨hA, hseries⟩ := real_taylor_on_disk S.corr F hF hreal
  let G := hA.hasStrictDerivAt.localInverse S.corr (deriv S.corr 0) 0 hder.ne'
  have hG : IsLocalInverseBranch S.corr G := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [h0] using hA.analyticAt_localInverse hder.ne'
    · simpa only [h0] using (hA.hasStrictDerivAt.eventually_left_inverse hder.ne').self_of_nhds
    · simpa only [h0] using hA.hasStrictDerivAt.eventually_right_inverse hder.ne'
  refine ⟨⟨G, hG⟩, ?_⟩
  intro U hU
  obtain ⟨_, hs, hu, hstrict⟩ := theorem_2_4 b heven hb hall S.corr hseries U hU γ hγ hgap'
  exact ⟨hs, hu.trans_lt hstrict⟩

set_option maxHeartbeats 1000000 in
private theorem compare_endpoints :
    Real.pi / (2 * 0.881545409) ≤ (1.7818666069360661 : ℝ) ∧
    (1.7818666069360661 : ℝ) <
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.4737e-4 := by
  constructor
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 * 0.881545409)).mpr
    linarith only [Real.pi_lt_d20]
  · have hsqrt : Real.sqrt 2 ≤ 1.41421356238 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hlog : Real.log (1 + Real.sqrt 2) ≤ 0.88137358705 := by
      apply (Real.log_le_iff_le_exp (show 0 < 1 + Real.sqrt 2 by positivity)).2
      calc
        1 + Real.sqrt 2 ≤ 1 + 1.41421356238 := by linarith only [hsqrt]
        _ ≤ ∑ j ∈ Finset.range 14, (0.88137358705 : ℝ)^j / (j.factorial : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial_succ]
        _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 14
    have hpositive : 0 < Real.log (1 + Real.sqrt 2) :=
      Real.log_pos (lt_add_of_pos_right _ (by positivity))
    apply lt_sub_iff_add_lt.mpr
    apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hpositive)).mpr
    linarith only [hlog, Real.pi_gt_d20]

theorem solution :
    (∃ G : ℝ → ℝ, IsLocalInverseBranch (cqCorr 0.136419125 0.34101124 0.05276111) G) ∧
    (∀ G : ℝ → ℝ, IsLocalInverseBranch (cqCorr 0.136419125 0.34101124 0.05276111) G →
      Summable (fun n : ℕ => |taylorCoeff (n + 1) G| * (0.881545409 : ℝ) ^ (n + 1)) ∧
      ∑' n : ℕ, |taylorCoeff (n + 1) G| * (0.881545409 : ℝ) ^ (n + 1) < 1) ∧
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2 * 0.881545409) ∧
    Real.pi / (2 * 0.881545409) ≤ (1.7818666069360661 : ℝ) ∧
    (1.7818666069360661 : ℝ) <
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.4737e-4 := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let a (j : ℕ) := |taylorCoeff (2*j+3) H|
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
  have hsumS : Summable (fun j : ℕ => |taylorCoeff (2*j+3) S.corr|) := by
    rw [hS]
    exact hsum
  have hgapS : 0.881545409 + (∑' j : ℕ, |taylorCoeff (2*j+3) S.corr|) <
      taylorCoeff 1 S.corr := by
    rw [hS]
    exact hgap
  obtain ⟨hex, hmajorant⟩ := inverse_certificate S 0.881545409 (by norm_num) hsumS hgapS
  rw [hS] at hex hmajorant
  exact ⟨hex, hmajorant,
    limitingScheme_bound_of_coefficient_gap S 0.881545409 (by norm_num) hsumS hgapS,
    compare_endpoints⟩
