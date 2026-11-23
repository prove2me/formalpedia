-- Prove2me | solution 1 for GrothendieckLB.Supplement.limitingScheme_bound_of_coefficient_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:48:42.838164+00:00
-- url     : https://prove2.me/submissions/e5be45ba-30d4-4759-b81c-18c40f16b01e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_theorem_2_4
import Theorems.Thm_GrothendieckLB_Supplement_theorem_3_7
import Theorems.Thm_GrothendieckLB_Supplement_theorem_3_9
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.TaylorSeries

open Filter MeasureTheory GrothendieckLB GrothendieckLB.Supplement
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

private theorem allowable_dilate {ρ : ℝ → ℝ} (hρ : IsAllowableCorr ρ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : IsAllowableCorr (fun t => ρ (q*t)) := by
  obtain ⟨c, he, hsum, hnorm, hrep⟩ := hρ
  have hb (n : ℕ) : |c n * q^n| ≤ |c n| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 n)]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hq0 hq1)
  have hs := Summable.of_nonneg_of_le (fun n : ℕ => abs_nonneg (c n * q^n)) hb hsum
  refine ⟨fun n => c n * q^n, fun n hn => by simp [he n hn], hs,
    (hs.tsum_le_tsum hb hsum).trans hnorm, ?_⟩
  intro t ht
  have hqt : |q*t| < 1 := by
    rw [abs_mul, abs_of_nonneg hq0]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg t) hq1) ht
  change ρ (q*t) = ∑' n : ℕ, c n * q^n * t^n
  rw [hrep (q*t) hqt]
  exact tsum_congr fun n => by rw [mul_pow]; ring

private noncomputable def dilateScheme {k : ℕ} (S : LimitingScheme k)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : LimitingScheme k :=
  { S with ρ := fun i t => S.ρ i (q*t),
           ρ_allowable := fun i => allowable_dilate (S.ρ_allowable i) hq0 hq1 }

private theorem strict_rounding {k : ℕ} (S : LimitingScheme k)
    (hA : AnalyticAt ℝ S.corr 0) (hder : deriv S.corr 0 ≠ 0)
    (G : ℝ → ℝ) (hG : IsLocalInverseBranch S.corr G) (hG1 : 0 < taylorCoeff 1 G)
    (γ : ℝ) (hγ : 0 < γ)
    (hrad : ∃ R : ℝ, γ < R ∧ Summable (fun n => |taylorCoeff n G| * R^n))
    (hsum : Summable (fun n : ℕ => |taylorCoeff (n+1) G| * γ^(n+1)))
    (hs : (∑' n : ℕ, |taylorCoeff (n+1) G| * γ^(n+1)) < 1) :
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2*γ) := by
  let w (n : ℕ) := |taylorCoeff (n+1) G| * γ^(n+1)
  let q := ∑' j : ℕ, w (2*j)
  have hpos (n : ℕ) : 0 ≤ w n := mul_nonneg (abs_nonneg _) (pow_nonneg hγ.le _)
  have hi : Function.Injective (fun j : ℕ => 2*j) := by
    intro i j h
    change 2*i = 2*j at h
    omega
  have hodd : Summable (fun j : ℕ => w (2*j)) := hsum.comp_injective hi
  have hq : 0 < q := by
    apply hodd.tsum_pos (fun j => hpos (2*j)) 0
    simpa [w] using mul_pos (abs_pos.mpr hG1.ne') hγ
  have hq1 : q ≤ 1 := (tsum_comp_le_tsum_of_inj (f := w) hsum hpos hi).trans hs.le
  let T := dilateScheme S q hq.le hq1
  let U (z : ℝ) := q⁻¹ * G z
  have hscale : HasDerivAt (fun x : ℝ => q*x) q 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul q
  have houter : HasDerivAt S.corr (deriv S.corr 0) (q*0) := by
    simpa using hA.differentiableAt.hasDerivAt
  have hT : HasDerivAt T.corr (deriv S.corr 0 * q) 0 := houter.comp 0 hscale
  have hU : IsLocalInverseBranch T.corr U := by
    refine ⟨analyticAt_const.mul hG.1, ?_, ?_⟩
    · change q⁻¹ * G 0 = 0
      rw [hG.2.1, mul_zero]
    · filter_upwards [hG.2.2] with z hz
      change S.corr (q * (q⁻¹ * G z)) = z
      rwa [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  have hc (n : ℕ) (r : ℝ) : |taylorCoeff n U| * r^n = q⁻¹ * (|taylorCoeff n G| * r^n) := by
    have hc' : taylorCoeff n U = q⁻¹ * taylorCoeff n G := by
      unfold taylorCoeff U
      rw [iteratedDeriv_const_mul_field]
      ring
    rw [hc', abs_mul, abs_of_nonneg (inv_nonneg.mpr hq.le), mul_assoc]
  have hTne : deriv T.corr 0 ≠ 0 := by
    rw [hT.deriv]
    exact mul_ne_zero hder hq.ne'
  apply theorem_3_9 T hTne U hU γ hγ
  · obtain ⟨R, hR, hsR⟩ := hrad
    refine ⟨R, hR, ?_⟩
    simpa only [hc] using hsR.mul_left q⁻¹
  · calc
      (∑' j : ℕ, |taylorCoeff (2*j+1) U| * γ^(2*j+1)) = ∑' j : ℕ, q⁻¹ * w (2*j) :=
        tsum_congr fun j => hc (2*j+1) γ
      _ = q⁻¹ * q := tsum_mul_left
      _ = 1 := inv_mul_cancel₀ hq.ne'

theorem solution {k : ℕ} (S : LimitingScheme k)
    (γ : ℝ) (hγ : 0 < γ)
    (hsum : Summable (fun j : ℕ => |taylorCoeff (2*j+3) S.corr|))
    (hgap : γ + (∑' j : ℕ, |taylorCoeff (2*j+3) S.corr|) < taylorCoeff 1 S.corr) :
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2*γ) := by
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
  have hdG : HasStrictDerivAt G (deriv S.corr 0)⁻¹ 0 := by
    simpa only [h0] using hA.hasStrictDerivAt.to_localInverse hder.ne'
  have hG1 : 0 < taylorCoeff 1 G := by
    simpa [taylorCoeff, iteratedDeriv_one, hdG.hasDerivAt.deriv] using inv_pos.mpr hder
  obtain ⟨hrad, hMsum, hM, hlt⟩ := theorem_2_4 b heven hb hall S.corr hseries G hG γ hγ hgap'
  exact strict_rounding S hA hder.ne' G hG hG1 γ hγ hrad hMsum (lt_of_le_of_lt hM hlt)
