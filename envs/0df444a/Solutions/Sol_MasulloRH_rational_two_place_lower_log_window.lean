-- Prove2me | solution 1 for MasulloRH.rational_two_place_lower_log_window
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:04:38.682046+00:00
-- url     : https://prove2.me/submissions/4498cbd5-97d2-4598-8d80-84f1242d25ba

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecificLimits.Normed

section
open Set MeasureTheory Filter
open scoped Topology

private theorem fiber_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v b : ℝ) (e : E) :
    (∫ t : ℝ, if v < t ∧ t ≤ b then e else 0) = (max (b-v) 0) • e := by
  simpa only [Set.indicator_apply, Set.mem_Ioc, Real.volume_real_Ioc] using
    (integral_indicator_const (μ := (volume : Measure ℝ)) e (measurableSet_Ioc (a:=v) (b:=b)))

private theorem log_layer {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (v : X → ℝ) (hv : Measurable v) (F : X → ℂ) (hF : Measurable F) (b : ℝ)
    (hL : Integrable (fun x => max (b-v x) 0 * ‖F x‖) μ) :
    (∫ x, max (b-v x) 0 • F x ∂μ) = ∫ t in Iic b, ∫ x in {x | v x < t}, F x ∂μ := by
  let H (q : X × ℝ) := if v q.1 < q.2 ∧ q.2 ≤ b then F q.1 else 0
  have hM : Measurable H :=
    (hF.comp measurable_fst).ite ((measurableSet_lt (hv.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) measurable_const
  have hI : Integrable H (μ.prod volume) := by
    apply (integrable_prod_iff hM.aestronglyMeasurable).mpr
    constructor
    · apply ae_of_all
      intro x
      have hconst : IntegrableOn (fun _ : ℝ => F x) (Ioc (v x) b) := integrableOn_const measure_Ioc_lt_top.ne
      apply (hconst.integrable_indicator measurableSet_Ioc).congr
      filter_upwards with t
      simp only [Set.indicator_apply, Set.mem_Ioc, H]
    · apply hL.congr
      filter_upwards with x
      dsimp only [H]
      simp_rw [apply_ite norm, norm_zero]
      rw [fiber_int, smul_eq_mul]
  calc
    _ = ∫ x, ∫ t : ℝ, H (x,t) ∂volume ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => (fiber_int _ _ _).symm)
    _ = ∫ t, ∫ x, H (x,t) ∂μ := integral_integral_swap hI
    _ = _ := by
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ≤ b
      · simp only [Set.indicator_of_mem (show t ∈ Iic b from ht), H,ht,and_true]
        exact integral_indicator (s := {x | v x < t}) (measurableSet_lt hv measurable_const)
      · simp [H,ht]

private theorem lower_log_estimate {X I : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (v : X → ℝ) (hv : Measurable v) (F : I → X → ℂ) (hF : ∀ i, Measurable (F i))
    (A B C δ : ℝ) (hwin : -C ≤ A) (hd : 0 < δ)
    (K : I → ℝ) (hK : Summable K)
    (hL : ∀ i, Integrable (fun x => max (B-C-v x) 0 * ‖F i x‖) μ)
    (hbound : ∀ i t, t ≤ B-C → ‖∫ x in {x | v x < t}, F i x ∂μ‖ ≤ K i * Real.exp (δ*t)) :
    let D i := ∫ x, (max (A+B-v x) 0 - max (A-max (-C) (v x-B)) 0) • F i x ∂μ
    (∀ i, D i = ∫ t in Iic (B-C), ∫ x in {x | v x < t}, F i x ∂μ) ∧
    Summable (fun i => ‖D i‖) ∧
    (∑' i, ‖D i‖) ≤ (∑' i, K i) * (Real.exp (δ*(B-C))/δ) := by
  intro D
  have he (x : X) : max (A+B-v x) 0 - max (A-max (-C) (v x-B)) 0 = max (B-C-v x) 0 := by
    rcases le_total (v x-B) (-C) with h | h
    · rw [max_eq_left h,max_eq_left (by linarith : 0 ≤ A+B-v x),max_eq_left (by linarith : 0 ≤ A- -C),max_eq_left (by linarith : 0 ≤ B-C-v x)]; ring
    · rw [max_eq_right h,show A-(v x-B)=A+B-v x by ring,sub_self,max_eq_right (by linarith : B-C-v x ≤ 0)]
  have hEq (i : I) : D i = ∫ t in Iic (B-C), ∫ x in {x | v x < t}, F i x ∂μ := by
    simp only [D,he]
    exact log_layer μ v hv (F i) (hF i) _ (hL i)
  let E := Real.exp (δ*(B-C))/δ
  have hpt (i : I) : ‖D i‖ ≤ K i * E := by
    rw [hEq]
    calc
      _ ≤ ∫ t in Iic (B-C), K i * Real.exp (δ*t) := by
        apply norm_integral_le_of_norm_le
        · exact (integrableOn_exp_mul_Iic hd _).const_mul _
        · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iic] with t ht using hbound i t ht
      _ = _ := by rw [integral_const_mul,integral_exp_mul_Iic hd]
  have hsum := (hK.mul_right E).of_nonneg_of_le (fun i => norm_nonneg (D i)) hpt
  exact ⟨hEq,hsum,(hsum.tsum_le_tsum hpt (hK.mul_right E)).trans_eq tsum_mul_right⟩

open MeasureTheory Set

theorem MasulloRH.mixed_sublevel_oscillation_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] (v : X → ℝ) (w : Y → ℝ) (hv : Measurable v) (hw : Measurable w)
    (f : X → ℂ) (g : Y → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (δ A t : ℝ) (_hA : 0 ≤ A)
    (hb : ∀ r, ‖∫ x in {x | v x < r}, f x ∂μ‖ ≤ A * Real.exp (δ*r))
    (hW : Integrable (fun y => Real.exp (-δ*w y)*‖g y‖) ν) :
    ‖∫ q in {q : X × Y | v q.1 + w q.2 < t}, f q.1 * g q.2 ∂(μ.prod ν)‖ ≤
    A * Real.exp (δ*t) * ∫ y, Real.exp (-δ*w y)*‖g y‖ ∂ν := by
  let S := {q : X × Y | v q.1 + w q.2 < t}
  have hm : MeasurableSet S := measurableSet_lt ((hv.comp measurable_fst).add (hw.comp measurable_snd)) measurable_const
  have H := (hf.mul_prod hg).indicator hm
  rw [← integral_indicator hm, integral_prod_symm _ H]
  have eq (y : Y) : (∫ x, S.indicator (fun q => f q.1 * g q.2) (x,y) ∂μ) =
      (∫ x in {x | v x < t-w y}, f x ∂μ) * g y := by
    rw [← integral_mul_const, ← integral_indicator (measurableSet_lt hv measurable_const)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Set.indicator_apply,S,Set.mem_ofPred_eq,lt_sub_iff_add_lt]
  simp_rw [eq]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hW.const_mul _)
  filter_upwards with y
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_right (hb (t-w y)) (norm_nonneg _)).trans_eq ?_
  rw [mul_sub,sub_eq_add_neg,Real.exp_add,neg_mul]
  ring
open Set MeasureTheory Filter
open scoped Topology

private theorem interp_min (t k δ : ℝ) (hδ : 0 ≤ δ) (hd : δ ≤ 1) :
    min (Real.exp t) (Real.exp (-k)) ≤ Real.exp (δ*t) * Real.exp (-(1-δ)*k) := by
  rw [← Real.exp_add, ← Real.exp_monotone.map_min]
  apply Real.exp_le_exp.mpr
  by_cases h : t ≤ -k
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr (le_of_not_ge h))]

theorem MasulloRational.one_ray_log_defect
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] (v : X → ℝ) (w : Y → ℝ) (hv : Measurable v) (hw : Measurable w)
    (f : ℕ → X → ℂ) (g : ℕ → Y → ℂ) (hf : ∀ j, Measurable (f j)) (hg : ∀ j, Measurable (g j))
    (hi : ∀ j, Integrable (f j) μ) (hi' : ∀ j, Integrable (g j) ν)
    (L δ A C : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hd : δ < 1) (hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hfW : ∀ j, Integrable (fun x => Real.exp (-δ*v x)*‖f j x‖) μ)
    (hgW : ∀ j, Integrable (fun y => Real.exp (-δ*w y)*‖g j y‖) ν)
    (hgC : ∀ j, (∫ y, Real.exp (-δ*w y)*‖g j y‖ ∂ν) ≤ C)
    (hprim : ∀ j t, ‖∫ x in {x | v x < t}, f j x ∂μ‖ ≤ A * min (Real.exp t) (Real.exp (-(j:ℝ)*L)))
    (U V W : ℝ) (hUV : -W ≤ U) :
    let r := Real.exp (-(1-δ)*L)
    let D j := ∫ q : X×Y,
      (max (U+V-(v q.1+w q.2)) 0 - max (U-max (-W) ((v q.1+w q.2)-V)) 0) •
        (f j q.1 * g j q.2) ∂(μ.prod ν)
    Summable (fun j => ‖D j‖) ∧ (∑' j, ‖D j‖) ≤ (A*C)/(1-r) * (Real.exp (δ*(V-W))/δ) := by
  intro r D
  have hr : r < 1 := by dsimp [r]; apply Real.exp_lt_one_iff.mpr; nlinarith [mul_pos (sub_pos.mpr hd) hL]
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  let K (j : ℕ) := r^j * (A*C)
  have hs := (hasSum_geometric_of_lt_one hr0 hr).mul_right (A*C)
  have hM (j : ℕ) : Integrable (fun q : X×Y => max (V-W-(v q.1+w q.2)) 0 * ‖f j q.1 * g j q.2‖) (μ.prod ν) := by
    let Z := Real.exp (δ*(V-W))/δ
    have hwgt := ((hfW j).mul_prod (hgW j)).const_mul Z
    apply hwgt.mono'
    · exact (((measurable_const.sub ((hv.comp measurable_fst).add (hw.comp measurable_snd))).max measurable_const).mul
        (((hf j).comp measurable_fst).mul ((hg j).comp measurable_snd)).norm).aestronglyMeasurable
    · filter_upwards with q
      set a := V-W-(v q.1+w q.2)
      have hpos : 0 ≤ max a 0 * ‖f j q.1 * g j q.2‖ := by positivity
      rw [Real.norm_eq_abs,abs_of_nonneg hpos,norm_mul]
      have hmax : max a 0 ≤ Real.exp (δ*a)/δ := by
        apply max_le
        · apply (le_div_iff₀ hδ).mpr
          linarith [Real.add_one_le_exp (δ*a)]
        · positivity
      refine (mul_le_mul_of_nonneg_right hmax (by positivity : 0 ≤ ‖f j q.1‖ * ‖g j q.2‖)).trans_eq ?_
      dsimp [Z,a]
      rw [show δ*(V-W-(v q.1+w q.2))= δ*(V-W) + (-δ*v q.1) + (-δ*w q.2) by ring,Real.exp_add,Real.exp_add]
      ring
  have hbound (j : ℕ) (t : ℝ) : ‖∫ q in {q : X×Y | v q.1+w q.2<t}, f j q.1*g j q.2 ∂(μ.prod ν)‖ ≤ K j*Real.exp (δ*t) := by
    have hp (b : ℝ) : ‖∫ x in {x | v x < b}, f j x ∂μ‖ ≤ (A*r^j)*Real.exp (δ*b) := by
      have H := interp_min b ((j:ℝ)*L) δ hδ.le hd.le
      have hpow : Real.exp (-(1-δ)*((j:ℝ)*L)) = r^j := by
        rw [show -(1-δ)*((j:ℝ)*L)= (j:ℝ)*(-(1-δ)*L) by ring,Real.exp_nat_mul]
      rw [hpow,← neg_mul] at H
      exact (hprim j b).trans ((mul_le_mul_of_nonneg_left H hA).trans_eq (by ring))
    have H := MasulloRH.mixed_sublevel_oscillation_bound μ ν v w hv hw (f j) (g j) (hi j) (hi' j) δ (A*r^j) t (by positivity) hp (hgW j)
    exact H.trans ((mul_le_mul_of_nonneg_left (hgC j) (by positivity : 0 ≤ A*r^j*Real.exp (δ*t))).trans_eq (by dsimp [K]; ring))
  have H := lower_log_estimate (μ.prod ν) (fun q : X×Y => v q.1+w q.2) ((hv.comp measurable_fst).add (hw.comp measurable_snd))
    (fun j (q : X×Y) => f j q.1*g j q.2) (fun j => ((hf j).comp measurable_fst).mul ((hg j).comp measurable_snd))
    U V W δ hUV hδ K hs.summable hM (fun j t _ => hbound j t)
  refine ⟨H.2.1, H.2.2.trans_eq ?_⟩
  rw [show (∑' j, K j) = _ from hs.tsum_eq]; simp only [div_eq_mul_inv]; ring
end

section
open MeasureTheory
open scoped Padic ENNReal

private theorem padic_ball_period_zero (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]]
    [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψ : ψ ((p : ℚ_[p])⁻¹) ≠ 1)
    (g : ℚ_[p] → ℂ) (L R : ℝ) (ξ : ℚ_[p]) (hξ : ξ ≠ 0)
    (hg : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y)
    (hL : (p : ℝ)/‖ξ‖ ≤ L) (hR : (p : ℝ)/‖ξ‖ < R) :
    ∫ y in Metric.ball 0 R, g y * ψ (ξ*y) ∂μ = 0 := by
  let d : ℚ_[p] := ξ⁻¹ * (p : ℚ_[p])⁻¹
  have hm : ξ*d = (p : ℚ_[p])⁻¹ := by simp [d,hξ]
  have hd : ‖d‖ = (p : ℝ)/‖ξ‖ := by simp [d,Padic.norm_p,div_eq_mul_inv,mul_comm]
  have stable (y : ℚ_[p]) : d+y ∈ Metric.ball 0 R ↔ y ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball,dist_zero_right]
    have hdr : ‖d‖ < R := hd ▸ hR
    constructor
    · intro hy
      have hyp := (Padic.nonarchimedean (-d) (d+y)).trans_lt (max_lt (by simpa using hdr) hy)
      simpa using hyp
    · intro hy
      exact (Padic.nonarchimedean d y).trans_lt (max_lt hdr hy)
  let F : ℚ_[p] → ℂ := (Metric.ball 0 R).indicator (fun y => g y * ψ (ξ*y))
  have ht (y : ℚ_[p]) : F (d+y) = ψ ((p : ℚ_[p])⁻¹)*F y := by
    by_cases hy : y ∈ Metric.ball 0 R
    · simp only [F,Set.indicator_of_mem ((stable y).2 hy),Set.indicator_of_mem hy,
        hg y d (hd ▸ hL), mul_add,ψ.map_add_eq_mul,hm,mul_left_comm]
    · simp only [F, Set.indicator_of_notMem (mt (stable y).1 hy),Set.indicator_of_notMem hy,mul_zero]
  have hi := integral_add_left_eq_self (μ := μ) F d
  simp_rw [ht] at hi
  rw [integral_const_mul] at hi
  have hz : (∫ y, F y ∂μ) = 0 := by
    by_contra hn
    exact hψ (mul_right_cancel₀ hn (hi.trans (one_mul _).symm))
  simpa only [F,integral_indicator measurableSet_ball] using hz

theorem MasulloRational.padic_ball_primitive (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψ : ψ ((p : ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1) (g : ℚ_[p] → ℂ) (V M S L : ℝ)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hS : 0 < S) (hL : 0 < L)
    (hμ : ∀ r : ℝ, 0 < r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (V*r))
    (hbound : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, S ≤ ‖y‖ → g y = 0)
    (hperiod : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y) :
    let B := max 1 ((p : ℝ)/L)
    let C := M*V*(max 1 (max (p : ℝ) (S*B)))
    ∀ (R : ℝ) (ξ : ℚ_[p]), 0 < R →
      ‖∫ y in Metric.ball 0 R, g y * ψ (ξ*y) ∂μ‖ ≤ C * min R (1 / max 1 ‖ξ‖) := by
  intro B C R ξ hR
  have hMV := mul_nonneg hM hV
  have hB : 1 ≤ B := le_max_left _ _
  let A := max 1 (max (p : ℝ) (S*B))
  have hA : 1 ≤ A := le_max_left _ _
  have hup : M*V ≤ C := le_mul_of_one_le_right hMV hA
  have hC := hMV.trans hup
  let H := fun y : ℚ_[p] => g y * ψ (ξ*y)
  have hH (y) : ‖H y‖ ≤ M := by
    calc ‖H y‖ = ‖g y‖ * ‖ψ (ξ*y)‖ := norm_mul _ _
         _ ≤ M * 1 := mul_le_mul (hbound _) (hunit _) (norm_nonneg _) hM
         _ = M := mul_one _
  have small (a : ℝ) (ha : 0 < a) : ‖∫ y in Metric.ball 0 a, H y ∂μ‖ ≤ M*V*a := by
    have hm := hμ a ha
    have hm' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    rw [ENNReal.toReal_ofReal (mul_nonneg hV ha.le)] at hm'
    calc
      ‖∫ y in Metric.ball 0 a, H y ∂μ‖ ≤ M * μ.real (Metric.ball 0 a) :=
        norm_setIntegral_le_of_norm_le_const (hm.trans_lt ENNReal.ofReal_lt_top) fun y _ => hH y
      _ ≤ M*(V*a) := mul_le_mul_of_nonneg_left hm' hM
      _ = M*V*a := (mul_assoc _ _ _).symm
  have cap : ‖∫ y in Metric.ball 0 R, H y ∂μ‖ ≤ M*V*S := by
    by_cases hrs : R ≤ S
    · exact (small _ hR).trans (mul_le_mul_of_nonneg_left hrs hMV)
    · have same : (Metric.ball 0 R).indicator H = (Metric.ball 0 S).indicator H := by
        funext y
        by_cases hy : ‖y‖ < S
        · have hr : ‖y‖ < R := hy.trans (lt_of_not_ge hrs)
          simp [Set.indicator,Metric.mem_ball,hr,hy]
        · simp [Set.indicator,Metric.mem_ball,hy,H,hsupp y (le_of_not_gt hy)]
      have hh := congrArg (fun F : ℚ_[p] → ℂ => ∫ y, F y ∂μ) same
      simp only [integral_indicator measurableSet_ball] at hh
      rw [hh]
      exact small _ hS
  change ‖∫ y in Metric.ball 0 R, H y ∂μ‖ ≤ C * min R (1 / max 1 ‖ξ‖)
  rw [mul_min_of_nonneg _ _ hC]
  refine le_min ((small R hR).trans (mul_le_mul_of_nonneg_right hup hR.le)) ?_
  rw [← div_eq_mul_one_div]
  have hden : 0 < max 1 ‖ξ‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply (le_div_iff₀ hden).2
  by_cases slow : ‖ξ‖ ≤ B
  · have hden' : max 1 ‖ξ‖ ≤ B := max_le hB slow
    calc
      _ ≤ (M*V*S)*B := mul_le_mul cap hden' hden.le (mul_nonneg hMV hS.le)
      _ = (M*V)*(S*B) := mul_assoc _ _ _
      _ ≤ C := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) hMV
  · have hb : B < ‖ξ‖ := lt_of_not_ge slow
    have hf : 0 < ‖ξ‖ := lt_trans zero_lt_one (hB.trans_lt hb)
    rw [max_eq_right (hB.trans hb.le)]
    by_cases short : R ≤ (p : ℝ)/‖ξ‖
    · calc
        _ ≤ (M*V*R)*‖ξ‖ := mul_le_mul_of_nonneg_right (small R hR) hf.le
        _ = (M*V)*(R*‖ξ‖) := mul_assoc _ _ _
        _ ≤ (M*V)*(p : ℝ) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hf).1 short) hMV
        _ ≤ C := mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) hMV
    · have hplevel : (p : ℝ)/L < ‖ξ‖ := lt_of_le_of_lt (le_max_right _ _) hb
      have hd : (p : ℝ)/‖ξ‖ ≤ L := (div_le_iff₀ hf).2 (by
        have hp' := (div_lt_iff₀ hL).1 hplevel
        linarith [mul_comm L ‖ξ‖])
      have hz := padic_ball_period_zero p μ ψ hψ g L R ξ (norm_pos_iff.mp hf) hperiod hd (lt_of_not_ge short)
      change (∫ y in Metric.ball 0 R, H y ∂μ) = 0 at hz
      simpa [hz] using hC

private theorem padic_singleton_null_of_ball_bound (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] (μ : Measure ℚ_[p]) (V : ℝ) (hV : 0 ≤ V)
    (hμ : ∀ r : ℝ, 0 < r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (V*r)) :
    μ {(0:ℚ_[p])} = 0 := by
  have bound (r : ℝ) (hr : 0 < r) : μ {(0:ℚ_[p])} ≤ ENNReal.ofReal (V*r) :=
    (measure_mono (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr))).trans (hμ r hr)
  have htop : μ {(0:ℚ_[p])} ≠ ⊤ := (lt_of_le_of_lt (bound 1 zero_lt_one) ENNReal.ofReal_lt_top).ne
  by_contra hne
  let a := (μ {(0:ℚ_[p])}).toReal
  have ha : 0 < a := ENNReal.toReal_pos hne htop
  let r := a/(1+V)
  have h1 : 0 < 1+V := by linarith
  have hr : 0 < r := div_pos ha h1
  have hsmall := ENNReal.toReal_mono ENNReal.ofReal_ne_top (bound r hr)
  rw [ENNReal.toReal_ofReal (mul_nonneg hV hr.le)] at hsmall
  have halt : V*r < a := calc
    _ < (1+V)*r := by linarith
    _ = a := by dsimp only [r]; field_simp
  exact halt.not_ge hsmall

theorem MasulloRational.padic_log_ball_negative_frequency (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψ : ψ ((p : ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1) (g : ℚ_[p] → ℂ) (V M S L : ℝ)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hS : 0 < S) (hL : 0 < L)
    (hμ : ∀ r : ℝ, 0 < r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (V*r))
    (hbound : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, S ≤ ‖y‖ → g y = 0)
    (hperiod : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y) :
    let B := max 1 ((p : ℝ)/L)
    let C := M*V*(max 1 (max (p : ℝ) (S*B)))
    ∀ (η : ℚ_[p]), ‖η‖ = 1 → ∀ (j : ℕ) (t : ℝ),
      ‖∫ y in {y : ℚ_[p] | Real.log ‖y‖ < t},
          g y * ψ ((η*((p:ℚ_[p])⁻¹)^j)*y) ∂μ‖ ≤
        C * min (Real.exp t) (Real.exp (-(j:ℝ)*Real.log p)) := by
  intro B C η hη j t
  have hx := padic_singleton_null_of_ball_bound p μ V hV hμ
  have ha : ∀ᵐ y ∂μ, y ≠ 0 := measure_eq_zero_iff_ae_notMem.mp hx
  have he : {y : ℚ_[p] | Real.log ‖y‖ < t} =ᵐ[μ] Metric.ball 0 (Real.exp t) := by
    filter_upwards [ha] with y hy
    apply propext
    change (Real.log ‖y‖ < t) ↔ y ∈ Metric.ball 0 (Real.exp t)
    simpa only [Metric.mem_ball,dist_zero_right] using Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hy)
  have hp : 1 ≤ (p:ℝ) := Nat.one_le_cast.mpr (Fact.out (p:=p.Prime)).one_le
  have hf : 1 / max 1 ‖η*((p:ℚ_[p])⁻¹)^j‖ = Real.exp (-(j:ℝ)*Real.log p) := by
    rw [norm_mul,hη,one_mul,norm_pow,norm_inv,Padic.norm_p,inv_inv,max_eq_right (one_le_pow₀ hp),
      neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le hp),one_div]
  rw [setIntegral_congr_set he, ← hf]
  exact padic_ball_primitive p μ ψ hψ hunit g V M S L hV hM hS hL hμ hbound hsupp hperiod
    (Real.exp t) (η*((p:ℚ_[p])⁻¹)^j) (Real.exp_pos t)
end

section
open MeasureTheory Set
open scoped Interval

namespace MasulloMixed

noncomputable def realPhase (t x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I * (x : ℂ))

theorem norm_realPhase (t x : ℝ) : ‖realPhase t x‖ = 1 := by
  unfold realPhase
  rw [mul_right_comm, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

theorem hasDerivAt_realPhase (t x : ℝ) :
    HasDerivAt (realPhase t) (realPhase t x * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)) x := by
  let k : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  have h : HasDerivAt (fun z : ℂ ↦ k * z) k (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul k
  exact ((Complex.hasDerivAt_exp _).comp (x : ℂ) h).comp_ofReal

theorem real_fourier_interval_by_parts {f : ℝ → ℂ} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ≠ 0) (hf : ContDiff ℝ 1 f) :
    ‖∫ x in a..b, f x * realPhase t x‖ ≤
      (‖f b‖ + ‖f a‖ + ∫ x in a..b, ‖deriv f x‖) / (2 * Real.pi * |t|) := by
  let k : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  have hk : ‖k‖ = 2 * Real.pi * |t| := by
    simp [k, abs_of_pos Real.pi_pos]
  have hc : Continuous (realPhase t) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_realPhase t x).continuousAt
  have hd := hf.differentiable_one
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := a) (b := b) hf.continuous.continuousOn hc.continuousOn
    (fun x _ ↦ (hd x).hasDerivAt) (fun x _ ↦ hasDerivAt_realPhase t x)
    (hf.continuous_deriv_one.intervalIntegrable a b)
    ((hc.mul continuous_const).intervalIntegrable a b)
  change (∫ x in a..b, f x * (realPhase t x * k)) = _ at hibp
  simp_rw [← mul_assoc] at hibp
  rw [intervalIntegral.integral_mul_const] at hibp
  have hbulk : ‖∫ x in a..b, deriv f x * realPhase t x‖ ≤ ∫ x in a..b, ‖deriv f x‖ := by
    simpa only [norm_mul, norm_realPhase, mul_one] using
      (intervalIntegral.norm_integral_le_integral_norm (f := fun x ↦ deriv f x * realPhase t x) hab)
  have hbd := (norm_sub_le (f b * realPhase t b) (f a * realPhase t a))
  simp only [norm_mul, norm_realPhase, mul_one] at hbd
  apply (le_div_iff₀ (mul_pos Real.two_pi_pos (abs_pos.mpr ht))).mpr
  rw [← hk, ← norm_mul, hibp]
  exact (norm_sub_le _ _).trans (add_le_add hbd hbulk)

theorem real_fourier_interval_min {f : ℝ → ℂ} {b t A : ℝ}
    (hb : 0 ≤ b) (ht : t ≠ 0) (hf : ContDiff ℝ 1 f)
    (hA : ∀ x, ‖f x‖ ≤ A) (hD : Integrable (deriv f)) :
    ‖∫ x in -b..b, f x * realPhase t x‖ ≤
      min (2*b*A) ((2*A + ∫ x, ‖deriv f x‖) / (2*Real.pi*|t|)) := by
  have hab : -b ≤ b := by linarith
  refine le_min ?_ ?_
  · apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := A) ?_).trans
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]; exact le_of_eq (by ring)
    · intro x _
      simpa only [norm_mul, norm_realPhase, mul_one] using hA x
  · apply (real_fourier_interval_by_parts hab ht hf).trans
    apply div_le_div_of_nonneg_right _ (mul_nonneg Real.two_pi_pos.le (abs_nonneg t))
    have hInt : (∫ x in -b..b, ‖deriv f x‖) ≤ ∫ x, ‖deriv f x‖ := by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral hD.norm (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
    linarith [hA b, hA (-b)]


end MasulloMixed
namespace MasulloMixed

open MeasureTheory Filter Set

/-- Centered real log cutoffs coincide almost everywhere with an ordinary interval. -/
theorem integral_log_norm_lt_eq_interval (g : ℝ → ℂ) (t : ℝ) :
    (∫ x in {x : ℝ | Real.log ‖x‖ < t}, g x) = ∫ x in -(Real.exp t)..Real.exp t, g x := by
  have heq : {x : ℝ | Real.log ‖x‖ < t} =ᵐ[volume] Ioo (-(Real.exp t)) (Real.exp t) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with x hx
    apply propext
    change Real.log ‖x‖ < t ↔ -Real.exp t < x ∧ x < Real.exp t
    rw [Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hx),Real.norm_eq_abs,abs_lt]
  rw [setIntegral_congr_set heq,intervalIntegral.integral_of_le (by linarith [Real.exp_pos t]),
    integral_Ioc_eq_integral_Ioo]

/-- Simultaneous physical-width and reciprocal-frequency bounds for every integral lattice index. -/
theorem real_fourier_log_cutoff_min_signed {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hA : ∀ x, ‖f x‖ ≤ M) (hD : Integrable (deriv f))
    (j : ℤ) (t η : ℝ) (hη : |η| = 1) :
    ‖∫ x in {x : ℝ | Real.log ‖x‖ < t}, f x * realPhase (η*p^j) x‖ ≤
      (max (2*M) ((2*M+∫ x, ‖deriv f x‖)/(2*Real.pi))) *
        min (Real.exp t) (Real.exp (-(j:ℝ)*Real.log p)) := by
  rw [integral_log_norm_lt_eq_interval]
  have hp0 := lt_trans zero_lt_one hp
  have hpj : 0 < p^j := zpow_pos hp0 j
  have hz : η*p^j ≠ 0 := mul_ne_zero (by intro h; simp [h] at hη) hpj.ne'
  apply (real_fourier_interval_min (Real.exp_pos t).le hz hf hA hD).trans
  let B := (2*M+∫ x, ‖deriv f x‖)/(2*Real.pi)
  have hmax : 0 ≤ max (2*M) B := (mul_nonneg (by norm_num) hM).trans (le_max_left _ _)
  have hrecip : (p^j)⁻¹ = Real.exp (-(j:ℝ)*Real.log p) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hp0, ← Real.exp_neg]
    congr 1; ring
  have hrec : (2*M+∫ x, ‖deriv f x‖)/(2*Real.pi*|p^j|) = B*Real.exp (-(j:ℝ)*Real.log p) := by
    rw [abs_of_pos hpj, ←hrecip, ← div_eq_mul_inv, div_div]
  rw [abs_mul, hη, one_mul, hrec]
  change min (2*Real.exp t*M) _ ≤ (max (2*M) B) * _
  rw [mul_min_of_nonneg _ _ hmax]
  apply min_le_min
  · calc _ = (2*M)*Real.exp t := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos t).le
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem real_fourier_log_cutoff_min {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hA : ∀ x, ‖f x‖ ≤ M) (hD : Integrable (deriv f))
    (j : ℤ) (t : ℝ) :
    ‖∫ x in {x : ℝ | Real.log ‖x‖ < t}, f x * realPhase (p^j) x‖ ≤
      (max (2*M) ((2*M+∫ x, ‖deriv f x‖)/(2*Real.pi))) *
        min (Real.exp t) (Real.exp (-(j:ℝ)*Real.log p)) := by
  simpa only [one_mul] using real_fourier_log_cutoff_min_signed hp hM f hf hA hD j t 1 (by norm_num)

end MasulloMixed
end

section
open MeasureTheory Set Filter
open scoped Padic ENNReal

private theorem oscillatory_weight_control {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (h : X → ℝ) (hh : Measurable h) (f a : X → ℂ) (hf : Measurable f) (ha : Measurable a)
    (hu : ∀ x, ‖a x‖ ≤ 1) (δ : ℝ)
    (hw : Integrable (fun x => Real.exp (-δ*h x)*‖f x‖) μ) :
    Integrable (fun x => Real.exp (-δ*h x)*‖f x*a x‖) μ ∧
      (∫ x, Real.exp (-δ*h x)*‖f x*a x‖ ∂μ) ≤ ∫ x, Real.exp (-δ*h x)*‖f x‖ ∂μ := by
  have hdom (x : X) : Real.exp (-δ*h x)*‖f x*a x‖ ≤ Real.exp (-δ*h x)*‖f x‖ := by
    rw [norm_mul]
    gcongr; exact mul_le_of_le_one_right (norm_nonneg _) (hu x)
  have hi : Integrable (fun x => Real.exp (-δ*h x)*‖f x*a x‖) μ := by
    apply hw.mono' (((measurable_const.mul hh).exp.mul (hf.mul ha).norm).aestronglyMeasurable)
    filter_upwards with x
    change ‖Real.exp (-δ*h x)*‖f x*a x‖‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hdom x
  exact ⟨hi,integral_mono hi hw hdom⟩

theorem MasulloRational.two_place_log_defect_of_moments (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψm : Measurable ψ) (hψ : ψ ((p:ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1)
    (f : ℝ → ℂ) (g : ℚ_[p] → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdif : Integrable (deriv f)) (hgm : Measurable g) (hgi : Integrable g μ)
    (Mr Vp Mp Rp Lp : ℝ) (hMr : 0≤Mr) (hV : 0≤Vp) (hM : 0≤Mp) (hR : 0<Rp) (hL : 0<Lp)
    (hμ : ∀ r : ℝ, 0<r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (Vp*r))
    (hfB : ∀ x, ‖f x‖≤Mr) (hgB : ∀ y, ‖g y‖≤Mp) (hgS : ∀ y, Rp≤‖y‖ → g y=0)
    (hgP : ∀ y d : ℚ_[p], ‖d‖≤Lp → g (d+y)=g y)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hmr : Integrable (fun x : ℝ => Real.exp (-δ*Real.log ‖x‖)*‖f x‖))
    (hmp : Integrable (fun y : ℚ_[p] => Real.exp (-δ*Real.log ‖y‖)*‖g y‖) μ)
    (η : ℝ) (ηp : ℚ_[p]) (hη : |η|=1) (hηp : ‖ηp‖=1)
    (U V W : ℝ) (hUV : -W≤U) :
    let v (x : ℝ × ℚ_[p]) := Real.log ‖x.1‖ + Real.log ‖x.2‖
    let F (k : ℤ) (x : ℝ) := f x * Complex.exp
      (((2*Real.pi*(η*(p:ℝ)^k):ℝ):ℂ)*Complex.I*(x:ℂ))
    let G (k : ℤ) (y : ℚ_[p]) := g y * ψ ((ηp*(p:ℚ_[p])^k)*y)
    let D (k : ℤ) := ∫ x : ℝ × ℚ_[p],
      (max (U+V-v x) 0 - max (U-max (-W) (v x-V)) 0) • (F k x.1 * G k x.2)
      ∂(volume.prod μ)
    let Ar := max (2*Mr) ((2*Mr+∫ x, ‖deriv f x‖)/(2*Real.pi))
    let Ap := Mp*Vp*max 1 (max (p:ℝ) (Rp*max 1 ((p:ℝ)/Lp)))
    let Hr := ∫ x : ℝ, Real.exp (-δ*Real.log ‖x‖)*‖f x‖
    let Hp := ∫ y : ℚ_[p], Real.exp (-δ*Real.log ‖y‖)*‖g y‖ ∂μ
    Summable (fun k : ℤ => ‖D k‖) ∧
    (∑' k : ℤ, ‖D k‖) ≤ (Ar*Hp+Ap*Hr)/(1-Real.exp (-(1-δ)*Real.log (p:ℝ))) *
       (Real.exp (δ*(V-W))/δ) := by
  intro v F G D Ar Ap Hr Hp
  let vr (x : ℝ) := Real.log ‖x‖
  let vp (y : ℚ_[p]) := Real.log ‖y‖
  have hvr : Measurable vr := Real.measurable_log.comp (measurable_id.norm)
  have hvp : Measurable vp := Real.measurable_log.comp (measurable_id.norm)
  let e (k : ℤ) := MasulloMixed.realPhase (η*(p:ℝ)^k)
  let ep (k : ℤ) := fun y : ℚ_[p] => ψ ((ηp*(p:ℚ_[p])^k)*y)
  have he (k : ℤ) : Measurable (e k) := (continuous_iff_continuousAt.mpr (fun x => (MasulloMixed.hasDerivAt_realPhase (η*(p:ℝ)^k) x).continuousAt)).measurable
  have hen (k : ℤ) (x : ℝ) : ‖e k x‖≤1 := by
    exact (MasulloMixed.norm_realPhase _ _).le
  have hep (k : ℤ) : Measurable (ep k) := hψm.comp (continuous_const.mul continuous_id).measurable
  have hFm (k : ℤ) : Measurable (F k) := hf.continuous.measurable.mul (he k)
  have hGm (k : ℤ) : Measurable (G k) := hgm.mul (hep k)
  have hFi (k : ℤ) : Integrable (F k) := hi.mul_bdd (he k).aestronglyMeasurable (ae_of_all _ (hen k))
  have hGi (k : ℤ) : Integrable (G k) μ :=
    hgi.mul_bdd (hep k).aestronglyMeasurable (ae_of_all _ (fun y => hunit _))
  have hFw (k : ℤ) : Integrable (fun x => Real.exp (-δ*vr x)*‖F k x‖) ∧
      (∫ x : ℝ, Real.exp (-δ*vr x)*‖F k x‖) ≤ Hr :=
    oscillatory_weight_control volume vr hvr f (e k) hf.continuous.measurable (he k) (hen k) δ hmr
  have hGw (k : ℤ) : Integrable (fun y => Real.exp (-δ*vp y)*‖G k y‖) μ ∧
      (∫ y : ℚ_[p], Real.exp (-δ*vp y)*‖G k y‖ ∂μ) ≤ Hp :=
    oscillatory_weight_control μ vp hvp g (ep k) hgm (hep k) (fun y => hunit _) δ hmp
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpL := Real.log_pos hp
  have hAr : 0≤Ar := (mul_nonneg (by norm_num) hMr).trans (le_max_left _ _)
  have hAp : 0≤Ap := by dsimp [Ap]; positivity
  have hHr : 0≤Hr := integral_nonneg (fun x => by positivity)
  have hHp : 0≤Hp := integral_nonneg (fun y => by positivity)
  let r := Real.exp (-(1-δ)*Real.log (p:ℝ))
  let Z := Real.exp (δ*(V-W))/δ
  have pos : Summable (fun j : ℕ => ‖D (j:ℤ)‖) ∧
      (∑' j : ℕ, ‖D (j:ℤ)‖) ≤ Ar*Hp/(1-r)*Z := by
    apply MasulloRational.one_ray_log_defect volume μ vr vp hvr hvp (fun j => F (j:ℤ))
      (fun j => G (j:ℤ)) (fun j => hFm _) (fun j => hGm _) (fun j => hFi _) (fun j => hGi _)
      (Real.log (p:ℝ)) δ Ar Hp hpL hδ hδ1 hAr hHp
      (fun j => (hFw _).1) (fun j => (hGw _).1) (fun j => (hGw _).2) _ U V W hUV
    intro j t
    simpa only [F,vr,Ar,MasulloMixed.realPhase,Int.cast_natCast] using MasulloMixed.real_fourier_log_cutoff_min_signed hp hMr f hf hfB hdif (j:ℤ) t η hη
  let D' (k : ℤ) := ∫ x : ℚ_[p] × ℝ,
      (max (U+V-(vp x.1+vr x.2)) 0 - max (U-max (-W) ((vp x.1+vr x.2)-V)) 0) •
        (G k x.1 * F k x.2) ∂(μ.prod volume)
  have swap (k : ℤ) : D' k = D k := by
    unfold D' D
    rw [← integral_prod_swap]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [Prod.swap, v,vr,vp]
    rw [add_comm (Real.log ‖_‖) (Real.log ‖_‖),mul_comm]
  have neg : Summable (fun j : ℕ => ‖D (-(j:ℤ))‖) ∧
      (∑' j : ℕ, ‖D (-(j:ℤ))‖) ≤ Ap*Hr/(1-r)*Z := by
    have hb (j : ℕ) (t : ℝ) : ‖∫ y in {y | vp y < t}, G (-(j:ℤ)) y ∂μ‖ ≤
        Ap*min (Real.exp t) (Real.exp (-(j:ℝ)*Real.log (p:ℝ))) := by
      simpa only [vp,G,zpow_neg,zpow_natCast,inv_pow] using
        MasulloRational.padic_log_ball_negative_frequency p μ ψ hψ hunit g Vp Mp Rp Lp hV hM hR hL
          hμ hgB hgS hgP ηp hηp j t
    have ht := MasulloRational.one_ray_log_defect μ volume vp vr hvp hvr (fun j : ℕ => G (-(j:ℤ)))
      (fun j : ℕ => F (-(j:ℤ))) (fun j => hGm _) (fun j => hFm _) (fun j => hGi _) (fun j => hFi _)
      (Real.log (p:ℝ)) δ Ap Hr hpL hδ hδ1 hAp hHr
      (fun j => (hGw _).1) (fun j => (hFw _).1) (fun j => (hFw _).2) hb U V W hUV
    change Summable (fun j : ℕ => ‖D' (-(j:ℤ))‖) ∧
      (∑' j : ℕ, ‖D' (-(j:ℤ))‖) ≤ Ap*Hr/(1-r)*Z at ht
    simpa only [swap] using ht
  have hns : Summable (fun j : ℕ => ‖D (-(↑j+1))‖) := by
    exact (summable_nat_add_iff 1).mpr neg.1
  have htotal := Summable.of_nat_of_neg_add_one (f:=fun k : ℤ => ‖D k‖) pos.1 hns
  refine ⟨htotal,?_⟩
  rw [← tsum_nat_add_neg_add_one htotal,pos.1.tsum_add hns]
  have hn' : (∑' j : ℕ, ‖D (-(↑j+1))‖) ≤ Ap*Hr/(1-r)*Z := by
    have h := neg.1.tsum_eq_zero_add
    simp only [Nat.cast_zero,neg_zero,Nat.cast_add,Nat.cast_one] at h
    have hn0 := norm_nonneg (D 0)
    linarith [neg.2]
  calc _ ≤ Ar*Hp/(1-r)*Z+Ap*Hr/(1-r)*Z := add_le_add pos.2 hn'
       _ = _ := by dsimp only [r,Z]; ring
end

section
open MeasureTheory Set
open scoped Padic ENNReal

theorem MasulloRational.padic_compact_integrable (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p])
    (g : ℚ_[p] → ℂ) (hg : Measurable g) (R M V : ℝ) (_hR : 0<R)
    (hvol : μ (Metric.ball 0 R) ≤ ENNReal.ofReal (V*R))
    (hb : ∀ y, ‖g y‖≤M) (hc : ∀ y, R≤‖y‖ → g y=0) : Integrable g μ := by
  have hfin := hvol.trans_lt ENNReal.ofReal_lt_top
  have hi : IntegrableOn g (Metric.ball 0 R) μ :=
    (integrableOn_const (C:=M) hfin.ne).mono' hg.aestronglyMeasurable (ae_of_all _ hb)
  have he : (Metric.ball (0:ℚ_[p]) R).indicator g = g := by
    funext y
    by_cases hy : y ∈ Metric.ball (0:ℚ_[p]) R
    · simp [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy,hc y (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hy)]
  rw [← he]
  exact hi.integrable_indicator measurableSet_ball
end

section
open MeasureTheory Set Filter

namespace MasulloMixed

/-- Bounded integrable data on the real line have every subcritical negative absolute moment. -/
theorem real_negative_log_moment_integrable {f : ℝ → ℂ} {δ M : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hf : Integrable f) (hM : ∀ x : ℝ, ‖f x‖ ≤ M) :
    Integrable (fun x : ℝ => Real.exp (-δ * Real.log ‖x‖) * ‖f x‖) := by
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  let w := (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-δ))
  have hw : Integrable w := (integrable_indicator_iff measurableSet_Ioo).mpr
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith))
  have hw₀ (x : ℝ) : 0 ≤ w x := by
    by_cases h : x ∈ Ioo (0:ℝ) 1
    · simp only [w,indicator_of_mem h]; exact Real.rpow_nonneg h.1.le _
    · simp [w,h]
  have hmaj : Integrable (fun x : ℝ => ‖f x‖ + M * (w x + w (-x))) :=
    hf.norm.add ((hw.add hw.comp_neg).const_mul M)
  apply hmaj.mono'
  · have hexp : Measurable (fun x : ℝ => Real.exp (-δ * Real.log ‖x‖)) := by fun_prop
    exact hexp.aestronglyMeasurable.mul hf.norm.aestronglyMeasurable
  · filter_upwards [volume.ae_ne (0:ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    by_cases hfar : 1 ≤ ‖x‖
    · have he : Real.exp (-δ * Real.log ‖x‖) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (Real.log_nonneg hfar))
      exact (mul_le_of_le_one_left (norm_nonneg _) he).trans
        (le_add_of_nonneg_right (mul_nonneg hM₀ (add_nonneg (hw₀ _) (hw₀ _))))
    · have hn : ‖x‖ < 1 := lt_of_not_ge hfar
      have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hsum : w x + w (-x) = ‖x‖^(-δ) := by
        rcases lt_or_gt_of_ne hx with h|h
        · have hpos : -x ∈ Ioo (0:ℝ) 1 := ⟨neg_pos.mpr h, by simpa [Real.norm_eq_abs,abs_of_neg h] using hn⟩
          have hneg : x ∉ Ioo (0:ℝ) 1 := fun hh => h.not_gt hh.1
          simp [w, hpos, hneg, Real.norm_eq_abs, abs_of_neg h]
        · have hpos : x ∈ Ioo (0:ℝ) 1 := ⟨h, by simpa [Real.norm_eq_abs,abs_of_pos h] using hn⟩
          have hneg : -x ∉ Ioo (0:ℝ) 1 := fun hh => by linarith [hh.1]
          simp [w, hpos, hneg, Real.norm_eq_abs, abs_of_pos h]
      rw [hsum,Real.rpow_def_of_pos hp,mul_comm (Real.log ‖x‖) (-δ)]
      calc Real.exp _ * ‖f x‖ ≤ Real.exp _ * M := mul_le_mul_of_nonneg_left (hM x) (Real.exp_pos _).le
           _ ≤ _ := by rw [mul_comm _ M]; exact le_add_of_nonneg_left (norm_nonneg _)

open scoped SchwartzMap

theorem schwartz_negative_log_moment_integrable (f : 𝓢(ℝ,ℂ)) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    Integrable (fun x : ℝ => Real.exp (-δ * Real.log ‖x‖) * ‖f x‖) :=
  real_negative_log_moment_integrable hδ hδ₁ f.integrable (f.norm_le_seminorm ℝ)

end MasulloMixed
end

section
open MeasureTheory Set
open scoped Padic ENNReal

theorem MasulloRational.padic_lower_log_moment {p : ℕ} [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p])
    (g : ℚ_[p] → ℂ) (hg : Measurable g) (V M S δ : ℝ) (_hV : 0 ≤ V) (hM : 0 ≤ M)
    (hS : 0 < S) (hδ : 0 < δ) (hδ' : δ < 1)
    (hμ : ∀ r : ℝ, 0 < r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (V*r))
    (hbound : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, S ≤ ‖y‖ → g y = 0) :
    Integrable (fun y : ℚ_[p] => Real.exp (-δ*Real.log ‖y‖) * ‖g y‖) μ := by
  let z := Real.exp (-1)
  let A := M*max 1 (Real.exp (-δ*Real.log S+δ))
  let R (n : ℕ) := 2*S*z^n
  let H (n : ℕ) := A*(Real.exp δ)^n
  let U (n : ℕ) := Metric.ball (0:ℚ_[p]) (R n)
  let F (n : ℕ) := (U n).indicator (fun _ => ENNReal.ofReal (H n))
  have hz : 0 < z := Real.exp_pos _
  have hz' : z < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hA : 0 ≤ A := mul_nonneg hM (zero_le_one.trans (le_max_left _ _))
  have hMA : M ≤ A := le_mul_of_one_le_right hM (le_max_left _ _)
  have hR (n : ℕ) : 0 < R n := by dsimp only [R]; positivity
  have hH (n : ℕ) : 0 ≤ H n := by dsimp only [H]; positivity
  have hfull (y : ℚ_[p]) : ‖Real.exp (-δ*Real.log ‖y‖) * ‖g y‖‖ₑ ≤ ∑' n, F n y := by
    rw [Real.enorm_eq_ofReal (by positivity)]
    by_cases hy : S ≤ ‖y‖
    · simp [hsupp y hy]
    by_cases hzero : y = 0
    · subst y
      refine le_trans ?_ (ENNReal.le_tsum 0)
      have hmem : (0:ℚ_[p]) ∈ U 0 := Metric.mem_ball_self (hR 0)
      simp only [F,Set.indicator_of_mem hmem,H,pow_zero,mul_one,norm_zero,Real.log_zero,mul_zero,
        Real.exp_zero,one_mul]
      exact ENNReal.ofReal_le_ofReal ((hbound _).trans hMA)
    have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hzero
    have hypS : ‖y‖/S ≤ 1 := (div_le_one hS).mpr (le_of_not_ge hy)
    obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one (div_pos hyp hS) hypS hz hz'
    have hmem : y ∈ U n := by
      simp only [U,Metric.mem_ball,dist_zero_right]
      have hv := (div_le_iff₀ hS).mp hhi
      change ‖y‖ < 2*S*z^n
      nlinarith only [hv,mul_pos (pow_pos hz n) hS]
    have hlog : Real.log S - ((n:ℝ)+1) < Real.log ‖y‖ := by
      have hh := Real.log_lt_log (mul_pos (pow_pos hz _) hS) ((lt_div_iff₀ hS).mp hlo)
      rw [Real.log_mul (pow_pos hz _).ne' hS.ne',Real.log_pow] at hh
      dsimp only [z] at hh
      rw [Real.log_exp] at hh
      push_cast at hh
      linarith
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [show F n y = ENNReal.ofReal (H n) from Set.indicator_of_mem hmem _]
    apply ENNReal.ofReal_le_ofReal
    have hx : -δ*Real.log ‖y‖ ≤ (-δ*Real.log S+δ)+(n:ℝ)*δ := by nlinarith [mul_pos hδ (sub_pos.mpr hlog)]
    calc
      _ ≤ Real.exp ((-δ*Real.log S+δ)+(n:ℝ)*δ)*M :=
        mul_le_mul (Real.exp_le_exp.mpr hx) (hbound _) (norm_nonneg _) (Real.exp_nonneg _)
      _ ≤ H n := by
        rw [Real.exp_add,Real.exp_nat_mul]
        dsimp only [H,A]
        calc
          _ = (M*Real.exp (-δ*Real.log S+δ))*(Real.exp δ)^n := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hM) (by positivity)
  have hgeom : Summable (fun n : ℕ => (A*(V*(2*S)))*(Real.exp (δ-1))^n) :=
    (summable_geometric_of_lt_one (Real.exp_nonneg _) (Real.exp_lt_one_iff.mpr (by linarith))).mul_left _
  have hmass (n : ℕ) : ∫⁻ y, F n y ∂μ ≤ ENNReal.ofReal ((A*(V*(2*S)))*(Real.exp (δ-1))^n) := by
    rw [show (∫⁻ y, F n y ∂μ) = ENNReal.ofReal (H n)*μ (U n) from lintegral_indicator_const measurableSet_ball _]
    apply (mul_le_mul_right (hμ (R n) (hR n)) _).trans_eq
    rw [← ENNReal.ofReal_mul (hH n)]
    congr 1
    dsimp only [H,R,z]
    rw [sub_eq_add_neg,Real.exp_add,mul_pow]
    ring
  refine ⟨((Real.measurable_exp.comp (measurable_const.mul (Real.measurable_log.comp measurable_norm))).mul hg.norm).aestronglyMeasurable,?_⟩
  calc
    _ ≤ ∫⁻ y, ∑' n, F n y ∂μ := lintegral_mono hfull
    _ = ∑' n, ∫⁻ y, F n y ∂μ := lintegral_tsum (fun n => (measurable_const.indicator measurableSet_ball).aemeasurable)
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((A*(V*(2*S)))*(Real.exp (δ-1))^n) := ENNReal.tsum_le_tsum hmass
    _ < ⊤ := hgeom.tsum_ofReal_lt_top
end

section
open MeasureTheory Set Filter
open scoped Padic ENNReal

theorem solution (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψm : Measurable ψ) (hψ : ψ ((p:ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1)
    (f : ℝ → ℂ) (g : ℚ_[p] → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdif : Integrable (deriv f)) (hgm : Measurable g)
    (Mr Vp Mp Rp Lp : ℝ) (hMr : 0≤Mr) (hV : 0≤Vp) (hM : 0≤Mp) (hR : 0<Rp) (hL : 0<Lp)
    (hμ : ∀ r : ℝ, 0<r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (Vp*r))
    (hfB : ∀ x, ‖f x‖≤Mr) (hgB : ∀ y, ‖g y‖≤Mp) (hgS : ∀ y, Rp≤‖y‖ → g y=0)
    (hgP : ∀ y d : ℚ_[p], ‖d‖≤Lp → g (d+y)=g y)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (η : ℝ) (ηp : ℚ_[p]) (hη : |η|=1) (hηp : ‖ηp‖=1)
    (U V W : ℝ) (hUV : -W≤U) :
    let v (x : ℝ × ℚ_[p]) := Real.log ‖x.1‖ + Real.log ‖x.2‖
    let F (k : ℤ) (x : ℝ) := f x * Complex.exp
      (((2*Real.pi*(η*(p:ℝ)^k):ℝ):ℂ)*Complex.I*(x:ℂ))
    let G (k : ℤ) (y : ℚ_[p]) := g y * ψ ((ηp*(p:ℚ_[p])^k)*y)
    let D (k : ℤ) := ∫ x : ℝ × ℚ_[p],
      (max (U+V-v x) 0 - max (U-max (-W) (v x-V)) 0) • (F k x.1 * G k x.2)
      ∂(volume.prod μ)
    let Ar := max (2*Mr) ((2*Mr+∫ x, ‖deriv f x‖)/(2*Real.pi))
    let Ap := Mp*Vp*max 1 (max (p:ℝ) (Rp*max 1 ((p:ℝ)/Lp)))
    let Hr := ∫ x : ℝ, Real.exp (-δ*Real.log ‖x‖)*‖f x‖
    let Hp := ∫ y : ℚ_[p], Real.exp (-δ*Real.log ‖y‖)*‖g y‖ ∂μ
    Summable (fun k : ℤ => ‖D k‖) ∧
    (∑' k : ℤ, ‖D k‖) ≤ (Ar*Hp+Ap*Hr)/(1-Real.exp (-(1-δ)*Real.log (p:ℝ))) *
       (Real.exp (δ*(V-W))/δ) := by
  have hgi := MasulloRational.padic_compact_integrable p μ g hgm Rp Mp Vp hR (hμ Rp hR) hgB hgS
  have hmr := MasulloMixed.real_negative_log_moment_integrable hδ hδ1 hi hfB
  have hmp : Integrable (fun y : ℚ_[p] => Real.exp (-δ*Real.log ‖y‖)*‖g y‖) μ :=
    MasulloRational.padic_lower_log_moment μ g hgm Vp Mp Rp δ hV hM hR hδ hδ1 hμ hgB hgS
  exact MasulloRational.two_place_log_defect_of_moments p μ ψ hψm hψ hunit f g hf hi hdif hgm hgi
    Mr Vp Mp Rp Lp hMr hV hM hR hL hμ hfB hgB hgS hgP δ hδ hδ1 hmr hmp η ηp hη hηp U V W hUV
end
