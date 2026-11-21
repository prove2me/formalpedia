-- Prove2me | solution 1 for MasulloRH.rational_upper_annular_trace_vanishes_uniformly
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:05:51.802938+00:00
-- url     : https://prove2.me/submissions/7d362186-f114-49d1-b68b-ebbee5f9a187

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Group.AddChar
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.MellinTransform


open MeasureTheory Set
open scoped Interval

namespace MasulloMixed

noncomputable def realPhase (t x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I * (x : ℂ))

private theorem norm_realPhase (t x : ℝ) : ‖realPhase t x‖ = 1 := by
  unfold realPhase
  rw [mul_right_comm, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

private theorem hasDerivAt_realPhase (t x : ℝ) :
    HasDerivAt (realPhase t) (realPhase t x * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)) x := by
  let k : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  have h : HasDerivAt (fun z : ℂ ↦ k * z) k (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul k
  exact ((Complex.hasDerivAt_exp _).comp (x : ℂ) h).comp_ofReal

open Filter Topology
open scoped SchwartzMap

/-- The two estimates on either half-line retain the single finite endpoint. -/
theorem real_fourier_halfline_min (f : 𝓢(ℝ, ℂ)) {a t : ℝ} (ht : t ≠ 0)
    (S : Set ℝ) (hS : S = Ioi a ∨ S = Iic a) :
    ‖∫ x in S, f x * realPhase t x‖ ≤ min (∫ x in S, ‖f x‖)
      ((‖f a‖ + ∫ x in S, ‖deriv f x‖) / (2 * Real.pi * |t|)) := by
  let k : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  have hk : ‖k‖ = 2 * Real.pi * |t| := by
    simp [k, abs_of_pos Real.pi_pos]
  have hc : Continuous (realPhase t) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_realPhase t x).continuousAt
  have hbound : ∀ᵐ x : ℝ, ‖realPhase t x‖ ≤ 1 :=
    Eventually.of_forall fun x ↦ (norm_realPhase t x).le
  have hg : Integrable (fun x ↦ f x * realPhase t x) :=
    (f.integrable (μ := volume)).mul_bdd hc.aestronglyMeasurable hbound
  have hd : Integrable (fun x ↦ deriv f x * realPhase t x) := by
    have h := ((SchwartzMap.derivCLM ℝ ℂ f).integrable (μ := volume)).mul_bdd hc.aestronglyMeasurable hbound
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hI : Integrable (fun x ↦ f x * (realPhase t x * k)) := by
    simpa only [mul_assoc] using hg.mul_const k
  have hdecay : Tendsto ((f : ℝ → ℂ) * realPhase t) (cocompact ℝ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Pi.mul_apply, norm_mul, norm_realPhase, mul_one]
      using (tendsto_zero_iff_norm_tendsto_zero.mp f.tendsto_cocompact)
  have hcont : Continuous ((f : ℝ → ℂ) * realPhase t) := f.continuous.mul hc
  have hIBP : ∃ c : ℂ, ‖c‖ = ‖f a‖ ∧
      (∫ x in S, f x * (realPhase t x * k)) =
        c - ∫ x in S, deriv f x * realPhase t x := by
    have hend : ‖f a * realPhase t a‖ = ‖f a‖ := by rw [norm_mul, norm_realPhase, mul_one]
    rcases hS with rfl | rfl
    · refine ⟨-(f a * realPhase t a), (norm_neg _).trans hend, ?_⟩
      have h := integral_Ioi_mul_deriv_eq_deriv_mul
        (a := a) (fun x _ ↦ f.differentiableAt.hasDerivAt) (fun x _ ↦ hasDerivAt_realPhase t x)
        hI.integrableOn hd.integrableOn hcont.continuousAt.continuousWithinAt
        (hdecay.mono_left atTop_le_cocompact)
      simpa only [Pi.mul_apply, zero_sub] using h
    · refine ⟨f a * realPhase t a, hend, ?_⟩
      have h := integral_Iic_mul_deriv_eq_deriv_mul
        (a := a) (fun x _ ↦ f.differentiableAt.hasDerivAt) (fun x _ ↦ hasDerivAt_realPhase t x)
        hI.integrableOn hd.integrableOn hcont.continuousAt.continuousWithinAt
        (hdecay.mono_left atBot_le_cocompact)
      simpa only [Pi.mul_apply, sub_zero] using h
  obtain ⟨c, hca, he⟩ := hIBP
  simp_rw [← mul_assoc] at he
  rw [MeasureTheory.integral_mul_const] at he
  refine le_min ?_ ?_
  · simpa only [norm_mul, norm_realPhase, mul_one] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict S) (fun x ↦ f x * realPhase t x))
  · apply (le_div_iff₀ (mul_pos Real.two_pi_pos (abs_pos.mpr ht))).mpr
    rw [← hk, ← norm_mul, he, ← hca]
    apply (norm_sub_le _ _).trans
    apply add_le_add_right
    simpa only [norm_mul, norm_realPhase, mul_one] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict S) (fun x ↦ deriv f x * realPhase t x))

end MasulloMixed



open MeasureTheory Set Filter
open scoped SchwartzMap

private theorem schwartz_weighted_tail_parts (f : 𝓢(ℝ,ℂ)) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x : ℝ, (1+|x|)^M * ‖f x‖ ≤ C) ∧
      ∀ b : ℝ, 0 ≤ b → ∀ S : Set ℝ, MeasurableSet S → (∀ x ∈ S, b ≤ |x|) →
        (1+b)^M * (∫ x in S, ‖f x‖) ≤ C := by
  let P := (2:ℝ)^(M-1)
  let A := fun x : ℝ => P*(‖f x‖ + ‖x‖^M * ‖f x‖)
  let U := P * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ M 0 f)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hA (x : ℝ) : 0 ≤ A x := by dsimp only [A]; positivity
  have hi : Integrable A := ((f.integrable.norm).add (f.integrable_pow_mul volume M)).const_mul P
  have hpol (x : ℝ) : (1+|x|)^M * ‖f x‖ ≤ A x := by
    have h := mul_le_mul_of_nonneg_right (add_pow_le (zero_le_one (α:=ℝ)) (norm_nonneg x) M) (norm_nonneg (f x))
    dsimp only [A,P]
    simp only [Real.norm_eq_abs, one_pow] at h ⊢
    linarith only [h]
  have hU : 0 ≤ U := mul_nonneg hP (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  refine ⟨max U (∫ x, A x), hU.trans (le_max_left _ _), ?_, ?_⟩
  · intro x
    apply (hpol x).trans
    apply le_trans _ (le_max_left _ _)
    exact mul_le_mul_of_nonneg_left (add_le_add (f.norm_le_seminorm ℝ x)
      (f.norm_pow_mul_le_seminorm ℝ M x)) hP
  · intro b hb S hS hsub
    rw [← integral_const_mul]
    apply le_trans _ (le_max_right _ _)
    calc
      _ ≤ ∫ x in S, A x := by
        apply setIntegral_mono_on ((f.integrable.norm.const_mul _).integrableOn) hi.integrableOn hS
        intro x hx
        apply le_trans _ (hpol x)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by linarith) (by linarith [hsub x hx]) M) (norm_nonneg _)
      _ ≤ ∫ x, A x := setIntegral_le_integral hi (Filter.Eventually.of_forall hA)

theorem MasulloRH.schwartz_first_derivative_and_endpoint_tails
    (f : 𝓢(ℝ,ℂ)) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 ≤ b → ∀ S : Set ℝ, MeasurableSet S →
      (∀ x ∈ S, b ≤ |x|) →
        ‖f b‖ + ‖f (-b)‖ + (∫ x in S, ‖f x‖) + (∫ x in S, ‖deriv f x‖)
          ≤ C/(1+b)^M := by
  obtain ⟨P,hP,hPt,hPi⟩ := schwartz_weighted_tail_parts f M
  obtain ⟨Q,hQ,_,hQi⟩ := schwartz_weighted_tail_parts (SchwartzMap.derivCLM ℝ ℂ f) M
  refine ⟨1+3*P+Q,by linarith,?_⟩
  intro b hb S hS hsub
  have h1 := hPt b
  have h2 := hPt (-b)
  rw [abs_of_nonneg hb] at h1
  rw [abs_neg,abs_of_nonneg hb] at h2
  have h3 := hPi b hb S hS hsub
  have h4 := hQi b hb S hS hsub
  simp only [SchwartzMap.derivCLM_apply] at h4
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+b) M)).mpr
  linarith only [h1,h2,h3,h4]


namespace MasulloMixed

open Filter Topology
open scoped SchwartzMap

/-- Uniform simultaneous decay in the cutoff and the Fourier frequency, including zero. -/
theorem real_fourier_schwartz_two_tails (f : 𝓢(ℝ,ℂ)) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ), 0 ≤ b → ∀ t : ℝ,
      ‖∫ x in Ioi b, f x * realPhase t x‖ + ‖∫ x in Iic (-b), f x * realPhase t x‖
        ≤ C / ((1+b)^M * (1+|t|)) := by
  obtain ⟨A, hA, hmass⟩ := MasulloRH.schwartz_first_derivative_and_endpoint_tails f M
  refine ⟨4*A, by positivity, ?_⟩
  intro b hb t
  have hp : 0 < (1+b)^M := by positivity
  have hside (a : ℝ) (ha : a = b ∨ a = -b) (S : Set ℝ) (hm : MeasurableSet S)
      (hS : S = Ioi a ∨ S = Iic a) (hs : ∀ x ∈ S, b ≤ |x|) :
      ‖∫ x in S, f x * realPhase t x‖ * (1+|t|) ≤ 2 * (A/(1+b)^M) := by
    have ho := hmass b hb S hm hs
    have hf0 : 0 ≤ ∫ x in S, ‖f x‖ := integral_nonneg fun _ ↦ norm_nonneg _
    have hd0 : 0 ≤ ∫ x in S, ‖deriv f x‖ := integral_nonneg fun _ ↦ norm_nonneg _
    have hraw : ‖∫ x in S, f x * realPhase t x‖ ≤ ∫ x in S, ‖f x‖ := by
      simpa only [norm_mul, norm_realPhase, mul_one] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict S) (fun x ↦ f x * realPhase t x))
    have h1 : ‖∫ x in S, f x * realPhase t x‖ ≤ A/(1+b)^M :=
      hraw.trans (by linarith only [ho, hd0, norm_nonneg (f b), norm_nonneg (f (-b))])
    have h2 : ‖∫ x in S, f x * realPhase t x‖ * |t| ≤ A/(1+b)^M := by
      by_cases ht : t = 0
      · simp [ht, div_nonneg hA.le hp.le]
      have hq := (le_div_iff₀ (mul_pos Real.two_pi_pos (abs_pos.mpr ht))).mp
        ((real_fourier_halfline_min f ht S hS).trans (min_le_right _ _))
      have htπ : |t| ≤ 2*Real.pi*|t| := by
        calc
          _ = 1*|t| := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.two_le_pi]) (abs_nonneg t)
      apply (mul_le_mul_of_nonneg_left htπ (norm_nonneg _)).trans (hq.trans ?_)
      rcases ha with ha | ha <;> rw [ha] <;> linarith only [ho, hf0, norm_nonneg (f b), norm_nonneg (f (-b))]
    rw [mul_add, mul_one]
    linarith only [h1,h2]
  have hx := hside b (Or.inl rfl) (Ioi b) measurableSet_Ioi (Or.inl rfl)
    (fun x hx ↦ (le_of_lt hx).trans (le_abs_self x))
  have hy := hside (-b) (Or.inr rfl) (Iic (-b)) measurableSet_Iic (Or.inr rfl)
    (fun x hx ↦ (show b ≤ -x by linarith [show x ≤ -b from hx]).trans (neg_le_abs x))
  rw [← div_div]
  apply (le_div_iff₀ (by positivity : 0 < 1+|t|)).mpr
  rw [add_mul, mul_div_assoc]
  linarith only [hx,hy]

end MasulloMixed


open MeasureTheory Filter Set
open scoped SchwartzMap

namespace MasulloMixed

theorem real_log_exterior_positive_frequency (f : 𝓢(ℝ,ℂ)) {p : ℝ} (hp : 0 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, |η| = 1 → ∀ (j : ℕ) (r : ℝ),
      ‖∫ x in {x : ℝ | r ≤ Real.log ‖x‖}, f x * realPhase (η*p^j) x‖ ≤
        (K*(p⁻¹)^j)*Real.exp (-r) := by
  obtain ⟨K,hK,h⟩ := real_fourier_schwartz_two_tails f 1
  refine ⟨K,hK.le,?_⟩
  intro η hη j r
  let B := Real.exp r
  let τ := η*p^j
  have hB : 0 < B := Real.exp_pos _
  have hτ : |τ| = p^j := by simp [τ,abs_mul,hη,abs_of_pos hp]
  have hc : Continuous (realPhase τ) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_realPhase τ x).continuousAt
  have hInt : Integrable (fun x ↦ f x * realPhase τ x) :=
    (f.integrable (μ := volume)).mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ (norm_realPhase τ x).le)
  have hset : {x : ℝ | r ≤ Real.log ‖x‖} =ᵐ[volume] (Ioi B ∪ Iic (-B) : Set ℝ) := by
    filter_upwards [volume.ae_ne (0:ℝ), volume.ae_ne B] with x hx hxb
    apply propext
    change (r ≤ Real.log ‖x‖) ↔ B < x ∨ x ≤ -B
    rw [← Real.exp_le_exp, Real.exp_log (norm_pos_iff.mpr hx), Real.norm_eq_abs,le_abs]
    change (B ≤ x ∨ B ≤ -x) ↔ _
    constructor
    · rintro (hr | hr)
      · exact Or.inl (lt_of_le_of_ne hr (Ne.symm hxb))
      · exact Or.inr (by linarith)
    · rintro (hr | hr)
      · exact Or.inl hr.le
      · exact Or.inr (by linarith)
  have hd : Disjoint (Ioi B) (Iic (-B)) := Set.disjoint_left.mpr fun x hx hy ↦ by
    change B < x at hx; change x ≤ -B at hy; linarith
  rw [setIntegral_congr_set hset,setIntegral_union hd measurableSet_Iic hInt.integrableOn hInt.integrableOn]
  apply (norm_add_le _ _).trans
  apply (h B hB.le τ).trans
  rw [pow_one,hτ, Real.exp_neg, inv_pow]
  change K/((1+B)*(1+p^j)) ≤ K*(p^j)⁻¹*B⁻¹
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_div, mul_comm (p^j) B]
  apply div_le_div_of_nonneg_left hK.le (mul_pos hB (pow_pos hp j))
  exact mul_le_mul (by linarith) (by linarith) (pow_pos hp j).le (by linarith)

end MasulloMixed

open Set MeasureTheory Filter
open scoped Topology

private theorem finite_band_layer {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (v : X → ℝ) (hv : Measurable v) (F : X → ℂ) (hF : Measurable F) (hI : Integrable F μ)
    (b T : ℝ) :
    (∫ x, (max (T-max (v x) b) 0) • F x ∂μ) =
      ∫ t in Ioc b T, ∫ x in {x | v x < t}, F x ∂μ := by
  let P := (volume : Measure ℝ).restrict (Ioc b T)
  let H (q : X × ℝ) := if v q.1 < q.2 then F q.1 else 0
  have hm : Measurable H := (hF.comp measurable_fst).ite (measurableSet_lt (hv.comp measurable_fst) measurable_snd) measurable_const
  have : IsFiniteMeasure P := ⟨by simp [P]⟩
  have hI' : Integrable H (μ.prod P) := by
    apply (hI.comp_fst P).norm.mono' hm.aestronglyMeasurable
    filter_upwards with q
    dsimp [H]
    split_ifs <;> simp
  calc
    _ = ∫ x, ∫ t, H (x,t) ∂P ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      have ht : ∀ t, t ∈ Ioc b T → H (x,t) = (Ioo (v x) (T+1)).indicator (fun _ => F x) t := by
        intro t ht
        simp only [H,Set.indicator_apply,Set.mem_Ioo,show t<T+1 by linarith [ht.2],and_true]
      rw [show (∫ t, H (x,t) ∂P) = ∫ t in Ioc b T, (Ioo (v x) (T+1)).indicator (fun _ => F x) t from setIntegral_congr_fun measurableSet_Ioc ht]
      rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo]
      have hset : Ioo (v x) (T+1) ∩ Ioc b T = Ioc (max (v x) b) T := by
        ext t; simp only [mem_inter_iff,mem_Ioo,mem_Ioc,max_lt_iff]; constructor
        · rintro ⟨⟨h1,_⟩,h2,h3⟩; exact ⟨⟨h1,h2⟩,h3⟩
        · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨⟨h1,by linarith⟩,h2,h3⟩
      rw [hset, setIntegral_const,Real.volume_real_Ioc]
    _ = ∫ t, ∫ x, H (x,t) ∂μ ∂P := integral_integral_swap hI'
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      exact integral_indicator (s := {x | v x < t}) (measurableSet_lt hv measurable_const)

private theorem upper_log_estimate {X I : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (v : X → ℝ) (hv : Measurable v) (F : I → X → ℂ) (hF : ∀ i, Measurable (F i))
    (hi : ∀ i, Integrable (F i) μ) (b T δ : ℝ) (hb : b ≤ T) (hd : 0 < δ)
    (a : I → ℂ) (K : I → ℝ) (hK : Summable K) (hpos : ∀ i, 0 ≤ K i)
    (htail : ∀ i t, b ≤ t → ‖(∫ x in {x | v x < t}, F i x ∂μ) - a i‖ ≤ K i * Real.exp (-δ*t)) :
    let R i := (∫ x, max (T-max (v x) b) 0 • F i x ∂μ) - (T-b) • a i
    Summable (fun i => ‖R i‖) ∧ (∑' i, ‖R i‖) ≤ (∑' i, K i)* (Real.exp (-δ*b)/δ) := by
  intro R
  let E := Real.exp (-δ*b)/δ
  have hpt (i : I) : ‖R i‖ ≤ K i * E := by
    have ha : IntegrableOn (fun t => ∫ x in {x | v x < t}, F i x ∂μ) (Ioc b T) := by
      let P := (volume : Measure ℝ).restrict (Ioc b T)
      have : IsFiniteMeasure P := ⟨by simp [P]⟩
      have H : Integrable (fun q : X × ℝ => if v q.1 < q.2 then F i q.1 else 0) (μ.prod P) := by
        apply ((hi i).comp_fst P).norm.mono' (((hF i).comp measurable_fst).ite (measurableSet_lt (hv.comp measurable_fst) measurable_snd) measurable_const).aestronglyMeasurable
        filter_upwards with q
        split_ifs <;> simp
      exact H.integral_prod_right.congr (ae_of_all _ (fun t => integral_indicator (s := {x | v x < t}) (measurableSet_lt hv measurable_const)))
    have hc : (∫ _ in Ioc b T, a i) = (T-b) • a i := by rw [setIntegral_const,Real.volume_real_Ioc,max_eq_left (sub_nonneg.mpr hb)]
    have he : IntegrableOn (fun t => K i * Real.exp (-δ*t)) (Ioi b) :=
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) b).const_mul _
    change ‖(∫ x, _ ∂μ) - _‖ ≤ _
    rw [finite_band_layer μ v hv _ (hF i) (hi i),← hc,← integral_sub ha (integrableOn_const measure_Ioc_lt_top.ne)]
    calc
      _ ≤ ∫ t in Ioc b T, K i * Real.exp (-δ*t) := by
        apply norm_integral_le_of_norm_le (he.mono_set Ioc_subset_Ioi_self)
        filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with t ht using htail i t ht.1.le
      _ ≤ ∫ t in Ioi b, K i * Real.exp (-δ*t) := setIntegral_mono_set he (ae_of_all _ (fun _ => mul_nonneg (hpos i) (Real.exp_pos _).le)) (ae_of_all _ (fun _ h => h.1))
      _ = _ := by rw [integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr hd)]; simp [E]
  have hsum := (hK.mul_right E).of_nonneg_of_le (fun i => norm_nonneg (R i)) hpt
  exact ⟨hsum,(hsum.tsum_le_tsum hpt (hK.mul_right E)).trans_eq tsum_mul_right⟩

open MeasureTheory Set

theorem MasulloRH.mixed_exterior_oscillation_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] (v : X → ℝ) (w : Y → ℝ) (hv : Measurable v) (hw : Measurable w)
    (f : X → ℂ) (g : Y → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (δ A t : ℝ)
    (hb : ∀ r, ‖∫ x in {x | r ≤ v x}, f x ∂μ‖ ≤ A * Real.exp (-δ*r))
    (hW : Integrable (fun y => Real.exp (δ*w y)*‖g y‖) ν) :
    ‖∫ q in {q : X × Y | t ≤ v q.1 + w q.2}, f q.1 * g q.2 ∂(μ.prod ν)‖ ≤
    A * Real.exp (-δ*t) * ∫ y, Real.exp (δ*w y)*‖g y‖ ∂ν := by
  let S := {q : X × Y | t ≤ v q.1 + w q.2}
  have hm : MeasurableSet S := measurableSet_le measurable_const ((hv.comp measurable_fst).add (hw.comp measurable_snd))
  have H := (hf.mul_prod hg).indicator hm
  rw [← integral_indicator hm, integral_prod_symm _ H]
  have eq (y : Y) : (∫ x, S.indicator (fun q => f q.1 * g q.2) (x,y) ∂μ) =
      (∫ x in {x | t-w y ≤ v x}, f x ∂μ) * g y := by
    rw [← integral_mul_const, ← integral_indicator (measurableSet_le measurable_const hv)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Set.indicator_apply,S,Set.mem_ofPred_eq,sub_le_iff_le_add]
  simp_rw [eq]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hW.const_mul _)
  filter_upwards with y
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_right (hb (t-w y)) (norm_nonneg _)).trans_eq ?_
  rw [show -δ*(t-w y) = -δ*t+δ*w y by ring,Real.exp_add]
  ring
open Set MeasureTheory Filter
open scoped Topology

private theorem abstract_upper_ray
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] (v : X → ℝ) (w : Y → ℝ) (hv : Measurable v) (hw : Measurable w)
    (f : ℕ → X → ℂ) (g : ℕ → Y → ℂ) (hf : ∀ j, Measurable (f j)) (hg : ∀ j, Measurable (g j))
    (hi : ∀ j, Integrable (f j) μ) (hi' : ∀ j, Integrable (g j) ν)
    (r δ A C : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (hd : 0 < δ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hgW : ∀ j, Integrable (fun y => Real.exp (δ*w y)*‖g j y‖) ν)
    (hgC : ∀ j, (∫ y, Real.exp (δ*w y)*‖g j y‖ ∂ν) ≤ C)
    (hprim : ∀ j t, ‖∫ x in {x | t ≤ v x}, f j x ∂μ‖ ≤ (A*r^j)*Real.exp (-δ*t))
    (b T : ℝ) (hb : b ≤ T) :
    let mass j := (∫ x, f j x ∂μ)*(∫ y, g j y ∂ν)
    let D j := (∫ q : X×Y, max (T - max (v q.1+w q.2) b) 0 • (f j q.1 * g j q.2) ∂(μ.prod ν)) -
      (T-b) • mass j
    Summable (fun j => ‖D j‖) ∧ (∑' j, ‖D j‖) ≤ (A*C)/(1-r) * (Real.exp (-δ*b)/δ) := by
  intro mass D
  let K (j : ℕ) := r^j*(A*C)
  have hs := (hasSum_geometric_of_lt_one hr hr').mul_right (A*C)
  have hp (j : ℕ) (t : ℝ) (ht : b ≤ t) :
      ‖(∫ q in {q : X×Y | v q.1+w q.2<t}, f j q.1*g j q.2 ∂(μ.prod ν)) - mass j‖ ≤ K j*Real.exp (-δ*t) := by
    let s := {q : X×Y | v q.1+w q.2 < t}
    have hm : MeasurableSet s := measurableSet_lt ((hv.comp measurable_fst).add (hw.comp measurable_snd)) measurable_const
    have h := integral_add_compl hm ((hi j).mul_prod (hi' j))
    rw [integral_prod_mul] at h
    have hh : (∫ q in s, f j q.1 * g j q.2 ∂(μ.prod ν)) - mass j =
        -(∫ q in sᶜ, f j q.1 * g j q.2 ∂(μ.prod ν)) := by dsimp [mass]; rw [← h]; abel
    rw [hh, norm_neg]
    have hc : sᶜ = {q : X×Y | t ≤ v q.1+w q.2} := by ext q; simp [s]
    rw [hc]
    have H := MasulloRH.mixed_exterior_oscillation_bound μ ν v w hv hw (f j) (g j) (hi j) (hi' j) δ (A*r^j) t (hprim j) (hgW j)
    exact H.trans ((mul_le_mul_of_nonneg_left (hgC j) (by positivity : 0 ≤ A*r^j*Real.exp (-δ*t))).trans_eq (by dsimp [K]; ring))
  have H := upper_log_estimate (μ.prod ν) (fun q : X×Y => v q.1+w q.2) ((hv.comp measurable_fst).add (hw.comp measurable_snd))
    (fun j (q : X×Y) => f j q.1*g j q.2) (fun j => ((hf j).comp measurable_fst).mul ((hg j).comp measurable_snd))
    (fun j => (hi j).mul_prod (hi' j)) b T δ hb hd mass K hs.summable (fun j => by dsimp [K]; positivity) hp
  refine ⟨H.1,H.2.trans_eq ?_⟩
  rw [show (∑' j, K j) = _ from hs.tsum_eq]; simp only [div_eq_mul_inv]; ring

open MeasureTheory
open scoped Padic ENNReal

private theorem padic_ball_period_zero (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p] ]
    [BorelSpace ℚ_[p] ] (μ : Measure ℚ_[p]) [μ.IsAddLeftInvariant]
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

private theorem padic_ball_estimate (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
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

theorem MasulloRational.padic_ball_exterior (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
    (μ : Measure ℚ_[p]) [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψ : ψ ((p : ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1) (g : ℚ_[p] → ℂ) (V M S L : ℝ)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hS : 0 < S) (hL : 0 < L)
    (hμ : ∀ r : ℝ, 0 < r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (V*r))
    (hbound : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, S ≤ ‖y‖ → g y = 0)
    (hperiod : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y)
    (hint : ∀ ξ : ℚ_[p], Integrable (fun y => g y * ψ (ξ*y)) μ)
    (m : ℝ) (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (R : ℝ) (ξ : ℚ_[p]), 0 < R →
      ‖∫ y in (Metric.ball 0 R)ᶜ, g y * ψ (ξ*y) ∂μ‖ ≤ K * R^(-m) / (1 + ‖ξ‖) := by
  let B : ℝ := max 1 ((p : ℝ)/L)
  let C : ℝ := M*V*(max 1 (max (p : ℝ) (S*B)))
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hM hV) (zero_le_one.trans (le_max_left _ _))
  refine ⟨4*C*S^m,by positivity,?_⟩
  intro R ξ hR
  let H := fun y : ℚ_[p] => g y * ψ (ξ*y)
  have outer_zero (r : ℝ) (hr : S ≤ r) : (∫ y in (Metric.ball 0 r)ᶜ, H y ∂μ) = 0 := by
    have h := setIntegral_congr_fun (μ := μ) (f := H) (g := fun _ => 0)
      (s := (Metric.ball 0 r)ᶜ) measurableSet_ball.compl (by
        intro y hy
        simp only [Set.mem_compl_iff,Metric.mem_ball,dist_zero_right,not_lt] at hy
        simp [H, hsupp y (hr.trans hy)])
    simpa only [integral_zero] using h
  by_cases large : S ≤ R
  · change ‖∫ y in (Metric.ball 0 R)ᶜ, H y ∂μ‖ ≤ _
    rw [outer_zero R large, norm_zero]
    positivity
  have hRS := (lt_of_not_ge large).le
  have hb (r : ℝ) (hr : 0 < r) : ‖∫ y in Metric.ball 0 r, H y ∂μ‖ ≤ C * (1/max 1 ‖ξ‖) := by
    have h := padic_ball_estimate p μ ψ hψ hunit g V M S L hV hM hS hL hμ hbound hsupp hperiod r ξ hr
    exact h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
  have ht : (∫ y, H y ∂μ) = ∫ y in Metric.ball 0 S, H y ∂μ := by
    rw [← integral_add_compl (s := Metric.ball 0 S) measurableSet_ball (hint ξ), outer_zero S le_rfl, add_zero]
  change ‖∫ y in (Metric.ball 0 R)ᶜ, H y ∂μ‖ ≤ _
  rw [setIntegral_compl measurableSet_ball (hint ξ),ht]
  have hD : 0 < max 1 ‖ξ‖ := zero_lt_one.trans_le (le_max_left _ _)
  have hsum : 1+‖ξ‖ ≤ 2 * max 1 ‖ξ‖ := by
    linarith [le_max_right (1:ℝ) ‖ξ‖,le_max_left (1:ℝ) ‖ξ‖]
  have hmR : 1 ≤ S^m * R^(-m) := by
    rw [Real.rpow_neg hR.le,← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hR _),one_mul]
    exact Real.rpow_le_rpow hR.le hRS hm
  have hupper : (4*C) ≤ 4*C*S^m*R^(-m) := by
    rw [mul_assoc (4*C)]
    exact le_mul_of_one_le_right (by positivity) hmR
  calc
    _ ≤ ‖∫ y in Metric.ball 0 S, H y ∂μ‖ + ‖∫ y in Metric.ball 0 R, H y ∂μ‖ := norm_sub_le _ _
    _ ≤ C*(1/max 1 ‖ξ‖) + C*(1/max 1 ‖ξ‖) := add_le_add (hb S hS) (hb R hR)
    _ = (2*C) / (max 1 ‖ξ‖) := by ring
    _ ≤ (4*C) / (1+‖ξ‖) := by
      rw [div_le_div_iff₀ hD (by positivity)]
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hsum)]
    _ ≤ _ := div_le_div_of_nonneg_right hupper (by positivity)

private theorem padic_singleton_null_of_ball_bound (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p] ] (μ : Measure ℚ_[p]) (V : ℝ) (hV : 0 ≤ V)
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

theorem MasulloRational.padic_log_exterior_negative_frequency (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
    (μ : Measure ℚ_[p]) [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψ : ψ ((p : ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1) (g : ℚ_[p] → ℂ) (V M S L : ℝ)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hS : 0 < S) (hL : 0 < L)
    (hμ : ∀ r : ℝ, 0 < r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (V*r))
    (hbound : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, S ≤ ‖y‖ → g y = 0)
    (hperiod : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y)
    (hint : ∀ ξ : ℚ_[p], Integrable (fun y => g y * ψ (ξ*y)) μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (η : ℚ_[p]), ‖η‖ = 1 → ∀ (j : ℕ) (r : ℝ),
      ‖∫ y in {y : ℚ_[p] | r ≤ Real.log ‖y‖},
          g y * ψ ((η*((p:ℚ_[p])⁻¹)^j)*y) ∂μ‖ ≤
        (K*((p:ℝ)⁻¹)^j)*Real.exp (-r) := by
  obtain ⟨K,hK,h⟩ := padic_ball_exterior p μ ψ hψ hunit g V M S L hV hM hS hL hμ
    hbound hsupp hperiod hint 1 zero_le_one
  refine ⟨K,hK,?_⟩
  intro η hη j r
  have hx := padic_singleton_null_of_ball_bound p μ V hV hμ
  have ha : ∀ᵐ y ∂μ, y ≠ 0 := measure_eq_zero_iff_ae_notMem.mp hx
  have he : {y : ℚ_[p] | r ≤ Real.log ‖y‖} =ᵐ[μ] (Metric.ball 0 (Real.exp r))ᶜ := by
    filter_upwards [ha] with y hy
    apply propext
    change (r ≤ Real.log ‖y‖) ↔ y ∉ Metric.ball 0 (Real.exp r)
    simp only [Metric.mem_ball,dist_zero_right,not_lt]
    exact Real.le_log_iff_exp_le (norm_pos_iff.mpr hy)
  rw [setIntegral_congr_set he]
  apply (h (Real.exp r) (η*((p:ℚ_[p])⁻¹)^j) (Real.exp_pos r)).trans
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out (p:=p.Prime)).pos
  rw [norm_mul,hη,one_mul,norm_pow,norm_inv,Padic.norm_p,inv_inv,
    Real.rpow_neg_one,← Real.exp_neg,inv_pow]
  calc
    _ ≤ K * Real.exp (-r) / (p:ℝ)^j := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = _ := by ring

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

open Set MeasureTheory Filter
open scoped SchwartzMap Padic ENNReal Topology

private theorem actual_upper_rays (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
    (μ : Measure ℚ_[p]) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψm : Measurable ψ) (hψ : ψ ((p:ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1)
    (f : 𝓢(ℝ,ℂ)) (g : ℚ_[p] → ℂ) (hgm : Measurable g) (hgi : Integrable g μ)
    (V M S L : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M) (hS : 0 < S) (hL : 0 < L)
    (hμ : ∀ u : ℝ, 0 < u → μ (Metric.ball 0 u) ≤ ENNReal.ofReal (V*u))
    (hgB : ∀ y, ‖g y‖ ≤ M) (hgS : ∀ y, S ≤ ‖y‖ → g y = 0)
    (hgP : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y) :
    let v (z : ℝ × ℚ_[p]) := Real.log ‖z.1‖ + Real.log ‖z.2‖
    let F (η : ℝ) (k : ℤ) (x : ℝ) := f x * MasulloMixed.realPhase (η*(p:ℝ)^k) x
    let G (ηp : ℚ_[p]) (k : ℤ) (y : ℚ_[p]) := g y * ψ ((ηp*(p:ℚ_[p])^k)*y)
    let E (η : ℝ) (ηp : ℚ_[p]) (b T : ℝ) (k : ℤ) :=
      (∫ z : ℝ × ℚ_[p], max (T - max (v z) b) 0 • (F η k z.1 * G ηp k z.2) ∂(volume.prod μ))
        - (T-b) • ((∫ x, F η k x) * (∫ y, G ηp k y ∂μ))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : ℝ) (ηp : ℚ_[p]), |η|=1 → ‖ηp‖=1 → ∀ (b T : ℝ), b ≤ T →
      (Summable (fun j : ℕ ↦ ‖E η ηp b T (j:ℤ)‖) ∧
        (∑' j : ℕ, ‖E η ηp b T (j:ℤ)‖) ≤ C * Real.exp (-b)) ∧
      (Summable (fun j : ℕ ↦ ‖E η ηp b T (-(j:ℤ))‖) ∧
        (∑' j : ℕ, ‖E η ηp b T (-(j:ℤ))‖) ≤ C * Real.exp (-b)) := by
  intro v F G E
  let vr (x : ℝ) := Real.log ‖x‖
  let vp (y : ℚ_[p]) := Real.log ‖y‖
  have hvr : Measurable vr := Real.measurable_log.comp measurable_id.norm
  have hvp : Measurable vp := Real.measurable_log.comp measurable_id.norm
  let Wr := fun x : ℝ => Real.exp (vr x)*‖f x‖
  let Wp := fun y : ℚ_[p] => Real.exp (vp y)*‖g y‖
  have hiWr : Integrable Wr := by
    apply (f.integrable_pow_mul volume 1).congr
    filter_upwards [volume.ae_ne (0:ℝ)] with x hx
    change ‖x‖^1 * ‖f x‖ = Real.exp (Real.log ‖x‖) * ‖f x‖
    rw [pow_one,Real.exp_log (norm_pos_iff.mpr hx)]
  have hiWp : Integrable Wp μ := by
    apply (hgi.norm.const_mul (max 1 S)).mono' ((hvp.exp.mul hgm.norm).aestronglyMeasurable)
    filter_upwards with y
    change ‖Real.exp (Real.log ‖y‖) * ‖g y‖‖ ≤ max 1 S * ‖g y‖
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    by_cases hy : y = 0
    · subst y; simpa using mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) S) (norm_nonneg (g 0))
    · rw [Real.exp_log (norm_pos_iff.mpr hy)]
      by_cases hys : ‖y‖ ≤ S
      · exact mul_le_mul_of_nonneg_right (hys.trans (le_max_right _ _)) (norm_nonneg _)
      · simp [hgS y (le_of_lt (lt_of_not_ge hys))]
  have hnonWr : 0 ≤ ∫ x, Wr x := integral_nonneg fun x ↦ by dsimp [Wr]; positivity
  have hnonWp : 0 ≤ ∫ y, Wp y ∂μ := integral_nonneg fun y ↦ by dsimp [Wp]; positivity
  have hchar (ξ : ℚ_[p]) : Measurable (fun y ↦ ψ (ξ*y)) := hψm.comp (continuous_const.mul continuous_id).measurable
  have hcharInt (ξ : ℚ_[p]) : Integrable (fun y ↦ g y*ψ (ξ*y)) μ :=
    hgi.mul_bdd (hchar ξ).aestronglyMeasurable (ae_of_all _ fun y ↦ hunit _)
  have hp : 1 < (p:ℝ) := by exact_mod_cast (Fact.out (p := p.Prime)).one_lt
  have hp0 : 0 < (p:ℝ) := zero_lt_one.trans hp
  obtain ⟨A,hA,hAr⟩ := MasulloMixed.real_log_exterior_positive_frequency f hp0
  obtain ⟨B,hB,hBr⟩ := MasulloRational.padic_log_exterior_negative_frequency
    p μ ψ hψ hunit g V M S L hV hM hS hL hμ hgB hgS hgP hcharInt
  let q := (p:ℝ)⁻¹
  have hq : 0 ≤ q := inv_nonneg.mpr hp0.le
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hp
  let C₁ := A*(∫ y, Wp y ∂μ)/(1-q)
  let C₂ := B*(∫ x, Wr x)/(1-q)
  have hden : 0 < 1-q := sub_pos.mpr hq1
  refine ⟨max C₁ C₂,(div_nonneg (mul_nonneg hA hnonWp) hden.le).trans (le_max_left _ _),?_⟩
  intro η ηp hη hηp b T hb
  let e (k : ℤ) := MasulloMixed.realPhase (η*(p:ℝ)^k)
  let ep (k : ℤ) (y : ℚ_[p]) := ψ ((ηp*(p:ℚ_[p])^k)*y)
  have he (k : ℤ) : Measurable (e k) := (continuous_iff_continuousAt.mpr (fun x =>
    (MasulloMixed.hasDerivAt_realPhase (η*(p:ℝ)^k) x).continuousAt)).measurable
  have hen (k : ℤ) (x : ℝ) : ‖e k x‖ ≤ 1 := (MasulloMixed.norm_realPhase _ _).le
  have hFm (k : ℤ) : Measurable (F η k) := f.continuous.measurable.mul (he k)
  have hGm (k : ℤ) : Measurable (G ηp k) := hgm.mul (hchar _)
  have hFi (k : ℤ) : Integrable (F η k) := f.integrable.mul_bdd (he k).aestronglyMeasurable (ae_of_all _ (hen k))
  have hGi (k : ℤ) : Integrable (G ηp k) μ := hcharInt _
  have hFw (k : ℤ) : Integrable (fun x => Real.exp (1*vr x)*‖F η k x‖) ∧
      (∫ x, Real.exp (1*vr x)*‖F η k x‖) ≤ ∫ x, Wr x := by
    simpa [Wr,e,F] using oscillatory_weight_control volume vr hvr f (e k) f.continuous.measurable
      (he k) (hen k) (-1) (by simpa [Wr] using hiWr)
  have hGw (k : ℤ) : Integrable (fun y => Real.exp (1*vp y)*‖G ηp k y‖) μ ∧
      (∫ y, Real.exp (1*vp y)*‖G ηp k y‖ ∂μ) ≤ ∫ y, Wp y ∂μ := by
    simpa [Wp,ep,G] using oscillatory_weight_control μ vp hvp g (ep k) hgm
      (hchar _) (fun y ↦ hunit _) (-1) (by simpa [Wp] using hiWp)
  constructor
  · have h := abstract_upper_ray volume μ vr vp hvr hvp (fun j : ℕ ↦ F η (j:ℤ)) (fun j : ℕ ↦ G ηp (j:ℤ))
      (fun _ ↦ hFm _) (fun _ ↦ hGm _) (fun _ ↦ hFi _) (fun _ ↦ hGi _)
      q 1 A (∫ y, Wp y ∂μ) hq hq1 zero_lt_one hA hnonWp
      (fun _ ↦ (hGw _).1) (fun _ ↦ (hGw _).2) (fun j t ↦ by
        simpa only [F,vr,zpow_natCast,neg_one_mul] using hAr η hη j t) b T hb
    change Summable (fun j : ℕ ↦ ‖E η ηp b T (j:ℤ)‖) ∧
      (∑' j : ℕ, ‖E η ηp b T (j:ℤ)‖) ≤ C₁*(Real.exp (-1*b)/1) at h
    refine ⟨h.1,?_⟩
    exact (by simpa only [neg_one_mul,div_one] using h.2 : _ ≤ C₁*Real.exp (-b)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h := abstract_upper_ray μ volume vp vr hvp hvr (fun j : ℕ ↦ G ηp (-(j:ℤ))) (fun j : ℕ ↦ F η (-(j:ℤ)))
      (fun _ ↦ hGm _) (fun _ ↦ hFm _) (fun _ ↦ hGi _) (fun _ ↦ hFi _)
      q 1 B (∫ x, Wr x) hq hq1 zero_lt_one hB hnonWr
      (fun _ ↦ (hFw _).1) (fun _ ↦ (hFw _).2) (fun j t ↦ by
        simpa only [G,vp,q,zpow_neg,zpow_natCast,inv_pow,neg_one_mul] using hBr ηp hηp j t) b T hb
    let D' (k : ℤ) := (∫ z : ℚ_[p] × ℝ, max (T - max (vp z.1+vr z.2) b) 0 •
      (G ηp k z.1 * F η k z.2) ∂(μ.prod volume)) - (T-b) • ((∫ y, G ηp k y ∂μ)*(∫ x, F η k x))
    have hswap (k : ℤ) : D' k = E η ηp b T k := by
      unfold D' E
      rw [← integral_prod_swap (μ := volume) (ν := μ)]
      congr 1
      · apply integral_congr_ae
        filter_upwards with z
        dsimp only [v,vr,vp,Prod.swap]
        rw [add_comm (Real.log ‖_‖) (Real.log ‖_‖),mul_comm]
      · rw [mul_comm]
    change Summable (fun j : ℕ ↦ ‖D' (-(j:ℤ))‖) ∧
      (∑' j : ℕ, ‖D' (-(j:ℤ))‖) ≤ C₂*(Real.exp (-1*b)/1) at h
    simp only [hswap,neg_one_mul,div_one] at h
    exact ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)⟩

open Filter

theorem MasulloRH.bool_int_bilateral_ray_bound (E : Bool × ℤ → ℂ) (A : ℝ)
    (h : ∀ s : Bool,
      (Summable (fun j : ℕ => ‖E (s,(j:ℤ))‖) ∧ (∑' j : ℕ, ‖E (s,(j:ℤ))‖) ≤ A) ∧
      (Summable (fun j : ℕ => ‖E (s,-(j:ℤ))‖) ∧ (∑' j : ℕ, ‖E (s,-(j:ℤ))‖) ≤ A)) :
    Summable (fun i => ‖E i‖) ∧ (∑' i, ‖E i‖) ≤ 4*A := by
  have hr (s : Bool) :
      Summable (fun j : ℤ => ‖E (s,j)‖) ∧ (∑' j : ℤ, ‖E (s,j)‖) ≤ 2*A := by
    obtain ⟨⟨hp,hpA⟩,⟨hm,hmA⟩⟩ := h s
    have hm' : Summable (fun j : ℕ => ‖E (s,-((j:ℤ)+1))‖) := by
      simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hm
    refine ⟨Summable.of_nat_of_neg_add_one (f:=fun z : ℤ => ‖E (s,z)‖) hp hm', ?_⟩
    rw [tsum_of_nat_of_neg_add_one (f:=fun z : ℤ => ‖E (s,z)‖) hp hm']
    have h0 := hm.tsum_eq_zero_add
    simp only [Nat.cast_zero, neg_zero, Nat.cast_add, Nat.cast_one] at h0
    linarith [norm_nonneg (E (s,0))]
  have hs : Summable (fun i => ‖E i‖) := (summable_prod_of_nonneg (fun i => norm_nonneg (E i))).mpr
    ⟨fun s => (hr s).1, (hasSum_fintype _).summable⟩
  refine ⟨hs,?_⟩
  rw [hs.tsum_prod,tsum_fintype]
  calc
    _ ≤ ∑ _s : Bool, 2*A := Finset.sum_le_sum (fun s _ => (hr s).2)
    _ = _ := by simp; ring

theorem MasulloRH.zero_mass_mixed_window_trace (J : Bool × ℤ → ℝ → ℝ → ℂ)
    (mass : Bool × ℤ → ℂ) (hm : HasSum mass 0) (A : ℝ)
    (h : ∀ (b T : ℝ), b ≤ T → ∀ s : Bool,
      let E := fun i : Bool × ℤ => J i b T - (T-b) • mass i
      (Summable (fun j : ℕ => ‖E (s,(j:ℤ))‖) ∧ (∑' j : ℕ, ‖E (s,(j:ℤ))‖) ≤ A*Real.exp (-b)) ∧
      (Summable (fun j : ℕ => ‖E (s,-(j:ℤ))‖) ∧ (∑' j : ℕ, ‖E (s,-(j:ℤ))‖) ≤ A*Real.exp (-b))) :
    (∀ b T : ℝ, b ≤ T →
      Summable (fun i => J i b T) ∧ ‖∑' i, J i b T‖ ≤ 4*A*Real.exp (-b)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℝ in atTop, ∀ T : ℝ, b ≤ T → ‖∑' i, J i b T‖ < ε := by
  have hp (b T : ℝ) (hbt : b ≤ T) := bool_int_bilateral_ray_bound
    (fun i => J i b T - (T-b) • mass i) (A*Real.exp (-b)) (h b T hbt)
  have hfinal (b T : ℝ) (hbt : b ≤ T) :
      Summable (fun i => J i b T) ∧ ‖∑' i, J i b T‖ ≤ 4*A*Real.exp (-b) := by
    obtain ⟨hs,hA⟩ := hp b T hbt
    have hj := hs.of_norm.hasSum.add (hm.const_smul (T-b))
    simp only [sub_add_cancel,smul_zero,add_zero] at hj
    refine ⟨hj.summable, ?_⟩
    rw [hj.tsum_eq]
    exact (norm_tsum_le_tsum_norm hs).trans (hA.trans_eq (mul_assoc _ _ _).symm)
  refine ⟨hfinal,?_⟩
  intro ε hε
  have ht : Tendsto (fun b : ℝ => 4*A*Real.exp (-b)) atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (4*A))
  filter_upwards [ht.eventually_lt_const hε] with b hb
  exact fun T hbt => ((hfinal b T hbt).2).trans_lt hb

open MeasureTheory Set
open scoped Padic ENNReal

theorem MasulloRational.padic_compact_integrable (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ] (μ : Measure ℚ_[p])
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
open MeasureTheory Filter
open scoped SchwartzMap Padic ENNReal Topology

theorem solution (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
    (μ : Measure ℚ_[p]) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψm : Measurable ψ) (hψ : ψ ((p:ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1)
    (f : 𝓢(ℝ,ℂ)) (g : ℚ_[p] → ℂ) (hgm : Measurable g)
    (V M S L : ℝ) (hV : 0 ≤ V) (hM : 0 ≤ M) (hS : 0 < S) (hL : 0 < L)
    (hμ : ∀ u : ℝ, 0 < u → μ (Metric.ball 0 u) ≤ ENNReal.ofReal (V*u))
    (hgB : ∀ y, ‖g y‖ ≤ M) (hgS : ∀ y, S ≤ ‖y‖ → g y = 0)
    (hgP : ∀ y d : ℚ_[p], ‖d‖ ≤ L → g (d+y) = g y) :
    let v (z : ℝ × ℚ_[p]) := Real.log ‖z.1‖ + Real.log ‖z.2‖
    let F (i : Bool × ℤ) (x : ℝ) := f x * Complex.exp
      (((2*Real.pi*((if i.1 then -1 else 1)*(p:ℝ)^i.2):ℝ):ℂ)*Complex.I*(x:ℂ))
    let G (i : Bool × ℤ) (y : ℚ_[p]) := g y * ψ (((if i.1 then -1 else 1)*(p:ℚ_[p])^i.2)*y)
    let mass (i : Bool × ℤ) := (∫ x, F i x)*(∫ y, G i y ∂μ)
    let J (i : Bool × ℤ) (b T : ℝ) := ∫ z : ℝ × ℚ_[p],
      max (T - max (v z) b) 0 • (F i z.1 * G i z.2) ∂(volume.prod μ)
    HasSum mass 0 → ∃ C : ℝ, 0 ≤ C ∧
      (∀ b T : ℝ, b ≤ T → Summable (fun i ↦ J i b T) ∧ ‖∑' i, J i b T‖ ≤ C*Real.exp (-b)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ b : ℝ in atTop, ∀ T : ℝ, b ≤ T → ‖∑' i, J i b T‖ < ε := by
  intro v F G mass J hmass
  have hgi := MasulloRational.padic_compact_integrable p μ g hgm S M V hS (hμ S hS) hgB hgS
  obtain ⟨A,hA,h⟩ := actual_upper_rays p μ ψ hψm hψ hunit f g hgm hgi V M S L hV hM hS hL hμ hgB hgS hgP
  refine ⟨4*A,by positivity,MasulloRH.zero_mass_mixed_window_trace J mass hmass A ?_⟩
  intro b T hb s
  cases s
  · exact h 1 1 (by norm_num) (by simp) b T hb
  · exact h (-1) (-1) (by norm_num) (by simp) b T hb
