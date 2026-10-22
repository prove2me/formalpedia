-- Prove2me | solution 1 for InfoGen.Expected.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T05:07:41.068369+00:00
-- url     : https://prove2.me/submissions/f097cc10-a4ac-4a7d-8875-59db66323661

import Mathlib
import Definitions.Def_InfoGen_Expected_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGenProof

lemma entropy_young (d y : ℝ) (hd : 0 ≤ d) :
    d * y ≤ klFun d + Real.exp y - 1 := by
  rcases eq_or_lt_of_le hd with hd | hd
  · subst d
    simp only [zero_mul, klFun_zero]
    linarith [Real.exp_pos y]
  · have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - Real.log d)) hd.le
    rw [Real.exp_sub, Real.exp_log hd] at h
    have he : d * (Real.exp y / d) = Real.exp y := by field_simp
    rw [he] at h
    unfold klFun
    nlinarith

lemma entropy_young_abs (d y : ℝ) (hd : 0 ≤ d) :
    d * |y| ≤ klFun d + Real.exp y + Real.exp (-y) := by
  have h := entropy_young d |y| hd
  have he := Real.exp_abs_le y
  linarith

end InfoGenProof

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGenProof

variable {α : Type*} [MeasurableSpace α]

lemma finite_kl_density (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hKL : klDiv P Q ≠ ⊤) :
    P ≪ Q ∧ Integrable (fun x => klFun (P.rnDeriv Q x).toReal) Q := by
  have hac : P ≪ Q := by
    by_contra h
    exact hKL (klDiv_of_not_ac h)
  have hi : Integrable (llr P Q) P := by
    by_contra h
    exact hKL (klDiv_of_not_integrable h)
  exact ⟨hac, (integrable_klFun_rnDeriv_iff hac).2 hi⟩

lemma entropy_integrable (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : α → ℝ) (hF : Measurable F) (c : ℝ≥0)
    (hsub : HasSubgaussianMGF F c Q) (hKL : klDiv P Q ≠ ⊤) : Integrable F P := by
  obtain ⟨hac, hk⟩ := finite_kl_density P Q hKL
  have hp : Integrable (fun x => Real.exp (F x)) Q := by
    simpa only [one_mul] using hsub.integrable_exp_mul 1
  have hm : Integrable (fun x => Real.exp (-F x)) Q := by
    simpa only [neg_one_mul] using hsub.integrable_exp_mul (-1)
  apply (integrable_toReal_rnDeriv_mul_iff hac).1
  refine ((hk.add hp).add hm).mono' ?_ ?_
  · exact (((Measure.measurable_rnDeriv P Q).ennreal_toReal).mul hF).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
      entropy_young_abs (P.rnDeriv Q x).toReal (F x) ENNReal.toReal_nonneg

lemma entropy_integral_inequality (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : α → ℝ) (hF : Measurable F) (c : ℝ≥0)
    (hsub : HasSubgaussianMGF F c Q) (hKL : klDiv P Q ≠ ⊤) (t : ℝ) :
    t * (∫ x, F x ∂P) ≤ (klDiv P Q).toReal + (c : ℝ) * t ^ 2 / 2 := by
  obtain ⟨hac, hk⟩ := finite_kl_density P Q hKL
  have hFP := entropy_integrable P Q F hF c hsub hKL
  let a : ℝ := (c : ℝ) * t ^ 2 / 2
  let Y : α → ℝ := fun x => t * F x - a
  have hY : Integrable Y P := (hFP.const_mul t).sub (integrable_const a)
  have hdY : Integrable (fun x => (P.rnDeriv Q x).toReal * Y x) Q :=
    (integrable_toReal_rnDeriv_mul_iff hac).2 hY
  have hex : (fun x => Real.exp (Y x)) =
      (fun x => Real.exp (-a) * Real.exp (t * F x)) := by
    funext x
    simp only [Y, Real.exp_sub, Real.exp_neg]
    ring
  have he : Integrable (fun x => Real.exp (Y x)) Q := by
    rw [hex]
    exact (hsub.integrable_exp_mul t).const_mul _
  have heb : (∫ x, Real.exp (Y x) ∂Q) ≤ 1 := by
    rw [hex, integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left (hsub.mgf_le t) (Real.exp_pos (-a)).le
    change Real.exp (-a) * (∫ x, Real.exp (t * F x) ∂Q) ≤
      Real.exp (-a) * Real.exp a at hm
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using hm
  have hy := integral_mono hdY ((hk.add he).sub (integrable_const (1 : ℝ)))
    (fun x => entropy_young (P.rnDeriv Q x).toReal (Y x) ENNReal.toReal_nonneg)
  rw [integral_toReal_rnDeriv_mul hac] at hy
  change (∫ x, Y x ∂P) ≤ ∫ x, (klFun (P.rnDeriv Q x).toReal + Real.exp (Y x) - 1) ∂Q at hy
  have hsum := integral_add hk he
  have hsubi := integral_sub (hk.add he) (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) Q)
  dsimp only [Pi.add_apply] at hsum hsubi
  rw [hsubi, hsum, ← toReal_klDiv_eq_integral_klFun hac] at hy
  have hYi : (∫ x, Y x ∂P) = t * (∫ x, F x ∂P) - a := by
    dsimp only [Y]
    rw [integral_sub (hFP.const_mul _) (integrable_const _), integral_const_mul]
    simp
  rw [hYi] at hy
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hy
  dsimp only [a] at hy
  linarith

end InfoGenProof

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGenProof

lemma entropy_scalar_bound (m c K : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (h : ∀ t : ℝ, t * m ≤ K + c * t ^ 2 / 2) :
    |m| ≤ Real.sqrt (2 * c * K) := by
  have hs : m ^ 2 ≤ 2 * c * K := by
    rcases eq_or_lt_of_le hc with hc | hc
    · subst c
      have hm : m = 0 := by
        by_contra hm
        have hh := h ((K + 1) / m)
        simp only [zero_mul, zero_div, add_zero] at hh
        rw [div_mul_cancel₀ _ hm] at hh
        linarith
      simp [hm]
    · have hh := h (m / c)
      have hp : 0 < 2 * c := by positivity
      have hh' := mul_le_mul_of_nonneg_left hh hp.le
      field_simp at hh'
      nlinarith
  have hrad : 0 ≤ 2 * c * K := by positivity
  have hr := Real.sq_sqrt hrad
  have ha : |m| ^ 2 = m ^ 2 := sq_abs m
  nlinarith [Real.sqrt_nonneg (2 * c * K), abs_nonneg m]

theorem entropy_bound {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : α → ℝ) (hF : Measurable F) (c : ℝ≥0)
    (hsub : HasSubgaussianMGF F c Q) (hKL : klDiv P Q ≠ ⊤) :
    Integrable F P ∧
      |∫ x, F x ∂P| ≤ Real.sqrt (2 * (c : ℝ) * (klDiv P Q).toReal) := by
  refine ⟨entropy_integrable P Q F hF c hsub hKL, ?_⟩
  exact entropy_scalar_bound _ _ _ c.coe_nonneg ENNReal.toReal_nonneg
    (entropy_integral_inequality P Q F hF c hsub hKL)

end InfoGenProof

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators
open LearnStability.Characterization

namespace InfoGenProof

theorem measurable_risk {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ℓ : W → Z → ℝ)
    (hℓ : Measurable (Function.uncurry ℓ)) :
    Measurable (risk ℓ μ) :=
  hℓ.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_gap {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (ℓ : W → Z → ℝ)
    (hℓ : Measurable (Function.uncurry ℓ)) :
    Measurable (fun p : (Fin n → Z) × W => risk ℓ μ p.2 - empRisk ℓ p.1 p.2) := by
  apply ((measurable_risk μ ℓ hℓ).comp measurable_snd).sub
  exact (Finset.measurable_sum Finset.univ fun i _ =>
    hℓ.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))).div_const n

theorem empirical_mgf {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (σ : ℝ≥0)
    (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (w : W) :
    HasSubgaussianMGF (fun s : Fin n → Z => empRisk ℓ s w - risk ℓ μ w)
      (σ ^ 2 / (n : ℝ≥0)) (sampleLaw μ n) := by
  have hm : Measurable (fun z => ℓ w z - risk ℓ μ w) :=
    (hℓ.comp (measurable_const.prodMk measurable_id)).sub_const _
  have hind : iIndepFun (fun (i : Fin n) (s : Fin n → Z) =>
      ℓ w (s i) - risk ℓ μ w) (sampleLaw μ n) :=
    iIndepFun_pi (fun _ => hm.aemeasurable)
  have hcoord (i : Fin n) : HasSubgaussianMGF
      (fun s : Fin n → Z => ℓ w (s i) - risk ℓ μ w) (σ ^ 2) (sampleLaw μ n) := by
    apply HasSubgaussianMGF.of_map
      (μ := sampleLaw μ n) (Y := fun s : Fin n → Z => s i)
      (X := fun z => ℓ w z - risk ℓ μ w) (measurable_pi_apply i).aemeasurable
    simpa only [sampleLaw, (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq]
      using hσ w
  have hsum : HasSubgaussianMGF
      (fun s : Fin n → Z => ∑ i, (ℓ w (s i) - risk ℓ μ w))
      ((n : ℝ≥0) * σ ^ 2) (sampleLaw μ n) := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun hind
      (s := Finset.univ) (fun i _ => hcoord i)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc : NNReal.mk (((n : ℝ)⁻¹) ^ 2) (sq_nonneg _) *
      ((n : ℝ≥0) * σ ^ 2) = σ ^ 2 / (n : ℝ≥0) := by
    apply NNReal.eq
    change (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * (σ : ℝ) ^ 2) = (σ : ℝ) ^ 2 / n
    field_simp
  have hs : HasSubgaussianMGF
      (fun s : Fin n → Z => (n : ℝ)⁻¹ * ∑ i, (ℓ w (s i) - risk ℓ μ w))
      (NNReal.mk (((n : ℝ)⁻¹) ^ 2) (sq_nonneg _) * ((n : ℝ≥0) * σ ^ 2))
      (sampleLaw μ n) := by
    convert! hsum.const_mul ((n : ℝ)⁻¹) using 1
  rw [hc] at hs
  apply hs.congr
  filter_upwards [] with s
  simp only [empRisk, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end InfoGenProof

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators
open LearnStability.Characterization

namespace InfoGenProof

theorem product_mgf {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : A × B → ℝ) (hF : Measurable F) (c : ℝ≥0)
    (hsec : ∀ b, HasSubgaussianMGF (fun a => F (a,b)) c μ) :
    HasSubgaussianMGF F c (μ.prod ν) := by
  have hm (t : ℝ) : Measurable (fun p => Real.exp (t * F p)) :=
    (hF.const_mul t).exp
  have hi (t : ℝ) : Integrable (fun b => ∫ a, Real.exp (t * F (a,b)) ∂μ) ν := by
    apply (integrable_const (Real.exp ((c : ℝ) * t ^ 2 / 2))).mono'
      (hm t).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards [] with b
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun a => Real.exp_nonneg _)]
    exact (hsec b).mgf_le t
  have hp (t : ℝ) : Integrable (fun p => Real.exp (t * F p)) (μ.prod ν) := by
    apply (integrable_prod_iff' (hm t).aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun b => (hsec b).integrable_exp_mul t), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hi t
  refine ⟨hp, fun t => ?_⟩
  change (∫ p, Real.exp (t * F p) ∂μ.prod ν) ≤ Real.exp ((c : ℝ) * t ^ 2 / 2)
  rw [integral_prod_symm _ (hp t)]
  calc
    (∫ b, ∫ a, Real.exp (t * F (a,b)) ∂μ ∂ν) ≤
        ∫ _b, Real.exp ((c : ℝ) * t ^ 2 / 2) ∂ν :=
      integral_mono (hi t) (integrable_const _) (fun b => (hsec b).mgf_le t)
    _ = Real.exp ((c : ℝ) * t ^ 2 / 2) := by simp

theorem gap_product_mgf {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (σ : ℝ≥0)
    (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (ν : Measure W) [IsProbabilityMeasure ν] :
    HasSubgaussianMGF
      (fun p : (Fin n → Z) × W => risk ℓ μ p.2 - empRisk ℓ p.1 p.2)
      (σ ^ 2 / (n : ℝ≥0)) ((sampleLaw μ n).prod ν) := by
  have : IsProbabilityMeasure (sampleLaw μ n) := by
    dsimp [sampleLaw]
    infer_instance
  apply product_mgf (sampleLaw μ n) ν _ (measurable_gap μ n ℓ hℓ) _
  intro w
  apply ((empirical_mgf μ n hn ℓ hℓ σ hσ w).neg).congr
  filter_upwards [] with s
  exact neg_sub _ _

end InfoGenProof

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGen.Expected

open LearnStability.Characterization

/-- Theorem 1 (Xu & Raginsky, arXiv:1705.07809v2, p. 4, eq. (10)). Let `S` be an i.i.d. sample of
size `n ≥ 1` from `μ` and `W` the output of the learning algorithm `κ = P_{W|S}`. If `ℓ(w, Z)` is
`σ`-subgaussian under `μ` for every hypothesis `w` and `I(S; W) < ∞`, then
`|gen(μ, P_{W|S})| ≤ √((2σ²/n) I(S; W))`. -/
theorem theorem_1 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (hI : mutualInfo (sampleLaw μ n ⊗ₘ κ) ≠ ⊤) :
    |genError ℓ μ κ|
      ≤ Real.sqrt (2 * (σ : ℝ) ^ 2 / n * (mutualInfo (sampleLaw μ n ⊗ₘ κ)).toReal) := by
  have _ := hℓ0
  have : IsProbabilityMeasure (sampleLaw μ n) := by
    dsimp [sampleLaw]
    infer_instance
  let P := sampleLaw μ n ⊗ₘ κ
  have : IsProbabilityMeasure P := by
    dsimp [P, sampleLaw]
    infer_instance
  have hsub : HasSubgaussianMGF
      (fun p : (Fin n → Z) × W => risk ℓ μ p.2 - empRisk ℓ p.1 p.2)
      (σ ^ 2 / (n : ℝ≥0)) (P.fst.prod P.snd) := by
    simpa only [P, Measure.fst_compProd] using
      InfoGenProof.gap_product_mgf μ n hn ℓ hℓ σ hσ P.snd
  have hbound := InfoGenProof.entropy_bound P (P.fst.prod P.snd)
    (fun p : (Fin n → Z) × W => risk ℓ μ p.2 - empRisk ℓ p.1 p.2)
    (InfoGenProof.measurable_gap μ n ℓ hℓ) (σ ^ 2 / (n : ℝ≥0)) hsub hI
  have hc : 2 * ((σ ^ 2 / (n : ℝ≥0) : ℝ≥0) : ℝ) *
      (InformationTheory.klDiv P (P.fst.prod P.snd)).toReal =
      2 * (σ : ℝ) ^ 2 / n * (mutualInfo P).toReal := by
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, mutualInfo]
    ring
  rw [hc] at hbound
  exact hbound.2

end InfoGen.Expected

open InfoGen.Expected LearnStability.Characterization

theorem solution {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (hI : mutualInfo (sampleLaw μ n ⊗ₘ κ) ≠ ⊤) :
    |genError ℓ μ κ|
      ≤ Real.sqrt (2 * (σ : ℝ) ^ 2 / n * (mutualInfo (sampleLaw μ n ⊗ₘ κ)).toReal) := by
  exact InfoGen.Expected.theorem_1 μ n hn ℓ hℓ hℓ0 κ σ hσ hI
