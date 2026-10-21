-- Prove2me | solution 1 for InfoInundation.Screening.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:07:10.643639+00:00
-- url     : https://prove2.me/submissions/add21c78-f663-4c41-bf47-4fc1856a1fa5

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoInundation.Screening

lemma ii_aux_int (G : Measure ℝ) [IsFiniteMeasure G] (s r p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    Integrable (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) G := by
  have hw : ∀ σ : ℝ, 0 < σ ^ 2 + s ^ 2 := fun σ => by positivity
  have hc : Continuous (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) := by
    apply Continuous.mul
    · exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (hw x).ne')
    · apply Real.continuous_exp.comp
      apply Continuous.neg
      exact continuous_const.div (by fun_prop) (fun x => by have := hw x; positivity)
  refine Integrable.of_bound hc.aestronglyMeasurable ((s ^ 2) ^ (-p) * Real.exp (|r| / (2 * s ^ 2))) ?_
  refine Filter.Eventually.of_forall (fun σ => ?_)
  have h1 : (σ ^ 2 + s ^ 2) ^ (-p) ≤ (s ^ 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg σ]) (by linarith)
  have h2 : Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) ≤ Real.exp (|r| / (2 * s ^ 2)) := by
    apply Real.exp_le_exp.2
    have a1 : -(r / (2 * (σ ^ 2 + s ^ 2))) ≤ |r| / (2 * (σ ^ 2 + s ^ 2)) := by
      rw [← neg_div]
      apply div_le_div_of_nonneg_right _ (by have := hw σ; positivity)
      linarith [neg_abs_le r]
    have a2 : |r| / (2 * (σ ^ 2 + s ^ 2)) ≤ |r| / (2 * s ^ 2) := by
      apply div_le_div_of_nonneg_left (abs_nonneg r) (by positivity)
      nlinarith [sq_nonneg σ]
    linarith
  rw [Real.norm_of_nonneg (by have := hw σ; positivity)]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

lemma ii_aux_pos (G : Measure ℝ) [IsProbabilityMeasure G] (s r p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    0 < auxMoment G s r p := by
  unfold auxMoment
  rw [integral_pos_iff_support_of_nonneg (fun σ => by have : 0 < σ ^ 2 + s ^ 2 := by positivity
                                                      positivity) (ii_aux_int G s r p hs hp)]
  have : Function.support (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) = Set.univ := by
    ext σ
    have : 0 < σ ^ 2 + s ^ 2 := by positivity
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    positivity
  rw [this]; simp

lemma ii_lik (μ s σ z : ℝ) (hs : 0 < s) :
    likelihood μ s σ z = (Real.sqrt (2 * Real.pi))⁻¹ *
      ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-((z - μ) ^ 2 / (2 * (σ ^ 2 + s ^ 2))))) := by
  have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
  unfold likelihood psi
  rw [Real.sq_sqrt (by positivity)]
  have e1 : (σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (σ ^ 2 + s ^ 2))⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow]
  rw [e1, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
  have : 0 < Real.sqrt (σ ^ 2 + s ^ 2) := Real.sqrt_pos.2 hw
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp

lemma ii_lik_int (G : Measure ℝ) [IsFiniteMeasure G] (μ s z : ℝ) (hs : 0 < s) :
    Integrable (fun σ => likelihood μ s σ z) G := by
  have := (ii_aux_int G s ((z - μ) ^ 2) (1 / 2) hs (by norm_num)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
  simp only
  rw [ii_lik μ s σ z hs]

/-- `∫ (σ²+s²)^(-q) · likelihood = c · auxMoment (q + 1/2)`. -/
lemma ii_num (G : Measure ℝ) (μ s z q : ℝ) (hs : 0 < s) :
    ∫ σ, (σ ^ 2 + s ^ 2) ^ (-q) * likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (q + 1 / 2) := by
  unfold auxMoment
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
  simp only
  have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
  rw [ii_lik μ s σ z hs, neg_add, Real.rpow_add hw]
  ring

lemma ii_den (G : Measure ℝ) (μ s z : ℝ) (hs : 0 < s) :
    ∫ σ, likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (0 + 1 / 2) := by
  have := ii_num G μ s z 0 hs
  simpa using this

lemma ii_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ s : ℝ) (θ ε : Ω → ℝ) (hε : Measurable ε)
    (hθlaw : P.map θ = gaussianReal μ (s ^ 2).toNNReal)
    (hεlaw : P.map ε = gaussianReal 0 1) (hind : IndepFun θ ε P) (σ : ℝ) :
    P.map (fun ω => θ ω + σ * ε ω) = gaussianReal μ (σ ^ 2 + s ^ 2).toNNReal := by
  have hE : HasLaw ε (gaussianReal 0 1) P := ⟨hε.aemeasurable, hεlaw⟩
  have h1 := gaussianReal_const_mul hE σ
  have hi : IndepFun θ (fun ω => σ * ε ω) P :=
    hind.comp (φ := id) (ψ := fun x => σ * x) measurable_id (measurable_const_mul σ)
  have h2 := gaussianReal_add_gaussianReal_of_indepFun hi hθlaw h1.map_eq
  have e : (fun ω => θ ω + σ * ε ω) = θ + fun ω => σ * ε ω := rfl
  rw [e, h2]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, mul_one, Real.coe_toNNReal',
      NNReal.coe_mk]
    rw [max_eq_left (by positivity), max_eq_left (by positivity)]
    ring

lemma ii_pdf (μ s σ z : ℝ) (hs : 0 < s) :
    likelihood μ s σ z = gaussianPDFReal μ (σ ^ 2 + s ^ 2).toNNReal z := by
  have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
  unfold likelihood psi gaussianPDFReal
  rw [Real.sq_sqrt (by positivity), Real.coe_toNNReal _ hw.le]
  have : Real.sqrt Real.pi * Real.sqrt (2 * (σ ^ 2 + s ^ 2)) = Real.sqrt (2 * Real.pi * (σ ^ 2 + s ^ 2)) := by
    rw [← Real.sqrt_mul Real.pi_pos.le]
    congr 1
    ring
  rw [this, one_div, neg_div]

lemma ii_lik_nonneg (μ s σ z : ℝ) (hs : 0 < s) : 0 ≤ likelihood μ s σ z := by
  rw [ii_lik μ s σ z hs]
  have : 0 < σ ^ 2 + s ^ 2 := by positivity
  positivity

lemma ii_lik_cont (μ s : ℝ) (hs : 0 < s) : Continuous (fun p : ℝ × ℝ => likelihood μ s p.1 p.2) := by
  have : (fun p : ℝ × ℝ => likelihood μ s p.1 p.2) = fun p : ℝ × ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      ((p.1 ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-((p.2 - μ) ^ 2 / (2 * (p.1 ^ 2 + s ^ 2))))) := by
    funext p; exact ii_lik μ s p.1 p.2 hs
  rw [this]
  apply Continuous.mul continuous_const
  apply Continuous.mul
  · exact Continuous.rpow_const (by fun_prop) (fun p => Or.inl (by positivity))
  · apply Real.continuous_exp.comp
    apply Continuous.neg
    exact Continuous.div (by fun_prop) (by fun_prop) (fun p => by positivity)

lemma ii_F_meas (G : Measure ℝ) [IsProbabilityMeasure G] (μ s : ℝ) (hs : 0 < s) (h : ℝ → ℝ)
    (hh : Measurable h) : Measurable (fun z => postExp G μ s z h) := by
  unfold postExp
  have hc := ii_lik_cont μ s hs
  have h1 : StronglyMeasurable (Function.uncurry fun (σ z : ℝ) => h σ * likelihood μ s σ z) :=
    ((hh.comp measurable_fst).mul hc.measurable).stronglyMeasurable
  have h2 : StronglyMeasurable (Function.uncurry fun (σ z : ℝ) => likelihood μ s σ z) :=
    hc.measurable.stronglyMeasurable
  exact (h1.integral_prod_left (μ := G)).measurable.div (h2.integral_prod_left (μ := G)).measurable

lemma ii_F_bound (G : Measure ℝ) [IsProbabilityMeasure G] (μ s z : ℝ) (hs : 0 < s) (h : ℝ → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : ∀ x, |h x| ≤ C) : |postExp G μ s z h| ≤ C := by
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hD : 0 < ∫ σ, likelihood μ s σ z ∂G := by
    rw [ii_den G μ s z hs]
    exact mul_pos (by positivity) (ii_aux_pos G s _ _ hs (by norm_num))
  have hL := ii_lik_int G μ s z hs
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hli : Integrable (fun σ => h σ * likelihood μ s σ z) G :=
    hL.bdd_mul hh.aestronglyMeasurable (Filter.Eventually.of_forall (fun σ => by simpa [Real.norm_eq_abs] using hC σ))
  unfold postExp
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have := norm_integral_le_of_norm_le (hL.const_mul C) (f := fun σ => h σ * likelihood μ s σ z) (μ := G)
    (Filter.Eventually.of_forall (fun σ => by
      rw [norm_mul, Real.norm_of_nonneg (ii_lik_nonneg μ s σ z hs), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC σ) (ii_lik_nonneg μ s σ z hs)))
  rw [integral_const_mul, Real.norm_eq_abs] at this
  exact this

lemma ii_M {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Measure ℝ) [IsProbabilityMeasure G] (μ s : ℝ) (hs : 0 < s) (θ Sig ε : Ω → ℝ)
    (hθ : Measurable θ) (hSig : Measurable Sig) (hε : Measurable ε)
    (hθlaw : P.map θ = gaussianReal μ (s ^ 2).toNNReal) (hSiglaw : P.map Sig = G)
    (hεlaw : P.map ε = gaussianReal 0 1) (hind : iIndepFun ![θ, Sig, ε] P)
    (k f : ℝ → ℝ) (hk : Measurable k) (hf : Measurable f) (Ck Cf : ℝ)
    (hkb : ∀ x, |k x| ≤ Ck) (hfb : ∀ x, |f x| ≤ Cf) :
    ∫ ω, k (Sig ω) * f (θ ω + Sig ω * ε ω) ∂P = ∫ z, f z * ∫ σ, k σ * likelihood μ s σ z ∂G := by
  set ν : Measure (ℝ × ℝ) := (gaussianReal μ (s ^ 2).toNNReal).prod (gaussianReal 0 1) with hν
  have hmeas : ∀ i, Measurable (![θ, Sig, ε] i) := by
    intro i; fin_cases i <;> simpa
  have hI12 : IndepFun (fun ω => (θ ω, ε ω)) Sig P := by
    have := hind.indepFun_prodMk hmeas 0 2 1 (by decide) (by decide)
    exact this
  have hI02 : IndepFun θ ε P := by
    have := hind.indepFun (i := 0) (j := 2) (by decide)
    exact this
  have hP3 : P.map (fun ω => (Sig ω, (θ ω, ε ω))) = G.prod ν := by
    have h1 := (indepFun_iff_map_prod_eq_prod_map_map hSig.aemeasurable (hθ.prodMk hε).aemeasurable).1 hI12.symm
    have h2 := (indepFun_iff_map_prod_eq_prod_map_map hθ.aemeasurable hε.aemeasurable).1 hI02
    rw [h1, h2, hθlaw, hεlaw, hSiglaw]
  have hT : Measurable (fun ω => (Sig ω, (θ ω, ε ω))) := hSig.prodMk (hθ.prodMk hε)
  have hΦm : Measurable (fun x : ℝ × (ℝ × ℝ) => k x.1 * f (x.2.1 + x.1 * x.2.2)) :=
    (hk.comp measurable_fst).mul (hf.comp ((measurable_snd.fst).add (measurable_fst.mul measurable_snd.snd)))
  have hCk : 0 ≤ Ck := le_trans (abs_nonneg _) (hkb 0)
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg _) (hfb 0)
  have hΦint : Integrable (fun x : ℝ × (ℝ × ℝ) => k x.1 * f (x.2.1 + x.1 * x.2.2)) (G.prod ν) := by
    refine Integrable.of_bound hΦm.aestronglyMeasurable (Ck * Cf) (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hkb _) (hfb _) (abs_nonneg _) hCk
  have hνfst : ν.map Prod.fst = gaussianReal μ (s ^ 2).toNNReal := by
    rw [hν, Measure.map_fst_prod]; simp
  have hνsnd : ν.map Prod.snd = gaussianReal 0 1 := by
    rw [hν, Measure.map_snd_prod]; simp
  have hνind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd ν :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hv : ∀ σ : ℝ, (σ ^ 2 + s ^ 2).toNNReal ≠ 0 := fun σ =>
    (Real.toNNReal_pos.2 (by positivity)).ne'
  -- the inner integral
  have hinner : ∀ σ : ℝ, ∫ q : ℝ × ℝ, k σ * f (q.1 + σ * q.2) ∂ν =
      k σ * ∫ z, likelihood μ s σ z * f z := by
    intro σ
    rw [integral_const_mul]
    congr 1
    have hmap := ii_law ν μ s Prod.fst Prod.snd measurable_snd hνfst hνsnd hνind σ
    have haem : AEMeasurable (fun q : ℝ × ℝ => q.1 + σ * q.2) ν := by fun_prop
    have e1 : ∫ z, f z ∂(ν.map (fun q : ℝ × ℝ => q.1 + σ * q.2)) = ∫ q, f (q.1 + σ * q.2) ∂ν :=
      integral_map haem hf.aestronglyMeasurable
    rw [hmap] at e1
    rw [← e1, integral_gaussianReal_eq_integral_smul (hv σ)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [smul_eq_mul]
    rw [ii_pdf μ s σ z hs]
  have hstep1 : ∫ ω, k (Sig ω) * f (θ ω + Sig ω * ε ω) ∂P =
      ∫ σ, k σ * (∫ z, likelihood μ s σ z * f z) ∂G := by
    have e1 : ∫ x : ℝ × (ℝ × ℝ), k x.1 * f (x.2.1 + x.1 * x.2.2) ∂(P.map (fun ω => (Sig ω, (θ ω, ε ω)))) =
        ∫ ω, k (Sig ω) * f (θ ω + Sig ω * ε ω) ∂P :=
      integral_map hT.aemeasurable hΦm.aestronglyMeasurable
    have e3 : ∫ σ, ∫ q : ℝ × ℝ, k σ * f (q.1 + σ * q.2) ∂ν ∂G =
        ∫ σ, k σ * (∫ z, likelihood μ s σ z * f z) ∂G :=
      integral_congr_ae (μ := G) (Filter.Eventually.of_forall (fun σ => hinner σ))
    rw [← e1, hP3, integral_prod _ hΦint]
    exact e3
  rw [hstep1]
  -- Fubini
  have hlikint : ∀ σ : ℝ, Integrable (fun z => likelihood μ s σ z) volume := by
    intro σ
    have : (fun z => likelihood μ s σ z) = gaussianPDFReal μ (σ ^ 2 + s ^ 2).toNNReal :=
      funext (fun z => ii_pdf μ s σ z hs)
    rw [this]; exact integrable_gaussianPDFReal _ _
  have hlikone : ∀ σ : ℝ, ∫ z, likelihood μ s σ z = 1 := by
    intro σ
    have : (fun z => likelihood μ s σ z) = gaussianPDFReal μ (σ ^ 2 + s ^ 2).toNNReal :=
      funext (fun z => ii_pdf μ s σ z hs)
    rw [this]; exact integral_gaussianPDFReal_eq_one _ (hv σ)
  have hFm : Measurable (fun p : ℝ × ℝ => k p.1 * (likelihood μ s p.1 p.2 * f p.2)) :=
    (hk.comp measurable_fst).mul (((ii_lik_cont μ s hs).measurable).mul (hf.comp measurable_snd))
  have hFint : Integrable (fun p : ℝ × ℝ => k p.1 * (likelihood μ s p.1 p.2 * f p.2)) (G.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall (fun σ => ?_)
      have := ((hlikint σ).bdd_mul (f := f) hf.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hfb z))).const_mul (k σ)
      refine this.congr (Filter.Eventually.of_forall (fun z => ?_))
      ring
    · have hmeas2 : AEStronglyMeasurable (fun σ => ∫ z, ‖k σ * (likelihood μ s σ z * f z)‖) G :=
        (hFm.aestronglyMeasurable (μ := G.prod volume)).norm.integral_prod_right' (ν := volume)
      refine Integrable.of_bound hmeas2 (Ck * Cf) (Filter.Eventually.of_forall (fun σ => ?_))
      have hint : Integrable (fun z => ‖k σ * (likelihood μ s σ z * f z)‖) volume := by
        have := ((hlikint σ).bdd_mul (f := f) hf.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hfb z))).const_mul (k σ)
        exact (this.congr (Filter.Eventually.of_forall (fun z => by simp only; ring))).norm
      have hle : ∫ z, ‖k σ * (likelihood μ s σ z * f z)‖ ≤ ∫ z, (Ck * Cf) * likelihood μ s σ z := by
        apply integral_mono hint ((hlikint σ).const_mul _)
        intro z
        simp only
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (ii_lik_nonneg μ s σ z hs), Real.norm_eq_abs, Real.norm_eq_abs]
        have := mul_le_mul (hkb σ) (hfb z) (abs_nonneg _) hCk
        nlinarith [ii_lik_nonneg μ s σ z hs, abs_nonneg (k σ), abs_nonneg (f z), mul_nonneg (abs_nonneg (k σ)) (abs_nonneg (f z))]
      rw [integral_const_mul, hlikone σ, mul_one] at hle
      rw [Real.norm_of_nonneg (integral_nonneg (fun z => norm_nonneg _))]
      exact hle
  have hswap := integral_integral_swap (f := fun (σ z : ℝ) => k σ * (likelihood μ s σ z * f z)) hFint
  have e2 : ∀ σ : ℝ, k σ * ∫ z, likelihood μ s σ z * f z = ∫ z, k σ * (likelihood μ s σ z * f z) := by
    intro σ; rw [integral_const_mul]
  have e3 : ∫ σ, k σ * (∫ z, likelihood μ s σ z * f z) ∂G = ∫ σ, (∫ z, k σ * (likelihood μ s σ z * f z)) ∂G :=
    integral_congr_ae (μ := G) (Filter.Eventually.of_forall (fun σ => e2 σ))
  have e4 : ∫ z, ∫ σ, k σ * (likelihood μ s σ z * f z) ∂G = ∫ z, f z * ∫ σ, k σ * likelihood μ s σ z ∂G := by
    refine integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (fun z => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (μ := G) (Filter.Eventually.of_forall (fun σ => ?_))
    simp only
    ring
  exact (e3.trans hswap).trans e4

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s) (θ Sig ε : Ω → ℝ)
    (hθ : Measurable θ) (hSig : Measurable Sig) (hε : Measurable ε)
    (hθlaw : P.map θ = gaussianReal μ (s ^ 2).toNNReal) (hSiglaw : P.map Sig = G)
    (hεlaw : P.map ε = gaussianReal 0 1) (hind : iIndepFun ![θ, Sig, ε] P)
    (h : ℝ → ℝ) (hh : Measurable h) (hhb : ∃ C : ℝ, ∀ x, |h x| ≤ C) :
    P[h ∘ Sig | MeasurableSpace.comap (fun ω => θ ω + Sig ω * ε ω) inferInstance]
      =ᵐ[P] fun ω => postExp G μ s (θ ω + Sig ω * ε ω) h := by
  haveI := hG.isProb
  obtain ⟨C, hC⟩ := hhb
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  set Z : Ω → ℝ := fun ω => θ ω + Sig ω * ε ω with hZdef
  have hZ : Measurable Z := hθ.add (hSig.mul hε)
  have hm : MeasurableSpace.comap Z inferInstance ≤ ‹MeasurableSpace Ω› := hZ.comap_le
  set F : ℝ → ℝ := fun z => postExp G μ s z h with hF
  have hFm : Measurable F := ii_F_meas G μ s hs h hh
  have hFb : ∀ z, |F z| ≤ C := fun z => ii_F_bound G μ s z hs h hh C hC
  have hf_int : Integrable (h ∘ Sig) P :=
    Integrable.of_bound (hh.comp hSig).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hC (Sig ω)))
  have hFZint : Integrable (fun ω => F (Z ω)) P :=
    Integrable.of_bound (hFm.comp hZ).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hFb (Z ω)))
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap Z inferInstance] (fun ω => F (Z ω)) P := by
    have : StronglyMeasurable[MeasurableSpace.comap Z inferInstance] (fun ω => F (Z ω)) :=
      hFm.stronglyMeasurable.comp_measurable (comap_measurable Z)
    exact this.aestronglyMeasurable
  have key := ae_eq_condExp_of_forall_setIntegral_eq hm (μ := P) (f := h ∘ Sig) (g := fun ω => F (Z ω))
    hf_int (fun t _ _ => hFZint.integrableOn) ?_ hgm
  · exact key.symm
  · intro t ht _
    obtain ⟨A, hA, rfl⟩ := ht
    have hAZ : MeasurableSet (Z ⁻¹' A) := hZ hA
    rw [← integral_indicator hAZ, ← integral_indicator hAZ]
    have hind1 : ∀ ω, (Z ⁻¹' A).indicator (fun ω => F (Z ω)) ω =
        (fun _ : ℝ => (1 : ℝ)) (Sig ω) * (A.indicator F) (Z ω) := by
      intro ω
      by_cases hω : Z ω ∈ A
      · simp [Set.indicator, hω]
      · simp [Set.indicator, hω]
    have hind2 : ∀ ω, (Z ⁻¹' A).indicator (h ∘ Sig) ω = h (Sig ω) * (A.indicator (fun _ => (1 : ℝ))) (Z ω) := by
      intro ω
      by_cases hω : Z ω ∈ A
      · simp [Set.indicator, hω]
      · simp [Set.indicator, hω]
    rw [integral_congr_ae (Filter.Eventually.of_forall hind1), integral_congr_ae (Filter.Eventually.of_forall hind2)]
    have hbF : ∀ x, |A.indicator F x| ≤ C := by
      intro x
      by_cases hx : x ∈ A
      · simp [Set.indicator, hx, hFb x]
      · simp [Set.indicator, hx, hC0]
    have hb1 : ∀ x, |A.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
    have M1 := ii_M P G μ s hs θ Sig ε hθ hSig hε hθlaw hSiglaw hεlaw hind (fun _ => 1) (A.indicator F)
      measurable_const (hFm.indicator hA) 1 C (fun x => by simp) hbF
    have M2 := ii_M P G μ s hs θ Sig ε hθ hSig hε hθlaw hSiglaw hεlaw hind h (A.indicator (fun _ => (1 : ℝ)))
      hh (measurable_const.indicator hA) C 1 hC hb1
    rw [M1, M2]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only
    have hD : ∫ σ, likelihood μ s σ z ∂G ≠ 0 := by
      have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by
        have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
        positivity
      rw [ii_den G μ s z hs]
      exact mul_ne_zero hc (ii_aux_pos G s _ _ hs (by norm_num)).ne'
    by_cases hz : z ∈ A
    · simp only [Set.indicator_of_mem hz, hF, one_mul]
      unfold postExp
      field_simp
    · simp [Set.indicator_of_notMem hz]
