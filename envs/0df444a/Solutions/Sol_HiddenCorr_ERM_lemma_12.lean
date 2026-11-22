-- Prove2me | solution 1 for HiddenCorr.ERM.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T20:17:29.784924+00:00
-- url     : https://prove2.me/submissions/0eb0a29a-1972-46f9-bec3-6e22d596ce02

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

/-!
Proof of Lemma 12 (Chen–Gentile–Kaplan–Koren). Write the random quantity as the norm of
`∑ⱼ Xⱼ` in the Hilbert space `H = ⨁_{i<r} ℝ^k` (an `L²` product), where
`Xⱼ = (T_{ij} Vⱼ)ᵢ` are independent, centered, with `‖Xⱼ‖ ≤ bⱼ = B (∑ᵢ T_{ij}²)^{1/2}`.
A one-step Hoeffding argument gives `E exp(μ‖a + Xⱼ‖²) ≤ e^{μ bⱼ²} exp(μ(1+2μbⱼ²)‖a‖²)`;
iterating over the summands yields `E exp(μ‖∑ Xⱼ‖²) ≤ exp(2μσ²)` whenever `μσ² ≤ 1/4`,
`σ² = ∑ bⱼ² = B²‖T‖_F²`. Taking `μ = 1/(4σ²)` and `W^p ≤ (p/(2μ))^{p/2} e^{μW²}` gives
`‖W‖_{L_p} ≤ 6 σ √p`.
-/

namespace HiddenCorrL12

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- One step: Hoeffding's lemma for the scalar `⟪a, X⟫`. -/
lemma step (a : H) (X : Ω → H) (hX : Measurable X) (b : ℝ) (hb : 0 ≤ b)
    (hXb : ∀ᵐ ω ∂P, ‖X ω‖ ≤ b) (hc : ∀ c : H, ∫ ω, inner ℝ c (X ω) ∂P = 0) (μ : ℝ) (hμ : 0 ≤ μ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * ‖X ω + a‖ ^ 2)) ∂P ≤
      ENNReal.ofReal (Real.exp (μ * b ^ 2) * Real.exp (μ * (1 + 2 * μ * b ^ 2) * ‖a‖ ^ 2)) := by
  set Y : Ω → ℝ := fun ω => inner ℝ a (X ω) with hYdef
  have hYm : Measurable Y := by
    simp only [hYdef]
    exact (continuous_const.inner continuous_id).measurable.comp hX
  have hYb : ∀ᵐ ω ∂P, Y ω ∈ Set.Icc (-(‖a‖ * b)) (‖a‖ * b) := by
    filter_upwards [hXb] with ω hω
    have h1 := abs_real_inner_le_norm a (X ω)
    have h2 : ‖a‖ * ‖X ω‖ ≤ ‖a‖ * b := mul_le_mul_of_nonneg_left hω (norm_nonneg _)
    rw [Set.mem_Icc]
    constructor
    · linarith [neg_abs_le (Y ω)]
    · linarith [le_abs_self (Y ω)]
  have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hYm.aemeasurable hYb (hc a)
  have hmgf := hsg.mgf_le (2 * μ)
  have hint := hsg.integrable_exp_mul (2 * μ)
  have hcoef : (((‖‖a‖ * b - -(‖a‖ * b)‖₊ / 2) ^ 2 : NNReal) : ℝ) = (‖a‖ * b) ^ 2 := by
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    have : ‖a‖ * b - -(‖a‖ * b) = 2 * (‖a‖ * b) := by ring
    rw [this, abs_of_nonneg (by positivity)]
    push_cast
    ring
  rw [hcoef] at hmgf
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * ‖X ω + a‖ ^ 2)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * b ^ 2) * Real.exp (μ * ‖a‖ ^ 2)) *
          ENNReal.ofReal (Real.exp (2 * μ * Y ω)) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hXb] with ω hω
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have h4 : ‖X ω + a‖ ^ 2 = ‖X ω‖ ^ 2 + 2 * Y ω + ‖a‖ ^ 2 := by
          rw [norm_add_sq_real, real_inner_comm]
        have h3 : ‖X ω‖ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hω 2
        rw [h4]; nlinarith
    _ = ENNReal.ofReal (Real.exp (μ * b ^ 2) * Real.exp (μ * ‖a‖ ^ 2)) *
          ENNReal.ofReal (mgf Y P (2 * μ)) := by
        rw [lintegral_const_mul]
        · congr 1
          rw [mgf, ofReal_integral_eq_lintegral_ofReal hint
            (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
        · exact ENNReal.measurable_ofReal.comp
            (Real.measurable_exp.comp (measurable_const.mul hYm))
    _ ≤ ENNReal.ofReal (Real.exp (μ * b ^ 2) * Real.exp (μ * ‖a‖ ^ 2)) *
          ENNReal.ofReal (Real.exp ((‖a‖ * b) ^ 2 * (2 * μ) ^ 2 / 2)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (μ * b ^ 2) * Real.exp (μ * (1 + 2 * μ * b ^ 2) * ‖a‖ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
        congr 3
        ring

variable [SecondCountableTopology H]

/-- Sub-Gaussian bound for `‖∑ Xⱼ‖²` by induction over the summands. -/
lemma mgf_bound {ι : Type*} (X : ι → Ω → H) (hXm : ∀ j, Measurable (X j))
    (hind : iIndepFun X P)
    (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hXb : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ b j)
    (hc : ∀ j, ∀ c : H, ∫ ω, inner ℝ c (X j ω) ∂P = 0) (F : Finset ι) :
    ∀ μ : ℝ, 0 ≤ μ → μ * ∑ j ∈ F, b j ^ 2 ≤ 1 / 4 →
    ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * ‖∑ j ∈ F, X j ω‖ ^ 2)) ∂P ≤
      ENNReal.ofReal (Real.exp (2 * μ * ∑ j ∈ F, b j ^ 2)) := by
  classical
  induction F using Finset.induction_on with
  | empty => intro μ _ _; simp
  | insert i F hi ih =>
    intro μ hμ hμF
    rw [Finset.sum_insert hi] at hμF ⊢
    set S : Ω → H := fun ω => ∑ j ∈ F, X j ω with hSdef
    have hSm : Measurable S := Finset.measurable_sum F (fun j _ => hXm j)
    have hindep : IndepFun S (X i) P := by
      have := hind.indepFun_finsetSum_of_notMem hXm hi
      convert this using 1
      funext ω; simp [hSdef]
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map hSm.aemeasurable
      (hXm i).aemeasurable).1 hindep
    set σ2 := ∑ j ∈ F, b j ^ 2 with hσ2
    have hσ2nn : 0 ≤ σ2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    set μ' := μ * (1 + 2 * μ * b i ^ 2) with hμ'
    have hg : Measurable (fun z : H × H => ENNReal.ofReal (Real.exp (μ * ‖z.2 + z.1‖ ^ 2))) := by
      fun_prop
    have key : ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * ‖X i ω + S ω‖ ^ 2)) ∂P
        = ∫⁻ a, ∫⁻ x, ENNReal.ofReal (Real.exp (μ * ‖x + a‖ ^ 2)) ∂(P.map (X i)) ∂(P.map S) := by
      rw [← lintegral_prod _ hg.aemeasurable, ← hmap, lintegral_map hg (hSm.prodMk (hXm i))]
    have inner_le : ∀ a : H, ∫⁻ x, ENNReal.ofReal (Real.exp (μ * ‖x + a‖ ^ 2)) ∂(P.map (X i)) ≤
        ENNReal.ofReal (Real.exp (μ * b i ^ 2)) *
          ENNReal.ofReal (Real.exp (μ' * ‖a‖ ^ 2)) := by
      intro a
      rw [lintegral_map (by fun_prop) (hXm i), ← ENNReal.ofReal_mul (by positivity)]
      exact step a (X i) (hXm i) (b i) (hb i) (hXb i) (hc i) μ hμ
    have hμ'nn : 0 ≤ μ' := by positivity
    have hμσ : μ * σ2 ≤ 1 / 4 := by nlinarith [sq_nonneg (b i)]
    have hμ'σ : μ' * σ2 ≤ 1 / 4 := by
      have : μ' * σ2 = μ * σ2 + μ * b i ^ 2 * (2 * (μ * σ2)) := by rw [hμ']; ring
      rw [this]
      have h1 : 0 ≤ μ * b i ^ 2 := by positivity
      nlinarith
    simp_rw [Finset.sum_insert hi]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * ‖X i ω + S ω‖ ^ 2)) ∂P
        ≤ ∫⁻ a, ENNReal.ofReal (Real.exp (μ * b i ^ 2)) *
            ENNReal.ofReal (Real.exp (μ' * ‖a‖ ^ 2)) ∂(P.map S) := by
          rw [key]; exact lintegral_mono inner_le
      _ = ENNReal.ofReal (Real.exp (μ * b i ^ 2)) *
            ∫⁻ ω, ENNReal.ofReal (Real.exp (μ' * ‖S ω‖ ^ 2)) ∂P := by
          rw [lintegral_const_mul _ (by fun_prop), lintegral_map (by fun_prop) hSm]
      _ ≤ ENNReal.ofReal (Real.exp (μ * b i ^ 2)) *
            ENNReal.ofReal (Real.exp (2 * μ' * σ2)) := by
          gcongr
          exact ih μ' hμ'nn hμ'σ
      _ ≤ ENNReal.ofReal (Real.exp (2 * μ * (b i ^ 2 + σ2))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have : 2 * μ' * σ2 = 2 * (μ * σ2) + μ * b i ^ 2 * (4 * (μ * σ2)) := by rw [hμ']; ring
          rw [this]
          have h1 : 0 ≤ μ * b i ^ 2 := by positivity
          nlinarith

end Generic

lemma rpow_le_exp_aux (W μ p : ℝ) (hW : 0 ≤ W) (hμ : 0 < μ) (hp : 0 < p) :
    W ^ p ≤ (p / (2 * μ)) ^ (p / 2) * Real.exp (μ * W ^ 2) := by
  set q := p / 2 with hq
  have hq0 : 0 < q := by positivity
  set y := μ * W ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : y / q ≤ Real.exp (y / q) := by linarith [Real.add_one_le_exp (y / q)]
  have h2 : (y / q) ^ q ≤ Real.exp y := by
    calc (y / q) ^ q ≤ Real.exp (y / q) ^ q :=
          Real.rpow_le_rpow (by positivity) h1 hq0.le
      _ = Real.exp y := by rw [← Real.exp_mul]; congr 1; field_simp
  have h3 : W ^ p = (q / μ) ^ q * (y / q) ^ q := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : q / μ * (y / q) = W ^ 2 := by rw [hy]; field_simp
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hW]
    congr 1; rw [hq]; push_cast; ring
  have h4 : p / (2 * μ) = q / μ := by rw [hq]; field_simp
  rw [h3, h4]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

lemma final_real (σ p : ℝ) (hσ : 0 < σ) (hp : 1 ≤ p) :
    ((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2) * Real.exp (1 / 2)) ^ (1 / p) ≤
      6 * σ * Real.sqrt p := by
  have hp0 : 0 < p := by linarith
  rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.rpow_mul (by positivity),
    ← Real.exp_mul]
  have hpp : p / 2 * (1 / p) = 1 / 2 := by field_simp
  rw [hpp, ← Real.sqrt_eq_rpow]
  have hpm : p / (2 * (1 / (4 * σ ^ 2))) = 2 * σ ^ 2 * p := by field_simp; ring
  rw [hpm, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_sq hσ.le]
  have he : Real.exp (1 / 2 * (1 / p)) ≤ 3 := by
    have h1 : 1 / p ≤ 1 := by rw [div_le_one hp0]; exact hp
    have : 1 / 2 * (1 / p) ≤ 1 := by linarith
    calc Real.exp (1 / 2 * (1 / p)) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have he0 : 0 ≤ Real.exp (1 / 2 * (1 / p)) := (Real.exp_pos _).le
  calc Real.sqrt 2 * σ * Real.sqrt p * Real.exp (1 / 2 * (1 / p))
      ≤ 2 * σ * Real.sqrt p * 3 := by
        apply mul_le_mul _ he he0 (by positivity)
        apply mul_le_mul_of_nonneg_right _ hsp
        exact mul_le_mul_of_nonneg_right hs2 hσ.le
    _ = 6 * σ * Real.sqrt p := by ring

section Generic2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

/-- `L_p` bound for the norm of a sum of independent centered bounded Hilbert-space vectors. -/
lemma moment_bound {ι : Type*} [Fintype ι] (X : ι → Ω → H) (hXm : ∀ j, Measurable (X j))
    (hind : iIndepFun X P)
    (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hXb : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ b j)
    (hc : ∀ j, ∀ c : H, ∫ ω, inner ℝ c (X j ω) ∂P = 0) (σ : ℝ) (hσ : 0 < σ)
    (hσb : ∑ j, b j ^ 2 = σ ^ 2) (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ ω, ENNReal.ofReal ‖∑ j, X j ω‖ ^ p ∂P) ^ (1 / p) ≤
      ENNReal.ofReal (6 * σ * Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hμpos : 0 < 1 / (4 * σ ^ 2) := by positivity
  have hmgf := mgf_bound X hXm hind b hb hXb hc Finset.univ (1 / (4 * σ ^ 2)) hμpos.le
    (by rw [hσb]; field_simp; norm_num)
  rw [hσb, show 2 * (1 / (4 * σ ^ 2)) * σ ^ 2 = 1 / 2 by field_simp; norm_num] at hmgf
  have hK0 : 0 ≤ (p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2) := by positivity
  have hSm : Measurable (fun ω => ∑ j, X j ω) := Finset.measurable_sum _ (fun j _ => hXm j)
  have hL : ∫⁻ ω, ENNReal.ofReal ‖∑ j, X j ω‖ ^ p ∂P ≤
      ENNReal.ofReal ((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2) * Real.exp (1 / 2)) := by
    calc ∫⁻ ω, ENNReal.ofReal ‖∑ j, X j ω‖ ^ p ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal ((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2)) *
            ENNReal.ofReal (Real.exp (1 / (4 * σ ^ 2) * ‖∑ j, X j ω‖ ^ 2)) ∂P := by
          apply lintegral_mono
          intro ω
          dsimp only
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le, ← ENNReal.ofReal_mul hK0]
          exact ENNReal.ofReal_le_ofReal (rpow_le_exp_aux _ _ p (norm_nonneg _) hμpos hp0)
      _ = ENNReal.ofReal ((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2)) *
            ∫⁻ ω, ENNReal.ofReal (Real.exp (1 / (4 * σ ^ 2) * ‖∑ j, X j ω‖ ^ 2)) ∂P := by
          rw [lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (measurable_const.mul (hSm.norm.pow_const 2)))
      _ ≤ ENNReal.ofReal ((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2)) *
            ENNReal.ofReal (Real.exp (1 / 2)) := by gcongr
      _ = ENNReal.ofReal ((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2) * Real.exp (1 / 2)) :=
          (ENNReal.ofReal_mul hK0).symm
  have hpinv : 0 ≤ 1 / p := by positivity
  calc (∫⁻ ω, ENNReal.ofReal ‖∑ j, X j ω‖ ^ p ∂P) ^ (1 / p)
      ≤ ENNReal.ofReal ((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2) * Real.exp (1 / 2)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hL hpinv
    _ = ENNReal.ofReal (((p / (2 * (1 / (4 * σ ^ 2)))) ^ (p / 2) * Real.exp (1 / 2)) ^ (1 / p)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hpinv
    _ ≤ ENNReal.ofReal (6 * σ * Real.sqrt p) := ENNReal.ofReal_le_ofReal (final_real σ p hσ hp)

end Generic2

/-- The main case `B > 0`, `‖T‖_F > 0`. -/
lemma main_case {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k s r : ℕ) (V : Fin s → Ω → EuclideanSpace ℝ (Fin k))
    (hVm : ∀ j, Measurable (V j)) (hVind : iIndepFun V P) (hV0 : ∀ j, ∫ ω, V j ω ∂P = 0)
    (B : ℝ) (hVB : ∀ j, ∀ᵐ ω ∂P, ‖V j ω‖ ≤ B) (T : Matrix (Fin r) (Fin s) ℝ) (p : ℝ)
    (hp : 1 ≤ p) (hB : 0 < B) (hτ : 0 < Real.sqrt (∑ i, ∑ j, T i j ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.sqrt (∑ i, ‖∑ j, T i j • V j ω‖ ^ 2)) ^ p ∂P) ^ (1 / p) ≤
      ENNReal.ofReal (6 * B * Real.sqrt (∑ i, ∑ j, T i j ^ 2) * Real.sqrt p) := by
  let X : Fin s → Ω → PiLp 2 (fun _ : Fin r => EuclideanSpace ℝ (Fin k)) :=
    fun j ω => WithLp.toLp 2 (fun i => T i j • V j ω)
  let g : Fin s → EuclideanSpace ℝ (Fin k) → PiLp 2 (fun _ : Fin r => EuclideanSpace ℝ (Fin k)) :=
    fun j v => WithLp.toLp 2 (fun i => T i j • v)
  have hgm : ∀ j, Measurable (g j) := fun j =>
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_lambda _ (fun i => measurable_id.const_smul (T i j)))
  have hXm : ∀ j, Measurable (X j) := fun j => (hgm j).comp (hVm j)
  have hXind : iIndepFun X P := hVind.comp g hgm
  have hnormX : ∀ j ω, ‖X j ω‖ ^ 2 = (∑ i, T i j ^ 2) * ‖V j ω‖ ^ 2 := by
    intro j ω
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [X, norm_smul, mul_pow]
  have hcol : ∀ j, 0 ≤ ∑ i, T i j ^ 2 := fun j => Finset.sum_nonneg (fun i _ => sq_nonneg (T i j))
  let b : Fin s → ℝ := fun j => B * Real.sqrt (∑ i, T i j ^ 2)
  have hb : ∀ j, 0 ≤ b j := fun j => by positivity
  have hXb : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ b j := by
    intro j
    filter_upwards [hVB j] with ω hω
    have h1 : ‖X j ω‖ ^ 2 ≤ b j ^ 2 := by
      rw [hnormX]
      simp only [b]
      rw [mul_pow, Real.sq_sqrt (hcol j)]
      have : ‖V j ω‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hω 2
      nlinarith [hcol j]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hb j) (by norm_num)).1 h1
  have hc : ∀ j, ∀ c : PiLp 2 (fun _ : Fin r => EuclideanSpace ℝ (Fin k)),
      ∫ ω, inner ℝ c (X j ω) ∂P = 0 := by
    intro j c
    have hint : Integrable (V j) P :=
      Integrable.of_bound (hVm j).aestronglyMeasurable B (hVB j)
    have : ∀ ω, inner ℝ c (X j ω) = ∑ i, T i j * inner ℝ (c i) (V j ω) := by
      intro ω
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [X, real_inner_smul_right]
    simp_rw [this]
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [integral_const_mul, integral_inner hint, hV0 j, inner_zero_right, mul_zero]
    · intro i _
      exact (hint.const_inner (c i)).const_mul _
  have hσb : ∑ j, b j ^ 2 = (B * Real.sqrt (∑ i, ∑ j, T i j ^ 2)) ^ 2 := by
    have htot : 0 ≤ ∑ i, ∑ j, T i j ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (T i j)))
    rw [mul_pow, Real.sq_sqrt htot, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [b]
    rw [mul_pow, Real.sq_sqrt (hcol j)]
  have hWeq : ∀ ω, Real.sqrt (∑ i, ‖∑ j, T i j • V j ω‖ ^ 2) = ‖∑ j, X j ω‖ := by
    intro ω
    rw [← Real.sqrt_sq (norm_nonneg (∑ j, X j ω)), PiLp.norm_sq_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [hWeq]
  have := moment_bound X hXm hXind b hb hXb hc (B * Real.sqrt (∑ i, ∑ j, T i j ^ 2))
    (by positivity) hσb p hp
  rw [show 6 * B * Real.sqrt (∑ i, ∑ j, T i j ^ 2) * Real.sqrt p =
    6 * (B * Real.sqrt (∑ i, ∑ j, T i j ^ 2)) * Real.sqrt p by ring]
  exact this

end HiddenCorrL12

open HiddenCorrL12 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k s r : ℕ)
        (V : Fin s → Ω → EuclideanSpace ℝ (Fin k)),
        (∀ j, Measurable (V j)) → iIndepFun V P → (∀ j, ∫ ω, V j ω ∂P = 0) →
        ∀ B : ℝ, (∀ j, ∀ᵐ ω ∂P, ‖V j ω‖ ≤ B) →
        ∀ (T : Matrix (Fin r) (Fin s) ℝ) (p : ℝ), 1 ≤ p →
          (∫⁻ ω, ENNReal.ofReal (Real.sqrt (∑ i, ‖∑ j, T i j • V j ω‖ ^ 2)) ^ p ∂P) ^ (1 / p) ≤
            ENNReal.ofReal (C * B * Real.sqrt (∑ i, ∑ j, T i j ^ 2) * Real.sqrt p) := by
  refine ⟨6, by norm_num, ?_⟩
  intro Ω _ P _ k s r V hVm hVind hV0 B hVB T p hp
  have hp0 : 0 < p := by linarith
  by_cases hσ : 0 < B ∧ 0 < Real.sqrt (∑ i, ∑ j, T i j ^ 2)
  · exact main_case P k s r V hVm hVind hV0 B hVB T p hp hσ.1 hσ.2
  · have hW0 : ∀ᵐ ω ∂P, Real.sqrt (∑ i, ‖∑ j, T i j • V j ω‖ ^ 2) = 0 := by
      rcases not_and_or.1 hσ with hB | hτ0
      · have : ∀ᵐ ω ∂P, ∀ j, V j ω = 0 := ae_all_iff.2 (fun j => (hVB j).mono
          (fun ω h => norm_le_zero_iff.1 (h.trans (not_lt.1 hB))))
        filter_upwards [this] with ω h
        simp [h]
      · have hsum : ∑ i, ∑ j, T i j ^ 2 ≤ 0 :=
          Real.sqrt_eq_zero'.1 (le_antisymm (not_lt.1 hτ0) (Real.sqrt_nonneg _))
        have h1 : ∑ i, ∑ j, T i j ^ 2 = 0 := le_antisymm hsum
          (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (T i j))))
        have hT : ∀ i j, T i j = 0 := by
          intro i j
          have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
            Finset.sum_nonneg (fun j _ => sq_nonneg (T i j)))).1 h1 i (Finset.mem_univ _)
          have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
            sq_nonneg (T i j))).1 h2 j (Finset.mem_univ _)
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
        exact ae_of_all _ (fun ω => by simp [hT])
    have : ∫⁻ ω, ENNReal.ofReal (Real.sqrt (∑ i, ‖∑ j, T i j • V j ω‖ ^ 2)) ^ p ∂P = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hW0] with ω h
        rw [h, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp0]
    rw [this, ENNReal.zero_rpow_of_pos (by positivity)]
    exact bot_le
