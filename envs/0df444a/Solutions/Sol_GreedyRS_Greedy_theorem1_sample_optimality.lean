-- Prove2me | solution 1 for GreedyRS.Greedy.theorem1_sample_optimality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:11:49.263328+00:00
-- url     : https://prove2.me/submissions/e9369d7a-be92-4769-807a-f88a1bbc7fce

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
import Theorems.Thm_GreedyRS_Greedy_ec1_5_liminf_bound
import Theorems.Thm_GreedyRS_Greedy_lemma1_argmin_finite
import Theorems.Thm_GreedyRS_Greedy_eq4_3_min_prob
import Theorems.Thm_GreedyRS_Greedy_lemma2_Cfun_strictAnti_continuous
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace G11
open GreedyRS.Greedy

lemma iInf_coe_eq_iff (p : ℕ → Prop) (m : ℕ) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = m ↔ p m ∧ ∀ n, p n → m ≤ n := by
  constructor
  · intro h
    have hle : ∀ n, p n → m ≤ n := by
      intro n hn
      have : (m : ℕ∞) ≤ n := h ▸ iInf₂_le n hn
      exact_mod_cast this
    refine ⟨?_, hle⟩
    by_contra hpm
    have : ((m + 1 : ℕ) : ℕ∞) ≤ ⨅ (n : ℕ) (_ : p n), (n : ℕ∞) := by
      refine le_iInf₂ fun n hn => ?_
      have h1 := hle n hn
      have h2 : n ≠ m := fun h => hpm (h ▸ hn)
      exact_mod_cast (show m + 1 ≤ n by omega)
    rw [h] at this
    have : m + 1 ≤ m := by exact_mod_cast this
    omega
  · rintro ⟨hpm, hle⟩
    apply le_antisymm
    · exact iInf₂_le m hpm
    · exact le_iInf₂ fun n hn => by exact_mod_cast hle n hn

lemma iInf_coe_eq_top_iff (p : ℕ → Prop) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = ⊤ ↔ ∀ n, ¬ p n := by
  simp only [iInf_eq_top, ENat.coe_ne_top, imp_false]

lemma meas_hit {α : Type*} [MeasurableSpace α] (p : α → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {a | p a n}) :
    Measurable fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞) := by
  apply measurable_to_countable'
  intro N
  induction N using ENat.recTopCoe with
  | top =>
    have : (fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞)) ⁻¹' {⊤} = ⋂ n, {a | p a n}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff]
      rw [iInf_coe_eq_top_iff]; rfl
    rw [this]; exact MeasurableSet.iInter fun n => (hp n).compl
  | coe m =>
    have : (fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞)) ⁻¹' {(m : ℕ∞)} =
        {a | p a m} ∩ ⋂ n ∈ Finset.range m, {a | p a n}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_range]
      rw [iInf_coe_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hn hpn => ?_⟩
        have := h2 n hpn; omega
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hpn => ?_⟩
        by_contra hlt
        exact h2 n (by omega) hpn
    rw [this]
    exact (hp m).inter (MeasurableSet.biInter (Finset.range m).countable_toSet
      fun n _ => (hp n).compl)

lemma meas_crossTime (x : ℝ) : Measurable fun z : ℕ → ℝ => crossTime x 1 z := by
  unfold crossTime
  apply meas_hit (fun z n => 1 ≤ n ∧ zbar z n < x)
  intro n
  show MeasurableSet ({z : ℕ → ℝ | 1 ≤ n} ∩ {z | zbar z n < x})
  refine (MeasurableSet.const _).inter (measurableSet_lt ?_ measurable_const)
  unfold zbar
  exact (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).div_const _

/-- Standardisation of a row turns `crossBelow` of its running mean into `crossTime`. -/
lemma crossBelow_eq_crossTime (x : ℕ → ℝ) (m L σ : ℝ) (hσ : 0 < σ) :
    crossBelow (fun n => (∑ j ∈ Finset.range n, x j) / n) L 1 =
      crossTime ((L - m) / σ) 1 (fun j => (x j - m) / σ) := by
  unfold crossBelow crossTime
  refine iInf_congr fun n => iInf_congr_Prop ?_ (fun _ => rfl)
  · constructor
    · rintro ⟨hn, h⟩
      refine ⟨hn, ?_⟩
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      unfold zbar
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, div_div, div_lt_div_iff₀ (by positivity) hσ]
      rw [div_lt_iff₀ hn'] at h
      nlinarith
    · rintro ⟨hn, h⟩
      refine ⟨hn, ?_⟩
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      unfold zbar at h
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, div_div, div_lt_div_iff₀ (by positivity) hσ] at h
      rw [div_lt_iff₀ hn']
      nlinarith

lemma gauss_standardize (m : ℝ) (w : ℝ≥0) (hw : 0 < w) :
    (gaussianReal m w).map (fun t => (t - m) / Real.sqrt w) = gaussianReal 0 1 := by
  have hσ : 0 < Real.sqrt w := Real.sqrt_pos.2 (by exact_mod_cast hw)
  have : (fun t => (t - m) / Real.sqrt w) = (fun t => t / Real.sqrt w) ∘ (fun t => t - m) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
    gaussianReal_map_div_const]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt (NNReal.coe_nonneg w)]
    exact div_self (by exact_mod_cast hw.ne')

variable {Ω : Type*} [MeasurableSpace Ω]

lemma rows_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) :
    P.map (fun ω i j => X i j ω) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun _ : ℕ => gaussianReal (μ i) (v i))) := by
  have hjm : Measurable (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) :=
    measurable_pi_lambda _ fun p => hX.meas p.1 p.2
  have hjoint : P.map (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) =
      Measure.infinitePi (fun p : ℕ × ℕ => gaussianReal (μ p.1) (v p.1)) := by
    have h := hX.indep.map_fun_eq_infinitePi_map (fun p : ℕ × ℕ => hX.meas p.1 p.2)
    rw [h]
    congr 1; ext1 p; exact hX.law p.1 p.2
  have hcomp : (fun ω i j => X i j ω) =
      (MeasurableEquiv.curry ℕ ℕ ℝ) ∘ (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) := by
    ext ω i j; rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.curry ℕ ℕ ℝ).measurable hjm, hjoint]
  exact Measure.infinitePi_map_curry (fun i (_ : ℕ) => gaussianReal (μ i) (v i))

lemma row_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (i : ℕ) :
    P.map (fun ω j => X i j ω) = Measure.infinitePi (fun _ : ℕ => gaussianReal (μ i) (v i)) := by
  have hrm : Measurable (fun ω i j => X i j ω) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hX.meas i j
  have : (fun ω j => X i j ω) = (fun f : ℕ → ℕ → ℝ => f i) ∘ (fun ω i j => X i j ω) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply i) hrm, rows_law P μ v X hX,
    Measure.infinitePi_map_eval]

lemma rows_indep (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) :
    iIndepFun (fun i ω j => X i j ω) P := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_lambda _ fun j => hX.meas i j)]
  rw [rows_law P μ v X hX]
  congr 1; ext1 i
  exact (row_law P μ v X hX i).symm

end G11

namespace G2C
open GreedyRS.Greedy

lemma Phi_mono : Monotone Phi := fun _ _ h => (cdf (gaussianReal 0 1)).mono h

lemma Phi_strictMono : StrictMono Phi := by
  intro a b hab
  have h1 : Phi b - Phi a = (gaussianReal 0 1).real (Set.Ioc a b) := by
    simp only [Phi, cdf_eq_real]
    have hI : Set.Ioc a b = Set.Iic b \ Set.Iic a := by
      ext x; simp only [Set.mem_Ioc, Set.mem_diff, Set.mem_Iic, not_le]; tauto
    rw [hI, measureReal_diff (Set.Iic_subset_Iic.2 hab.le) measurableSet_Iic]
  have h2 : 0 < (gaussianReal 0 1).real (Set.Ioc a b) := by
    have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
      intro h0
      have := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h0
      simp [Real.volume_Ioc] at this
      linarith
    exact ENNReal.toReal_pos hpos (measure_ne_top _ _)
  linarith

lemma Phi_continuous : Continuous Phi := by
  set f := cdf (gaussianReal 0 1) with hf
  have hmono : Monotone f := f.mono
  rw [continuous_iff_continuousAt]
  intro a
  have hsing : f.measure {a} = 0 := by
    rw [hf, measure_cdf]
    have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
    exact gaussianReal_absolutelyContinuous (0 : ℝ) hv (Real.volume_singleton)
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  have hle : Function.leftLim f a ≤ f a := hmono.leftLim_le le_rfl
  have heq : Function.leftLim f a = f a := le_antisymm hle (by linarith)
  have hleft : ContinuousWithinAt f (Set.Iio a) a :=
    (hmono.continuousWithinAt_Iio_iff_leftLim_eq).2 heq
  have hright : ContinuousWithinAt f (Set.Ici a) a := f.right_continuous a
  exact continuousAt_iff_continuous_left'_right'.2 ⟨hleft, hright.mono Set.Ioi_subset_Ici_self⟩

lemma Phi_nonneg (t : ℝ) : 0 ≤ Phi t := cdf_nonneg _ _

lemma Phi_neg_le (s : ℝ) (hs : 0 ≤ s) : Phi (-s) ≤ Real.exp (-(s ^ 2) / 2) := by
  have hint : Integrable (fun x : ℝ => Real.exp (-s * id x)) (gaussianReal 0 1) := by
    exact integrable_exp_mul_gaussianReal (-s)
  have := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := -s) (-s)
    (by linarith) hint
  rw [mgf_id_gaussianReal] at this
  simp only [Phi, cdf_eq_real]
  have hset : {ω : ℝ | id ω ≤ -s} = Set.Iic (-s) := by ext; simp
  rw [hset] at this
  refine this.trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Uniform bound on the terms for `x ≥ θ > 0`. -/
lemma term_bound (θ x : ℝ) (hθ : 0 < θ) (hx : θ ≤ x) (n : ℕ) :
    ‖Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1)‖ ≤
      Real.exp (-(θ ^ 2) / 2) ^ (n + 1) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsq : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Phi_nonneg _) hn1.le)]
  have h1 : Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) ≤ Phi (-(Real.sqrt ((n : ℝ) + 1) * θ)) := by
    apply Phi_mono
    nlinarith
  have h2 := Phi_neg_le (Real.sqrt ((n : ℝ) + 1) * θ) (by positivity)
  have h3 : Real.exp (-((Real.sqrt ((n : ℝ) + 1) * θ) ^ 2) / 2) =
      Real.exp (-(θ ^ 2) / 2) ^ (n + 1) := by
    rw [← Real.exp_nat_mul, mul_pow, Real.sq_sqrt hn1.le]
    congr 1; push_cast; ring
  calc Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1)
      ≤ Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) :=
        div_le_self (Phi_nonneg _) (by linarith)
    _ ≤ _ := h1.trans (h2.trans h3.le)

lemma summable_geom (θ : ℝ) (hθ : 0 < θ) :
    Summable fun n : ℕ => Real.exp (-(θ ^ 2) / 2) ^ (n + 1) := by
  have hr : Real.exp (-(θ ^ 2) / 2) < 1 := by
    rw [Real.exp_lt_one_iff]; have := sq_pos_of_pos hθ; linarith
  have h := summable_geometric_of_lt_one (Real.exp_pos _).le hr
  exact (summable_nat_add_iff 1).2 h

lemma summable_terms (x : ℝ) (hx : 0 < x) :
    Summable fun n : ℕ => Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1) :=
  Summable.of_norm_bounded (summable_geom x hx) (fun n => term_bound x x hx le_rfl n)

theorem Cfun_strictAnti_continuous :
    StrictAntiOn Cfun (Set.Ioi 0) ∧ ContinuousOn Cfun (Set.Ioi 0) := by
  constructor
  · intro x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    unfold Cfun
    rw [Real.exp_lt_exp]
    refine Summable.tsum_lt_tsum (i := 0) ?_ ?_ (summable_terms y hy) (summable_terms x hx)
    · intro n
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hsq : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
      apply div_le_div_of_nonneg_right _ hn1.le
      apply Phi_mono
      nlinarith
    · simp only [CharP.cast_eq_zero, zero_add, Real.sqrt_one, neg_mul, one_mul, div_one]
      exact Phi_strictMono (by linarith)
  · intro x hx
    simp only [Set.mem_Ioi] at hx
    have hθ : 0 < x / 2 := by linarith
    have hcont : ContinuousOn (fun y => ∑' n : ℕ,
        Phi (-(Real.sqrt ((n : ℝ) + 1)) * y) / ((n : ℝ) + 1)) (Set.Ici (x / 2)) := by
      refine continuousOn_tsum (fun n => ?_) (summable_geom (x / 2) hθ) ?_
      · exact ((Phi_continuous.comp (continuous_const.mul continuous_id)).div_const _).continuousOn
      · intro n y hy
        exact term_bound (x / 2) y hθ hy n
    have hca : ContinuousAt (fun y => ∑' n : ℕ,
        Phi (-(Real.sqrt ((n : ℝ) + 1)) * y) / ((n : ℝ) + 1)) x :=
      hcont.continuousAt (Ici_mem_nhds (by linarith))
    exact (Real.continuous_exp.continuousAt.comp hca).continuousWithinAt

end G2C

namespace G15
open GreedyRS.Greedy

/-- `C(x) → ∞` as `x → 0+`: `C` exceeds any level at some point of `(0, X)`. -/
lemma Cfun_large (M X : ℝ) (hX : 0 < X) : ∃ x ∈ Set.Ioo 0 X, M < Cfun x := by
  set p := Phi (-1) with hp
  have hp0 : 0 < p := lt_of_le_of_lt (G2C.Phi_nonneg (-2)) (G2C.Phi_strictMono (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop (Real.log (max M 1) / p))
  set N' := N + 1 with hN'
  have hS := hN N' (by omega)
  set x := min (X / 2) (1 / Real.sqrt N') with hx
  have hsqN : 0 < Real.sqrt N' := Real.sqrt_pos.2 (by positivity)
  have hx0 : 0 < x := lt_min (by linarith) (by positivity)
  have hxX : x < X := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨x, ⟨hx0, hxX⟩, ?_⟩
  have hterm : ∀ n ∈ Finset.range N', p * (1 / ((n : ℝ) + 1)) ≤
      Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1) := by
    intro n hn
    have hn' : (n : ℝ) + 1 ≤ N' := by
      have := Finset.mem_range.1 hn; exact_mod_cast (show n + 1 ≤ N' by omega)
    have h1 : Real.sqrt ((n : ℝ) + 1) * x ≤ 1 := by
      calc Real.sqrt ((n : ℝ) + 1) * x ≤ Real.sqrt N' * (1 / Real.sqrt N') := by
            apply mul_le_mul (Real.sqrt_le_sqrt hn') (min_le_right _ _) hx0.le hsqN.le
        _ = 1 := by field_simp
    have h2 : p ≤ Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) := G2C.Phi_mono (by linarith)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hsum : p * ∑ n ∈ Finset.range N', (1 / ((n : ℝ) + 1)) ≤
      ∑' n : ℕ, Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    refine Summable.sum_le_tsum _ (fun n _ => ?_) (G2C.summable_terms x hx0)
    exact div_nonneg (G2C.Phi_nonneg _) (by positivity)
  have hlog : Real.log (max M 1) < ∑' n : ℕ, Phi (-(Real.sqrt ((n : ℝ) + 1)) * x) / ((n : ℝ) + 1) := by
    have : Real.log (max M 1) < p * ∑ n ∈ Finset.range N', (1 / ((n : ℝ) + 1)) := by
      rw [div_lt_iff₀ hp0] at hS; linarith
    linarith
  unfold Cfun
  calc M ≤ max M 1 := le_max_left _ _
    _ = Real.exp (Real.log (max M 1)) := (Real.exp_log (by positivity)).symm
    _ < _ := Real.exp_lt_exp.2 hlog

/-- Existence of a level: `C((γ - γ')/σ̄) = a` for some `γ' ∈ (0, γ)` whenever `a > C(γ/σ̄)`. -/
lemma exists_level (γ σbar a : ℝ) (hγ : 0 < γ) (hσ : 0 < σbar) (ha : Cfun (γ / σbar) < a)
    (hcont : ContinuousOn Cfun (Set.Ioi 0)) :
    ∃ γ' ∈ Set.Ioo 0 γ, Cfun ((γ - γ') / σbar) = a := by
  have hX : 0 < γ / σbar := div_pos hγ hσ
  obtain ⟨x1, ⟨hx1, hx1X⟩, hCx1⟩ := Cfun_large a (γ / σbar) hX
  have hc : ContinuousOn Cfun (Set.Icc x1 (γ / σbar)) :=
    hcont.mono fun t ht => lt_of_lt_of_le hx1 ht.1
  obtain ⟨x, hx, hCx⟩ := intermediate_value_Icc' hx1X.le hc ⟨ha.le, hCx1.le⟩
  have hxne : x ≠ γ / σbar := by rintro rfl; linarith
  have hxlt : x < γ / σbar := lt_of_le_of_ne hx.2 hxne
  have hxpos : 0 < x := lt_of_lt_of_le hx1 hx.1
  refine ⟨γ - σbar * x, ⟨?_, ?_⟩, ?_⟩
  · rw [lt_div_iff₀ hσ] at hxlt; nlinarith
  · nlinarith
  · have : (γ - (γ - σbar * x)) / σbar = x := by field_simp; ring
    rw [this, hCx]

end G15

namespace G1
open GreedyRS.Greedy

lemma levels (C : ℝ → ℝ) (hanti : StrictAntiOn C (Set.Ioi 0)) (hcont : ContinuousOn C (Set.Ioi 0))
    (X x0 : ℝ) (hx0 : 0 < x0) (hX : x0 < X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < x0)
    (hδ2 : x0 + δ < X) :
    ∃ ε : ℝ, 0 < 2 * ε ∧ 2 * ε < C x0 - C X ∧
      (∃ xm ∈ Set.Ioo x0 (x0 + δ), C xm = C x0 - 2 * ε) ∧
      (∃ xp ∈ Set.Ioo (x0 - δ) x0, C xp = C x0 + 2 * ε) := by
  have hmem : ∀ t, 0 < t → t ∈ Set.Ioi (0 : ℝ) := fun t ht => ht
  have hL : C x0 < C (x0 - δ) := hanti (hmem _ (by linarith)) (hmem _ hx0) (by linarith)
  have hR : C (x0 + δ) < C x0 := hanti (hmem _ hx0) (hmem _ (by linarith)) (by linarith)
  have hXX : C X < C x0 := hanti (hmem _ hx0) (hmem _ (by linarith)) hX
  set ε := min (min (C (x0 - δ) - C x0) (C x0 - C (x0 + δ))) (C x0 - C X) / 4 with hε
  have hεpos : 0 < ε := by
    rw [hε]; apply div_pos _ (by norm_num)
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have h1 : ε ≤ (C (x0 - δ) - C x0) / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (min_le_left _ _).trans (min_le_left _ _)
  have h2 : ε ≤ (C x0 - C (x0 + δ)) / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (min_le_left _ _).trans (min_le_right _ _)
  have h3 : ε ≤ (C x0 - C X) / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_right _ (by norm_num)
    exact min_le_right _ _
  refine ⟨ε, by linarith, by linarith, ?_, ?_⟩
  · have hc : ContinuousOn C (Set.Icc x0 (x0 + δ)) :=
      hcont.mono fun t ht => hmem _ (by linarith [ht.1])
    obtain ⟨xm, hxm, hCxm⟩ := intermediate_value_Icc' (by linarith) hc
      (show C x0 - 2 * ε ∈ Set.Icc (C (x0 + δ)) (C x0) from ⟨by linarith, by linarith⟩)
    refine ⟨xm, ⟨lt_of_le_of_ne hxm.1 ?_, lt_of_le_of_ne hxm.2 ?_⟩, hCxm⟩
    · rintro rfl; linarith
    · rintro rfl; linarith
  · have hc : ContinuousOn C (Set.Icc (x0 - δ) x0) :=
      hcont.mono fun t ht => hmem _ (by linarith [ht.1])
    obtain ⟨xp, hxp, hCxp⟩ := intermediate_value_Icc' (by linarith) hc
      (show C x0 + 2 * ε ∈ Set.Icc (C x0) (C (x0 - δ)) from ⟨by linarith, by linarith⟩)
    refine ⟨xp, ⟨lt_of_le_of_ne hxp.1 ?_, lt_of_le_of_ne hxp.2 ?_⟩, hCxp⟩
    · rintro rfl; linarith
    · rintro rfl; linarith

/-- `min_{n ≥ 1} y(n) > a` iff some `b > a` is a lower bound (rational `b` suffices). -/
lemma aboveFrom_iff_rat (y : ℕ → ℝ) (a : ℝ) :
    AboveFrom y 1 a ↔ ∃ q : ℚ, a < q ∧ ∀ n, (q : ℝ) ≤ y (1 + n) := by
  constructor
  · rintro ⟨hb, ha⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha
    exact ⟨q, hq1, fun n => hq2.le.trans (ciInf_le hb n)⟩
  · rintro ⟨q, hq, hle⟩
    refine ⟨⟨q, by rintro _ ⟨n, rfl⟩; exact hle n⟩, lt_of_lt_of_le hq (le_ciInf hle)⟩

lemma meas_zbar (n : ℕ) : Measurable fun z : ℕ → ℝ => zbar z n := by
  unfold zbar
  exact (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).div_const _

lemma meas_above (x : ℝ) : MeasurableSet {z : ℕ → ℝ | AboveFrom (zbar z) 1 x} := by
  have : {z : ℕ → ℝ | AboveFrom (zbar z) 1 x} =
      ⋃ q : ℚ, ({z : ℕ → ℝ | x < q} ∩ ⋂ n : ℕ, {z | (q : ℝ) ≤ zbar z (1 + n)}) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    exact aboveFrom_iff_rat _ _
  rw [this]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
    (MeasurableSet.iInter fun n => measurableSet_le measurable_const (meas_zbar _))

lemma meas_argmin_top : MeasurableSet {z : ℕ → ℝ | argminFrom (zbar z) 1 = ⊤} := by
  have hm : Measurable fun z : ℕ → ℝ => argminFrom (zbar z) 1 := by
    unfold argminFrom
    apply G11.meas_hit (fun z m => 1 ≤ m ∧ ∀ n, 1 ≤ n → zbar z m ≤ zbar z n)
    intro m
    have : {z : ℕ → ℝ | 1 ≤ m ∧ ∀ n, 1 ≤ n → zbar z m ≤ zbar z n} =
        {z | 1 ≤ m} ∩ ⋂ n : ℕ, ({z : ℕ → ℝ | 1 ≤ n}ᶜ ∪ {z | zbar z m ≤ zbar z n}) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
        Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun n => by by_cases hn : 1 ≤ n <;> simp [hn, h2]⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun n hn => (h2 n).resolve_left (by simp [hn])⟩
    rw [this]
    exact (MeasurableSet.const _).inter (MeasurableSet.iInter fun n =>
      (MeasurableSet.const _).compl.union (measurableSet_le (meas_zbar _) (meas_zbar _)))
  exact hm (MeasurableSet.singleton _)

/-- Running mean of a row versus the standardised running mean. -/
lemma runMean_std (x : ℕ → ℝ) (m s : ℝ) (hs : 0 < s) (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ Finset.range n, x j) / n = m + s * zbar (fun j => (x j - m) / s) n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold zbar
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

lemma above_std (x : ℕ → ℝ) (m s a : ℝ) (hs : 0 < s) :
    AboveFrom (fun n => (∑ j ∈ Finset.range n, x j) / n) 1 a ↔
      AboveFrom (zbar (fun j => (x j - m) / s)) 1 ((a - m) / s) := by
  rw [aboveFrom_iff_rat, aboveFrom_iff_rat]
  have key : ∀ n, (∑ j ∈ Finset.range (1 + n), x j) / ((1 + n : ℕ) : ℝ) =
      m + s * zbar (fun j => (x j - m) / s) (1 + n) := fun n => runMean_std x m s hs _ (by omega)
  constructor
  · rintro ⟨q, hq, hle⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (a - m) / s < (q - m) / s from
      div_lt_div_of_pos_right (by linarith) hs)
    refine ⟨r, hr1, fun n => ?_⟩
    have h1 := hle n
    simp only [Nat.cast_add, Nat.cast_one] at h1 key
    rw [key n] at h1
    have : (q - m) / s ≤ zbar (fun j => (x j - m) / s) (1 + n) := by
      rw [div_le_iff₀ hs]; linarith
    linarith
  · rintro ⟨q, hq, hle⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show a < m + s * q by
      rw [div_lt_iff₀ hs] at hq; linarith)
    refine ⟨r, hr1, fun n => ?_⟩
    have h1 := hle n
    have h2 := key n
    simp only [Nat.cast_add, Nat.cast_one] at h2
    show (r : ℝ) ≤ (∑ j ∈ Finset.range (1 + n), x j) / ((1 + n : ℕ) : ℝ)
    push_cast
    rw [h2]
    nlinarith

lemma argmin_std (x : ℕ → ℝ) (m s : ℝ) (hs : 0 < s) :
    argminFrom (fun n => (∑ j ∈ Finset.range n, x j) / n) 1 =
      argminFrom (zbar (fun j => (x j - m) / s)) 1 := by
  unfold argminFrom
  refine iInf_congr fun k => iInf_congr_Prop ?_ (fun _ => rfl)
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun n hn => ?_⟩
    have := h n hn
    simp only at this
    rw [runMean_std x m s hs k hk, runMean_std x m s hs n hn] at this
    nlinarith
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun n hn => ?_⟩
    show (∑ j ∈ Finset.range k, x j) / (k : ℝ) ≤ (∑ j ∈ Finset.range n, x j) / (n : ℝ)
    rw [runMean_std x m s hs k hk, runMean_std x m s hs n hn]
    nlinarith [h n hn]

end G1

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / σbar) < c) :
    (∃ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / σbar) = c) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / σbar) = c →
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          ≤ Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k 1 ⌊c * k⌋₊) Filter.atTop ∧
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          = ENNReal.ofReal (1 / GreedyRS.Greedy.Cfun (γ0 / Real.sqrt (v 0))) ∧
      0 < P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)} := by
  open GreedyRS.Greedy in
  obtain ⟨hanti, hcont⟩ := GreedyRS.Greedy.lemma2_Cfun_strictAnti_continuous
  refine ⟨G15.exists_level γ σbar c hγ hσbar hc hcont, fun γ0 hγ0 hC0 => ?_⟩
  -- standardisation of the best row
  set σ0 := Real.sqrt (v 0) with hσ0def
  have hσ0 : 0 < σ0 := Real.sqrt_pos.2 (by exact_mod_cast hv 0)
  set Z0 : Ω → (ℕ → ℝ) := fun ω j => (X 0 j ω - μ 0) / σ0 with hZ0
  have hφm : Measurable (fun (y : ℕ → ℝ) (j : ℕ) => (y j - μ 0) / σ0) :=
    measurable_pi_lambda _ fun j => ((measurable_pi_apply j).sub_const _).div_const _
  have hRm : Measurable (fun ω (j : ℕ) => X 0 j ω) := measurable_pi_lambda _ fun j => hX.meas 0 j
  have hZ0m : Measurable Z0 := hφm.comp hRm
  have hZ0law : P.map Z0 = stdNormalSeq := by
    have : Z0 = (fun (y : ℕ → ℝ) (j : ℕ) => (y j - μ 0) / σ0) ∘ (fun ω (j : ℕ) => X 0 j ω) := rfl
    rw [this, ← Measure.map_map hφm hRm, G11.row_law P μ v X hX 0]
    have h := Measure.infinitePi_map_pi (fun _ : ℕ => gaussianReal (μ 0) (v 0))
      (f := fun (_ : ℕ) (t : ℝ) => (t - μ 0) / σ0) (fun _ => by fun_prop)
    refine h.trans ?_
    unfold stdNormalSeq
    congr 1; ext1 j
    exact G11.gauss_standardize _ _ (hv 0)
  have hPA : ∀ a : ℝ, P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 a} =
      stdNormalSeq {z | AboveFrom (zbar z) 1 ((a - μ 0) / σ0)} := by
    intro a
    have hset : {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 a} =
        Z0 ⁻¹' {z | AboveFrom (zbar z) 1 ((a - μ 0) / σ0)} := by
      ext ω
      exact G1.above_std (fun j => X 0 j ω) (μ 0) σ0 a hσ0
    rw [hset, ← Measure.map_apply hZ0m (G1.meas_above _), hZ0law]
  have heq : P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)} =
      ENNReal.ofReal (1 / Cfun (γ0 / σ0)) := by
    rw [hPA]
    have h1 : (μ 0 - γ0 - μ 0) / σ0 = -(γ0 / σ0) := by ring
    rw [h1, (GreedyRS.Greedy.eq4_3_min_prob (-(γ0 / σ0))
      (neg_neg_of_pos (div_pos hγ0.1 hσ0))).2, neg_neg]
  have hNn : P {ω | argminFrom (runMean (fun i j => X i j ω) 0) 1 = ⊤} = 0 := by
    have hset : {ω | argminFrom (runMean (fun i j => X i j ω) 0) 1 = ⊤} =
        Z0 ⁻¹' {z | argminFrom (zbar z) 1 = ⊤} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [show runMean (fun i j => X i j ω) 0 = fun n => (∑ j ∈ Finset.range n, X 0 j ω) / n from rfl,
        G1.argmin_std (fun j => X 0 j ω) (μ 0) σ0 hσ0]
    rw [hset, ← Measure.map_apply hZ0m G1.meas_argmin_top, hZ0law]
    have h := GreedyRS.Greedy.lemma1_argmin_finite
    rw [ae_iff] at h
    convert h using 2
    ext z; simp [lt_top_iff_ne_top]
  have hCpos : 0 < Cfun (γ0 / σ0) := by unfold Cfun; exact Real.exp_pos _
  refine ⟨?_, heq, by rw [heq]; exact ENNReal.ofReal_pos.2 (by positivity)⟩
  -- approximate levels γε ↑ γ0
  set x0 := (γ - γ0) / σbar with hx0def
  set XX := γ / σbar with hXXdef
  have hx0 : 0 < x0 := div_pos (by linarith [hγ0.2]) hσbar
  have hx0X : x0 < XX := div_lt_div_of_pos_right (by linarith [hγ0.1]) hσbar
  set δ0 := min x0 (XX - x0) / 2 with hδ0
  have hδ0pos : 0 < δ0 := by rw [hδ0]; exact div_pos (lt_min hx0 (by linarith)) (by norm_num)
  have hδ0a : δ0 < x0 := by
    have := min_le_left x0 (XX - x0); rw [hδ0]; linarith
  have hδ0b : x0 + δ0 < XX := by
    have := min_le_right x0 (XX - x0); rw [hδ0]; linarith
  set d : ℕ → ℝ := fun j => δ0 / ((j : ℝ) + 1) with hd
  have hdpos : ∀ j, 0 < d j := fun j => div_pos hδ0pos (by positivity)
  have hdle : ∀ j, d j ≤ δ0 := fun j =>
    div_le_self hδ0pos.le (by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith)
  have hlev : ∀ j : ℕ, ∃ ε γε : ℝ, (0 < 2 * ε ∧ 2 * ε < c - Cfun (γ / σbar)) ∧
      γε ∈ Set.Ioo 0 γ ∧ Cfun ((γ - γε) / σbar) = c - 2 * ε ∧
      γ0 - σbar * d j < γε ∧ γε < γ0 := by
    intro j
    obtain ⟨ε, hε1, hε2, ⟨xm, hxm, hCm⟩, -⟩ :=
      G1.levels Cfun hanti hcont XX x0 hx0 hx0X (d j) (hdpos j)
        (lt_of_le_of_lt (hdle j) hδ0a) (by linarith [hdle j])
    have hγx : ∀ t, (γ - (γ - σbar * t)) / σbar = t := fun t => by field_simp; ring
    have hγ0x : γ0 = γ - σbar * x0 := by rw [hx0def]; field_simp; ring
    have hγX : γ = σbar * XX := by rw [hXXdef]; field_simp
    refine ⟨ε, γ - σbar * xm, ⟨hε1, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [← hC0]; exact hε2
    · have : xm < XX := by linarith [hxm.2, hdle j]
      nlinarith
    · nlinarith [hxm.1]
    · rw [hγx, hCm, hC0]
    · rw [hγ0x]; nlinarith [hxm.2]
    · rw [hγ0x]; nlinarith [hxm.1]
  choose ε γε hj using hlev
  set L := Filter.liminf (fun k : ℕ => pcs P X k 1 ⌊c * k⌋₊) Filter.atTop with hL
  set S : ℕ → Set Ω := fun j => {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γε j)}
    with hS
  have hSL : ∀ j, P (S j) ≤ L := by
    intro j
    have h := (GreedyRS.Greedy.ec1_5_liminf_bound P μ v X hX hv γ σbar hγ hσbar hgap hvar c hc
      (ε j) (hj j).1).2 (γε j) (hj j).2.1 (hj j).2.2.1
    rw [hNn, tsub_zero] at h
    exact h
  set D : ℕ → Set Ω := fun J => ⋂ j, ⋂ (_ : J ≤ j), S j with hD
  have hDmono : Monotone D := by
    intro J J' hJJ' ω hω
    simp only [hD, Set.mem_iInter] at hω ⊢
    exact fun j hj' => hω j (hJJ'.trans hj')
  have hdlim : ∀ t, 0 < t → ∀ᶠ j in atTop, σbar * d j < t := by
    intro t ht
    have h0 : Tendsto (fun j : ℕ => σbar * d j) atTop (𝓝 0) := by
      have : Tendsto (fun j : ℕ => δ0 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat δ0 |>.comp (tendsto_add_atTop_nat 1) |>.congr
          (fun j => by simp)
      simpa using this.const_mul σbar
    exact h0.eventually (gt_mem_nhds ht)
  have hsub : {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)} ⊆ ⋃ J, D J := by
    rintro ω ⟨hb, hlt⟩
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hdlim _ (sub_pos.2 hlt))
    refine Set.mem_iUnion.2 ⟨J, ?_⟩
    simp only [hD, Set.mem_iInter]
    intro j hjJ
    refine ⟨hb, ?_⟩
    have h1 := hJ j hjJ
    have h2 := (hj j).2.2.2.1
    linarith
  calc P {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
      ≤ P (⋃ J, D J) := measure_mono hsub
    _ = ⨆ J, P (D J) := hDmono.measure_iUnion
    _ ≤ L := iSup_le fun J => (measure_mono (by
          intro ω hω
          simp only [hD, Set.mem_iInter] at hω
          exact hω J le_rfl)).trans (hSL J)
