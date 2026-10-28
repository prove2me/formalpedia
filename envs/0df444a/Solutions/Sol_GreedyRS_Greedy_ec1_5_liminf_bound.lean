-- Prove2me | solution 1 for GreedyRS.Greedy.ec1_5_liminf_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:08:04.977997+00:00
-- url     : https://prove2.me/submissions/9be9ab74-bb85-4a66-8870-913742e9be57

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
import Theorems.Thm_GreedyRS_Greedy_lemma2_crossing_time
import Theorems.Thm_GreedyRS_Greedy_eq4_4_crossing_comparison
import Theorems.Thm_GreedyRS_Greedy_eq3_2_boundary_crossing
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

namespace G15
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- SLLN for the standardised crossing times `Ñ_i(x)` of the rows `i ≥ 1` (any means and
positive variances). -/
lemma slln_std (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (hv : ∀ i, 0 < v i) (x : ℝ)
    (hfin : stdNormalSeq {z | crossTime x 1 z < ⊤} = 1)
    (hmean : Cn0 x 1 = ENNReal.ofReal (Cfun x)) :
    ∀ᵐ ω ∂P, (∀ i, crossTime x 1 (fun j => (X (i + 1) j ω - μ (i + 1)) / Real.sqrt (v (i + 1))) < ⊤) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ((crossTime x 1 (fun j => (X (i + 1) j ω - μ (i + 1)) / Real.sqrt (v (i + 1))) : ℕ∞) :
          ℝ≥0∞).toReal) atTop (𝓝 (Cfun x)) := by
  haveI : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance
  have hfinset : MeasurableSet {z : ℕ → ℝ | crossTime x 1 z < ⊤} := by
    have : {z : ℕ → ℝ | crossTime x 1 z < ⊤} = (fun z => crossTime x 1 z) ⁻¹' {⊤}ᶜ := by
      ext z; simp [lt_top_iff_ne_top]
    rw [this]; exact G11.meas_crossTime x (MeasurableSet.singleton _).compl
  set φ : ℕ → (ℕ → ℝ) → (ℕ → ℝ) := fun i y j => (y j - μ i) / Real.sqrt (v i) with hφ
  have hφm : ∀ i, Measurable (φ i) := fun i => measurable_pi_lambda _ fun j =>
    ((measurable_pi_apply j).sub_const _).div_const _
  set R : ℕ → Ω → (ℕ → ℝ) := fun i ω j => X i j ω with hR
  have hRm : ∀ i, Measurable (R i) := fun i => measurable_pi_lambda _ fun j => hX.meas i j
  set Z : ℕ → Ω → (ℕ → ℝ) := fun i => φ (i + 1) ∘ R (i + 1) with hZ
  have hZm : ∀ i, Measurable (Z i) := fun i => (hφm _).comp (hRm _)
  have hZlaw : ∀ i, P.map (Z i) = stdNormalSeq := by
    intro i
    rw [hZ, ← Measure.map_map (hφm _) (hRm _), G11.row_law P μ v X hX (i + 1)]
    have h := Measure.infinitePi_map_pi (fun _ : ℕ => gaussianReal (μ (i + 1)) (v (i + 1)))
      (f := fun (_ : ℕ) (t : ℝ) => (t - μ (i + 1)) / Real.sqrt (v (i + 1))) (fun _ => by fun_prop)
    refine h.trans ?_
    unfold stdNormalSeq
    congr 1; ext1 j
    exact G11.gauss_standardize _ _ (hv (i + 1))
  set H : (ℕ → ℝ) → ℝ := fun z => ((crossTime x 1 z : ℕ∞) : ℝ≥0∞).toReal with hH
  have hHm : Measurable H :=
    (measurable_of_countable (fun n : ℕ∞ => ((n : ℝ≥0∞)).toReal)).comp (G11.meas_crossTime x)
  set Y : ℕ → Ω → ℝ := fun i => H ∘ Z i with hY
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := by
    intro i
    have hz : IdentDistrib (Z i) (Z 0) P P :=
      ⟨(hZm i).aemeasurable, (hZm 0).aemeasurable, by rw [hZlaw i, hZlaw 0]⟩
    exact hz.comp hHm
  have hRind := G11.rows_indep P μ v X hX
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) Y) := by
    intro i j hij
    have hij' : i + 1 ≠ j + 1 := fun h => hij (by omega)
    have h1 : IndepFun (R (i + 1)) (R (j + 1)) P := hRind.indepFun hij'
    have h2 := h1.comp (hHm.comp (hφm (i + 1))) (hHm.comp (hφm (j + 1)))
    exact h2
  have hlin : ∫⁻ z, ((crossTime x 1 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq = ENNReal.ofReal (Cfun x) :=
    hmean
  have hHint : Integrable H stdNormalSeq := by
    refine integrable_toReal_of_lintegral_ne_top
      ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (G11.meas_crossTime x)).aemeasurable
      ?_
    rw [hlin]; exact ENNReal.ofReal_ne_top
  have hint : Integrable (Y 0) P := by
    have : Integrable H (P.map (Z 0)) := by rw [hZlaw 0]; exact hHint
    exact (integrable_map_measure hHm.aestronglyMeasurable (hZm 0).aemeasurable).1 this
  have hfinae : ∀ᵐ z ∂stdNormalSeq, crossTime x 1 z < ⊤ := by
    rw [ae_iff]
    have : {z | ¬ crossTime x 1 z < ⊤} = {z | crossTime x 1 z < ⊤}ᶜ := by ext; simp
    rw [this, prob_compl_eq_one_sub hfinset, hfin, tsub_self]
  have hmeanY : P[Y 0] = Cfun x := by
    have h1 : ∫ ω, Y 0 ω ∂P = ∫ z, H z ∂(P.map (Z 0)) :=
      (integral_map (hZm 0).aemeasurable hHm.aestronglyMeasurable).symm
    rw [h1, hZlaw 0]
    show ∫ z, ((crossTime x 1 z : ℕ∞) : ℝ≥0∞).toReal ∂stdNormalSeq = _
    rw [integral_toReal (f := fun z => ((crossTime x 1 z : ℕ∞) : ℝ≥0∞))
      ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (G11.meas_crossTime x)).aemeasurable
      (hfinae.mono fun z hz => by simpa using hz), hlin,
      ENNReal.toReal_ofReal (by unfold Cfun; exact (Real.exp_pos _).le)]
  have hslln := strong_law_ae Y hint hindep hident
  have hfinω : ∀ᵐ ω ∂P, ∀ i, crossTime x 1 (Z i ω) < ⊤ := by
    rw [ae_all_iff]
    intro i
    exact (ae_map_iff (hZm i).aemeasurable hfinset).1 (by rw [hZlaw i]; exact hfinae)
  filter_upwards [hslln, hfinω] with ω h1 h2
  refine ⟨fun i => h2 i, ?_⟩
  rw [hmeanY] at h1
  refine h1.congr fun n => ?_
  simp only [smul_eq_mul, hY, hH, Function.comp_apply]
  rfl

end G15

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / σbar) < c)
    (ε : ℝ) (hε : 0 < 2 * ε ∧ 2 * ε < c - GreedyRS.Greedy.Cfun (γ / σbar)) :
    (∃ γε ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γε) / σbar) = c - 2 * ε) ∧
    ∀ γε ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γε) / σbar) = c - 2 * ε →
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γε)}
          - P {ω | GreedyRS.Greedy.argminFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 = ⊤}
        ≤ Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k 1 ⌊c * k⌋₊) Filter.atTop := by
  open GreedyRS.Greedy in
  obtain ⟨-, hcont⟩ := GreedyRS.Greedy.lemma2_Cfun_strictAnti_continuous
  refine ⟨G15.exists_level γ σbar (c - 2 * ε) hγ hσbar (by linarith) hcont, fun γε hγε hCε => ?_⟩
  have hCpos : 0 < Cfun (γ / σbar) := by unfold Cfun; exact Real.exp_pos _
  have hcpos : 0 < c := by linarith
  have hεpos : 0 < ε := by linarith [hε.1]
  set x := (γ - γε) / σbar with hxdef
  have hx : 0 < x := div_pos (by linarith [hγε.2]) hσbar
  have hL2 := (GreedyRS.Greedy.lemma2_crossing_time).1 x hx
  have hS := G15.slln_std P μ v X hX hv x hL2.1 hL2.2
  rw [hCε] at hS
  set Ab := {ω | AboveFrom (runMean (fun i j => X i j ω) 0) 1 (μ 0 - γε)} with hAb
  set Nn := {ω | argminFrom (runMean (fun i j => X i j ω) 0) 1 = ⊤} with hNn
  set E : ℕ → Set Ω := fun k => {ω | (∑ i ∈ Finset.Ico 1 k,
      crossBelow (runMean (fun i j => X i j ω) i) (boundary (runMean (fun i j => X i j ω) 0) 1) 1)
        + argminFrom (runMean (fun i j => X i j ω) 0) 1 ≤ ((⌊c * k⌋₊ : ℕ) : ℕ∞)} with hE
  have hEle : ∀ k : ℕ, P (E k) ≤ pcs P X k 1 ⌊c * k⌋₊ := fun k =>
    GreedyRS.Greedy.eq3_2_boundary_crossing P X k ⌊c * k⌋₊
  set G : Set Ω := {ω | (∀ i, crossTime x 1
      (fun j => (X (i + 1) j ω - μ (i + 1)) / Real.sqrt (v (i + 1))) < ⊤) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ((crossTime x 1 (fun j => (X (i + 1) j ω - μ (i + 1)) / Real.sqrt (v (i + 1))) : ℕ∞) :
          ℝ≥0∞).toReal) atTop (𝓝 (c - 2 * ε))} with hG
  have hGc : P Gᶜ = 0 := by rw [ae_iff] at hS; exact hS
  set D : ℕ → Set Ω := fun K => ⋂ k, ⋂ (_ : K ≤ k), E k with hD
  have hDmono : Monotone D := by
    intro K K' hKK' ω hω
    simp only [hD, Set.mem_iInter] at hω ⊢
    exact fun k hk => hω k (hKK'.trans hk)
  have hsub : (Ab \ Nn) ∩ G ⊆ ⋃ K, D K := by
    rintro ω ⟨⟨hAω, hNω⟩, hfin, ht⟩
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 hNω
    choose a ha using fun i => ENat.ne_top_iff_exists.1 (hfin i).ne
    have hta : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (a i : ℝ)) atTop
        (𝓝 (c - 2 * ε)) := by
      refine ht.congr fun n => ?_
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ha i]; simp
    have hev1 : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (a i : ℝ) < c - ε :=
      hta.eventually (gt_mem_nhds (by linarith))
    have hev3 : ∀ᶠ n : ℕ in atTop, (M : ℝ) + c ≤ (n : ℝ) * ε :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const hεpos).eventually_ge_atTop _
    have hev4 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hev1.and hev3).and hev4)
    refine Set.mem_iUnion.2 ⟨N + 1, ?_⟩
    simp only [hD, Set.mem_iInter]
    intro k hk
    obtain ⟨⟨h1, h3⟩, h4⟩ := hN (k - 1) (by omega)
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hkpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
    rw [inv_mul_lt_iff₀ hkpos] at h1
    have hre : ∀ f : ℕ → ℕ∞, ∑ i ∈ Finset.Ico 1 k, f i = ∑ i ∈ Finset.range (k - 1), f (i + 1) := by
      intro f
      rw [Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => by rw [add_comm]
    have hle : ∑ i ∈ Finset.Ico 1 k, crossBelow (runMean (fun i j => X i j ω) i)
        (boundary (runMean (fun i j => X i j ω) 0) 1) 1 ≤
        ((∑ i ∈ Finset.range (k - 1), a i : ℕ) : ℕ∞) := by
      rw [hre, Nat.cast_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [ha i]
      exact GreedyRS.Greedy.eq4_4_crossing_comparison (fun i j => X i j ω) μ v γ σbar γε hσbar hγε
        (i + 1) (by omega) (hgap (i + 1) (by omega)) (hvar (i + 1)) (hv (i + 1)) hAω
    have hnat : (∑ i ∈ Finset.range (k - 1), a i) + M ≤ ⌊c * k⌋₊ := by
      apply Nat.le_floor
      push_cast
      have : ((k - 1 : ℕ) : ℝ) * (c - ε) + M ≤ c * k := by rw [hk1] at h3 ⊢; nlinarith [hcpos]
      linarith
    show (∑ i ∈ Finset.Ico 1 k, crossBelow (runMean (fun i j => X i j ω) i)
        (boundary (runMean (fun i j => X i j ω) 0) 1) 1)
          + argminFrom (runMean (fun i j => X i j ω) 0) 1 ≤ ((⌊c * k⌋₊ : ℕ) : ℕ∞)
    rw [← hM]
    calc (∑ i ∈ Finset.Ico 1 k, crossBelow (runMean (fun i j => X i j ω) i)
          (boundary (runMean (fun i j => X i j ω) 0) 1) 1) + (M : ℕ∞)
        ≤ ((∑ i ∈ Finset.range (k - 1), a i : ℕ) : ℕ∞) + M := by gcongr
      _ = (((∑ i ∈ Finset.range (k - 1), a i) + M : ℕ) : ℕ∞) := by push_cast; rfl
      _ ≤ ((⌊c * k⌋₊ : ℕ) : ℕ∞) := by exact_mod_cast hnat
  have hliminf : ⨆ K, P (D K) ≤ Filter.liminf (fun k : ℕ => P (E k)) atTop := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    refine iSup_mono fun K => le_iInf₂ fun k hk => measure_mono ?_
    intro ω hω
    simp only [hD, Set.mem_iInter] at hω
    exact hω k hk
  calc P Ab - P Nn ≤ P (Ab \ Nn) := le_measure_sdiff
    _ ≤ P ((Ab \ Nn) ∩ G) + P Gᶜ := by
        calc P (Ab \ Nn) ≤ P (((Ab \ Nn) ∩ G) ∪ Gᶜ) := measure_mono (fun ω hω => by
                by_cases h : ω ∈ G
                · exact Or.inl ⟨hω, h⟩
                · exact Or.inr h)
          _ ≤ _ := measure_union_le _ _
    _ = P ((Ab \ Nn) ∩ G) := by rw [hGc, add_zero]
    _ ≤ P (⋃ K, D K) := measure_mono hsub
    _ = ⨆ K, P (D K) := hDmono.measure_iUnion
    _ ≤ Filter.liminf (fun k : ℕ => P (E k)) atTop := hliminf
    _ ≤ _ := Filter.liminf_le_liminf (Eventually.of_forall hEle)
