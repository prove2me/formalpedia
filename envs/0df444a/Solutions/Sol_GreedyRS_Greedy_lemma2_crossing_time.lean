-- Prove2me | solution 1 for GreedyRS.Greedy.lemma2_crossing_time
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T11:18:55.312758+00:00
-- url     : https://prove2.me/submissions/db7d429d-c2d7-4bc9-9459-7ecded6e8d8a

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
import Theorems.Thm_GreedyRS_Greedy_eq4_3_min_prob
import Theorems.Thm_GreedyRS_Greedy_lemma2_pos_part
import Theorems.Thm_GreedyRS_Greedy_lemma2_zero_part
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

namespace GL2
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω]

lemma seq_sum_law (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P) (m : ℝ) (w : ℝ≥0)
    (hlaw : ∀ j, P.map (Y j) = gaussianReal m w) (n : ℕ) :
    P.map (∑ j ∈ Finset.range n, Y j) = gaussianReal (n * m) (n * w) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, zero_mul,
      gaussianReal_zero_var]
    show P.map (fun _ => (0:ℝ)) = _
    rw [Measure.map_const]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hi : IndepFun (∑ j ∈ Finset.range n, Y j) (Y n) P :=
      hind.indepFun_finsetSum_of_notMem hY (by simp)
    rw [gaussianReal_add_gaussianReal_of_indepFun hi ih (hlaw n)]
    congr 1
    · push_cast; ring
    · push_cast; ring

lemma seq_mean_atom (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P) (m : ℝ) (w : ℝ≥0) (hw : w ≠ 0)
    (hlaw : ∀ j, P.map (Y j) = gaussianReal m w) (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    P {ω | (∑ j ∈ Finset.range n, Y j ω) / n = a} = 0 := by
  have hmeas : Measurable (∑ j ∈ Finset.range n, Y j) := by
    have h := Finset.measurable_sum (Finset.range n) (fun j _ => hY j)
    convert h using 1; ext ω; simp
  have hsub : {ω | (∑ j ∈ Finset.range n, Y j ω) / n = a} ⊆
      (∑ j ∈ Finset.range n, Y j) ⁻¹' {n * a} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.sum_apply]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [← hω]; field_simp
  refine measure_mono_null hsub ?_
  rw [← Measure.map_apply hmeas (MeasurableSet.singleton _), seq_sum_law P Y hY hind m w hlaw n]
  have hnv : ((n : ℝ≥0) * w) ≠ 0 := mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) hw
  exact gaussianReal_absolutelyContinuous _ hnv (by simp)

lemma seq_slln (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P) (m : ℝ) (w : ℝ≥0)
    (hlaw : ∀ j, P.map (Y j) = gaussianReal m w) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, Y j ω) / n) atTop (𝓝 m) := by
  have hint : Integrable (Y 0) P := by
    have h1 : Integrable id (P.map (Y 0)) := by
      rw [hlaw 0]; exact (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id (hY 0).aemeasurable).1 h1
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) Y) :=
    fun i j hij => hind.indepFun hij
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    ⟨(hY i).aemeasurable, (hY 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
  have hmean : P[Y 0] = m := by
    have : ∫ x, x ∂(P.map (Y 0)) = ∫ ω, Y 0 ω ∂P :=
      integral_map (hY 0).aemeasurable aestronglyMeasurable_id
    rw [← this, hlaw 0, integral_id_gaussianReal]
  filter_upwards [strong_law_ae Y hint hindep hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  simp only [smul_eq_mul]
  rw [div_eq_inv_mul]

/-- A real sequence converging to `L` whose values (from index `1`) stay `≥ a` with `a < L`
and whose infimum is not `> a` attains the value `a`. -/
lemma attain_of_tendsto (y : ℕ → ℝ) (L a : ℝ) (hL : Tendsto y atTop (𝓝 L)) (haL : a < L)
    (hge : ∀ n, 1 ≤ n → a ≤ y n) (hnot : ¬ AboveFrom y 1 a) : ∃ n, 1 ≤ n ∧ y n = a := by
  by_contra hcon
  push Not at hcon
  have hgt : ∀ n, 1 ≤ n → a < y n := fun n hn => lt_of_le_of_ne (hge n hn) (fun h => hcon n hn h.symm)
  apply hnot
  have hbdd : BddBelow (Set.range fun n => y (1 + n)) :=
    ⟨a, by rintro _ ⟨n, rfl⟩; exact hge _ (by omega)⟩
  refine ⟨hbdd, ?_⟩
  -- eventually y n > (a + L)/2
  have hev : ∀ᶠ n in atTop, (a + L) / 2 < y n :=
    hL.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- finite minimum over 1..N
  obtain ⟨m0, hm0, hmin⟩ := Finset.exists_min_image (Finset.range (N + 1))
    (fun n => y (1 + n)) ⟨0, by simp⟩
  set b := min (y (1 + m0)) ((a + L) / 2) with hb
  have hab : a < b := lt_min (hgt _ (by omega)) (by linarith)
  have hle : b ≤ ⨅ n, y (1 + n) := by
    refine le_ciInf fun n => ?_
    by_cases hn : n ≤ N
    · exact (min_le_left _ _).trans (hmin n (by simp; omega))
    · exact (min_le_right _ _).trans (hN _ (by omega)).le
  linarith


lemma std_coords :
    (∀ j, Measurable (fun z : ℕ → ℝ => z j)) ∧
    iIndepFun (fun j (z : ℕ → ℝ) => z j) stdNormalSeq ∧
    ∀ j, stdNormalSeq.map (fun z : ℕ → ℝ => z j) = gaussianReal 0 1 := by
  refine ⟨fun j => measurable_pi_apply j, ?_, fun j => ?_⟩
  · unfold stdNormalSeq
    exact iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ => id)
      (fun _ => measurable_id)
  · unfold stdNormalSeq
    exact Measure.infinitePi_map_eval _ j

/-- For `x < 0`, `Pr{∀ n ≥ 1, Z̄(n) ≥ x} = Pr{min_{n ≥ 1} Z̄(n) > x}`. -/
lemma weak_eq_strict (x : ℝ) (hx : x < 0) :
    stdNormalSeq {z | crossTime x 1 z = ⊤} = stdNormalSeq {z | AboveFrom (zbar z) 1 x} := by
  haveI : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance
  obtain ⟨hm, hind, hlaw⟩ := std_coords
  have hT : ∀ z, crossTime x 1 z = ⊤ ↔ ∀ n, 1 ≤ n → x ≤ zbar z n := by
    intro z
    unfold crossTime
    rw [G11.iInf_coe_eq_top_iff]
    simp only [not_and, not_lt]
  apply le_antisymm
  · set N1 := ⋃ n : ℕ, ({z : ℕ → ℝ | 1 ≤ n} ∩ {z | zbar z n = x})
    set N2 := {z : ℕ → ℝ | ¬ Tendsto (fun n => zbar z n) atTop (𝓝 0)}
    have hN1 : stdNormalSeq N1 = 0 := by
      refine measure_iUnion_null fun n => ?_
      by_cases hn : 1 ≤ n
      · refine measure_mono_null Set.inter_subset_right ?_
        exact seq_mean_atom stdNormalSeq (fun j z => z j) hm hind 0 1 one_ne_zero hlaw x n hn
      · have : {z : ℕ → ℝ | 1 ≤ n} = ∅ := by ext; simp [hn]
        rw [this, Set.empty_inter, measure_empty]
    have hN2 : stdNormalSeq N2 = 0 := by
      have := seq_slln stdNormalSeq (fun j z => z j) hm hind 0 1 hlaw
      rw [ae_iff] at this
      exact this
    calc stdNormalSeq {z | crossTime x 1 z = ⊤}
        ≤ stdNormalSeq ({z | AboveFrom (zbar z) 1 x} ∪ (N1 ∪ N2)) := by
          apply measure_mono
          intro z hz
          rw [Set.mem_setOf_eq, hT] at hz
          by_cases hA : AboveFrom (zbar z) 1 x
          · exact Or.inl hA
          by_cases ht : Tendsto (fun n => zbar z n) atTop (𝓝 0)
          · obtain ⟨n, hn, he⟩ := attain_of_tendsto (zbar z) 0 x ht hx hz hA
            exact Or.inr (Or.inl (Set.mem_iUnion.2 ⟨n, hn, he⟩))
          · exact Or.inr (Or.inr ht)
      _ ≤ stdNormalSeq {z | AboveFrom (zbar z) 1 x} + (stdNormalSeq N1 + stdNormalSeq N2) :=
          (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
      _ = _ := by rw [hN1, hN2]; simp
  · apply measure_mono
    intro z hz
    rw [Set.mem_setOf_eq, hT]
    intro n hn
    obtain ⟨hb, hlt⟩ := hz
    have := ciInf_le hb (n - 1)
    have h' : 1 + (n - 1) = n := by omega
    rw [h'] at this
    linarith

end GL2

theorem solution :
    -- x > 0: finiteness and (4.1)
    (∀ x : ℝ, 0 < x →
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x 1 z < ⊤} = 1 ∧
        GreedyRS.Greedy.Cn0 x 1 = ENNReal.ofReal (GreedyRS.Greedy.Cfun x)) ∧
    StrictAntiOn (fun x => GreedyRS.Greedy.Cn0 x 1) (Set.Ioi 0) ∧
    ContinuousOn (fun x => GreedyRS.Greedy.Cn0 x 1) (Set.Ioi 0) ∧
    -- x < 0: infinite mean and (4.2)
    (∀ x : ℝ, x < 0 →
      GreedyRS.Greedy.Cn0 x 1 = ⊤ ∧
      GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x 1 z < ⊤} =
        ENNReal.ofReal (1 - Real.exp (-∑' n : ℕ,
          GreedyRS.Greedy.Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)))) ∧
    StrictMonoOn (fun x => GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x 1 z < ⊤})
      (Set.Iio 0) ∧
    ContinuousOn (fun x => GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime x 1 z < ⊤})
      (Set.Iio 0) ∧
    -- x = 0
    GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.crossTime 0 1 z < ⊤} = 1 ∧
      GreedyRS.Greedy.Cn0 0 1 = ⊤ := by
  open GreedyRS.Greedy in
  haveI : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance
  obtain ⟨hanti, hcont⟩ := GreedyRS.Greedy.lemma2_Cfun_strictAnti_continuous
  have hpos := GreedyRS.Greedy.lemma2_pos_part
  have hzero := GreedyRS.Greedy.lemma2_zero_part
  have hPhipos : ∀ t, 0 < Phi t := fun t =>
    lt_of_le_of_lt (G2C.Phi_nonneg (t - 1)) (G2C.Phi_strictMono (by linarith))
  have hCgt1 : ∀ y, 0 < y → 1 < Cfun y := by
    intro y hy
    unfold Cfun
    rw [Real.one_lt_exp_iff]
    refine Summable.tsum_pos (G2C.summable_terms y hy)
      (fun n => div_nonneg (G2C.Phi_nonneg _) (by positivity)) 0 ?_
    exact div_pos (hPhipos _) (by positivity)
  have hCpos : ∀ y, 0 < y → 0 < Cfun y := fun y hy => lt_trans one_pos (hCgt1 y hy)
  have hform : ∀ x : ℝ, Real.exp (-∑' n : ℕ, Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)) =
      1 / Cfun (-x) := by
    intro x
    unfold Cfun
    rw [one_div, ← Real.exp_neg]
    congr 2
    refine tsum_congr fun n => ?_
    rw [neg_mul_neg]
  have hset_ne : ∀ x : ℝ, {z : ℕ → ℝ | crossTime x 1 z < ⊤} = {z | crossTime x 1 z = ⊤}ᶜ := by
    intro x; ext z; simp [lt_top_iff_ne_top]
  have hmeas_top : ∀ x : ℝ, MeasurableSet {z : ℕ → ℝ | crossTime x 1 z = ⊤} := fun x =>
    G11.meas_crossTime x (MeasurableSet.singleton _)
  have hneg : ∀ x : ℝ, x < 0 →
      stdNormalSeq {z | crossTime x 1 z = ⊤} = ENNReal.ofReal (1 / Cfun (-x)) := by
    intro x hx
    rw [GL2.weak_eq_strict x hx, (GreedyRS.Greedy.eq4_3_min_prob x hx).2]
  have hfinneg : ∀ x : ℝ, x < 0 →
      stdNormalSeq {z | crossTime x 1 z < ⊤} = ENNReal.ofReal (1 - 1 / Cfun (-x)) := by
    intro x hx
    rw [hset_ne, prob_compl_eq_one_sub (hmeas_top x), hneg x hx,
      ENNReal.ofReal_sub _ (by have := hCpos (-x) (by linarith); positivity), ENNReal.ofReal_one]
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, hzero⟩
  · intro a ha b hb hab
    simp only
    rw [(hpos a ha).2, (hpos b hb).2]
    exact (ENNReal.ofReal_lt_ofReal_iff (hCpos a ha)).2 (hanti ha hb hab)
  · exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).congr fun x hx => (hpos x hx).2
  · intro x hx
    refine ⟨?_, ?_⟩
    · unfold Cn0
      apply lintegral_eq_top_of_measure_eq_top_ne_zero
      · exact ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
          (G11.meas_crossTime x)).aemeasurable
      · have : {z : ℕ → ℝ | ((crossTime x 1 z : ℕ∞) : ℝ≥0∞) = ⊤} = {z | crossTime x 1 z = ⊤} := by
          ext z; simp
        rw [this, hneg x hx]
        have := hCpos (-x) (by linarith)
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    · rw [hfinneg x hx, hform]
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only
    rw [hfinneg a ha, hfinneg b hb]
    have h1 := hCgt1 (-b) (by linarith)
    have h2 : Cfun (-a) < Cfun (-b) := hanti (show (0:ℝ) < -b by linarith)
      (show (0:ℝ) < -a by linarith) (by linarith)
    have h3 : 0 < Cfun (-a) := hCpos (-a) (by linarith)
    rw [ENNReal.ofReal_lt_ofReal_iff (by rw [sub_pos, div_lt_one (by linarith)]; exact h1)]
    have : 1 / Cfun (-b) < 1 / Cfun (-a) := one_div_lt_one_div_of_lt h3 h2
    linarith
  · have hc : ContinuousOn (fun x : ℝ => Cfun (-x)) (Set.Iio 0) :=
      hcont.comp continuous_neg.continuousOn (fun x hx => by
        simp only [Set.mem_Iio] at hx; simp only [Set.mem_Ioi]; linarith)
    have hc2 : ContinuousOn (fun x : ℝ => ENNReal.ofReal (1 - 1 / Cfun (-x))) (Set.Iio 0) := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine continuousOn_const.sub (continuousOn_const.div hc fun x hx => ?_)
      simp only [Set.mem_Iio] at hx
      exact (hCpos (-x) (by linarith)).ne'
    exact hc2.congr fun x hx => hfinneg x hx
