-- Prove2me | solution 1 for KroneckerWeyl.tendsto_average_torusFlow_closure_of_ae_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:52:24.49811+00:00
-- url     : https://prove2.me/submissions/2f0e3ce9-bac1-4dd3-ada8-80eec70bc676

import Mathlib
import Theorems.Thm_KroneckerWeyl_tendsto_average_torusFlow_closure

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Sol_KroneckerWeyl_tendsto_average_torusFlow_closure_of_ae_continuousAt

set_option linter.unusedSectionVars false

noncomputable section

section Approx

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Lower Lipschitz (inf-convolution) approximation of `f : Y → ℝ`, defined on `X ⊇ e(Y)`. -/
def lowerApprox (e : Y → X) (f : Y → ℝ) (n : ℕ) (x : X) : ℝ :=
  ⨅ y : Y, (f y + n * dist x (e y))

variable (e : Y → X) (f : Y → ℝ) (C : ℝ) (hC : ∀ y, |f y| ≤ C)
include hC

theorem bddBelow_aux (n : ℕ) (x : X) :
    BddBelow (Set.range fun y : Y => f y + n * dist x (e y)) := by
  refine ⟨-C, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h1 := (abs_le.mp (hC y)).1
  have h2 : (0 : ℝ) ≤ n * dist x (e y) := by positivity
  linarith

theorem lowerApprox_le (n : ℕ) (y : Y) : lowerApprox e f n (e y) ≤ f y := by
  have h := ciInf_le (bddBelow_aux e f C hC n (e y)) y
  simpa [lowerApprox] using h

variable [Nonempty Y]

theorem neg_le_lowerApprox (n : ℕ) (x : X) : -C ≤ lowerApprox e f n x := by
  apply le_ciInf
  intro y
  have h1 := (abs_le.mp (hC y)).1
  have h2 : (0 : ℝ) ≤ n * dist x (e y) := by positivity
  linarith

theorem lowerApprox_le_add (n : ℕ) (x x' : X) :
    lowerApprox e f n x ≤ lowerApprox e f n x' + n * dist x x' := by
  have key : lowerApprox e f n x - n * dist x x' ≤ lowerApprox e f n x' := by
    apply le_ciInf
    intro y
    have h1 : lowerApprox e f n x ≤ f y + n * dist x (e y) :=
      ciInf_le (bddBelow_aux e f C hC n x) y
    have h2 : dist x (e y) ≤ dist x x' + dist x' (e y) := dist_triangle _ _ _
    have h3 : (n : ℝ) * dist x (e y) ≤ n * dist x x' + n * dist x' (e y) := by
      have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
      linarith
    linarith
  linarith

theorem continuous_lowerApprox (n : ℕ) : Continuous (lowerApprox e f n) := by
  refine (LipschitzWith.of_le_add_mul (n : NNReal) fun x x' => ?_).continuous
  have := lowerApprox_le_add e f C hC n x x'
  simpa using this

theorem tendsto_lowerApprox (he : Isometry e) (y : Y) (hy : ContinuousAt f y) :
    Tendsto (fun n : ℕ => lowerApprox e f n (e y)) atTop (𝓝 (f y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hy (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hle := lowerApprox_le e f C hC n y
  have hge : f y - ε / 2 ≤ lowerApprox e f n (e y) := by
    apply le_ciInf
    intro z
    rw [he.dist_eq]
    by_cases hz : dist z y < δ
    · have h1 := hδf hz
      rw [Real.dist_eq] at h1
      have h2 := (abs_lt.mp h1).1
      have h3 : (0 : ℝ) ≤ n * dist y z := by positivity
      linarith
    · push Not at hz
      have h1 := (abs_le.mp (hC z)).1
      have h2 := (abs_le.mp (hC y)).2
      have hn' : 2 * C / δ < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
      have h3 : 2 * C < n * δ := by rwa [div_lt_iff₀ hδ] at hn'
      have h4 : (n : ℝ) * δ ≤ n * dist y z := by
        rw [dist_comm]; exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg n)
      linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Approx

section Squeeze

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

theorem eventually_lt_integral {α : Type*} {l : Filter α} (e : Y → X) (he : Isometry e)
    (ν : α → Measure Y) (hfin : ∀ a, IsFiniteMeasure (ν a)) (μ : Measure Y) [IsFiniteMeasure μ]
    (hν : ∀ h : X → ℝ, Continuous h →
      Tendsto (fun a => ∫ y, h (e y) ∂ν a) l (𝓝 (∫ y, h (e y) ∂μ)))
    (f : Y → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C)
    (hfc : ∀ᵐ y ∂μ, ContinuousAt f y) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a in l, ∫ y, f y ∂μ - ε < ∫ y, f y ∂ν a := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · refine Eventually.of_forall fun a => ?_
    simp only [Measure.eq_zero_of_isEmpty μ, Measure.eq_zero_of_isEmpty (ν a), integral_zero_measure]
    linarith
  have hL : Tendsto (fun n : ℕ => ∫ y, lowerApprox e f n (e y) ∂μ) atTop (𝓝 (∫ y, f y ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
      (integrable_const C) (fun n => ?_) ?_
    · exact ((continuous_lowerApprox e f C hC n).comp he.continuous).aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨neg_le_lowerApprox e f C hC n (e y),
        (lowerApprox_le e f C hC n y).trans (abs_le.mp (hC y)).2⟩
    · filter_upwards [hfc] with y hy using tendsto_lowerApprox e f C hC he y hy
  obtain ⟨n, hn⟩ :=
    (hL.eventually (lt_mem_nhds (show ∫ y, f y ∂μ - ε / 2 < ∫ y, f y ∂μ by linarith))).exists
  have hcont : Continuous (lowerApprox e f n) := continuous_lowerApprox e f C hC n
  filter_upwards [(hν _ hcont).eventually (lt_mem_nhds (show
    ∫ y, lowerApprox e f n (e y) ∂μ - ε / 2 < ∫ y, lowerApprox e f n (e y) ∂μ by linarith))]
    with a ha
  have := hfin a
  have hmono : ∫ y, lowerApprox e f n (e y) ∂ν a ≤ ∫ y, f y ∂ν a := by
    apply integral_mono
    · refine Integrable.of_bound (hcont.comp he.continuous).aestronglyMeasurable C
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨neg_le_lowerApprox e f C hC n (e y),
        (lowerApprox_le e f C hC n y).trans (abs_le.mp (hC y)).2⟩
    · exact Integrable.of_bound hf.aestronglyMeasurable C
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)
    · exact fun y => lowerApprox_le e f C hC n y
  linarith

theorem tendsto_integral_real {α : Type*} {l : Filter α} (e : Y → X) (he : Isometry e)
    (ν : α → Measure Y) (hfin : ∀ a, IsFiniteMeasure (ν a)) (μ : Measure Y) [IsFiniteMeasure μ]
    (hν : ∀ h : X → ℝ, Continuous h →
      Tendsto (fun a => ∫ y, h (e y) ∂ν a) l (𝓝 (∫ y, h (e y) ∂μ)))
    (f : Y → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C)
    (hfc : ∀ᵐ y ∂μ, ContinuousAt f y) :
    Tendsto (fun a => ∫ y, f y ∂ν a) l (𝓝 (∫ y, f y ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 := eventually_lt_integral e he ν hfin μ hν f hf C hC hfc ε hε
  have h2 := eventually_lt_integral e he ν hfin μ hν (fun y => -f y) hf.neg C
    (fun y => by rw [abs_neg]; exact hC y)
    (by filter_upwards [hfc] with y hy using hy.neg) ε hε
  filter_upwards [h1, h2] with a ha hb
  rw [integral_neg, integral_neg] at hb
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem tendsto_integral_complex {α : Type*} {l : Filter α} (e : Y → X) (he : Isometry e)
    (ν : α → Measure Y) (hfin : ∀ a, IsFiniteMeasure (ν a)) (μ : Measure Y) [IsFiniteMeasure μ]
    (hν : ∀ h : X → ℝ, Continuous h →
      Tendsto (fun a => ∫ y, h (e y) ∂ν a) l (𝓝 (∫ y, h (e y) ∂μ)))
    (f : Y → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C)
    (hfc : ∀ᵐ y ∂μ, ContinuousAt f y) :
    Tendsto (fun a => ∫ y, f y ∂ν a) l (𝓝 (∫ y, f y ∂μ)) := by
  have hre := tendsto_integral_real e he ν hfin μ hν (fun y => RCLike.re (f y))
    (Complex.measurable_re.comp hf) C (fun y => (Complex.abs_re_le_norm _).trans (hC y))
    (by filter_upwards [hfc] with y hy using Complex.continuous_re.continuousAt.comp hy)
  have him := tendsto_integral_real e he ν hfin μ hν (fun y => RCLike.im (f y))
    (Complex.measurable_im.comp hf) C (fun y => (Complex.abs_im_le_norm _).trans (hC y))
    (by filter_upwards [hfc] with y hy using Complex.continuous_im.continuousAt.comp hy)
  have hint : ∀ ν' : Measure Y, IsFiniteMeasure ν' → Integrable f ν' := fun ν' _ =>
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
  have key := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const (RCLike.I : ℂ))
  have hlim : (∫ y, f y ∂μ) = ((∫ y, RCLike.re (f y) ∂μ : ℝ) : ℂ) +
      ((∫ y, RCLike.im (f y) ∂μ : ℝ) : ℂ) * RCLike.I :=
    (integral_re_add_im (hint μ inferInstance)).symm
  rw [hlim]
  refine key.congr fun a => ?_
  exact integral_re_add_im (hint (ν a) (hfin a))

end Squeeze

section Flow

variable {ι : Type*}

/-- The linear flow on the torus with frequency vector `τ`. -/
def flow (τ : ι → ℝ) (t : ℝ) : UnitAddTorus ι := fun k => ((t * τ k : ℝ) : UnitAddCircle)

theorem continuous_flow (τ : ι → ℝ) : Continuous (flow τ) := by
  unfold flow
  fun_prop

variable [Fintype ι] (τ : ι → ℝ) (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) =
      closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)))

/-- The flow, as a map into the orbit closure. -/
def gflow (t : ℝ) : G :=
  ⟨flow τ t, by
    have : flow τ t ∈ (G : Set (UnitAddTorus ι)) := by
      rw [hG]; exact subset_closure ⟨t, rfl⟩
    exact this⟩

include hG in
theorem continuous_gflow : Continuous (gflow τ G hG) :=
  (continuous_flow τ).subtype_mk _

/-- Normalized push-forward of Lebesgue measure on `(a, b]` under the flow. -/
def avgMeasure (a b c : ℝ) : Measure G :=
  ENNReal.ofReal c • (volume.restrict (Set.Ioc a b)).map (gflow τ G hG)

theorem isFiniteMeasure_avgMeasure (a b c : ℝ) : IsFiniteMeasure (avgMeasure τ G hG a b c) := by
  refine ⟨?_⟩
  rw [avgMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem avg_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b c : ℝ) (hab : a ≤ b)
    (hc : 0 ≤ c) (F : G → E)
    (hF : AEStronglyMeasurable F ((volume.restrict (Set.Ioc a b)).map (gflow τ G hG))) :
    c • ∫ t in a..b, F (gflow τ G hG t) = ∫ y, F y ∂avgMeasure τ G hG a b c := by
  rw [avgMeasure, integral_smul_measure, integral_map (continuous_gflow τ G hG).aemeasurable hF,
    intervalIntegral.integral_of_le hab, ENNReal.toReal_ofReal hc]

variable (μ : Measure G) [IsProbabilityMeasure μ]

/-- Transfer of the continuous-case limit from interval averages to the measures `avgMeasure`. -/
theorem tendsto_avgMeasure_of_continuous (a b c : ℝ → ℝ)
    (habc : ∀ᶠ T in atTop, a T ≤ b T ∧ 0 ≤ c T) (h : UnitAddTorus ι → ℝ)
    (key : Tendsto (fun T => c T • ∫ t in a T..b T, ((h (flow τ t) : ℝ) : ℂ)) atTop
      (𝓝 (∫ g : G, ((h (g : UnitAddTorus ι) : ℝ) : ℂ) ∂μ))) (hh : Continuous h) :
    Tendsto (fun T => ∫ y, h (y : UnitAddTorus ι) ∂avgMeasure τ G hG (a T) (b T) (c T)) atTop
      (𝓝 (∫ g : G, h (g : UnitAddTorus ι) ∂μ)) := by
  have key2 := (Complex.continuous_re.tendsto _).comp key
  rw [integral_complex_ofReal, Complex.ofReal_re] at key2
  refine key2.congr' ?_
  filter_upwards [habc] with T hT
  have hF : AEStronglyMeasurable (fun y : G => ((h (y : UnitAddTorus ι) : ℝ) : ℂ))
      ((volume.restrict (Set.Ioc (a T) (b T))).map (gflow τ G hG)) :=
    (Complex.continuous_ofReal.comp (hh.comp continuous_subtype_val)).aestronglyMeasurable
  have := avg_eq τ G hG (a T) (b T) (c T) hT.1 hT.2 _ hF
  simp only [Function.comp_apply]
  rw [show (∫ t in a T..b T, ((h (flow τ t) : ℝ) : ℂ)) =
      ∫ t in a T..b T, ((h (gflow τ G hG t : UnitAddTorus ι) : ℝ) : ℂ) from rfl, this,
    integral_complex_ofReal, Complex.ofReal_re]

/-- Transfer of the conclusion from the measures `avgMeasure` back to interval averages. -/
theorem tendsto_average_of_avgMeasure (a b c : ℝ → ℝ)
    (habc : ∀ᶠ T in atTop, a T ≤ b T ∧ 0 ≤ c T) (u : UnitAddTorus ι → ℂ)
    (hu : Measurable fun g : G => u (g : UnitAddTorus ι))
    (H : Tendsto (fun T => ∫ y, u (y : UnitAddTorus ι) ∂avgMeasure τ G hG (a T) (b T) (c T))
      atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ))) :
    Tendsto (fun T => c T • ∫ t in a T..b T, u (flow τ t)) atTop
      (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) := by
  refine H.congr' ?_
  filter_upwards [habc] with T hT
  exact (avg_eq τ G hG (a T) (b T) (c T) hT.1 hT.2 _ hu.aestronglyMeasurable).symm

end Flow

end

end Sol_KroneckerWeyl_tendsto_average_torusFlow_closure_of_ae_continuousAt

open Sol_KroneckerWeyl_tendsto_average_torusFlow_closure_of_ae_continuousAt in
theorem solution {ι : Type*} [Finite ι] (τ : ι → ℝ)
    (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) =
      closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)))
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : UnitAddTorus ι → ℂ)
    (hu : Measurable fun g : G => u (g : UnitAddTorus ι))
    (hb : ∃ C : ℝ, ∀ g : G, ‖u (g : UnitAddTorus ι)‖ ≤ C)
    (hc : ∀ᵐ g ∂μ, ContinuousAt (fun g : G => u (g : UnitAddTorus ι)) g) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) ∧
      Tendsto
        (fun T : ℝ => (2 * T)⁻¹ • ∫ t in (-T)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) := by
  have := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := hb
  have hchild := fun v : C(UnitAddTorus ι, ℂ) =>
    KroneckerWeyl.tendsto_average_torusFlow_closure τ G hG μ v
  have hiso : Isometry (Subtype.val : G → UnitAddTorus ι) := isometry_subtype_coe
  have h1 : ∀ᶠ T : ℝ in atTop, (0 : ℝ) ≤ T ∧ 0 ≤ T⁻¹ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using ⟨hT, inv_nonneg.mpr hT⟩
  have h2 : ∀ᶠ T : ℝ in atTop, -T ≤ T ∧ 0 ≤ (2 * T)⁻¹ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using
      ⟨by linarith, inv_nonneg.mpr (by linarith)⟩
  constructor
  · refine tendsto_average_of_avgMeasure τ G hG μ (fun _ => 0) (fun T => T) (fun T => T⁻¹) h1 u
      hu ?_
    refine tendsto_integral_complex Subtype.val hiso
      (fun T => avgMeasure τ G hG 0 T T⁻¹) (fun T => isFiniteMeasure_avgMeasure τ G hG _ _ _) μ
      (fun h hh => ?_) (fun g : G => u g) hu C hC hc
    exact tendsto_avgMeasure_of_continuous τ G hG μ (fun _ => 0) (fun T => T) (fun T => T⁻¹) h1 h
      (hchild ⟨fun x => ((h x : ℝ) : ℂ), Complex.continuous_ofReal.comp hh⟩).1 hh
  · refine tendsto_average_of_avgMeasure τ G hG μ (fun T => -T) (fun T => T) (fun T => (2 * T)⁻¹)
      h2 u hu ?_
    refine tendsto_integral_complex Subtype.val hiso
      (fun T => avgMeasure τ G hG (-T) T (2 * T)⁻¹)
      (fun T => isFiniteMeasure_avgMeasure τ G hG _ _ _) μ
      (fun h hh => ?_) (fun g : G => u g) hu C hC hc
    exact tendsto_avgMeasure_of_continuous τ G hG μ (fun T => -T) (fun T => T)
      (fun T => (2 * T)⁻¹) h2 h
      (hchild ⟨fun x => ((h x : ℝ) : ℂ), Complex.continuous_ofReal.comp hh⟩).2 hh
