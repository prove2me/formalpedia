-- Prove2me | solution 1 for MTT.Cohomology.principal_period_equivariant_primitive
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-07T22:40:25.663432+00:00
-- url     : https://prove2.me/submissions/0e6bb8da-f243-43a3-be8c-a3cb5f9fc207

import Definitions.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.NumberTheory.ModularForms.LFunction
import Definitions.Def_MTT_PeriodPairing

/- Eichler primitive infrastructure reused from Chris Birkbeck (cbirkbeck),
Prove2Me accepted submission 919ac521-842b-4cd0-a813-afe3d8eacaf5. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixGroups ModularForm
open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped UpperHalfPlane Manifold
open ConjAct Pointwise
open MTT.Cohomology

namespace MTT.Eichler

/-! ### Part 1: complex analysis on the upper half-plane -/

/-- The open upper half-plane as a subset of `ℂ`. -/
def UHP : Set ℂ := {z | 0 < z.im}

lemma mem_UHP {z : ℂ} : z ∈ UHP ↔ 0 < z.im := Iff.rfl

lemma isOpen_UHP : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im

lemma convex_UHP : Convex ℝ UHP := convex_halfSpace_im_gt 0

lemma mk_mem_UHP {x y : ℝ} (hy : 0 < y) : (x : ℂ) + y * I ∈ UHP := by
  simp [mem_UHP, hy]

/-- A holomorphic function on the upper half-plane has a primitive there (wedge integral from `I`
plus Cauchy's theorem for rectangles). -/
theorem exists_primitive_UHP {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F UHP) :
    ∃ G : ℂ → ℂ, ∀ z ∈ UHP, HasDerivAt G (F z) z := by
  refine ⟨fun w => wedgeIntegral I w F, fun z hz => ?_⟩
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.ball z r ⊆ UHP := Metric.isOpen_iff.mp isOpen_UHP z hz
  have hcons : IsConservativeOn F (Metric.ball z r) := (hF.mono hball).isConservativeOn
  have hcont : ContinuousOn F (Metric.ball z r) := (hF.mono hball).continuousOn
  have hder : HasDerivAt (fun w => wedgeIntegral z w F) (F z) z :=
    hcons.hasDerivAt_wedgeIntegral hcont (Metric.mem_ball_self hr)
  have hzim : 0 < z.im := hz
  -- continuity along horizontal lines at positive height and vertical segments
  have hFc : ContinuousOn F UHP := hF.continuousOn
  have hhor : ∀ (y : ℝ), 0 < y → ∀ a b : ℝ,
      IntervalIntegrable (fun x : ℝ => F (x + y * I)) volume a b := by
    intro y hy a b
    apply ContinuousOn.intervalIntegrable
    refine hFc.comp (by fun_prop) ?_
    intro x _
    exact mk_mem_UHP hy
  have hver : ∀ (x : ℝ) (a b : ℝ), 0 < a → 0 < b →
      IntervalIntegrable (fun y : ℝ => F (x + y * I)) volume a b := by
    intro x a b ha hb
    apply ContinuousOn.intervalIntegrable
    refine hFc.comp (by fun_prop) ?_
    intro y hy
    have : 0 < y := by
      rcases Set.mem_uIcc.mp hy with h | h
      · exact lt_of_lt_of_le ha h.1
      · exact lt_of_lt_of_le hb h.1
    exact mk_mem_UHP this
  have key : ∀ w ∈ UHP, wedgeIntegral I w F = wedgeIntegral I z F + wedgeIntegral z w F := by
    intro w hw
    have hwim : 0 < w.im := hw
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn F (⟨z.re, 1⟩ : ℂ)
      (⟨w.re, z.im⟩ : ℂ) (by
        refine hF.mono ?_
        intro p hp
        rw [Complex.mem_reProdIm] at hp
        have h2 := hp.2
        simp only at h2
        rcases Set.mem_uIcc.mp h2 with h | h
        · exact lt_of_lt_of_le one_pos h.1
        · exact lt_of_lt_of_le hzim h.1)
    simp only at hrect
    simp only [wedgeIntegral, I_re, I_im, Complex.ofReal_one, one_mul] at hrect ⊢
    have h1 : ∫ x : ℝ in (0 : ℝ)..w.re, F (x + I) =
        (∫ x : ℝ in (0 : ℝ)..z.re, F (x + I)) + ∫ x : ℝ in z.re..w.re, F (x + I) := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · simpa using hhor 1 one_pos 0 z.re
      · simpa using hhor 1 one_pos z.re w.re
    have h2 : ∫ y : ℝ in (1 : ℝ)..w.im, F (w.re + y * I) =
        (∫ y : ℝ in (1 : ℝ)..z.im, F (w.re + y * I)) + ∫ y : ℝ in z.im..w.im, F (w.re + y * I) := by
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact hver w.re 1 z.im one_pos hzim
      · exact hver w.re z.im w.im hzim hwim
    rw [h1, h2, smul_add]
    have hrect' : ∫ x : ℝ in z.re..w.re, F (x + I) = (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) -
        I • (∫ y : ℝ in (1 : ℝ)..z.im, F (w.re + y * I)) +
        I • (∫ y : ℝ in (1 : ℝ)..z.im, F (z.re + y * I)) := by
      linear_combination hrect
    rw [hrect']
    abel
  have hev : (fun w => wedgeIntegral I w F) =ᶠ[𝓝 z]
      fun w => wedgeIntegral I z F + wedgeIntegral z w F := by
    filter_upwards [isOpen_UHP.mem_nhds hz] with w hw
    exact key w hw
  exact (hder.const_add (wedgeIntegral I z F)).congr_of_eventuallyEq hev

/-- Two primitives on the upper half-plane differ by a constant. -/
theorem eq_const_of_hasDerivAt_zero {G : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G 0 z) :
    ∀ z ∈ UHP, ∀ w ∈ UHP, G z = G w := by
  intro z hz w hw
  refine convex_UHP.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) ?_ ?_ hz hw
  · exact fun x hx => (hG x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [fderivWithin_eq_fderiv (isOpen_UHP.uniqueDiffWithinAt hx) (hG x hx).differentiableAt,
      (hG x hx).hasFDerivAt.fderiv]
    ext
    simp

lemma hasDerivAt_vertical {G F : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G (F z) z) (x : ℝ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => G ((x : ℂ) + s * I)) (F ((x : ℂ) + t * I) * I) t := by
  have h1 : HasDerivAt (fun w : ℂ => G ((x : ℂ) + w * I)) (F ((x : ℂ) + t * I) * I) (t : ℂ) := by
    have hin : HasDerivAt (fun w : ℂ => (x : ℂ) + w * I) I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (x : ℂ)
    exact HasDerivAt.comp (t : ℂ) (hG _ (mk_mem_UHP ht)) hin
  exact h1.comp_ofReal

/-- The fundamental theorem of calculus along a vertical segment. -/
theorem integral_vertical {G F : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G (F z) z)
    (hFc : ContinuousOn F UHP) (x : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in a..b, F ((x : ℂ) + t * I) = (G ((x : ℂ) + b * I) - G ((x : ℂ) + a * I)) / I := by
  have hint : IntervalIntegrable (fun t : ℝ => F ((x : ℂ) + t * I) * I) volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul (hFc.comp (by fun_prop) ?_) continuousOn_const
    intro y hy
    have : 0 < y := by
      rcases Set.mem_uIcc.mp hy with h | h
      · exact lt_of_lt_of_le ha h.1
      · exact lt_of_lt_of_le hb h.1
    exact mk_mem_UHP this
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => G ((x : ℂ) + s * I)) (F ((x : ℂ) + t * I) * I) t := by
    intro t ht
    have : 0 < t := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact lt_of_lt_of_le ha h.1
      · exact lt_of_lt_of_le hb h.1
    exact hasDerivAt_vertical hG x this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_mul_const] at this
  rw [eq_div_iff I_ne_zero]
  exact this

/-! ### Part 2: normalized primitives -/

/-- Exponential decay at `i∞`, uniformly on vertical strips. -/
def Decays (F : ℂ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ K : ℝ, ∃ C : ℝ, ∀ x y : ℝ, |x| ≤ K → T₀ ≤ y →
    ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-c * y)

lemma continuousOn_vertical {F : ℂ → ℂ} (hFc : ContinuousOn F UHP) (x : ℝ) :
    ContinuousOn (fun t : ℝ => F ((x : ℂ) + t * I)) (Ioi 0) := by
  refine hFc.comp (by fun_prop) ?_
  intro t ht; exact mk_mem_UHP ht

lemma Decays.integrableOn_Ioi {F : ℂ → ℂ} (hd : Decays F) (hFc : ContinuousOn F UHP) (x : ℝ)
    {a : ℝ} (ha : 0 < a) : IntegrableOn (fun t : ℝ => F ((x : ℂ) + t * I)) (Ioi a) := by
  obtain ⟨c, hc, T₀, hT⟩ := hd
  obtain ⟨C, hC⟩ := hT |x|
  set T₁ : ℝ := max a T₀ with hT₁
  have haT₁ : a ≤ T₁ := le_max_left _ _
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le ha haT₁
  have h1 : IntegrableOn (fun t : ℝ => F ((x : ℂ) + t * I)) (Ioc a T₁) := by
    refine (ContinuousOn.integrableOn_Icc (a := a) (b := T₁) ?_).mono_set Ioc_subset_Icc_self
    exact (continuousOn_vertical hFc x).mono (fun t ht => lt_of_lt_of_le ha ht.1)
  have h2 : IntegrableOn (fun t : ℝ => F ((x : ℂ) + t * I)) (Ioi T₁) := by
    have hexp : IntegrableOn (fun t : ℝ => C * Real.exp (-c * t)) (Ioi T₁) :=
      (exp_neg_integrableOn_Ioi T₁ hc).const_mul C
    refine Integrable.mono' hexp ?_ ?_
    · exact ((continuousOn_vertical hFc x).mono
        (fun t ht => lt_trans hT₁pos ht)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      exact hC x t le_rfl (le_trans (le_max_right _ _) (le_of_lt ht))
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi haT₁] at this

lemma tendsto_primitive_vertical {G F : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G (F z) z)
    (hFc : ContinuousOn F UHP) (x : ℝ) {a : ℝ} (ha : 0 < a)
    (hint : IntegrableOn (fun t : ℝ => F ((x : ℂ) + t * I)) (Ioi a)) :
    Tendsto (fun T : ℝ => G ((x : ℂ) + T * I)) atTop
      (𝓝 (G ((x : ℂ) + a * I) + I * ∫ t : ℝ in Ioi a, F ((x : ℂ) + t * I))) := by
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hint tendsto_id
  have h' : Tendsto (fun T : ℝ => G ((x : ℂ) + a * I) + I * ∫ t in a..T, F ((x : ℂ) + t * I))
      atTop (𝓝 (G ((x : ℂ) + a * I) + I * ∫ t : ℝ in Ioi a, F ((x : ℂ) + t * I))) :=
    (h.const_mul I).const_add _
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [integral_vertical hG hFc x ha hT]
  field_simp
  ring

lemma hasDerivAt_horizontal {G F : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G (F z) z) {y : ℝ}
    (hy : 0 < y) (s : ℝ) :
    HasDerivAt (fun x : ℝ => G ((x : ℂ) + y * I)) (F ((s : ℂ) + y * I)) s := by
  have h1 : HasDerivAt (fun w : ℂ => G (w + y * I)) (F ((s : ℂ) + y * I)) (s : ℂ) := by
    have hin : HasDerivAt (fun w : ℂ => w + (y : ℂ) * I) 1 (s : ℂ) := (hasDerivAt_id _).add_const _
    exact HasDerivAt.comp_add_const (s : ℂ) ((y : ℂ) * I) (hG _ (mk_mem_UHP hy))
  exact h1.comp_ofReal

lemma integral_horizontal {G F : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G (F z) z)
    (hFc : ContinuousOn F UHP) {y : ℝ} (hy : 0 < y) (x₁ x₂ : ℝ) :
    ∫ s in x₁..x₂, F ((s : ℂ) + y * I) = G ((x₂ : ℂ) + y * I) - G ((x₁ : ℂ) + y * I) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s _; exact hasDerivAt_horizontal hG hy s
  · apply ContinuousOn.intervalIntegrable
    refine hFc.comp (by fun_prop) ?_
    intro s _; exact mk_mem_UHP hy

lemma tendsto_sub_horizontal {G F : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G (F z) z)
    (hFc : ContinuousOn F UHP) (hd : Decays F) (x : ℝ) :
    Tendsto (fun T : ℝ => G ((x : ℂ) + T * I) - G (((0 : ℝ) : ℂ) + T * I)) atTop (𝓝 0) := by
  obtain ⟨c, hc, T₀, hT⟩ := hd
  obtain ⟨C, hC⟩ := hT |x|
  have hlim : Tendsto (fun T : ℝ => C * Real.exp (-c * T) * |x - 0|) atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ => Real.exp (-c * T)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
      refine h.congr fun T => ?_
      simp [neg_mul]
    simpa using (this.const_mul C).mul_const |x - 0|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (max T₀ 1)] with T hT
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hT)
  rw [norm_norm, ← integral_horizontal hG hFc hT0]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro s hs
  apply hC s T ?_ (le_trans (le_max_left _ _) hT)
  rw [Set.uIoc_eq_union] at hs
  rcases hs with hs | hs
  · rw [abs_le]; constructor
    · exact le_trans (neg_nonpos.mpr (abs_nonneg x)) hs.1.le
    · exact le_trans hs.2 (le_abs_self x)
  · rw [abs_le]; constructor
    · exact le_trans (neg_abs_le x) hs.1.le
    · exact le_trans hs.2 (abs_nonneg x)

/-- A holomorphic function with exponential decay has a primitive tending to `0` at `i∞`
along every vertical line. -/
theorem exists_normalized_primitive {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F UHP)
    (hd : Decays F) :
    ∃ G : ℂ → ℂ, (∀ z ∈ UHP, HasDerivAt G (F z) z) ∧
      ∀ x : ℝ, Tendsto (fun T : ℝ => G ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  obtain ⟨G, hG⟩ := exists_primitive_UHP hF
  have hFc := hF.continuousOn
  set L : ℂ := G (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I) +
    I * ∫ t : ℝ in Ioi (1 : ℝ), F (((0 : ℝ) : ℂ) + t * I) with hL
  have h0 : Tendsto (fun T : ℝ => G (((0 : ℝ) : ℂ) + T * I)) atTop (𝓝 L) :=
    tendsto_primitive_vertical hG hFc 0 one_pos (hd.integrableOn_Ioi hFc 0 one_pos)
  refine ⟨fun z => G z - L, fun z hz => (hG z hz).sub_const L, fun x => ?_⟩
  have hx : Tendsto (fun T : ℝ => G ((x : ℂ) + T * I)) atTop (𝓝 L) := by
    have := (tendsto_sub_horizontal hG hFc ⟨_, hd.choose_spec.1, hd.choose_spec.2⟩ x).add h0
    simp only [sub_add_cancel, zero_add] at this
    exact this
  simpa using hx.sub_const L

/-- At a finite cusp, the normalized primitive tends (along `s = 1/(n+1)`) to
`-i` times the improper vertical integral. -/
lemma tendsto_primitive_cusp {G F : ℂ → ℂ} (hG : ∀ z ∈ UHP, HasDerivAt G (F z) z)
    (hFc : ContinuousOn F UHP)
    (hnorm : ∀ x : ℝ, Tendsto (fun T : ℝ => G ((x : ℂ) + T * I)) atTop (𝓝 0))
    (x : ℝ) (hint : IntegrableOn (fun t : ℝ => F ((x : ℂ) + t * I)) (Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => G ((x : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)) atTop
      (𝓝 (-(I * ∫ t : ℝ in Ioi (0 : ℝ), F ((x : ℂ) + t * I)))) := by
  have hval : ∀ s : ℝ, 0 < s →
      G ((x : ℂ) + s * I) = -(I * ∫ t : ℝ in Ioi s, F ((x : ℂ) + t * I)) := by
    intro s hs
    have h1 := tendsto_primitive_vertical hG hFc x hs (hint.mono_set (Ioi_subset_Ioi hs.le))
    have h2 := tendsto_nhds_unique h1 (hnorm x)
    linear_combination h2
  have hs : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hmono : Monotone (fun n : ℕ => Ioi (1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    gcongr
  have hunion : ⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1)) = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩; exact lt_trans (hs n) hn
    · intro ht; obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht; exact ⟨n, hn⟩
  have hint' : IntegrableOn (fun t : ℝ => F ((x : ℂ) + t * I)) (⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1))) := by
    rw [hunion]; exact hint
  have hlim := tendsto_setIntegral_of_monotone (fun n => measurableSet_Ioi) hmono hint'
  rw [hunion] at hlim
  have := (hlim.const_mul I).neg
  refine this.congr' (Eventually.of_forall fun n => ?_)
  exact (hval (1 / ((n : ℝ) + 1)) (hs n)).symm

/-! ### Part 3: the integrands `h(w) w^j` -/

/-- `w ↦ h(w) w^j` on `ℂ` (junk outside `ℍ`). -/
def Fj (h : ℍ → ℂ) (j : ℕ) : ℂ → ℂ := fun w => h (UpperHalfPlane.ofComplex w) * w ^ j

lemma differentiableOn_Fj {h : ℍ → ℂ} (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (j : ℕ) :
    DifferentiableOn ℂ (Fj h j) UHP := by
  have h1 : DifferentiableOn ℂ (h ∘ UpperHalfPlane.ofComplex) UHP :=
    UpperHalfPlane.mdifferentiable_iff.mp hh
  have : Fj h j = fun w => (h ∘ UpperHalfPlane.ofComplex) w * w ^ j := rfl
  rw [this]
  exact h1.mul (differentiableOn_id.pow j)

lemma decays_Fj {h : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : h =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (-c * τ.im)) (j : ℕ) :
    Decays (Fj h j) := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hC
  refine ⟨c / 2, by positivity, max A 1, fun K => ?_⟩
  refine ⟨|C| * (|K| + 1) ^ j * ((j.factorial : ℝ) * (2 / c) ^ j), fun x y hx hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hyA : A ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : 0 < y := by linarith
  have him : 0 < ((x : ℂ) + y * I).im := by simp [hy0]
  have hτ2 : ((UpperHalfPlane.ofComplex ((x : ℂ) + y * I) : ℍ) : ℂ) = (x : ℂ) + y * I := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hτ : (UpperHalfPlane.ofComplex ((x : ℂ) + y * I)).im = y := by
    rw [← UpperHalfPlane.coe_im, hτ2]; simp
  have hbound := hA (UpperHalfPlane.ofComplex ((x : ℂ) + y * I)) (by rw [hτ]; exact hyA)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hbound
  have hb : ‖h (UpperHalfPlane.ofComplex ((x : ℂ) + y * I))‖ ≤
      C * Real.exp (-c * (UpperHalfPlane.ofComplex ((x : ℂ) + y * I)).im) := hbound
  rw [hτ] at hb
  have hbound' : ‖h (UpperHalfPlane.ofComplex ((x : ℂ) + y * I))‖ ≤ |C| * Real.exp (-c * y) :=
    le_trans hb (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hnorm : ‖(x : ℂ) + y * I‖ ≤ |K| + y := by
    calc ‖(x : ℂ) + y * I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + y := by simp [abs_of_pos hy0]
      _ ≤ |K| + y := by linarith [le_abs_self K]
  have hKy : |K| + y ≤ (|K| + 1) * y := by nlinarith [abs_nonneg K]
  have hpow : y ^ j ≤ (j.factorial : ℝ) * (2 / c) ^ j * Real.exp (c / 2 * y) := by
    have h1 := Real.pow_div_factorial_le_exp (c / 2 * y) (by positivity) j
    rw [div_le_iff₀ (by positivity)] at h1
    have e : y ^ j = (c / 2 * y) ^ j * (2 / c) ^ j := by
      rw [← mul_pow]; congr 1; field_simp
    rw [e]
    calc (c / 2 * y) ^ j * (2 / c) ^ j
        ≤ (Real.exp (c / 2 * y) * (j.factorial : ℝ)) * (2 / c) ^ j := by gcongr
      _ = _ := by ring
  have hFj : ‖Fj h j ((x : ℂ) + y * I)‖ =
      ‖h (UpperHalfPlane.ofComplex ((x : ℂ) + y * I))‖ * ‖(x : ℂ) + y * I‖ ^ j := by
    simp [Fj, norm_mul, norm_pow]
  rw [hFj]
  calc ‖h (UpperHalfPlane.ofComplex ((x : ℂ) + y * I))‖ * ‖(x : ℂ) + y * I‖ ^ j
      ≤ (|C| * Real.exp (-c * y)) * ((|K| + 1) * y) ^ j :=
        mul_le_mul hbound' (pow_le_pow_left₀ (norm_nonneg _) (le_trans hnorm hKy) j)
          (by positivity) (by positivity)
    _ = |C| * Real.exp (-c * y) * (|K| + 1) ^ j * y ^ j := by rw [mul_pow]; ring
    _ ≤ |C| * Real.exp (-c * y) * (|K| + 1) ^ j *
          ((j.factorial : ℝ) * (2 / c) ^ j * Real.exp (c / 2 * y)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = |C| * (|K| + 1) ^ j * ((j.factorial : ℝ) * (2 / c) ^ j) *
          (Real.exp (-c * y) * Real.exp (c / 2 * y)) := by ring
    _ = _ := by
        have e : Real.exp (-c * y) * Real.exp (c / 2 * y) = Real.exp (-(c / 2) * y) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e]

open UpperHalfPlane in
/-- Integrability of `t ↦ f(r+it) t^j` on `(0,∞)` for a cusp form (via the Mellin transform of the
translate). -/
lemma rational_translate_integrable
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ =>
      f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ)^j) (Set.Ioi 0) := by
  let : NeZero N := ⟨by omega⟩
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.upperRightHom r
  let gr : GL (Fin 2) ℝ := g.map (Rat.castHom ℝ)
  have hr : gr = Matrix.GeneralLinearGroup.upperRightHom (r : ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [gr, g]
  let : (MTT.GammaOne N).IsArithmetic := by dsimp [MTT.GammaOne]; infer_instance
  let : (toConjAct gr⁻¹ • MTT.GammaOne N).IsArithmetic := by
    have hh := Subgroup.IsArithmetic.conj (MTT.GammaOne N) g⁻¹
    simpa [gr] using hh
  let F := CuspForm.translate f gr
  have hconv := ((CuspForm.isStrongFEPair (by omega : (0 : ℤ) < k) F).hasMellin
    ((j : ℂ)+1)).1
  unfold MellinConvergent at hconv
  have hval (t : ℝ) (ht : 0 < t) :
      F (ofComplex (Complex.I * t)) = f (ofComplex ((r : ℂ) + Complex.I * t)) := by
    change (⇑f ∣[(k : ℤ)] gr) _ = _
    rw [ModularForm.slash_def, hr]
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    simp [σ, denom, Matrix.GeneralLinearGroup.upperRightHom]
    congr 1
    ext
    simp [coe_smul, σ, num, denom, ofComplex_apply_of_im_pos, ht]
    ring
  apply hconv.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [ModularForm.weakFEPair, add_sub_cancel_right, Complex.cpow_natCast,
    smul_eq_mul, hval t ht]
  ring

lemma integrableOn_Fj_cusp {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ => Fj f j ((r : ℂ) + t * I)) (Ioi (0 : ℝ)) := by
  have : (fun t : ℝ => Fj f j ((r : ℂ) + t * I)) = fun t : ℝ => ∑ m ∈ Finset.range (j + 1),
      ((r : ℂ) ^ m * I ^ (j - m) * (j.choose m : ℂ)) *
        (f (UpperHalfPlane.ofComplex ((r : ℂ) + I * t)) * (t : ℂ) ^ (j - m)) := by
    funext t
    simp only [Fj]
    rw [show (r : ℂ) + t * I = (r : ℂ) + I * t by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]; ring
  rw [this]
  exact integrable_finsetSum _ fun m _ =>
    (rational_translate_integrable hN hk f r (j - m)).const_mul _

open Classical in
/-- A normalized primitive (junk `0` when the hypotheses fail). -/
def normPrim (F : ℂ → ℂ) : ℂ → ℂ :=
  if h : DifferentiableOn ℂ F UHP ∧ Decays F then
    Classical.choose (exists_normalized_primitive h.1 h.2) else 0

lemma normPrim_spec {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F UHP) (hd : Decays F) :
    (∀ z ∈ UHP, HasDerivAt (normPrim F) (F z) z) ∧
      ∀ x : ℝ, Tendsto (fun T : ℝ => normPrim F ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  classical
  rw [normPrim, dif_pos ⟨hF, hd⟩]
  exact Classical.choose_spec (exists_normalized_primitive hF hd)

/-! ### Part 4: Möbius transport of the vector-valued primitives -/

section GLsection
open UpperHalfPlane

/-- An integer matrix viewed in `GL₂(ℚ)` (junk value `1` if the determinant vanishes). -/
def toGLQ (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℚ :=
  if h : ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

/-- An integer matrix viewed in `GL₂(ℝ)`, through `GL₂(ℚ)`. -/
def toGL (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ A)

lemma det_map_ne_zero {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0 := by
  rw [← RingHom.map_det]; simpa using h

lemma toGLQ_val {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (toGLQ A : Matrix (Fin 2) (Fin 2) ℚ) = (Int.castRingHom ℚ).mapMatrix A := by
  rw [toGLQ, dif_pos (det_map_ne_zero h)]; rfl

lemma toGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) (i j : Fin 2) :
    (toGL A : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [toGL, Matrix.GeneralLinearGroup.map_apply, toGLQ_val h]
  simp

lemma toGL_det_matrix {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (toGL A : Matrix (Fin 2) (Fin 2) ℝ).det = (A.det : ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [toGL_apply h]
  push_cast; ring

lemma toGL_det {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (Matrix.GeneralLinearGroup.det (toGL A) : ℝ) = (A.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_det_matrix h]

lemma toGL_SL (γ : SL(2, ℤ)) :
    toGL (γ : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  ext i j
  rw [toGL_apply (by simp), Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp

lemma toGL_det_pos {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) :
    0 < (Matrix.GeneralLinearGroup.det (toGL A) : ℝ) := by
  rw [toGL_det h.ne']; exact_mod_cast h

lemma σ_toGL {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (z : ℂ) : σ (toGL A) z = z := by
  simp [σ, toGL_det_matrix h.ne', h]

lemma coe_toGL_smul {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (τ : ℍ) :
    ((toGL A • τ : ℍ) : ℂ) =
      ((A 0 0 : ℂ) * τ + (A 0 1 : ℂ)) / ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) := by
  rw [coe_smul_of_det_pos (toGL_det_pos h)]
  simp [num, denom, toGL_apply h.ne']

lemma slash_toGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (k : ℤ) (f : ℍ → ℂ)
    (τ : ℍ) :
    (f ∣[k] toGL A) τ =
      f (toGL A • τ) * (A.det : ℂ) ^ (k - 1) * ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) ^ (-k) := by
  rw [ModularForm.slash_apply, σ_toGL h, toGL_det h.ne', abs_of_pos (by exact_mod_cast h)]
  simp [denom, toGL_apply h.ne']

lemma slash_mapGL_apply (γ : SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ) τ =
      f (Matrix.SpecialLinearGroup.mapGL ℝ γ • τ) *
        (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  rw [← toGL_SL, slash_toGL_apply (by simp)]
  simp

lemma denom_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  have := denom_ne_zero (toGL (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ
  simpa [denom, toGL_apply (show (γ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 by simp)] using this

end GLsection

/-! #### The coefficient action -/

def actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) : Binary ℂ →ₐ[ℂ] Binary ℂ :=
  @MvPolynomial.aeval ℂ (Binary ℂ) (Fin 2) _ _ _
    (fun i : Fin 2 => ∑ a : Fin 2, ((γ a i : ℤ) : ℂ) • (MvPolynomial.X a : Binary ℂ))

lemma act_eq_actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) : act γ P = actAlg γ P := rfl

lemma actAlg_comp (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (actAlg A).comp (actAlg B) = actAlg (A * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, actAlg, MvPolynomial.aeval_X, map_sum, map_smul,
    Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

lemma act_act (A B : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) :
    act A (act B P) = act (A * B) P := by
  rw [act_eq_actAlg, act_eq_actAlg, act_eq_actAlg, ← AlgHom.comp_apply, actAlg_comp]

lemma act_one (P : Binary ℂ) : act (1 : Matrix (Fin 2) (Fin 2) ℤ) P = P := by
  rw [act_eq_actAlg]
  have : actAlg 1 = AlgHom.id ℂ (Binary ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [actAlg, Matrix.one_apply]
  rw [this]
  rfl

lemma act_X (γ : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    act γ (MvPolynomial.X i) = ∑ a : Fin 2, ((γ a i : ℤ) : ℂ) • (MvPolynomial.X a : Binary ℂ) := by
  rw [act_eq_actAlg, actAlg, MvPolynomial.aeval_X]

lemma act_C (γ : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) :
    act γ (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [act_eq_actAlg]; simp [actAlg]

lemma binaryExponent_apply_zero (n j : ℕ) : binaryExponent n j 0 = j := by
  simp [binaryExponent]

lemma binaryExponent_apply_one (n j : ℕ) : binaryExponent n j 1 = n - j := by
  simp [binaryExponent]

lemma monomial_binaryExponent (n j : ℕ) (c : ℂ) :
    (MvPolynomial.monomial (binaryExponent n j) c : Binary ℂ) =
      MvPolynomial.C c * MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ (n - j) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
    binaryExponent_apply_zero, binaryExponent_apply_one, mul_assoc]

/-! #### Möbius maps on `ℂ` -/

/-- The Möbius map of an integer matrix on `ℂ`. -/
def mob (σ : Matrix (Fin 2) (Fin 2) ℤ) (z : ℂ) : ℂ :=
  (((σ 0 0 : ℤ) : ℂ) * z + ((σ 0 1 : ℤ) : ℂ)) / (((σ 1 0 : ℤ) : ℂ) * z + ((σ 1 1 : ℤ) : ℂ))

/-- The denominator `cz + d`. -/
def den (σ : Matrix (Fin 2) (Fin 2) ℤ) (z : ℂ) : ℂ :=
  ((σ 1 0 : ℤ) : ℂ) * z + ((σ 1 1 : ℤ) : ℂ)

lemma coe_ofComplex {z : ℂ} (hz : z ∈ UHP) :
    ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

lemma den_ne_zero (σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) : den σ z ≠ 0 := by
  have := denom_SL_ne_zero σ (UpperHalfPlane.ofComplex z)
  rwa [coe_ofComplex hz] at this

lemma mob_eq_coe_smul (σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) :
    mob σ z =
      ((Matrix.SpecialLinearGroup.mapGL ℝ σ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) := by
  rw [← toGL_SL, coe_toGL_smul (by simp), coe_ofComplex hz]
  rfl

lemma mob_mem_UHP (σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) : mob σ z ∈ UHP := by
  rw [mob_eq_coe_smul σ hz]
  exact (Matrix.SpecialLinearGroup.mapGL ℝ σ • UpperHalfPlane.ofComplex z).im_pos

lemma ofComplex_mob (σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) :
    UpperHalfPlane.ofComplex (mob σ z) =
      Matrix.SpecialLinearGroup.mapGL ℝ σ • UpperHalfPlane.ofComplex z := by
  rw [mob_eq_coe_smul σ hz, UpperHalfPlane.ofComplex_apply]

lemma det_SL_cast (σ : SL(2, ℤ)) :
    ((σ 0 0 : ℤ) : ℂ) * ((σ 1 1 : ℤ) : ℂ) - ((σ 0 1 : ℤ) : ℂ) * ((σ 1 0 : ℤ) : ℂ) = 1 := by
  have := σ.2
  rw [Matrix.det_fin_two] at this
  exact_mod_cast this

lemma hasDerivAt_mob (σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) :
    HasDerivAt (mob σ) (1 / den σ z ^ 2) z := by
  have hd := den_ne_zero σ hz
  have h1 : HasDerivAt (fun w : ℂ => ((σ 0 0 : ℤ) : ℂ) * w + ((σ 0 1 : ℤ) : ℂ))
      ((σ 0 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((σ 0 0 : ℤ) : ℂ)).add_const ((σ 0 1 : ℤ) : ℂ)
  have h2 : HasDerivAt (fun w : ℂ => ((σ 1 0 : ℤ) : ℂ) * w + ((σ 1 1 : ℤ) : ℂ))
      ((σ 1 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((σ 1 0 : ℤ) : ℂ)).add_const ((σ 1 1 : ℤ) : ℂ)
  refine (h1.div h2 hd).congr_deriv ?_
  have hdet := det_SL_cast σ
  have hd' : ((σ 1 0 : ℤ) : ℂ) * z + ((σ 1 1 : ℤ) : ℂ) ≠ 0 := hd
  unfold den
  field_simp
  linear_combination hdet

/-! #### Vector-valued functions -/

/-- `Σ_j C(n,j) a_j X^j Y^{n-j}`. -/
def vecOfConst (n : ℕ) (a : ℕ → ℂ) : Binary ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    MvPolynomial.monomial (binaryExponent n j) ((n.choose j : ℂ) * a j)

/-- The same, with function coefficients. -/
def vecOfFun (n : ℕ) (φ : ℕ → ℂ → ℂ) (z : ℂ) : Binary ℂ := vecOfConst n (fun j => φ j z)

/-- `h(w) (wX + Y)^n`. -/
def Fvec (h : ℍ → ℂ) (n : ℕ) : ℂ → Binary ℂ := vecOfFun n (Fj h)

/-- The vector of normalized primitives. -/
def Gvec (h : ℍ → ℂ) (n : ℕ) : ℂ → Binary ℂ := vecOfFun n (fun j => normPrim (Fj h j))

lemma lin_pow (w : ℂ) (n : ℕ) :
    (MvPolynomial.C w * MvPolynomial.X 0 + MvPolynomial.X 1 : Binary ℂ) ^ n =
      vecOfConst n (fun j => w ^ j) := by
  rw [add_pow, vecOfConst]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [monomial_binaryExponent, mul_pow, ← MvPolynomial.C_pow, MvPolynomial.C_mul,
    ← MvPolynomial.C_eq_coe_nat]
  ring

lemma Fvec_eq (h : ℍ → ℂ) (n : ℕ) (w : ℂ) :
    Fvec h n w = h (UpperHalfPlane.ofComplex w) •
      (MvPolynomial.C w * MvPolynomial.X 0 + MvPolynomial.X 1 : Binary ℂ) ^ n := by
  rw [lin_pow, Fvec, vecOfFun, vecOfConst, vecOfConst, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.smul_monomial, Fj]
  congr 1; ring

lemma act_lin (σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) :
    act σ (MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1 : Binary ℂ) =
      MvPolynomial.C (den σ z) * (MvPolynomial.C (mob σ z) * MvPolynomial.X 0 + MvPolynomial.X 1) := by
  have hd := den_ne_zero σ hz
  have hm : den σ z * mob σ z = ((σ 0 0 : ℤ) : ℂ) * z + ((σ 0 1 : ℤ) : ℂ) := by
    unfold mob den at hd ⊢
    field_simp
  have hR : MvPolynomial.C (den σ z) * (MvPolynomial.C (mob σ z) * MvPolynomial.X 0 +
      MvPolynomial.X 1 : Binary ℂ) =
      MvPolynomial.C (den σ z * mob σ z) * MvPolynomial.X 0 + MvPolynomial.C (den σ z) *
        MvPolynomial.X 1 := by
    rw [MvPolynomial.C_mul]; ring
  rw [hR, hm, act_eq_actAlg, map_add, map_mul, ← act_eq_actAlg, ← act_eq_actAlg,
    ← act_eq_actAlg, act_C, act_X, act_X]
  simp only [Fin.sum_univ_two, MvPolynomial.smul_eq_C_mul]
  unfold den
  simp only [map_add, map_mul]
  ring

lemma Fvec_mob (σ : SL(2, ℤ)) {h h' : ℍ → ℂ} {n : ℕ}
    (hrel : ∀ τ : ℍ, h (Matrix.SpecialLinearGroup.mapGL ℝ σ • τ) =
      (((σ 1 0 : ℤ) : ℂ) * τ + ((σ 1 1 : ℤ) : ℂ)) ^ (n + 2) * h' τ)
    {z : ℂ} (hz : z ∈ UHP) :
    Fvec h n (mob σ z) = den σ z ^ 2 • act σ (Fvec h' n z) := by
  rw [Fvec_eq, Fvec_eq, ofComplex_mob σ hz, hrel, coe_ofComplex hz, map_smul, act_eq_actAlg,
    map_pow, ← act_eq_actAlg, act_lin σ hz]
  unfold den
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, mul_pow]
  ring

/-! #### Coefficients and derivatives -/

lemma coeff_vecOfConst (n : ℕ) (a : ℕ → ℂ) (m : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff m (vecOfConst n a) =
      ∑ j ∈ Finset.range (n + 1),
        if binaryExponent n j = m then (n.choose j : ℂ) * a j else 0 := by
  simp [vecOfConst, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

lemma coeff_act_vecOfConst (σ : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) (a : ℕ → ℂ) (m : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff m (act σ (vecOfConst n a)) =
      ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℂ) * a j) *
        MvPolynomial.coeff m (act σ (MvPolynomial.monomial (binaryExponent n j) 1)) := by
  simp only [vecOfConst, map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (MvPolynomial.monomial (binaryExponent n j) ((n.choose j : ℂ) * a j) : Binary ℂ) =
      ((n.choose j : ℂ) * a j) • MvPolynomial.monomial (binaryExponent n j) 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, MvPolynomial.coeff_smul,
    smul_eq_mul]

lemma hasDerivAt_finset_sum' {ι : Type*} {u : Finset ι} {A : ι → ℂ → ℂ} {A' : ι → ℂ} {x : ℂ}
    (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) :
    HasDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  have := HasDerivAt.sum h
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [Finset.sum_apply]

lemma hasDerivAt_coeff_vecOfFun {n : ℕ} {φ φ' : ℕ → ℂ → ℂ} {z : ℂ}
    (hφ : ∀ j ∈ Finset.range (n + 1), HasDerivAt (φ j) (φ' j z) z) (m : Fin 2 →₀ ℕ) :
    HasDerivAt (fun w => MvPolynomial.coeff m (vecOfFun n φ w))
      (MvPolynomial.coeff m (vecOfFun n φ' z)) z := by
  have hfun : (fun w => MvPolynomial.coeff m (vecOfFun n φ w)) = fun w =>
      ∑ j ∈ Finset.range (n + 1),
        if binaryExponent n j = m then (n.choose j : ℂ) * φ j w else 0 := by
    funext w; exact coeff_vecOfConst n _ m
  rw [hfun, vecOfFun, coeff_vecOfConst]
  apply hasDerivAt_finset_sum'
  intro j hj
  by_cases hp : binaryExponent n j = m
  · simp only [hp, if_true]
    exact (hφ j hj).const_mul _
  · simp only [hp, if_false]
    exact hasDerivAt_const _ _

lemma hasDerivAt_coeff_act_vecOfFun (σ : Matrix (Fin 2) (Fin 2) ℤ) {n : ℕ} {φ φ' : ℕ → ℂ → ℂ}
    {z : ℂ} (hφ : ∀ j ∈ Finset.range (n + 1), HasDerivAt (φ j) (φ' j z) z) (m : Fin 2 →₀ ℕ) :
    HasDerivAt (fun w => MvPolynomial.coeff m (act σ (vecOfFun n φ w)))
      (MvPolynomial.coeff m (act σ (vecOfFun n φ' z))) z := by
  have hfun : (fun w => MvPolynomial.coeff m (act σ (vecOfFun n φ w))) = fun w =>
      ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℂ) * φ j w) *
        MvPolynomial.coeff m (act σ (MvPolynomial.monomial (binaryExponent n j) 1)) := by
    funext w; exact coeff_act_vecOfConst σ n _ m
  rw [hfun, vecOfFun, coeff_act_vecOfConst]
  apply hasDerivAt_finset_sum'
  intro j hj
  exact ((hφ j hj).const_mul _).mul_const _

lemma hasDerivAt_coeff_vecOfFun_comp {n : ℕ} {φ φ' : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {D z : ℂ}
    (hg : HasDerivAt g D z)
    (hφ : ∀ j ∈ Finset.range (n + 1), HasDerivAt (φ j) (φ' j (g z)) (g z)) (m : Fin 2 →₀ ℕ) :
    HasDerivAt (fun w => MvPolynomial.coeff m (vecOfFun n φ (g w)))
      (D * MvPolynomial.coeff m (vecOfFun n φ' (g z))) z := by
  have hfun : (fun w => MvPolynomial.coeff m (vecOfFun n φ (g w))) = fun w =>
      ∑ j ∈ Finset.range (n + 1),
        if binaryExponent n j = m then (n.choose j : ℂ) * φ j (g w) else 0 := by
    funext w; exact coeff_vecOfConst n _ m
  rw [hfun, vecOfFun, coeff_vecOfConst, Finset.mul_sum]
  apply hasDerivAt_finset_sum'
  intro j hj
  by_cases hp : binaryExponent n j = m
  · simp only [hp, if_true]
    have := ((hφ j hj).comp z hg).const_mul (n.choose j : ℂ)
    refine this.congr_deriv ?_
    ring
  · simp only [hp, if_false, mul_zero]
    exact hasDerivAt_const _ _

/-! #### The transport theorem -/

/-- The constant `K_h(σ)`. -/
def Kconst (σ : SL(2, ℤ)) (h h' : ℍ → ℂ) (n : ℕ) : Binary ℂ :=
  Gvec h n (mob σ I) - act σ (Gvec h' n I)

lemma I_mem_UHP : (I : ℂ) ∈ UHP := by simp [mem_UHP]

theorem transport (σ : SL(2, ℤ)) {h h' : ℍ → ℂ} {n : ℕ}
    (hrel : ∀ τ : ℍ, h (Matrix.SpecialLinearGroup.mapGL ℝ σ • τ) =
      (((σ 1 0 : ℤ) : ℂ) * τ + ((σ 1 1 : ℤ) : ℂ)) ^ (n + 2) * h' τ)
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (hh' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h')
    (hd : ∀ j, Decays (Fj h j)) (hd' : ∀ j, Decays (Fj h' j)) {z : ℂ} (hz : z ∈ UHP) :
    Gvec h n (mob σ z) = act σ (Gvec h' n z) + Kconst σ h h' n := by
  have hG : ∀ j, ∀ w ∈ UHP, HasDerivAt (normPrim (Fj h j)) (Fj h j w) w :=
    fun j => (normPrim_spec (differentiableOn_Fj hh j) (hd j)).1
  have hG' : ∀ j, ∀ w ∈ UHP, HasDerivAt (normPrim (Fj h' j)) (Fj h' j w) w :=
    fun j => (normPrim_spec (differentiableOn_Fj hh' j) (hd' j)).1
  have hconst : ∀ m : Fin 2 →₀ ℕ, ∀ w ∈ UHP,
      MvPolynomial.coeff m (Gvec h n (mob σ w)) - MvPolynomial.coeff m (act σ (Gvec h' n w)) =
      MvPolynomial.coeff m (Gvec h n (mob σ I)) - MvPolynomial.coeff m (act σ (Gvec h' n I)) := by
    intro m w hw
    refine eq_const_of_hasDerivAt_zero (G := fun w => MvPolynomial.coeff m (Gvec h n (mob σ w)) -
      MvPolynomial.coeff m (act σ (Gvec h' n w))) ?_ w hw I I_mem_UHP
    intro u hu
    have h1 : HasDerivAt (fun w => MvPolynomial.coeff m (Gvec h n (mob σ w)))
        ((1 / den σ u ^ 2) * MvPolynomial.coeff m (Fvec h n (mob σ u))) u :=
      hasDerivAt_coeff_vecOfFun_comp (hasDerivAt_mob σ hu)
        (fun j _ => hG j _ (mob_mem_UHP σ hu)) m
    have h2 : HasDerivAt (fun w => MvPolynomial.coeff m (act σ (Gvec h' n w)))
        (MvPolynomial.coeff m (act σ (Fvec h' n u))) u :=
      hasDerivAt_coeff_act_vecOfFun σ (fun j _ => hG' j u hu) m
    refine (h1.sub h2).congr_deriv ?_
    rw [Fvec_mob σ hrel hu, MvPolynomial.coeff_smul, smul_eq_mul]
    have hd0 := den_ne_zero σ hu
    field_simp
    ring
  ext m
  rw [MvPolynomial.coeff_add, Kconst, MvPolynomial.coeff_sub]
  have := hconst m z hz
  linear_combination this

/-! ### Part 5: cusp forms -/

section CuspForms
variable {N k : ℕ}

lemma isArithmetic_conj (hN : 0 < N) (σ : SL(2, ℤ)) :
    (toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)⁻¹ •
      MTT.GammaOne N).IsArithmetic := by
  let : NeZero N := ⟨by omega⟩
  let : (MTT.GammaOne N).IsArithmetic := by dsimp [MTT.GammaOne]; infer_instance
  simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, Matrix.SpecialLinearGroup.map_mapGL]
    using! Subgroup.IsArithmetic.conj (MTT.GammaOne N) (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹

lemma holo_slash (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (σ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ) :=
  (ModularFormClass.holo f).slash (k : ℤ) _

lemma decays_slash (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (σ : SL(2, ℤ)) (j : ℕ) :
    Decays (Fj (⇑f ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ) j) := by
  let : NeZero N := ⟨by omega⟩
  let : (MTT.GammaOne N).IsArithmetic := by dsimp [MTT.GammaOne]; infer_instance
  let := isArithmetic_conj hN σ
  let F := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' F
  exact decays_Fj hc hO j

lemma decays_self (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (j : ℕ) :
    Decays (Fj f j) := by
  have := decays_slash hN f 1 j
  simpa [map_one, SlashAction.slash_one] using this

lemma slash_rel (g : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    g (Matrix.SpecialLinearGroup.mapGL ℝ σ • τ) =
      (((σ 1 0 : ℤ) : ℂ) * τ + ((σ 1 1 : ℤ) : ℂ)) ^ k *
        (g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ) τ := by
  rw [slash_mapGL_apply]
  have hd := denom_SL_ne_zero σ τ
  rw [zpow_neg, zpow_natCast]
  field_simp

/-- Transport for cusp forms on `Γ₁(N)`. -/
lemma transport_cuspForm (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) :
    Gvec f (k - 2) (mob σ z) =
      act σ (Gvec (⇑f ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ) (k - 2) z) +
        Kconst σ f (⇑f ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ) (k - 2) := by
  refine transport σ ?_ (ModularFormClass.holo f) (holo_slash f σ) (decays_self hN f)
    (decays_slash hN f σ) hz
  intro τ
  rw [show k - 2 + 2 = k by omega]
  exact slash_rel (k := k) f σ τ

/-! #### Limits of coefficients -/

lemma tendsto_coeff_vecOfFun {n : ℕ} {φ : ℕ → ℂ → ℂ} {z : ℕ → ℂ} {a : ℕ → ℂ}
    (hφ : ∀ j ∈ Finset.range (n + 1), Tendsto (fun m => φ j (z m)) atTop (𝓝 (a j)))
    (e : Fin 2 →₀ ℕ) :
    Tendsto (fun m => MvPolynomial.coeff e (vecOfFun n φ (z m))) atTop
      (𝓝 (MvPolynomial.coeff e (vecOfConst n a))) := by
  simp only [vecOfFun, coeff_vecOfConst]
  apply tendsto_finset_sum
  intro j hj
  by_cases hp : binaryExponent n j = e
  · simp only [hp, if_true]; exact (hφ j hj).const_mul _
  · simp only [hp, if_false]; exact tendsto_const_nhds

lemma tendsto_coeff_act_vecOfFun (σ : Matrix (Fin 2) (Fin 2) ℤ) {n : ℕ} {φ : ℕ → ℂ → ℂ}
    {z : ℕ → ℂ} (hφ : ∀ j ∈ Finset.range (n + 1), Tendsto (fun m => φ j (z m)) atTop (𝓝 0))
    (e : Fin 2 →₀ ℕ) :
    Tendsto (fun m => MvPolynomial.coeff e (act σ (vecOfFun n φ (z m)))) atTop (𝓝 0) := by
  simp only [vecOfFun, coeff_act_vecOfConst]
  have := tendsto_finset_sum (Finset.range (n + 1)) fun j hj =>
    (((hφ j hj).const_mul (n.choose j : ℂ)).mul_const
      (MvPolynomial.coeff e (act σ (MvPolynomial.monomial (binaryExponent n j) 1))))
  simpa using this

lemma Kconst_eq_of_tendsto {σ : SL(2, ℤ)} {h h' : ℍ → ℂ} {n : ℕ}
    (hK : ∀ z ∈ UHP, Gvec h n (mob σ z) = act σ (Gvec h' n z) + Kconst σ h h' n)
    (z : ℕ → ℂ) (hz : ∀ m, z m ∈ UHP) (V : Binary ℂ)
    (h1 : ∀ e, Tendsto (fun m => MvPolynomial.coeff e (Gvec h n (mob σ (z m)))) atTop
      (𝓝 (MvPolynomial.coeff e V)))
    (h2 : ∀ e, Tendsto (fun m => MvPolynomial.coeff e (act σ (Gvec h' n (z m)))) atTop (𝓝 0)) :
    Kconst σ h h' n = V := by
  ext e
  have hlim := (h1 e).sub (h2 e)
  have hc : ∀ m, MvPolynomial.coeff e (Gvec h n (mob σ (z m))) -
      MvPolynomial.coeff e (act σ (Gvec h' n (z m))) = MvPolynomial.coeff e (Kconst σ h h' n) := by
    intro m; rw [hK (z m) (hz m), MvPolynomial.coeff_add]; ring
  simp only [hc, sub_zero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-! #### The vertical line above a cusp -/

lemma mob_vertical (σ : SL(2, ℤ)) (hc : ((σ 1 0 : ℤ) : ℂ) ≠ 0) {s : ℝ} (hs : 0 < s) :
    mob σ (((-((σ 1 1 : ℤ) : ℝ) / ((σ 1 0 : ℤ) : ℝ) : ℝ) : ℂ) +
        ((1 / (((σ 1 0 : ℤ) : ℝ) ^ 2 * s) : ℝ) : ℂ) * I) =
      ((((σ 0 0 : ℤ) : ℝ) / ((σ 1 0 : ℤ) : ℝ) : ℝ) : ℂ) + (s : ℂ) * I := by
  have hdet := det_SL_cast σ
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold mob
  push_cast
  set A : ℂ := ((σ 0 0 : ℤ) : ℂ) with hA
  set B : ℂ := ((σ 0 1 : ℤ) : ℂ) with hB
  set C : ℂ := ((σ 1 0 : ℤ) : ℂ) with hC
  set D : ℂ := ((σ 1 1 : ℤ) : ℂ) with hD
  have h1 : C * (-D / C + 1 / (C ^ 2 * s) * I) + D = I / (C * s) := by
    field_simp; ring
  have h2 : A * (-D / C + 1 / (C ^ 2 * s) * I) + B = A * I / (C ^ 2 * s) - 1 / C := by
    field_simp; linear_combination (-(C * s)) * hdet
  rw [h1, h2]
  have hI : I / (C * s) ≠ 0 := div_ne_zero I_ne_zero (mul_ne_zero hc hs')
  rw [div_eq_iff hI]
  field_simp
  linear_combination (-(C * s)) * Complex.I_sq

lemma mem_UHP_vertical (x : ℝ) {T : ℝ} (hT : 0 < T) : (x : ℂ) + (T : ℂ) * I ∈ UHP :=
  mk_mem_UHP hT

/-! #### Cusps -/

lemma mapGL_apply_Q (σ : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ((σ i j : ℤ) : ℚ) := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]; simp

lemma cuspAct_infty_SL (σ : SL(2, ℤ)) :
    cuspAct σ OnePoint.infty = if ((σ 1 0 : ℤ) : ℚ) = 0 then OnePoint.infty
      else ((((σ 0 0 : ℤ) : ℚ) / ((σ 1 0 : ℤ) : ℚ) : ℚ) : Cusp) := by
  unfold cuspAct
  rw [OnePoint.smul_infty_eq_ite]
  simp only [mapGL_apply_Q]

lemma cuspAct_mul (γ δ : SL(2, ℤ)) (x : Cusp) :
    cuspAct (γ * δ) x = cuspAct γ (cuspAct δ x) := by
  simp only [cuspAct, map_mul, mul_smul]

lemma exists_SL_infty_eq (r : ℚ) : ∃ σ : SL(2, ℤ), cuspAct σ OnePoint.infty = (r : Cusp) := by
  have hcop : IsCoprime r.num (r.den : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr r.reduced
  obtain ⟨s, t, hst⟩ := hcop
  let σ : SL(2, ℤ) := ⟨!![r.num, -t; (r.den : ℤ), s], by
    rw [Matrix.det_fin_two_of]; linear_combination hst⟩
  refine ⟨σ, ?_⟩
  rw [cuspAct_infty_SL]
  have h10 : (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (r.den : ℤ) := rfl
  have h00 : (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = r.num := rfl
  have hd : ((r.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [h10, h00, if_neg hd]
  congr 1
  push_cast
  exact Rat.num_div_den r

lemma cuspPrimitive_coe (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) :
    cuspPrimitive f (r : Cusp) = cuspPeriodPolynomial f r := rfl

lemma cuspPrimitive_infty (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    cuspPrimitive f OnePoint.infty = 0 := rfl

lemma cuspPeriodPolynomial_eq (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) :
    cuspPeriodPolynomial f r =
      vecOfConst (k - 2) (fun j => MTT.modularIntegral f (Polynomial.X ^ j) r) := by
  unfold cuspPeriodPolynomial vecOfConst
  rw [show k - 1 = k - 2 + 1 by omega]

lemma modularIntegral_X_pow (f : ℍ → ℂ) (j : ℕ) (r : ℚ) :
    MTT.modularIntegral f (Polynomial.X ^ j) r =
      (2 * Real.pi : ℂ) * ∫ t : ℝ in Ioi (0 : ℝ), Fj f j ((r : ℂ) + t * I) := by
  unfold MTT.modularIntegral
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Fj, Polynomial.eval_pow, Polynomial.eval_X]
  rw [mul_comm I (t : ℂ)]

/-! #### The value at `σ∞` -/

lemma mob_mul (γ σ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ UHP) :
    mob ((γ * σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) z = mob γ (mob σ z) := by
  rw [mob_eq_coe_smul (γ * σ) hz, mob_eq_coe_smul γ (mob_mem_UHP σ hz), ofComplex_mob σ hz,
    map_mul, mul_smul]

lemma vecOfConst_zero (n : ℕ) : vecOfConst n (fun _ => (0 : ℂ)) = 0 := by
  simp [vecOfConst]

/-- The value of the cusp primitive at the cusp `σ∞` is `2πi K_f(σ)`. -/
theorem cuspPrimitive_eq_Kconst (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (σ : SL(2, ℤ)) :
    cuspPrimitive f (cuspAct σ OnePoint.infty) =
      (2 * Real.pi * I : ℂ) •
        Kconst σ f (⇑f ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ) (k - 2) := by
  set n := k - 2 with hn
  set h' : ℍ → ℂ := ⇑f ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ with hh'
  have hK : ∀ z ∈ UHP, Gvec f n (mob σ z) = act σ (Gvec h' n z) + Kconst σ f h' n :=
    fun z hz => transport_cuspForm hN hk f σ hz
  have hnorm' : ∀ j (x : ℝ),
      Tendsto (fun T : ℝ => normPrim (Fj h' j) ((x : ℂ) + T * I)) atTop (𝓝 0) :=
    fun j x => (normPrim_spec (differentiableOn_Fj (holo_slash f σ) j) (decays_slash hN f σ j)).2 x
  have hnorm : ∀ j (x : ℝ),
      Tendsto (fun T : ℝ => normPrim (Fj f j) ((x : ℂ) + T * I)) atTop (𝓝 0) :=
    fun j x => (normPrim_spec (differentiableOn_Fj (ModularFormClass.holo f) j)
      (decays_self hN f j)).2 x
  have hG : ∀ j, ∀ w ∈ UHP, HasDerivAt (normPrim (Fj f j)) (Fj f j w) w :=
    fun j => (normPrim_spec (differentiableOn_Fj (ModularFormClass.holo f) j)
      (decays_self hN f j)).1
  have hTnat : Tendsto (fun m : ℕ => ((m : ℝ) + 1)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  by_cases hc : ((σ 1 0 : ℤ) : ℚ) = 0
  · rw [cuspAct_infty_SL, if_pos hc, cuspPrimitive_infty]
    have hc' : σ 1 0 = 0 := by exact_mod_cast hc
    have had : σ 0 0 * σ 1 1 = 1 := by
      have := σ.2
      rw [Matrix.det_fin_two, hc'] at this
      simpa using this
    have hd2 : σ 1 1 * σ 1 1 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    have had' : ((σ 0 0 : ℤ) : ℂ) * ((σ 1 1 : ℤ) : ℂ) = 1 := by exact_mod_cast had
    have hd2' : ((σ 1 1 : ℤ) : ℂ) * ((σ 1 1 : ℤ) : ℂ) = 1 := by exact_mod_cast hd2
    have hd : ((σ 1 1 : ℤ) : ℂ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hd2'; exact zero_ne_one hd2'
    have hmob : ∀ T : ℝ, mob σ (((0 : ℝ) : ℂ) + (T : ℂ) * I) =
        (((σ 0 1 * σ 1 1 : ℤ) : ℝ) : ℂ) + (T : ℂ) * I := by
      intro T
      unfold mob
      rw [hc']
      push_cast
      rw [div_eq_iff (by simpa using hd)]
      linear_combination ((T : ℂ) * I * ((σ 1 1 : ℤ) : ℂ)) * had' -
        ((T : ℂ) * I * ((σ 0 0 : ℤ) : ℂ) + ((σ 0 1 : ℤ) : ℂ)) * hd2'
    set z : ℕ → ℂ := fun m => ((0 : ℝ) : ℂ) + (((m : ℝ) + 1 : ℝ) : ℂ) * I with hz
    have hzU : ∀ m, z m ∈ UHP := fun m => mem_UHP_vertical 0 (by positivity)
    have hK0 : Kconst σ f h' n = 0 := by
      refine Kconst_eq_of_tendsto hK z hzU 0 ?_ ?_
      · intro e
        have h1 := tendsto_coeff_vecOfFun (n := n) (φ := fun j => normPrim (Fj f j))
          (z := fun m => (((σ 0 1 * σ 1 1 : ℤ) : ℝ) : ℂ) + (((m : ℝ) + 1 : ℝ) : ℂ) * I)
          (a := fun _ => 0) (fun j _ => (hnorm j _).comp hTnat) e
        rw [vecOfConst_zero] at h1
        refine h1.congr fun m => ?_
        simp only [z, Gvec]
        rw [hmob]
      · intro e
        exact tendsto_coeff_act_vecOfFun σ (n := n) (φ := fun j => normPrim (Fj h' j)) (z := z)
          (fun j _ => (hnorm' j 0).comp hTnat) e
    rw [hK0, smul_zero]
  · rw [cuspAct_infty_SL, if_neg hc, cuspPrimitive_coe, cuspPeriodPolynomial_eq hk]
    set q : ℚ := ((σ 0 0 : ℤ) : ℚ) / ((σ 1 0 : ℤ) : ℚ) with hq
    have hcZ : σ 1 0 ≠ 0 := fun h => hc (by rw [h]; simp)
    have hcC : ((σ 1 0 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hcZ
    have hcR : ((σ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hcZ
    set s : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hs_def
    set p : ℝ := -((σ 1 1 : ℤ) : ℝ) / ((σ 1 0 : ℤ) : ℝ) with hp
    set T : ℕ → ℝ := fun m => 1 / (((σ 1 0 : ℤ) : ℝ) ^ 2 * s m) with hT_def
    set z : ℕ → ℂ := fun m => (p : ℂ) + ((T m : ℝ) : ℂ) * I with hz
    have hs : ∀ m, 0 < s m := fun m => by positivity
    have hT : ∀ m, 0 < T m := fun m => by
      have := hs m
      have : (0 : ℝ) < ((σ 1 0 : ℤ) : ℝ) ^ 2 := by positivity
      positivity
    have hzU : ∀ m, z m ∈ UHP := fun m => mem_UHP_vertical p (hT m)
    have hmob : ∀ m, mob σ (z m) = ((q : ℝ) : ℂ) + ((s m : ℝ) : ℂ) * I := by
      intro m
      have := mob_vertical σ hcC (hs m)
      simp only [z, p, T]
      rw [this, hq]
      push_cast
      ring
    have hTinf : Tendsto T atTop atTop := by
      have : T = fun m : ℕ => ((m : ℝ) + 1) / ((σ 1 0 : ℤ) : ℝ) ^ 2 := by
        funext m; simp only [T, s]; field_simp
      rw [this]
      exact hTnat.atTop_div_const (by positivity)
    set V : Binary ℂ := vecOfConst n
      (fun j => -(I * ∫ t : ℝ in Ioi (0 : ℝ), Fj f j (((q : ℝ) : ℂ) + t * I))) with hV
    have hKV : Kconst σ f h' n = V := by
      refine Kconst_eq_of_tendsto hK z hzU V ?_ ?_
      · intro e
        have h1 := tendsto_coeff_vecOfFun (n := n) (φ := fun j => normPrim (Fj f j))
          (z := fun m => ((q : ℝ) : ℂ) + ((s m : ℝ) : ℂ) * I)
          (a := fun j => -(I * ∫ t : ℝ in Ioi (0 : ℝ), Fj f j (((q : ℝ) : ℂ) + t * I)))
          (fun j _ => ?_) e
        · refine h1.congr fun m => ?_
          simp only [Gvec]
          rw [hmob]
        · have hint : IntegrableOn (fun t : ℝ => Fj f j (((q : ℝ) : ℂ) + t * I)) (Ioi (0 : ℝ)) := by
            have := integrableOn_Fj_cusp hN hk f q j
            simpa [Complex.ofReal_ratCast] using this
          exact tendsto_primitive_cusp (hG j)
            (differentiableOn_Fj (ModularFormClass.holo f) j).continuousOn (hnorm j) (q : ℝ) hint
      · intro e
        exact tendsto_coeff_act_vecOfFun σ (n := n) (φ := fun j => normPrim (Fj h' j)) (z := z)
          (fun j _ => (hnorm' j p).comp hTinf) e
    rw [hKV, hV]
    simp only [vecOfConst, Finset.smul_sum, MvPolynomial.smul_monomial, modularIntegral_X_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp only [Complex.ofReal_ratCast]
    rw [hn]
    linear_combination (2 * (Real.pi : ℂ) * (((k - 2).choose j : ℕ) : ℂ) *
      ∫ t : ℝ in Ioi (0 : ℝ), Fj f j ((q : ℂ) + t * I)) * Complex.I_sq

/-! #### The cocycle and the main theorem -/

theorem Kconst_cocycle (hN : 0 < N) (hk : 2 ≤ k) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ σ : SL(2, ℤ)) (g' : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hg' : ⇑g' = ⇑g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ) :
    Kconst (γ * σ) g (⇑g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ (γ * σ)) (k - 2) =
      act γ (Kconst σ g' (⇑g' ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ) (k - 2)) +
        Kconst γ g (⇑g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ) (k - 2) := by
  have hI := I_mem_UHP
  have h1 := transport_cuspForm hN hk g (γ * σ) hI
  have h2 := transport_cuspForm hN hk g γ (mob_mem_UHP σ hI)
  have h3 := transport_cuspForm hN hk g' σ hI
  have hfun : ⇑g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ (γ * σ) =
      ⇑g' ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ σ := by
    rw [hg', map_mul, SlashAction.slash_mul]
  rw [← hg'] at h2 ⊢
  rw [hfun] at h1 ⊢
  rw [mob_mul γ σ hI, h2, h3, map_add, act_act, ← Matrix.SpecialLinearGroup.coe_mul] at h1
  linear_combination (-1 : Binary ℂ) * h1

/-- The slash relation for cusp primitives. -/
theorem cuspPrimitive_slash_relation_proof (hN : 0 < N) (hk : 2 ≤ k)
    (g g' : CuspForm (MTT.GammaOne N) (k : ℤ)) (γ : CongruenceSubgroup.Gamma0 N)
    (hg' : ∀ z : ℍ, g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
      (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z)
    (x : Cusp) :
    cuspPrimitive g (cuspAct γ.val x) =
      act γ.val.val (cuspPrimitive g' x) + cuspPrimitive g (cuspAct γ.val OnePoint.infty) := by
  have hfun : ⇑g' = ⇑g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ.val := by
    funext τ
    have h := slash_rel (k := k) (⇑g) γ.val τ
    rw [hg' τ] at h
    have hd : (((γ.val 1 0 : ℤ) : ℂ) * τ + ((γ.val 1 1 : ℤ) : ℂ)) ^ k ≠ 0 :=
      pow_ne_zero _ (denom_SL_ne_zero γ.val τ)
    exact mul_left_cancel₀ hd h
  rcases x with _ | r
  · show cuspPrimitive g (cuspAct γ.val OnePoint.infty) =
      act γ.val.val (cuspPrimitive g' OnePoint.infty) + cuspPrimitive g (cuspAct γ.val OnePoint.infty)
    rw [cuspPrimitive_infty, map_zero, zero_add]
  · show cuspPrimitive g (cuspAct γ.val (r : Cusp)) =
      act γ.val.val (cuspPrimitive g' (r : Cusp)) + cuspPrimitive g (cuspAct γ.val OnePoint.infty)
    obtain ⟨σ, hσ⟩ := exists_SL_infty_eq r
    rw [← hσ, ← cuspAct_mul, cuspPrimitive_eq_Kconst hN hk g (γ.val * σ),
      cuspPrimitive_eq_Kconst hN hk g' σ, cuspPrimitive_eq_Kconst hN hk g γ.val,
      Kconst_cocycle hN hk g γ.val σ g' hfun, smul_add, map_smul]

end CuspForms

end MTT.Eichler

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixGroups ModularForm ComplexConjugate
open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped UpperHalfPlane Manifold
open MTT.Cohomology
namespace MTT.Eichler

lemma vecOfConst_homogeneous (n : ℕ) (a : ℕ → ℂ) : vecOfConst n a ∈ MTT.Cohomology.Sym ℂ n := by
  apply Submodule.sum_mem
  intro j hj
  apply MvPolynomial.isHomogeneous_monomial
  have hjn : j ≤ n := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [Finsupp.degree_eq_sum]
  simp [binaryExponent, Finsupp.sum_fintype, Fin.sum_univ_two, Nat.add_sub_of_le hjn]

def conjugatePolynomial : Binary ℂ →+* Binary ℂ := MvPolynomial.map (starRingEnd ℂ)

lemma conjugate_act (A : Matrix (Fin 2) (Fin 2) ℤ) (Q : Binary ℂ) :
    conjugatePolynomial (act A Q) = act A (conjugatePolynomial Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [conjugatePolynomial, act_C]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    change conjugatePolynomial (actAlg A (p * MvPolynomial.X i)) =
      actAlg A (conjugatePolynomial (p * MvPolynomial.X i))
    simp only [map_mul, hp]
    congr 1
    simp [conjugatePolynomial, actAlg, MvPolynomial.smul_eq_C_mul]

lemma coeff_Gvec_deriv {N k : ℕ} (hN : 0 < N)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (e : Fin 2 →₀ ℕ)
    (z : UpperHalfPlane) : HasDerivAt (fun w => MvPolynomial.coeff e (Gvec f (k-2) w))
      (MvPolynomial.coeff e (f z • periodPower (k-2) z)) (z : ℂ) := by
  have hh := hasDerivAt_coeff_vecOfFun (n := k-2)
    (fun j _ => (normPrim_spec (differentiableOn_Fj (ModularFormClass.holo f) j)
      (decays_self hN f j)).1 z z.im_pos) e
  change HasDerivAt (fun w => MvPolynomial.coeff e (Gvec f (k-2) w))
    (MvPolynomial.coeff e (Fvec f (k-2) z)) z at hh
  simpa [Fvec_eq, periodPower] using hh

lemma real_deriv_of_complex {F : ℂ → ℂ} {a z : ℂ} (h : HasDerivAt F a z) :
    HasFDerivAt F (periodDifferential a 0) z := by
  convert! h.hasFDerivAt.restrictScalars ℝ using 1
  ext w
  simp [periodDifferential, mul_comm]

lemma conjugate_deriv_of_complex {F : ℂ → ℂ} {a z : ℂ} (h : HasDerivAt F a z) :
    HasFDerivAt (fun w => conj (F w)) (periodDifferential 0 (conj a)) z := by
  have hh := Complex.conjCLE.hasFDerivAt.comp z (h.hasFDerivAt.restrictScalars ℝ)
  convert! hh using 1
  ext w
  simp [periodDifferential, map_mul, mul_comm]

lemma mixed_Gvec_deriv {N k : ℕ} (hN : 0 < N)
    (g v : CuspForm (MTT.GammaOne N) (k : ℤ)) (Q : Binary ℂ)
    (z : UpperHalfPlane) (e : Fin 2 →₀ ℕ) :
    HasFDerivAt (fun w => MvPolynomial.coeff e
      (Gvec g (k-2) w - conjugatePolynomial (Gvec v (k-2) w) + Q))
      (periodDifferential
        (MvPolynomial.coeff e (g z • periodPower (k-2) z))
        (-MvPolynomial.coeff e (conj (v z) • periodPower (k-2) (conj (z : ℂ))))) z := by
  have hg := real_deriv_of_complex (coeff_Gvec_deriv hN g e z)
  have hv := conjugate_deriv_of_complex (coeff_Gvec_deriv hN v e z)
  have hh := (hg.sub hv).add_const (MvPolynomial.coeff e Q)
  have hc : conj (MvPolynomial.coeff e (v z • periodPower (k-2) z)) =
      MvPolynomial.coeff e (conj (v z) • periodPower (k-2) (conj (z : ℂ))) := by
    rw [← MvPolynomial.coeff_map]
    congr 1
    simp [periodPower, MvPolynomial.smul_eq_C_mul]
  convert! hh using 1
  rw [hc]
  ext w
  simp [periodDifferential]
  ring

end MTT.Eichler

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators MatrixGroups ModularForm ComplexConjugate
open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped UpperHalfPlane Manifold
open MTT.Cohomology
namespace MTT.Eichler

lemma normPrim_strip_bound {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F UHP)
    (hd : Decays F) (W : ℝ) (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ z.im → |z.re| ≤ W → ‖normPrim F z‖ ≤ C := by
  have hG := (normPrim_spec hF hd).1
  have hGc : ContinuousOn (normPrim F) UHP :=
    fun z hz => (hG z hz).continuousAt.continuousWithinAt
  have hlim := ((normPrim_spec hF hd).2 0).norm
  have hevent : ∀ᶠ y : ℝ in atTop, ‖normPrim F ((y : ℂ) * I)‖ ≤ 1 := by
    have he := hlim.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 : ℝ)))
    filter_upwards [he] with y hy
    simpa using hy.le
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hevent
  obtain ⟨c, hc, T₀, hT⟩ := hd
  obtain ⟨D, hD⟩ := hT W
  let T := max 1 (max T₀ T₁)
  have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_left _ _)
  let K : Set (ℝ × ℝ) := Icc (-W) W ×ˢ Icc 1 T
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => normPrim F ((p.1 : ℂ) + p.2 * I)) K := by
    apply hGc.comp (by fun_prop)
    intro p hp
    exact mk_mem_UHP (lt_of_lt_of_le one_pos hp.2.1)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max 0 (max B (|D| * W + 1)), le_max_left _ _, ?_⟩
  intro z hz hzr
  have heq : (z.re : ℂ) + z.im * I = z := Complex.re_add_im z
  by_cases hzy : z.im ≤ T
  · have hb := hB (z.re, z.im) ⟨abs_le.mp hzr, hz, hzy⟩
    have hbb : ‖normPrim F z‖ ≤ B := by simpa only [heq] using hb
    exact hbb.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have hyT : T ≤ z.im := (lt_of_not_ge hzy).le
    have hy0 : T₀ ≤ z.im := le_trans ((le_max_left T₀ T₁).trans (le_max_right 1 _)) hyT
    have hy1 : T₁ ≤ z.im := le_trans ((le_max_right T₀ T₁).trans (le_max_right 1 _)) hyT
    have hypos : 0 < z.im := lt_of_lt_of_le one_pos hz
    have hi := integral_horizontal hG hF.continuousOn hypos (0 : ℝ) z.re
    have hib : ‖normPrim F z - normPrim F ((z.im : ℂ) * I)‖ ≤
        (|D| * Real.exp (-c * z.im)) * |z.re| := by
      have hine : (∫ x in (0 : ℝ)..z.re, F ((x : ℂ) + z.im * I)) =
          normPrim F z - normPrim F ((z.im : ℂ) * I) := by
        simpa only [heq, Complex.ofReal_zero, zero_add] using hi
      rw [← hine]
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := z.re)
        (C := |D| * Real.exp (-c * z.im)) (fun x hx => by
          have hxW : |x| ≤ W := by
            rw [Set.uIoc_eq_union] at hx
            rcases hx with hx | hx
            · rw [abs_le]; exact ⟨(by linarith [hx.1]), hx.2.trans ((le_abs_self _).trans hzr)⟩
            · rw [abs_le]; exact ⟨(neg_le_of_abs_le hzr).trans hx.1.le, by linarith [hx.2]⟩
          exact (hD x z.im hxW hy0).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
    have hexp : Real.exp (-c * z.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hib' : ‖normPrim F z - normPrim F ((z.im : ℂ) * I)‖ ≤ |D| * W := by
      calc
        _ ≤ (|D| * Real.exp (-c * z.im)) * |z.re| := hib
        _ ≤ (|D| * 1) * W := mul_le_mul
          (mul_le_mul_of_nonneg_left hexp (abs_nonneg _)) hzr (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hb : ‖normPrim F z‖ ≤ |D| * W + 1 := by
      calc
        _ = ‖(normPrim F z - normPrim F ((z.im : ℂ) * I)) + normPrim F ((z.im : ℂ) * I)‖ := by rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add hib' (hT₁ z.im hy1))
    exact hb.trans ((le_max_right _ _).trans (le_max_right _ _))

lemma coeff_act_Gvec_strip_bound (h : UpperHalfPlane → ℂ)
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (hd : ∀ j, Decays (Fj h j))
    (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ z.im → |z.re| ≤ W →
      ‖MvPolynomial.coeff e (act A (Gvec h n z))‖ ≤ C := by
  classical
  choose C hC0 hC using fun j => normPrim_strip_bound (differentiableOn_Fj hh j) (hd j) W hW
  let b : ℕ → ℝ := fun j => ‖(n.choose j : ℂ)‖ * C j *
    ‖MvPolynomial.coeff e (act (R := ℂ) A (MvPolynomial.monomial (binaryExponent n j) 1))‖
  refine ⟨∑ j ∈ Finset.range (n+1), b j, Finset.sum_nonneg (fun j _ => by dsimp [b]; exact mul_nonneg (mul_nonneg (norm_nonneg _) (hC0 j)) (norm_nonneg _)), ?_⟩
  intro z hz hzr
  rw [Gvec, vecOfFun, coeff_act_vecOfConst]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (hC j z hz hzr) (norm_nonneg _)

lemma coeff_Gvec_cusp_bound {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (e : Fin 2 →₀ ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im → |z.re| ≤ W →
      ‖MvPolynomial.coeff e (act (δ⁻¹).val (Gvec f (k-2) (δ • z : UpperHalfPlane)))‖ ≤ C := by
  let f' := ⇑f ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ δ
  obtain ⟨C, hC0, hC⟩ := coeff_act_Gvec_strip_bound f' (holo_slash f δ)
    (decays_slash hN f δ) (k-2) 1 e W hW
  let K := Kconst δ f f' (k-2)
  refine ⟨C + ‖MvPolynomial.coeff e (act (δ⁻¹).val K)‖, by positivity, ?_⟩
  intro z hz hzr
  have ht := transport_cuspForm hN hk f δ (z := (z : ℂ)) z.im_pos
  rw [mob_eq_coe_smul δ z.im_pos] at ht
  simp only [UpperHalfPlane.ofComplex_apply] at ht
  change Gvec f (k-2) (δ • z : UpperHalfPlane) = act δ.val (Gvec f' (k-2) z) + K at ht
  rw [ht, map_add, act_act, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    act_one, MvPolynomial.coeff_add]
  apply (norm_add_le _ _).trans
  exact add_le_add (by simpa only [act_one] using hC z hz hzr) le_rfl

end MTT.Eichler

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixGroups ModularForm ComplexConjugate
open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped UpperHalfPlane Manifold
open MTT.Cohomology
namespace MTT.Eichler

lemma reflected_modular_integral {N k : ℕ}
    (h v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hv : ∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) (j : ℕ) (r : ℚ) :
    conj (MTT.modularIntegral v (Polynomial.X ^ j) r) =
      (-1 : ℂ)^j * MTT.modularIntegral h (Polynomial.X ^ j) (-r) := by
  rw [modularIntegral_X_pow, modularIntegral_X_pow, map_mul, ← integral_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal]
  rw [mul_left_comm]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hz : (r : ℂ) + t * I ∈ UHP := mk_mem_UHP ht
  have hr : periodReflect (UpperHalfPlane.ofComplex ((r : ℂ) + t * I)) =
      UpperHalfPlane.ofComplex (((-r : ℚ) : ℂ) + t * I) := by
    apply UpperHalfPlane.ext
    have hn : -(r : ℂ) + t * I ∈ UHP := by simpa [UHP] using ht
    change -conj (UpperHalfPlane.ofComplex ((r : ℂ) + t * I) : ℂ) = _
    rw [coe_ofComplex hz, Rat.cast_neg, coe_ofComplex hn]
    simp [map_add, map_mul]
    ring
  simp only [Fj, map_mul, map_pow, hv, hr]
  have hp : conj ((r : ℂ) + t * I) = (-1 : ℂ) * (((-r : ℚ) : ℂ) + t * I) := by
    simp [map_add, map_mul]; ring
  rw [hp, mul_pow]
  ring

lemma reflection_monomial (n j : ℕ) (a : ℂ) :
    act !![-1, 0; 0, 1] (MvPolynomial.monomial (binaryExponent n j) a) =
      MvPolynomial.monomial (binaryExponent n j) ((-1 : ℂ)^j * a) := by
  rw [monomial_binaryExponent, act_eq_actAlg, map_mul, map_mul, map_pow, map_pow]
  change _ = _
  simp [actAlg, monomial_binaryExponent, mul_pow]
  ring

lemma reflected_cusp_primitive {N k : ℕ}
    (h v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hv : ∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) (x : Cusp) :
    conjugatePolynomial (cuspPrimitive v x) =
      act !![-1, 0; 0, 1] (cuspPrimitive h (fractional !![-1, 0; 0, 1] x)) := by
  cases x with
  | none => simp [cuspPrimitive, fractional, conjugatePolynomial]
  | some r =>
    have hf : fractional !![-1,0;0,1] (some r) = some (-r) := by simp [fractional]; rfl
    rw [hf]
    change conjugatePolynomial (cuspPeriodPolynomial v r) =
      act !![-1,0;0,1] (cuspPeriodPolynomial h (-r))
    simp only [cuspPeriodPolynomial, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [reflection_monomial]
    simp [conjugatePolynomial, reflected_modular_integral h v hv j r, mul_comm, mul_left_comm]

end MTT.Eichler

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators MatrixGroups ModularForm ComplexConjugate
open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped UpperHalfPlane Manifold
open MTT.Cohomology
namespace MTT.Eichler

lemma Gvec_gamma {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma1 N) (z : UpperHalfPlane) :
    Gvec f (k-2) (γ.val • z : UpperHalfPlane) =
      act γ.val.val (Gvec f (k-2) z) +
        (2 * Real.pi * I : ℂ)⁻¹ • cuspPrimitive f (cuspAct γ.val OnePoint.infty) := by
  have hs := SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ.val)
    (show Matrix.SpecialLinearGroup.mapGL ℝ γ.val ∈ MTT.GammaOne N from ⟨γ.val, γ.property, rfl⟩)
  have ht := transport_cuspForm hN hk f γ.val (z := (z : ℂ)) z.im_pos
  rw [mob_eq_coe_smul γ.val z.im_pos, UpperHalfPlane.ofComplex_apply, hs] at ht
  change Gvec f (k-2) (γ.val • z : UpperHalfPlane) = _ at ht
  rw [ht, cuspPrimitive_eq_Kconst hN hk f γ.val, hs, smul_smul]
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [inv_mul_cancel₀ hc, one_smul]

lemma conjugate_smul (a : ℂ) (Q : Binary ℂ) :
    conjugatePolynomial (a • Q) = conj a • conjugatePolynomial Q := by
  simp [conjugatePolynomial, MvPolynomial.smul_eq_C_mul]

end MTT.Eichler
open MTT.Eichler

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ)
    (hP : P ∈ MTT.Cohomology.Sym ℂ (k - 2))
    (hcob : ∀ γ : CongruenceSubgroup.Gamma1 N,
      cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive h
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) =
      act γ.val.val P - P)
    (v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hv : ∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) :
    ∃ U : ℂ → Binary ℂ, IsMixedPeriodPrimitive g v U := by
  let s : ℂ := (2 * Real.pi * I : ℂ)⁻¹
  let Q : Binary ℂ := s • P
  let U : ℂ → Binary ℂ := fun w => Gvec g (k-2) w - conjugatePolynomial (Gvec v (k-2) w) + Q
  have htwo : conj (2 : ℂ) = (2 : ℂ) := by
    exact Complex.conj_ofReal 2
  have hs : conj s = -s := by
    simp only [s, map_inv₀, map_mul, htwo, Complex.conj_ofReal, Complex.conj_I, mul_neg, inv_neg]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro z
    apply (MTT.Cohomology.Sym ℂ (k-2)).add_mem
    · exact (vecOfConst_homogeneous _ _).sub ((vecOfConst_homogeneous _ _).map (starRingEnd ℂ))
    · exact (MTT.Cohomology.Sym ℂ (k-2)).smul_mem s hP
  · intro γ z
    have hp := hcob γ
    rw [← reflected_cusp_primitive h v hv] at hp
    have hp' := congrArg (fun R : Binary ℂ => s • R) hp
    simp only [smul_add, smul_sub, ← map_smul] at hp'
    change Gvec g (k-2) (γ.val • z : UpperHalfPlane) -
      conjugatePolynomial (Gvec v (k-2) (γ.val • z : UpperHalfPlane)) + Q =
      act γ.val.val (Gvec g (k-2) z - conjugatePolynomial (Gvec v (k-2) z) + Q)
    rw [Gvec_gamma hN hk g γ z, Gvec_gamma hN hk v γ z]
    change act γ.val.val (Gvec g (k-2) z) + s • cuspPrimitive g _ -
      conjugatePolynomial (act γ.val.val (Gvec v (k-2) z) + s • cuspPrimitive v _) + Q = _
    rw [map_add, conjugate_act, conjugate_smul, hs, neg_smul, map_add, map_sub]
    change _ = _ + act γ.val.val Q
    have hp'' : s • cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        s • conjugatePolynomial (cuspPrimitive v (cuspAct γ.val OnePoint.infty)) + Q = act γ.val.val Q := by
      dsimp [Q]
      rw [hp', sub_add_cancel]
    rw [← hp'']
    abel
  · intro z e
    exact mixed_Gvec_deriv hN g v Q z e
  · intro δ e W hW
    obtain ⟨Cg, hCg, hgb⟩ := coeff_Gvec_cusp_bound hN hk g δ e W hW
    obtain ⟨Cv, hCv, hvb⟩ := coeff_Gvec_cusp_bound hN hk v δ e W hW
    let D : ℝ := ‖MvPolynomial.coeff e (act (δ⁻¹).val Q)‖
    refine ⟨Cg + Cv + D, 0, by dsimp [D]; positivity, ?_⟩
    intro z hz hzr
    change ‖MvPolynomial.coeff e (act (δ⁻¹).val
      (Gvec g (k-2) (δ • z : UpperHalfPlane) - conjugatePolynomial (Gvec v (k-2) (δ • z : UpperHalfPlane)) + Q))‖ ≤ _
    rw [map_add, map_sub, ← conjugate_act, MvPolynomial.coeff_add, MvPolynomial.coeff_sub]
    simp only [pow_zero, mul_one]
    apply (norm_add_le _ _).trans
    apply add_le_add _ le_rfl
    apply (norm_sub_le _ _).trans
    apply add_le_add (hgb z hz hzr)
    simpa only [conjugatePolynomial, MvPolynomial.coeff_map, Complex.norm_conj] using hvb z hz hzr
