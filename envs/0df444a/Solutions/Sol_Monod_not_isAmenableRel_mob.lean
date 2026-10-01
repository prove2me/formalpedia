-- Prove2me | solution 1 for Monod.not_isAmenableRel_mob
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-01T10:56:51.128992+00:00
-- url     : https://prove2.me/submissions/be4e9942-d229-4ddf-a1b6-1b20f394b32f

import Definitions.Def_Monod_PiecewiseProjective
import Mathlib

section
/-! Shared definitions for the Carrière–Ghys argument (Monod C9, `not_isAmenableRel_mob`). -/

namespace Monod.Dev.CG

open Matrix

variable {A : Subring ℝ}

/-- `a_t = [[t, -1], [1, 0]]`, elliptic when `|t| < 2`: `x ↦ t - 1/x`. -/
def ell (t : A) : SpecialLinearGroup (Fin 2) A :=
  ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- `g = [[1, 1], [1, 2]]`. -/
def gConj : SpecialLinearGroup (Fin 2) A :=
  ⟨!![1, 1; 1, 2], by norm_num [Matrix.det_fin_two]⟩

/-- `b_t = g a_t g⁻¹`. -/
def bEl (t : A) : SpecialLinearGroup (Fin 2) A := gConj * ell t * gConj⁻¹

/-- The orbit relation of `SL(2, A)` on `P¹`. -/
def orbRel (A : Subring ℝ) : Set (OnePoint ℝ × OnePoint ℝ) :=
  {p | ∃ g : SpecialLinearGroup (Fin 2) A, mob g p.1 = p.2}

end Monod.Dev.CG
end

section
/-! A4 of the Carrière–Ghys argument: for `|t| < 2`, the elliptic Möbius map `a_t : x ↦ t - 1/x`
preserves the finite measure `dx / (x² - t x + 1)` on `P¹`, which has the same null sets as
`volP1`; so `a_t` is conservative and every a.e. wandering set for `a_t` is null. -/

namespace Monod.Dev.CG.A4

open MeasureTheory Matrix OnePoint Set Filter

variable {A : Subring ℝ}

/-! ### The Möbius action of `ell t` -/

lemma mob_mul (g h : SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (g * h) x = mob g (mob h x) := by
  unfold mob; rw [map_mul, mul_smul]

lemma mob_one (x : OnePoint ℝ) : mob (1 : SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob; rw [map_one, one_smul]

lemma mob_pow (g : SpecialLinearGroup (Fin 2) A) (n : ℕ) : mob (g ^ n) = (mob g)^[n] := by
  induction n with
  | zero => funext x; simp [mob_one]
  | succ n ih => funext x; rw [pow_succ, Function.iterate_succ_apply, mob_mul, ih]

lemma slToGL_apply (g : SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    (slToGL A g : GL (Fin 2) ℝ) i j = ((g i j : A) : ℝ) := by
  simp [slToGL]

lemma ell_apply (t : A) :
    ((ell t) 0 0 : ℝ) = t ∧ ((ell t) 0 1 : ℝ) = -1 ∧ ((ell t) 1 0 : ℝ) = 1 ∧
      ((ell t) 1 1 : ℝ) = 0 := by
  simp [ell]

lemma mob_ell_coe (t : A) (x : ℝ) (hx : x ≠ 0) :
    mob (ell t) (x : OnePoint ℝ) = (((t : ℝ) - x⁻¹ : ℝ) : OnePoint ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := ell_apply t
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply, h1, h2, h3, h4]
  rw [if_neg (by simpa using hx)]
  congr 1
  rw [one_mul, add_zero, ← sub_eq_add_neg, sub_div, mul_div_assoc, div_self hx, mul_one, one_div]

lemma mob_ell_zero (t : A) : mob (ell t) ((0 : ℝ) : OnePoint ℝ) = ∞ := by
  obtain ⟨h1, h2, h3, h4⟩ := ell_apply t
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply, h1, h2, h3, h4]
  simp

/-! ### The invariant weight `w(x) = 1 / (x² - τ x + 1)` -/

/-- The quadratic `x² - τ x + 1`. -/
noncomputable def qd (τ x : ℝ) : ℝ := x ^ 2 - τ * x + 1

/-- The density `w(x) = 1 / (x² - τ x + 1)`. -/
noncomputable def wt (τ x : ℝ) : ℝ := (qd τ x)⁻¹

/-- The map `x ↦ τ - 1/x` on `ℝ`. -/
noncomputable def fa (τ x : ℝ) : ℝ := τ - x⁻¹

lemma qd_pos {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : 0 < qd τ x := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hτ
  unfold qd
  nlinarith [mul_pos (sub_pos.2 h2) (by linarith : (0 : ℝ) < 2 + τ), sq_nonneg (2 * x - τ)]

lemma qd_ge {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : (1 - |τ| / 2) * (1 + x ^ 2) ≤ qd τ x := by
  unfold qd
  have h1 : τ * x ≤ |τ| * |x| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [sq_nonneg (1 - |x|), abs_nonneg τ, sq_abs x, abs_nonneg x]

lemma wt_pos {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : 0 < wt τ x := inv_pos.2 (qd_pos hτ x)

lemma continuous_wt {τ : ℝ} (hτ : |τ| < 2) : Continuous (wt τ) := by
  unfold wt qd
  exact Continuous.inv₀ (by fun_prop) (fun x => (qd_pos hτ x).ne')

lemma wt_le {τ : ℝ} (hτ : |τ| < 2) (x : ℝ) : wt τ x ≤ (1 - |τ| / 2)⁻¹ * (1 + x ^ 2)⁻¹ := by
  have hc : 0 < 1 - |τ| / 2 := by linarith
  unfold wt
  rw [← mul_inv]
  exact inv_anti₀ (mul_pos hc (by positivity)) (qd_ge hτ x)

lemma integrable_wt {τ : ℝ} (hτ : |τ| < 2) : Integrable (wt τ) := by
  refine (integrable_inv_one_add_sq.const_mul ((1 - |τ| / 2)⁻¹)).mono'
    (continuous_wt hτ).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (wt_pos hτ x)]
  exact wt_le hτ x

/-- The pointwise invariance identity `w(τ - 1/x) / x² = w(x)`. -/
lemma wt_fa {τ x : ℝ} (hx : x ≠ 0) : (x ^ 2)⁻¹ * wt τ (fa τ x) = wt τ x := by
  unfold wt fa qd
  rw [← mul_inv]
  congr 1
  field_simp
  ring

/-! ### Change of variables for `x ↦ τ - 1/x` -/

lemma image_fa_Ioi (τ : ℝ) : fa τ '' Ioi 0 = Iio τ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := inv_pos.2 (mem_Ioi.1 hx)
    simp only [mem_Iio, fa]
    linarith
  · intro hy
    refine ⟨(τ - y)⁻¹, inv_pos.2 (sub_pos.2 (mem_Iio.1 hy)), ?_⟩
    simp [fa]

lemma image_fa_Iio (τ : ℝ) : fa τ '' Iio 0 = Ioi τ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := inv_lt_zero.2 (mem_Iio.1 hx)
    simp only [mem_Ioi, fa]
    linarith
  · intro hy
    refine ⟨(τ - y)⁻¹, inv_lt_zero.2 (sub_neg.2 (mem_Ioi.1 hy)), ?_⟩
    simp [fa]

lemma injective_fa (τ : ℝ) : Function.Injective (fa τ) := fun x y h => by
  unfold fa at h
  exact inv_injective (by linarith)

lemma hasDerivAt_fa (τ : ℝ) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (fa τ) ((x ^ 2)⁻¹) x := by
  have h := (hasDerivAt_inv hx).const_sub τ
  rw [neg_neg] at h
  exact h

lemma measurable_fa (τ : ℝ) : Measurable (fa τ) := measurable_const.sub measurable_inv

/-- Change of variables on a set avoiding `0`. -/
lemma lintegral_image_fa (τ : ℝ) {s : Set ℝ} (hs : MeasurableSet s) (hs0 : ∀ x ∈ s, x ≠ 0)
    (B : Set ℝ) :
    ∫⁻ y in fa τ '' s, B.indicator (fun y => ENNReal.ofReal (wt τ y)) y =
      ∫⁻ x in s, (fa τ ⁻¹' B).indicator (fun x => ENNReal.ofReal (wt τ x)) x := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun x hx => (hasDerivAt_fa τ (hs0 x hx)).hasDerivWithinAt) (injective_fa τ).injOn]
  refine setLIntegral_congr_fun hs (fun x hx => ?_)
  have hx0 := hs0 x hx
  have hpos : 0 < (x ^ 2)⁻¹ := inv_pos.2 (by positivity)
  rw [abs_of_pos hpos]
  by_cases hB : fa τ x ∈ B
  · rw [indicator_of_mem hB, indicator_of_mem (show x ∈ fa τ ⁻¹' B from hB),
      ← ENNReal.ofReal_mul hpos.le, wt_fa hx0]
  · rw [indicator_of_notMem hB, indicator_of_notMem (show x ∉ fa τ ⁻¹' B from hB), mul_zero]

/-- The measure `w(x) dx` on `ℝ`. -/
noncomputable def muR (τ : ℝ) : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (wt τ x))

lemma muR_apply (τ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    muR τ B = ∫⁻ x, B.indicator (fun x => ENNReal.ofReal (wt τ x)) x := by
  rw [muR, withDensity_apply _ hB, lintegral_indicator hB]

lemma lintegral_split (F : ℝ → ENNReal) (a : ℝ) :
    ∫⁻ x, F x = (∫⁻ x in Iio a, F x) + ∫⁻ x in Ioi a, F x := by
  rw [← lintegral_add_compl F (measurableSet_Iio (a := a)), compl_Iio,
    setLIntegral_congr Ioi_ae_eq_Ici.symm]

lemma muR_fa (τ : ℝ) {B : Set ℝ} (hB : MeasurableSet B) : muR τ (fa τ ⁻¹' B) = muR τ B := by
  rw [muR_apply τ hB, muR_apply τ (measurable_fa τ hB),
    lintegral_split (B.indicator (fun x => ENNReal.ofReal (wt τ x))) τ,
    lintegral_split ((fa τ ⁻¹' B).indicator (fun x => ENNReal.ofReal (wt τ x))) 0,
    ← image_fa_Ioi τ, ← image_fa_Iio τ,
    lintegral_image_fa τ measurableSet_Ioi (fun x hx => (mem_Ioi.1 hx).ne') B,
    lintegral_image_fa τ measurableSet_Iio (fun x hx => (mem_Iio.1 hx).ne) B, add_comm]

lemma isFiniteMeasure_muR {τ : ℝ} (hτ : |τ| < 2) : IsFiniteMeasure (muR τ) :=
  isFiniteMeasure_withDensity_ofReal (integrable_wt hτ).hasFiniteIntegral

lemma muR_ae_ne (τ : ℝ) : ∀ᵐ x ∂(muR τ), x ≠ 0 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_iff.2 (by simp))

/-! ### Transport to `P¹` -/

lemma measurable_coeP : Measurable ((↑) : ℝ → OnePoint ℝ) := continuous_coe.measurable

lemma measurable_of_coe {f : OnePoint ℝ → OnePoint ℝ} (hf : Measurable (fun x : ℝ => f x)) :
    Measurable f := by
  intro S hS
  have : f ⁻¹' S = ((↑) : ℝ → OnePoint ℝ) '' ((fun x : ℝ => f x) ⁻¹' S) ∪ ({∞} ∩ f ⁻¹' S) := by
    ext p
    cases p with
    | infty => simp
    | coe x => simp
  rw [this]
  exact (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.2 (hf hS)).union
    ((Set.subsingleton_singleton.anti inter_subset_left).measurableSet)

lemma measurable_mob_ell (t : A) : Measurable (mob (ell t)) := by
  apply measurable_of_coe
  have : (fun x : ℝ => mob (ell t) x) =
      fun x : ℝ => if x = 0 then ∞ else ((fa t x : ℝ) : OnePoint ℝ) := by
    funext x
    split_ifs with h
    · rw [h]; exact mob_ell_zero t
    · exact mob_ell_coe t x h
  rw [this]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_coeP.comp (measurable_fa _))

/-- The measure `w(x) dx` transported to `P¹`. -/
noncomputable def nuP (τ : ℝ) : Measure (OnePoint ℝ) :=
  Measure.map ((↑) : ℝ → OnePoint ℝ) (muR τ)

lemma isFiniteMeasure_nuP {τ : ℝ} (hτ : |τ| < 2) : IsFiniteMeasure (nuP τ) := by
  have := isFiniteMeasure_muR hτ
  unfold nuP
  infer_instance

lemma nuP_ac (τ : ℝ) : nuP τ ≪ volP1 := by
  unfold nuP volP1 muR
  exact (withDensity_absolutelyContinuous _ _).map measurable_coeP

lemma volP1_ac {τ : ℝ} (hτ : |τ| < 2) : volP1 ≪ nuP τ := by
  unfold nuP volP1 muR
  exact (withDensity_absolutelyContinuous'
    (continuous_wt hτ).measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (wt_pos hτ x)).ne')).map measurable_coeP

lemma measurePreserving_mob_ell (t : A) :
    MeasurePreserving (mob (ell t)) (nuP t) (nuP t) := by
  refine ⟨measurable_mob_ell t, ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_mob_ell t) hS, nuP,
    Measure.map_apply measurable_coeP (measurable_mob_ell t hS),
    Measure.map_apply measurable_coeP hS, ← muR_fa (t : ℝ) (measurable_coeP hS)]
  apply measure_congr
  filter_upwards [muR_ae_ne (t : ℝ)] with x hx
  change (mob (ell t) (x : OnePoint ℝ) ∈ S) = (((fa t x : ℝ) : OnePoint ℝ) ∈ S)
  rw [mob_ell_coe t x hx]
  rfl

end Monod.Dev.CG.A4

namespace Monod.Dev.CG

open MeasureTheory Matrix

theorem chk_null_of_wandering {A : Subring ℝ} (t : A) (ht : |(t : ℝ)| < 2) (W : Set (OnePoint ℝ))
    (hW : NullMeasurableSet W volP1)
    (hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (ell t ^ m) ⁻¹' W) = 0) : volP1 W = 0 := by
  have := A4.isFiniteMeasure_nuP ht
  have hcons := (A4.measurePreserving_mob_ell t).conservative
  have h1 := hcons.measure_mem_forall_ge_image_notMem_eq_zero (hW.mono_ac (A4.nuP_ac _)) 1
  have h2 : ∀ m : ℕ, A4.nuP (t : ℝ) (W ∩ (mob (ell t))^[m + 1] ⁻¹' W) = 0 := fun m => by
    apply A4.nuP_ac
    have := hwand ((m + 1 : ℕ) : ℤ) (by omega)
    rwa [zpow_natCast, A4.mob_pow] at this
  have hsub : W ⊆ {x ∈ W | ∀ m ≥ 1, (mob (ell t))^[m] x ∉ W} ∪
      ⋃ m : ℕ, (W ∩ (mob (ell t))^[m + 1] ⁻¹' W) := by
    intro x hx
    by_cases h : ∀ m ≥ 1, (mob (ell t))^[m] x ∉ W
    · exact Or.inl ⟨hx, h⟩
    · push Not at h
      obtain ⟨m, hm, hmW⟩ := h
      refine Or.inr (Set.mem_iUnion.2 ⟨m - 1, hx, ?_⟩)
      rwa [Set.mem_preimage, Nat.sub_add_cancel hm]
  exact A4.volP1_ac ht
    (measure_mono_null hsub (measure_union_null h1 (measure_iUnion_null h2)))

end Monod.Dev.CG
end

section
namespace Monod.Dev.CG.A6

open Polynomial

theorem exists_hom_closure {R K : Type*} [CommRing R] [CommRing K] (t : R) (y : K)
    (h : ∀ p : ℤ[X], aeval t p = 0 → aeval y p = 0) :
    ∃ σ : Subring.closure ({t} : Set R) →+* K, σ ⟨t, Subring.subset_closure rfl⟩ = y := by
  let f : ℤ[X] →+* R := (aeval t : ℤ[X] →ₐ[ℤ] R).toRingHom
  let g : ℤ[X] →+* K := (aeval y : ℤ[X] →ₐ[ℤ] K).toRingHom
  have hle : Subring.closure ({t} : Set R) ≤ f.range :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr ⟨X, by simp [f]⟩)
  have hker : RingHom.ker f ≤ RingHom.ker g := fun p hp => by
    simp only [RingHom.mem_ker] at hp ⊢
    exact h p hp
  refine ⟨(Ideal.Quotient.lift (RingHom.ker f) g hker).comp
    ((f.quotientKerEquivRange.symm.toRingHom).comp (Subring.inclusion hle)), ?_⟩
  have h1 : f.quotientKerEquivRange.symm (Subring.inclusion hle ⟨t, Subring.subset_closure rfl⟩)
      = Ideal.Quotient.mk _ X := by
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    show t = f X
    simp [f]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h1]
  simp [g]


theorem coe_aeval_subring (A : Subring ℝ) (t : A) (p : ℤ[X]) :
    ((aeval t p : A) : ℝ) = aeval (t : ℝ) p := by
  simpa using (Polynomial.aeval_algHom_apply (A.subtype.toIntAlgHom) t p).symm

theorem exists_hom_closure_real (A : Subring ℝ) (t : A) {K : Type*} [CommRing K] (y : K)
    (h : ∀ p : ℤ[X], aeval (t : ℝ) p = 0 → aeval y p = 0) :
    ∃ σ : Subring.closure ({t} : Set A) →+* K, σ ⟨t, Subring.subset_closure rfl⟩ = y :=
  exists_hom_closure t y fun p hp => h p (by rw [← coe_aeval_subring, hp]; rfl)

/-- Case (a): a transcendental element. -/
theorem case_transcendental (A : Subring ℝ) (x : A) (hx : Transcendental ℤ (x : ℝ)) :
    ∃ t : A, |(t : ℝ)| < 2 ∧ ∃ (K : Type) (_ : NormedField K)
      (σ : Subring.closure ({t} : Set A) →+* K),
      ‖(2 : K)‖ ≤ 2 ∧ 1 / 2 ≤ ‖(2 : K)‖ ∧ 20 ≤ ‖σ ⟨t, Subring.subset_closure rfl⟩‖ := by
  set n : ℤ := ⌊(x : ℝ)⌋
  let t : A := x - n
  have ht : (t : ℝ) = x - n := by simp [t]
  have htr : Transcendental ℤ (t : ℝ) := by
    have := hx.aeval (X - C n) (by rw [natDegree_X_sub_C]; exact one_ne_zero)
      (by rw [leadingCoeff_X_sub_C]; exact one_mem _)
    simpa [ht] using this
  refine ⟨t, ?_, ℝ, inferInstance, ?_⟩
  · rw [ht, abs_lt]
    constructor
    · linarith [Int.floor_le (x : ℝ)]
    · linarith [Int.lt_floor_add_one (x : ℝ)]
  obtain ⟨σ, hσ⟩ := exists_hom_closure_real A t (20 : ℝ) fun p hp => by
    rw [transcendental_iff] at htr
    rw [htr p hp, map_zero]
  refine ⟨σ, by norm_num, by norm_num, by rw [hσ]; norm_num⟩


theorem padic_norm_two (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    ‖(2 : ℚ_[ℓ])‖ ≤ 2 ∧ 1 / 2 ≤ ‖(2 : ℚ_[ℓ])‖ := by
  have e : (2 : ℚ_[ℓ]) = ((2 : ℕ) : ℚ_[ℓ]) := by norm_num
  have hle : ‖(2 : ℚ_[ℓ])‖ ≤ 1 := by
    have := Padic.norm_int_le_one (p := ℓ) 2
    simpa using this
  refine ⟨hle.trans (by norm_num), ?_⟩
  by_cases h2 : ℓ = 2
  · subst h2
    rw [e, Padic.norm_p]
    norm_num
  · have hc : ℓ.Coprime 2 := (Nat.coprime_primes hℓ.out Nat.prime_two).2 h2
    rw [e, Padic.norm_natCast_eq_one_iff.2 hc]
    norm_num

/-- Case (b): every element of `A` is rational. -/
theorem case_rational (A : Subring ℝ) (hA : Dense (A : Set ℝ))
    (hrat : ∀ x : A, ∃ q : ℚ, (q : ℝ) = x) :
    ∃ t : A, |(t : ℝ)| < 2 ∧ ∃ (K : Type) (_ : NormedField K)
      (σ : Subring.closure ({t} : Set A) →+* K),
      ‖(2 : K)‖ ≤ 2 ∧ 1 / 2 ≤ ‖(2 : K)‖ ∧ 20 ≤ ‖σ ⟨t, Subring.subset_closure rfl⟩‖ := by
  obtain ⟨a, haA, ha⟩ := hA.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.2 (zero_lt_one' ℝ))
  obtain ⟨q, hq⟩ := hrat ⟨a, haA⟩
  have hqA : (q : ℝ) ∈ A := by rw [hq]; exact haA
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := by rw [hq]; exact ha.1
    exact_mod_cast this
  have hq1 : q < 1 := by
    have : (q : ℝ) < 1 := by rw [hq]; exact ha.2
    exact_mod_cast this
  have hden : q.den ≠ 1 := by
    intro h
    have hqn : (q.num : ℚ) = q := (Rat.den_eq_one_iff q).1 h
    have h0 : (0 : ℚ) < q.num := hqn ▸ hq0
    have h1 : (q.num : ℚ) < 1 := hqn ▸ hq1
    have h0' : 0 < q.num := by exact_mod_cast h0
    have h1' : q.num < 1 := by exact_mod_cast h1
    omega
  obtain ⟨ℓ, hℓ, k, hk⟩ : ∃ ℓ, ℓ.Prime ∧ ℓ ∣ q.den :=
    ⟨_, Nat.minFac_prime hden, Nat.minFac_dvd _⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  -- Bézout
  have hg : ((Int.gcd q.num q.den : ℕ) : ℤ) =
      q.num * Int.gcdA q.num q.den + q.den * Int.gcdB q.num q.den := Int.gcd_eq_gcd_ab _ _
  have hg1 : Int.gcd q.num q.den = 1 := by
    have := q.reduced
    simpa [Int.gcd] using this
  rw [hg1] at hg
  set u := Int.gcdA q.num q.den
  set v := Int.gcdB q.num q.den
  have hgR : (1 : ℝ) = q.num * u + q.den * v := by exact_mod_cast hg
  have hinv : ((ℓ : ℝ))⁻¹ = (k : ℝ) * ((q : ℝ) * u + v) := by
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    have hqd : (q : ℝ) = q.num / q.den := by rw [Rat.cast_def]
    have hkd : (q.den : ℝ) = ℓ * k := by exact_mod_cast hk
    have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have hk0 : (k : ℝ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hkd; exact hd hkd
    rw [hkd] at hgR
    rw [hqd, hkd]
    field_simp
    linear_combination hgR
  have hinvA : ((ℓ : ℝ))⁻¹ ∈ A := by
    rw [hinv]
    exact A.mul_mem (natCast_mem A k)
      (A.add_mem (A.mul_mem hqA (intCast_mem A u)) (intCast_mem A v))
  let t : A := ⟨((ℓ : ℝ))⁻¹ ^ 5, A.pow_mem hinvA 5⟩
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.one_lt.le
  have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
  refine ⟨t, ?_, ℚ_[ℓ], inferInstance, ?_⟩
  · show |((ℓ : ℝ))⁻¹ ^ 5| < 2
    have h0 : 0 < ((ℓ : ℝ))⁻¹ ^ 5 := by positivity
    have h1 : ((ℓ : ℝ))⁻¹ ^ 5 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hℓ1)
    rw [abs_of_pos h0]
    linarith
  obtain ⟨σ, hσ⟩ := exists_hom_closure_real A t (((ℓ : ℚ_[ℓ]))⁻¹ ^ 5) fun p hp => by
    set r : ℚ := ((ℓ : ℚ))⁻¹ ^ 5
    have e1 : ((t : ℝ)) = algebraMap ℚ ℝ r := by simp [r, t]
    have e2 : ((ℓ : ℚ_[ℓ]))⁻¹ ^ 5 = algebraMap ℚ ℚ_[ℓ] r := by simp [r]
    rw [e1, aeval_algebraMap_apply] at hp
    have hr : aeval r p = 0 := (map_eq_zero_iff _ (algebraMap ℚ ℝ).injective).1 hp
    rw [e2, aeval_algebraMap_apply, hr, map_zero]
  obtain ⟨h2a, h2b⟩ := padic_norm_two ℓ
  refine ⟨σ, h2a, h2b, ?_⟩
  rw [hσ, norm_pow, norm_inv, Padic.norm_p, inv_inv]
  calc (20 : ℝ) ≤ 2 ^ 5 := by norm_num
    _ ≤ (ℓ : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hℓ2 5


theorem aeval_affine {S : Type*} [CommRing S] [Algebra ℚ S] (m n : ℤ) (p : ℤ[X]) (z : S) :
    aeval ((m : S) * z - n) p =
      aeval z ((p.comp (C m * X - C n)).map (algebraMap ℤ ℚ)) := by
  rw [aeval_map_algebraMap, aeval_comp]
  simp

/-- Case (c): an irrational algebraic element. -/
theorem case_algebraic (A : Subring ℝ) (x : A) (hx : IsAlgebraic ℚ (x : ℝ))
    (hirr : ∀ q : ℚ, (q : ℝ) ≠ x) :
    ∃ t : A, |(t : ℝ)| < 2 ∧ ∃ (K : Type) (_ : NormedField K)
      (σ : Subring.closure ({t} : Set A) →+* K),
      ‖(2 : K)‖ ≤ 2 ∧ 1 / 2 ≤ ‖(2 : K)‖ ∧ 20 ≤ ‖σ ⟨t, Subring.subset_closure rfl⟩‖ := by
  classical
  set P := minpoly ℚ (x : ℝ)
  have hint : IsIntegral ℚ (x : ℝ) := hx.isIntegral
  have hdeg : 2 ≤ P.natDegree := (minpoly.two_le_natDegree_iff hint).2 (by
    rintro ⟨q, hq⟩
    exact hirr q (by simpa using hq))
  have hsep : P.Separable := (minpoly.irreducible hint).separable
  have hcard : Fintype.card (P.rootSet ℂ) = P.natDegree :=
    card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)
  have hxroot : ((x : ℝ) : ℂ) ∈ P.rootSet ℂ := by
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have : ((x : ℝ) : ℂ) = algebraMap ℝ ℂ x := rfl
    rw [this, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  obtain ⟨⟨x', hx'⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card (α := P.rootSet ℂ) (by omega)
    ⟨((x : ℝ) : ℂ), hxroot⟩
  have hne' : x' ≠ ((x : ℝ) : ℂ) := fun h => hne (Subtype.ext h)
  have hx'root : aeval x' P = 0 := (mem_rootSet.1 hx').2
  have hpos : 0 < ‖x' - ((x : ℝ) : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne')
  obtain ⟨m, hm⟩ := exists_nat_gt (21 / ‖x' - ((x : ℝ) : ℂ)‖)
  have hm' : 21 ≤ (m : ℝ) * ‖x' - ((x : ℝ) : ℂ)‖ := by
    rw [div_lt_iff₀ hpos] at hm
    linarith
  set n : ℤ := ⌊(m : ℝ) * x⌋
  let t : A := (m : ℤ) * x - n
  have ht : (t : ℝ) = ((m : ℤ) : ℝ) * x - n := by simp [t]
  have htb : |(t : ℝ)| < 1 := by
    rw [ht, abs_lt]
    push_cast
    constructor
    · linarith [Int.floor_le ((m : ℝ) * x)]
    · linarith [Int.lt_floor_add_one ((m : ℝ) * x)]
  refine ⟨t, htb.trans (by norm_num), ℂ, inferInstance, ?_⟩
  obtain ⟨σ, hσ⟩ := exists_hom_closure_real A t (((m : ℤ) : ℂ) * x' - n) fun p hp => by
    rw [ht, aeval_affine] at hp
    rw [aeval_affine]
    exact aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd ℚ _ hp) hx'root
  refine ⟨σ, by norm_num, by norm_num, ?_⟩
  rw [hσ]
  have e1 : ((m : ℤ) : ℂ) * x' - n =
      (m : ℂ) * (x' - ((x : ℝ) : ℂ)) + ((((m : ℝ) * x - n : ℝ)) : ℂ) := by
    push_cast; ring
  have h1 : ‖(m : ℂ) * (x' - ((x : ℝ) : ℂ))‖ = (m : ℝ) * ‖x' - ((x : ℝ) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_natCast]
  have h2 : ‖((((m : ℝ) * x - n : ℝ)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa [ht] using htb
  have h3 := norm_add_le ((m : ℂ) * (x' - ((x : ℝ) : ℂ)) + ((((m : ℝ) * x - n : ℝ)) : ℂ))
    (-((((m : ℝ) * x - n : ℝ)) : ℂ))
  rw [add_neg_cancel_right, norm_neg] at h3
  rw [e1]
  linarith

end Monod.Dev.CG.A6

namespace Monod.Dev.CG

open Polynomial

theorem chk_exists_t_ringHom (A : Subring ℝ) [Countable A] (hA : Dense (A : Set ℝ)) :
    ∃ t : A, |(t : ℝ)| < 2 ∧ ∃ (K : Type) (_ : NormedField K)
      (σ : Subring.closure ({t} : Set A) →+* K),
      ‖(2 : K)‖ ≤ 2 ∧ 1 / 2 ≤ ‖(2 : K)‖ ∧ 20 ≤ ‖σ ⟨t, Subring.subset_closure rfl⟩‖ := by
  by_cases h1 : ∃ x : A, Transcendental ℤ (x : ℝ)
  · obtain ⟨x, hx⟩ := h1
    exact A6.case_transcendental A x hx
  by_cases h2 : ∃ x : A, ∀ q : ℚ, (q : ℝ) ≠ x
  · obtain ⟨x, hx⟩ := h2
    have halg : IsAlgebraic ℤ (x : ℝ) := not_not.1 fun h => h1 ⟨x, h⟩
    exact A6.case_algebraic A x (halg.extendScalars (algebraMap ℤ ℚ).injective_int) hx
  exact A6.case_rational A hA fun x => by
    by_contra h
    exact h2 ⟨x, fun q hq => h ⟨q, hq⟩⟩

end Monod.Dev.CG
end

section
/-! A5 + A7 of the Carrière–Ghys argument: the ping-pong partition of `SL(2, A)`. -/

namespace Monod.Dev.CG.A57

open Matrix

section PingPong

variable {K : Type} [NormedField K]

/-- `z = w 0 / w 1` with `‖z‖ ≥ 10` (including `∞`). -/
def BigP (w : Fin 2 → K) : Prop := 10 * ‖w 1‖ ≤ ‖w 0‖

/-- `z = w 0 / w 1` with `‖z‖ ≤ 1/10`. -/
def SmallP (w : Fin 2 → K) : Prop := 10 * ‖w 0‖ ≤ ‖w 1‖

/-- The ping-pong set `X = BigP ∪ SmallP`. -/
def PX (w : Fin 2 → K) : Prop := BigP w ∨ SmallP w

/-- `‖z‖ ≥ 1/10`. -/
def Qp (w : Fin 2 → K) : Prop := ‖w 1‖ ≤ 10 * ‖w 0‖

/-- `‖z‖ ≤ 10`. -/
def Qm (w : Fin 2 → K) : Prop := ‖w 0‖ ≤ 10 * ‖w 1‖

lemma smul_apply0 (M : SpecialLinearGroup (Fin 2) K) (w : Fin 2 → K) :
    (M • w) 0 = M 0 0 * w 0 + M 0 1 * w 1 := by
  change ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma smul_apply1 (M : SpecialLinearGroup (Fin 2) K) (w : Fin 2 → K) :
    (M • w) 1 = M 1 0 * w 0 + M 1 1 * w 1 := by
  change ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma inv_smul_apply0 (M : SpecialLinearGroup (Fin 2) K) (w : Fin 2 → K) :
    (M⁻¹ • w) 0 = M 1 1 * w 0 - M 0 1 * w 1 := by
  rw [smul_apply0]
  simp [adjugate_fin_two, sub_eq_add_neg]

lemma inv_smul_apply1 (M : SpecialLinearGroup (Fin 2) K) (w : Fin 2 → K) :
    (M⁻¹ • w) 1 = -(M 1 0 * w 0) + M 0 0 * w 1 := by
  rw [smul_apply1]
  simp [adjugate_fin_two]

lemma mid_Qp {w : Fin 2 → K} (h : ¬ PX w) : Qp w := by
  simp only [PX, BigP, SmallP, not_or, not_le] at h
  simp only [Qp]; linarith [h.2]

lemma mid_Qm {w : Fin 2 → K} (h : ¬ PX w) : Qm w := by
  simp only [PX, BigP, SmallP, not_or, not_le] at h
  simp only [Qm]; linarith [h.1]

lemma big_Qp {w : Fin 2 → K} (h : BigP w) : Qp w := by
  simp only [BigP] at h; simp only [Qp]; nlinarith [norm_nonneg (w 1)]

lemma small_Qm {w : Fin 2 → K} (h : SmallP w) : Qm w := by
  simp only [SmallP] at h; simp only [Qm]; nlinarith [norm_nonneg (w 0)]

lemma norm_add_ge (a b : K) : ‖b‖ - ‖a‖ ≤ ‖a + b‖ := by
  have := norm_sub_le (a + b) a
  rw [add_sub_cancel_left] at this
  linarith

variable {E G : SpecialLinearGroup (Fin 2) K}

lemma E_big (hs : 20 ≤ ‖E 0 0‖) (h01 : E 0 1 = -1) (h10 : E 1 0 = 1) (h11 : E 1 1 = 0)
    (w : Fin 2 → K) (hw : Qp w) : BigP (E • w) := by
  simp only [BigP, Qp] at *
  rw [smul_apply0, smul_apply1, h01, h10, h11]
  have h1 := norm_sub_norm_le (E 0 0 * w 0) (w 1)
  rw [norm_mul] at h1
  have h3 : E 0 0 * w 0 + -1 * w 1 = E 0 0 * w 0 - w 1 := by ring
  have h4 : (1 : K) * w 0 + 0 * w 1 = w 0 := by ring
  rw [h3, h4]
  have := mul_le_mul_of_nonneg_right hs (norm_nonneg (w 0))
  linarith

lemma E_small (hs : 20 ≤ ‖E 0 0‖) (h01 : E 0 1 = -1) (h10 : E 1 0 = 1) (h11 : E 1 1 = 0)
    (w : Fin 2 → K) (hw : Qm w) : SmallP (E⁻¹ • w) := by
  simp only [SmallP, Qm] at *
  rw [inv_smul_apply0, inv_smul_apply1, h01, h10, h11]
  have h1 := norm_sub_norm_le (E 0 0 * w 1) (w 0)
  rw [norm_mul] at h1
  have h3 : -(1 * w 0) + E 0 0 * w 1 = E 0 0 * w 1 - w 0 := by ring
  have h4 : (0 : K) * w 0 - -1 * w 1 = w 1 := by ring
  rw [h3, h4]
  have := mul_le_mul_of_nonneg_right hs (norm_nonneg (w 1))
  linarith

lemma Ginv_Qm (h2 : ‖(2 : K)‖ ≤ 2) (h00 : G 0 0 = 1) (h01 : G 0 1 = 1) (h10 : G 1 0 = 1)
    (h11 : G 1 1 = 2) (w : Fin 2 → K) (hw : PX w) : Qm (G⁻¹ • w) := by
  simp only [Qm]
  rw [inv_smul_apply0, inv_smul_apply1, h00, h01, h10, h11]
  have e1 : (2 : K) * w 0 - 1 * w 1 = 2 * w 0 - w 1 := by ring
  have e2 : -((1 : K) * w 0) + 1 * w 1 = w 1 - w 0 := by ring
  rw [e1, e2]
  have u1 := norm_sub_le (2 * w 0) (w 1)
  rw [norm_mul] at u1
  have u2 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (w 0))
  have l1 := norm_sub_norm_le (w 1) (w 0)
  have l2 := norm_sub_norm_le (w 0) (w 1)
  rw [norm_sub_rev] at l2
  have n0 := norm_nonneg (w 0)
  have n1 := norm_nonneg (w 1)
  rcases hw with hw | hw <;> simp only [BigP, SmallP] at hw <;> linarith

lemma G_mid (h2 : ‖(2 : K)‖ ≤ 2) (h2' : 1 / 2 ≤ ‖(2 : K)‖) (h00 : G 0 0 = 1) (h01 : G 0 1 = 1)
    (h10 : G 1 0 = 1) (h11 : G 1 1 = 2) (w : Fin 2 → K) (hw : SmallP w) (hne : w ≠ 0) :
    ¬ PX (G • w) := by
  simp only [SmallP] at hw
  have n0 := norm_nonneg (w 0)
  have hy : 0 < ‖w 1‖ := by
    rcases (norm_nonneg (w 1)).lt_or_eq with h | h
    · exact h
    · exfalso; apply hne
      have h1 : w 1 = 0 := norm_eq_zero.mp h.symm
      have h0 : w 0 = 0 := norm_eq_zero.mp (by linarith)
      ext i; fin_cases i <;> simp [h0, h1]
  simp only [PX, BigP, SmallP, not_or, not_le]
  rw [smul_apply0, smul_apply1, h00, h01, h10, h11]
  have e1 : (1 : K) * w 0 + 1 * w 1 = w 0 + w 1 := by ring
  have e2 : (1 : K) * w 0 + 2 * w 1 = w 0 + 2 * w 1 := by ring
  rw [e1, e2]
  have a1 := norm_add_le (w 0) (w 1)
  have a2 := norm_add_ge (w 0) (w 1)
  have b1 := norm_add_le (w 0) (2 * w 1)
  have b2 := norm_add_ge (w 0) (2 * w 1)
  rw [norm_mul] at b1 b2
  have c1 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (w 1))
  have c2 := mul_le_mul_of_nonneg_right h2' (norm_nonneg (w 1))
  constructor <;> linarith

lemma iterate_pow {M : SpecialLinearGroup (Fin 2) K} {Q R : (Fin 2 → K) → Prop}
    (hRQ : ∀ w, R w → Q w) (hM : ∀ w, Q w → R (M • w)) :
    ∀ (n : ℕ) (w : Fin 2 → K), Q w → R (M ^ (n + 1) • w)
  | 0 => by simpa using hM
  | n + 1 => fun w hw => by
      rw [pow_succ, mul_smul]
      exact iterate_pow hRQ hM n _ (hRQ _ (hM w hw))

end PingPong

section Retraction

variable {A : Subring ℝ} (t : A)

/-- `R₀ = ℤ[t] ⊆ A`. -/
abbrev R0 : Subring A := Subring.closure ({t} : Set A)

/-- `t` as an element of `R₀`. -/
def t0 : R0 t := ⟨t, Subring.subset_closure rfl⟩

/-- The inclusion `SL(2, R₀) → SL(2, A)`. -/
def iota : SpecialLinearGroup (Fin 2) (R0 t) →* SpecialLinearGroup (Fin 2) A :=
  SpecialLinearGroup.map (R0 t).subtype

lemma iota_injective : Function.Injective (iota t) := by
  intro x y hxy
  ext i j
  have := congrArg (fun M : SpecialLinearGroup (Fin 2) A => (M : Matrix (Fin 2) (Fin 2) A) i j) hxy
  simpa [iota] using this

/-- `a_t` over `R₀`. -/
def ellR : SpecialLinearGroup (Fin 2) (R0 t) :=
  ⟨!![t0 t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- `g` over `R₀`. -/
def gR : SpecialLinearGroup (Fin 2) (R0 t) :=
  ⟨!![1, 1; 1, 2], by norm_num [Matrix.det_fin_two]⟩

lemma iota_apply (x : SpecialLinearGroup (Fin 2) (R0 t)) (i j : Fin 2) :
    iota t x i j = (x i j : A) := rfl

lemma iota_ellR : iota t (ellR t) = ell t := by
  ext i j; rw [iota_apply]; fin_cases i <;> fin_cases j <;> simp [ellR, ell, t0]

lemma iota_gR : iota t (gR t) = gConj := by
  ext i j; rw [iota_apply]; fin_cases i <;> fin_cases j <;> simp [gR, gConj]
  norm_cast

lemma iota_neg_one : iota t (-1) = -1 := by
  ext i j; rw [iota_apply]; fin_cases i <;> fin_cases j <;> simp

/-- A left-coset representative of `γ · SL(2, R₀)`. -/
noncomputable def rep (γ : SpecialLinearGroup (Fin 2) A) : SpecialLinearGroup (Fin 2) A :=
  (QuotientGroup.mk γ : SpecialLinearGroup (Fin 2) A ⧸ (iota t).range).out

lemma rep_inv_mul_mem (γ : SpecialLinearGroup (Fin 2) A) : (rep t γ)⁻¹ * γ ∈ (iota t).range := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (iota t).range γ
  rw [rep, hh, _root_.mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem h.2

lemma rep_mul (γ : SpecialLinearGroup (Fin 2) A) (x : SpecialLinearGroup (Fin 2) (R0 t)) :
    rep t (γ * iota t x) = rep t γ := by
  unfold rep
  congr 1
  rw [QuotientGroup.eq]
  simp

/-- The retraction `κ : SL(2, A) → SL(2, R₀)`, `κ(γ h) = κ(γ) h`. -/
noncomputable def kappa (γ : SpecialLinearGroup (Fin 2) A) : SpecialLinearGroup (Fin 2) (R0 t) :=
  Classical.choose (rep_inv_mul_mem t γ)

lemma iota_kappa (γ : SpecialLinearGroup (Fin 2) A) : iota t (kappa t γ) = (rep t γ)⁻¹ * γ :=
  Classical.choose_spec (rep_inv_mul_mem t γ)

lemma kappa_mul (γ : SpecialLinearGroup (Fin 2) A) (x : SpecialLinearGroup (Fin 2) (R0 t)) :
    kappa t (γ * iota t x) = kappa t γ * x := by
  apply iota_injective t
  rw [iota_kappa, rep_mul, map_mul, iota_kappa, mul_assoc]

end Retraction

end Monod.Dev.CG.A57

namespace Monod.Dev.CG

open Matrix

theorem chk_exists_pingpong_set {A : Subring ℝ} (t : A) (K : Type) [NormedField K]
    (σ : Subring.closure ({t} : Set A) →+* K) (h2 : ‖(2 : K)‖ ≤ 2) (h2' : 1 / 2 ≤ ‖(2 : K)‖)
    (hσ : 20 ≤ ‖σ ⟨t, Subring.subset_closure rfl⟩‖) :
    ∃ S : Set (SpecialLinearGroup (Fin 2) A), (∀ γ, -γ ∈ S ↔ γ ∈ S) ∧
      (∀ δ ∈ S, δ * bEl t ∉ S ∧ δ * bEl t ^ 2 ∉ S) ∧
      (∀ δ, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * ell t ^ m ∈ S) := by
  classical
  open A57 in
  have mapE : ∀ (x : SpecialLinearGroup (Fin 2) (R0 t)) (i j : Fin 2),
      SpecialLinearGroup.map σ x i j = σ (x i j) := fun _ _ _ => rfl
  set E : SpecialLinearGroup (Fin 2) K := SpecialLinearGroup.map σ (ellR t) with hE
  set G : SpecialLinearGroup (Fin 2) K := SpecialLinearGroup.map σ (gR t) with hG
  have hs : 20 ≤ ‖E 0 0‖ := by rw [hE, mapE]; exact hσ
  have hE01 : E 0 1 = -1 := by rw [hE, mapE]; simp [ellR]
  have hE10 : E 1 0 = 1 := by rw [hE, mapE]; simp [ellR]
  have hE11 : E 1 1 = 0 := by rw [hE, mapE]; simp [ellR]
  have hG00 : G 0 0 = 1 := by rw [hG, mapE]; simp [gR]
  have hG01 : G 0 1 = 1 := by rw [hG, mapE]; simp [gR]
  have hG10 : G 1 0 = 1 := by rw [hG, mapE]; simp [gR]
  have hG11 : G 1 1 = 2 := by rw [hG, mapE]; simp [gR]; exact map_ofNat σ 2
  let p0 : Fin 2 → K := ![0, 1]
  have hp0 : p0 ≠ 0 := fun h => by simpa [p0] using congrFun h 1
  let v : SpecialLinearGroup (Fin 2) A → (Fin 2 → K) := fun γ =>
    (SpecialLinearGroup.map σ (kappa t γ))⁻¹ • p0
  have hv_mul : ∀ γ x, v (γ * iota t x) = (SpecialLinearGroup.map σ x)⁻¹ • v γ := by
    intro γ x
    simp only [v, kappa_mul, map_mul, _root_.mul_inv_rev, mul_smul]
  have hv_ne : ∀ γ, v γ ≠ 0 := fun γ => (smul_ne_zero_iff_ne _).mpr hp0
  refine ⟨{γ | PX (v γ)}, ?_, ?_, ?_⟩
  · intro γ
    show PX (v (-γ)) ↔ PX (v γ)
    have : -γ = γ * iota t (-1) := by rw [iota_neg_one, mul_neg_one]
    rw [this, hv_mul]
    simp only [PX, BigP, SmallP, inv_smul_apply0, inv_smul_apply1, mapE]
    simp
  · intro δ hδ
    have hb : ∀ n : ℕ, δ * bEl t ^ (n + 1) ∉ {γ | PX (v γ)} := by
      intro n
      have hbR : bEl t = iota t (gR t * ellR t * (gR t)⁻¹) := by
        rw [map_mul, map_mul, map_inv, iota_ellR, iota_gR]; rfl
      rw [hbR, ← map_pow]
      show ¬ PX (v (δ * iota t _))
      rw [hv_mul]
      have key : (SpecialLinearGroup.map σ ((gR t * ellR t * (gR t)⁻¹) ^ (n + 1)))⁻¹ =
          G * (E⁻¹) ^ (n + 1) * G⁻¹ := by
        rw [map_pow, map_mul, map_mul, map_inv, conj_pow, inv_pow, hE, hG]
        group
      rw [key, mul_smul, mul_smul]
      apply G_mid h2 h2' hG00 hG01 hG10 hG11
      · exact iterate_pow (fun _ => small_Qm) (E_small hs hE01 hE10 hE11) n _
          (Ginv_Qm h2 hG00 hG01 hG10 hG11 _ hδ)
      · rw [smul_ne_zero_iff_ne, smul_ne_zero_iff_ne]; exact hv_ne δ
    exact ⟨by simpa using hb 0, hb 1⟩
  · intro δ hδ m hm
    show PX (v (δ * ell t ^ m))
    rw [← iota_ellR, ← map_zpow, hv_mul, map_zpow]
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast hm)
      rw [zpow_natCast, ← inv_pow]
      exact Or.inr (iterate_pow (fun _ => small_Qm) (E_small hs hE01 hE10 hE11) k _ (mid_Qm hδ))
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hm)
      rw [_root_.zpow_neg, inv_inv, zpow_natCast]
      exact Or.inl (iterate_pow (fun _ => big_Qp) (E_big hs hE01 hE10 hE11) k _ (mid_Qp hδ))

end Monod.Dev.CG
end

section
/-! # A8: the core of the Carrière–Ghys argument

A left invariant mean `P` on the orbit relation of `SL(2, A)` gives `u = P f_S`, where `f_S` is
the indicator of the pairs `(x, s x)` with `s ∈ S`.  Freeness off a countable set and the
ping-pong properties of `S` give `u + u ∘ b + u ∘ b² ≤ 1` and `1 ≤ u + u ∘ a^m` a.e.; the second
makes `{u < 1/2}` wandering for `a`, hence null, and the first is then contradictory. -/

namespace Monod.Dev.CG.A8

open Monod OnePoint Filter Topology Set MeasureTheory

variable {A : Subring ℝ}

/-! ### Möbius maps (copied from `DynBasic`) -/

/-- real entries -/
noncomputable abbrev ent (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) : ℝ :=
  ((g i j : A) : ℝ)

lemma slToGL_apply (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    (slToGL A g : GL (Fin 2) ℝ) i j = ent g i j := by
  simp [slToGL]

lemma det_ent (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun x : A => (x : ℝ)) h
  simpa using this

lemma mob_coe (g : Matrix.SpecialLinearGroup (Fin 2) A) (t : ℝ) :
    mob g (t : OnePoint ℝ) = if ent g 1 0 * t + ent g 1 1 = 0 then ∞ else
      (((ent g 0 0 * t + ent g 0 1) / (ent g 1 0 * t + ent g 1 1) : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply]

lemma mob_infty (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    mob g ∞ = if ent g 1 0 = 0 then ∞ else ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_infty_eq_ite]
  simp only [slToGL_apply]

lemma mob_mul (g h : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (g * h) x = mob g (mob h x) := by
  unfold mob
  rw [map_mul, mul_smul]

lemma mob_one (x : OnePoint ℝ) : mob (1 : Matrix.SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob
  rw [map_one, one_smul]

lemma mob_inv_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g⁻¹ (mob g x) = x := by
  rw [← mob_mul, inv_mul_cancel, mob_one]

lemma mob_mob_inv (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g (mob g⁻¹ x) = x := by
  rw [← mob_mul, mul_inv_cancel, mob_one]

lemma tendsto_coe_cobounded :
    Tendsto (fun x : ℝ => (x : OnePoint ℝ)) (Bornology.cobounded ℝ) (𝓝 ∞) := by
  rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact]
  exact tendsto_coe_infty

lemma tendsto_affine_cobounded {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    Tendsto (fun x : ℝ => c * x + d) (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 := tendsto_norm_cobounded_atTop (E := ℝ)
  have h2 : Tendsto (fun x : ℝ => |c| * ‖x‖ - |d|) (Bornology.cobounded ℝ) atTop := by
    apply tendsto_atTop_add_const_right
    exact h1.const_mul_atTop (abs_pos.2 hc)
  refine tendsto_atTop_mono (fun x => ?_) h2
  simp only [Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (c * x) (-d)
  rw [abs_mul, abs_neg, sub_neg_eq_add] at this
  linarith

lemma frac_eq (g : Matrix.SpecialLinearGroup (Fin 2) A) {x : ℝ} (hc : ent g 1 0 ≠ 0)
    (hx : ent g 1 0 * x + ent g 1 1 ≠ 0) :
    (ent g 0 0 * x + ent g 0 1) / (ent g 1 0 * x + ent g 1 1) =
      ent g 0 0 / ent g 1 0 - (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ := by
  have := det_ent g
  rw [eq_sub_iff_add_eq, div_eq_mul_inv, mul_inv, ← add_mul, ← div_eq_mul_inv]
  rw [div_eq_div_iff hx hc, add_mul, inv_mul_cancel₀ hc]
  linear_combination (-1 : ℝ) * this

lemma continuous_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) : Continuous (mob g) := by
  have hdet := det_ent g
  rw [OnePoint.continuous_iff]
  constructor
  · rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    by_cases hc : ent g 1 0 = 0
    · have hd : ent g 1 1 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      rw [mob_infty, if_pos hc]
      have : (fun x : ℝ => mob g (x : OnePoint ℝ)) =
          fun x : ℝ => (((ent g 0 0 / ent g 1 1) * x + ent g 0 1 / ent g 1 1 : ℝ) : OnePoint ℝ) := by
        funext x
        rw [mob_coe, if_neg (by rw [hc]; simpa using hd)]
        congr 1
        rw [hc, zero_mul, zero_add]; field_simp
      rw [this]
      have ha : ent g 0 0 ≠ 0 := by
        intro h; rw [h, hc] at hdet; simp at hdet
      exact tendsto_coe_cobounded.comp (tendsto_affine_cobounded (div_ne_zero ha hd) _)
    · rw [mob_infty, if_neg hc]
      have hev : ∀ᶠ x : ℝ in Bornology.cobounded ℝ, ent g 1 0 * x + ent g 1 1 ≠ 0 := by
        have := (tendsto_affine_cobounded hc (ent g 1 1)).eventually
          (Bornology.eventually_ne_cobounded (0 : ℝ))
        exact this
      have hlim : Tendsto (fun x : ℝ => ((ent g 0 0 / ent g 1 0 -
          (ent g 1 0 * (ent g 1 0 * x + ent g 1 1))⁻¹ : ℝ) : OnePoint ℝ))
          (Bornology.cobounded ℝ) (𝓝 ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ)) := by
        apply (continuous_coe.tendsto _).comp
        have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
          have := tendsto_affine_cobounded (mul_ne_zero hc hc) (ent g 1 0 * ent g 1 1)
          refine this.congr (fun x => ?_)
          ring
        have h4 := (tendsto_inv₀_cobounded.comp h3)
        have := (tendsto_const_nhds (x := ent g 0 0 / ent g 1 0)).sub h4
        simpa using this
      refine hlim.congr' ?_
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx, frac_eq g hc hx]
  · rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : ent g 1 0 * t + ent g 1 1 = 0
    · have hc : ent g 1 0 ≠ 0 := by
        intro h; rw [h, zero_mul, zero_add] at ht; rw [ht, h] at hdet; simp at hdet
      show Tendsto (fun x : ℝ => mob g (x : OnePoint ℝ)) (𝓝 t) (𝓝 (mob g (t : OnePoint ℝ)))
      rw [mob_coe, if_pos ht, ← nhdsNE_sup_pure t, tendsto_sup]
      constructor
      · have h3 : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1))
            (𝓝[≠] t) (𝓝[≠] 0) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          · have : Tendsto (fun x : ℝ => ent g 1 0 * (ent g 1 0 * x + ent g 1 1)) (𝓝 t)
                (𝓝 (ent g 1 0 * (ent g 1 0 * t + ent g 1 1))) :=
              ((continuous_const.mul ((continuous_const.mul continuous_id).add
                continuous_const)).tendsto t)
            rw [ht, mul_zero] at this
            exact tendsto_nhdsWithin_of_tendsto_nhds this
          · filter_upwards [self_mem_nhdsWithin] with x hx
            simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
            intro h0
            rcases mul_eq_zero.1 h0 with h | h
            · exact hc h
            · apply hx
              have : ent g 1 0 * (x - t) = 0 := by linarith
              rcases mul_eq_zero.1 this with h' | h'
              · exact absurd h' hc
              · linarith
        have h4 := tendsto_inv₀_nhdsNE_zero.comp h3
        have h5 := (tendsto_const_add_cobounded (ent g 0 0 / ent g 1 0)).comp
          ((tendsto_neg_cobounded).comp h4)
        refine (tendsto_coe_cobounded.comp h5).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff] at hx
        have hx' : ent g 1 0 * x + ent g 1 1 ≠ 0 := by
          intro h0; apply hx
          have : ent g 1 0 * (x - t) = 0 := by linarith
          rcases mul_eq_zero.1 this with h' | h'
          · exact absurd h' hc
          · linarith
        simp only [Function.comp_apply]
        rw [mob_coe, if_neg hx', frac_eq g hc hx', sub_eq_add_neg]
      · rw [tendsto_pure_left]
        intro s hs
        rw [mob_coe, if_pos ht]
        exact mem_of_mem_nhds hs
    · have hev : ∀ᶠ x : ℝ in 𝓝 t, ent g 1 0 * x + ent g 1 1 ≠ 0 :=
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt.eventually_ne ht
      have hcont : ContinuousAt (fun x : ℝ => (((ent g 0 0 * x + ent g 0 1) /
          (ent g 1 0 * x + ent g 1 1) : ℝ) : OnePoint ℝ)) t := by
        apply continuous_coe.continuousAt.comp
        exact (((continuous_const.mul continuous_id).add continuous_const).continuousAt).div
          (((continuous_const.mul continuous_id).add continuous_const).continuousAt) ht
      refine hcont.congr (Filter.EventuallyEq.symm ?_)
      filter_upwards [hev] with x hx
      rw [mob_coe, if_neg hx]

lemma measurable_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) : Measurable (mob g) :=
  (continuous_mob g).measurable

/-! ### Measurability on `P¹ × P¹` -/

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

attribute [local instance] secondCountable_P1

theorem countable_SL (A : Subring ℝ) [Countable A] :
    Countable (Matrix.SpecialLinearGroup (Fin 2) A) :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → A // Matrix.det M = 1})

attribute [local instance] countable_SL

lemma measurableSet_graph (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    MeasurableSet {p : OnePoint ℝ × OnePoint ℝ | mob g p.1 = p.2} :=
  measurableSet_eq_fun ((measurable_mob g).comp measurable_fst) measurable_snd

/-- The pairs `(x, s x)` with `s ∈ T`. -/
def gr (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) : Set (OnePoint ℝ × OnePoint ℝ) :=
  {p | ∃ s ∈ T, mob s p.1 = p.2}

/-- `f_T`, the indicator of `gr T`. -/
noncomputable def ind (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) :
    OnePoint ℝ × OnePoint ℝ → ℝ :=
  (gr T).indicator 1

open Classical in
lemma ind_apply (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) (p : OnePoint ℝ × OnePoint ℝ) :
    ind T p = if p ∈ gr T then 1 else 0 := by
  simp only [ind, Set.indicator_apply, Pi.one_apply]

lemma measurableSet_gr [Countable A] (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) :
    MeasurableSet (gr T) := by
  have : gr T = ⋃ s ∈ T, {p : OnePoint ℝ × OnePoint ℝ | mob s p.1 = p.2} := by
    ext p; simp [gr]
  rw [this]
  exact MeasurableSet.biUnion T.to_countable fun s _ => measurableSet_graph s

lemma isBddMeasOn_ind [Countable A] (R : Set (OnePoint ℝ × OnePoint ℝ))
    (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) : IsBddMeasOn R (ind T) := by
  refine ⟨measurable_one.indicator (measurableSet_gr T), 1, fun p _ => ?_⟩
  rw [ind_apply]
  split_ifs <;> norm_num

section Bdd

variable {X : Type*} [MeasurableSpace X]

lemma isBddMeasOn_add {R : Set (X × X)} {f g : X × X → ℝ} (hf : IsBddMeasOn R f)
    (hg : IsBddMeasOn R g) : IsBddMeasOn R (f + g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, fun p hp => (abs_add_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

lemma isBddMeasOn_smul {R : Set (X × X)} (c : ℝ) {f : X × X → ℝ} (hf : IsBddMeasOn R f) :
    IsBddMeasOn R (c • f) := by
  obtain ⟨C, hC⟩ := hf.2
  refine ⟨hf.1.const_smul c, |c| * C, fun p hp => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)

lemma isBddMeasOn_one (R : Set (X × X)) : IsBddMeasOn R (1 : X × X → ℝ) :=
  ⟨measurable_const, 1, fun p _ => by simp⟩

/-- Monotonicity of a left invariant mean, for an inequality holding off a null set of first
coordinates. -/
lemma ae_le_of_le {μ : Measure X} {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ}
    (hP : IsLeftInvariantMean μ R P) {f g : X × X → ℝ} (hf : IsBddMeasOn R f)
    (hg : IsBddMeasOn R g) {N : Set X} (hN : μ N = 0) (hle : ∀ p ∈ R, p.1 ∉ N → f p ≤ g p) :
    ∀ᵐ x ∂μ, P f x ≤ P g x := by
  set h : X × X → ℝ := g + (-1 : ℝ) • f with hh_def
  have hh : IsBddMeasOn R h := isBddMeasOn_add hg (isBddMeasOn_smul _ hf)
  set h' : X × X → ℝ := fun p => max (h p) 0 with hh'_def
  have hh' : IsBddMeasOn R h' := by
    obtain ⟨C, hC⟩ := hh.2
    refine ⟨hh.1.max measurable_const, C, fun p hp => ?_⟩
    refine le_trans ?_ (hC p hp)
    rw [abs_le]
    constructor
    · linarith [le_max_right (h p) 0, abs_nonneg (h p)]
    · exact max_le (le_abs_self _) (abs_nonneg _)
  have h0 : ∀ᵐ x ∂μ, 0 ≤ P h' x := hP.nonneg h' hh' fun p _ => le_max_right _ _
  have hc : P h' =ᵐ[μ] P h := by
    refine hP.congr h' h hh' hh (measure_mono_null ?_ hN)
    rintro _ ⟨p, ⟨hne, hR⟩, rfl⟩
    by_contra hpN
    apply hne
    have := hle p hR hpN
    show max (h p) 0 = h p
    apply max_eq_left
    simp only [hh_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hadd : P h =ᵐ[μ] P g + P ((-1 : ℝ) • f) := hP.add g _ hg (isBddMeasOn_smul _ hf)
  have hsm : P ((-1 : ℝ) • f) =ᵐ[μ] (-1 : ℝ) • P f := hP.smul _ f hf
  filter_upwards [h0, hc, hadd, hsm] with x h0 hc hadd hsm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsm
  rw [hc, hadd, hsm] at h0
  linarith

end Bdd

/-! ### The global partial transformations `φ_g` -/

/-- `x ↦ mob g⁻¹ x` as a measurable equivalence, with inverse `mob g`. -/
noncomputable def mobInvME (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    OnePoint ℝ ≃ᵐ OnePoint ℝ where
  toFun := mob g⁻¹
  invFun := mob g
  left_inv := mob_mob_inv g
  right_inv := mob_inv_mob g
  measurable_toFun := measurable_mob g⁻¹
  measurable_invFun := measurable_mob g

/-- The partial transformation `x ↦ mob g⁻¹ x` of the orbit relation, defined everywhere. -/
noncomputable def phi (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    PartialTransformation (Monod.Dev.CG.orbRel A) where
  dom := univ
  cod := univ
  measurableSet_dom := MeasurableSet.univ
  measurableSet_cod := MeasurableSet.univ
  e := ((MeasurableEquiv.Set.univ _).trans (mobInvME g)).trans (MeasurableEquiv.Set.univ _).symm
  graph_subset _ := ⟨g⁻¹, rfl⟩

lemma shiftRel_phi (g : Matrix.SpecialLinearGroup (Fin 2) A) (f : OnePoint ℝ × OnePoint ℝ → ℝ) :
    (phi g).shiftRel f = fun p => f (mob g p.1, p.2) := by
  funext p
  have h : p.1 ∈ (phi g).cod := mem_univ _
  simp only [PartialTransformation.shiftRel, dif_pos h]
  rfl

lemma shiftBase_phi (g : Matrix.SpecialLinearGroup (Fin 2) A) (F : OnePoint ℝ → ℝ) :
    (phi g).shiftBase F = F ∘ mob g := by
  funext y
  have h : y ∈ (phi g).cod := mem_univ _
  simp only [PartialTransformation.shiftBase, dif_pos h, Function.comp_apply]
  rfl

lemma mem_gr_shift (g : Matrix.SpecialLinearGroup (Fin 2) A)
    (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) (x y : OnePoint ℝ) :
    (mob g x, y) ∈ gr T ↔ (x, y) ∈ gr {s | s * g⁻¹ ∈ T} := by
  constructor
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s * g, by simpa using hs, ?_⟩
    simp only at hsy ⊢
    rw [mob_mul, hsy]
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s * g⁻¹, hs, ?_⟩
    simp only at hsy ⊢
    rw [mob_mul, mob_inv_mob, hsy]

lemma shiftRel_ind (g : Matrix.SpecialLinearGroup (Fin 2) A)
    (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) :
    (phi g).shiftRel (ind T) = ind {s | s * g⁻¹ ∈ T} := by
  rw [shiftRel_phi]
  funext ⟨x, y⟩
  classical
  simp only [ind, Set.indicator_apply, mem_gr_shift, Pi.one_apply]

/-- Invariance of a left invariant mean under `φ_g`, on the indicators `f_T`. -/
lemma P_ind_shift [Countable A] {P : (OnePoint ℝ × OnePoint ℝ → ℝ) → OnePoint ℝ → ℝ}
    (hP : IsLeftInvariantMean volP1 (Monod.Dev.CG.orbRel A) P)
    (g : Matrix.SpecialLinearGroup (Fin 2) A) (T : Set (Matrix.SpecialLinearGroup (Fin 2) A)) :
    P (ind {s | s * g⁻¹ ∈ T}) =ᵐ[volP1] P (ind T) ∘ mob g := by
  have := hP.invariant (phi g) (ind T) (isBddMeasOn_ind _ T)
  rwa [shiftRel_ind, shiftBase_phi] at this

/-! ### Null sets of `volP1` -/

lemma volP1_apply (Z : Set (OnePoint ℝ)) : volP1 Z = volume (((↑) : ℝ → OnePoint ℝ) ⁻¹' Z) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply volume Z

lemma volP1_univ : volP1 (univ : Set (OnePoint ℝ)) = ⊤ := by
  rw [volP1_apply, preimage_univ, Real.volume_univ]

lemma volP1_of_countable {Z : Set (OnePoint ℝ)} (hZ : Z.Countable) : volP1 Z = 0 := by
  rw [volP1_apply]
  exact (hZ.preimage OnePoint.coe_injective).measure_zero _

/-- Möbius maps send null sets to null sets (copied from `RedNull`). -/
lemma null_image_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) {S : Set (OnePoint ℝ)}
    (hS : volP1 S = 0) : volP1 (mob g '' S) = 0 := by
  rw [volP1_apply] at hS ⊢
  set a : ℝ := ((g 0 0 : A) : ℝ)
  set b : ℝ := ((g 0 1 : A) : ℝ)
  set c : ℝ := ((g 1 0 : A) : ℝ)
  set d : ℝ := ((g 1 1 : A) : ℝ)
  let φ : ℝ → ℝ := fun x => (a * x + b) / (c * x + d)
  let U : Set ℝ := {x | c * x + d ≠ 0}
  have hφ : DifferentiableOn ℝ φ (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact hx.2
  have h1 : volume (φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hφ
      (measure_mono_null Set.inter_subset_left hS)
  have hsub : ((↑) : ℝ → OnePoint ℝ) ⁻¹' (mob g '' S) ⊆
      φ '' (((↑) : ℝ → OnePoint ℝ) ⁻¹' S ∩ U) ∪ ((↑) : ℝ → OnePoint ℝ) ⁻¹' {mob g ∞} := by
    rintro y ⟨z, hz, hzy⟩
    cases z with
    | infty => exact Or.inr (by simp [← hzy])
    | coe x =>
      left
      rw [mob, OnePoint.smul_some_eq_ite] at hzy
      split_ifs at hzy with hx
      · exact absurd hzy.symm (OnePoint.coe_ne_infty y)
      · exact ⟨x, ⟨hz, hx⟩, OnePoint.coe_injective hzy⟩
  refine measure_mono_null hsub (measure_union_null h1 ?_)
  exact (Set.countable_singleton _).preimage OnePoint.coe_injective |>.measure_zero _

lemma null_preimage_mob (g : Matrix.SpecialLinearGroup (Fin 2) A) {S : Set (OnePoint ℝ)}
    (hS : volP1 S = 0) : volP1 (mob g ⁻¹' S) = 0 := by
  have : mob g ⁻¹' S = mob g⁻¹ '' S := by
    ext x
    constructor
    · intro hx; exact ⟨mob g x, hx, mob_inv_mob g x⟩
    · rintro ⟨y, hy, rfl⟩; simpa [Set.mem_preimage, mob_mob_inv] using hy
  rw [this]
  exact null_image_mob g⁻¹ hS

/-! ### Freeness off a countable set -/

lemma not_scalar {g : Matrix.SpecialLinearGroup (Fin 2) A} (hg1 : g ≠ 1) (hg2 : g ≠ -1) :
    (slToGL A g).val ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a, ha⟩
  have e : ∀ i j, ((g i j : A) : ℝ) = Matrix.scalar (Fin 2) a i j := fun i j => by
    rw [ha]; rfl
  have h00 := e 0 0
  have h11 := e 1 1
  have h01 := e 0 1
  have h10 := e 1 0
  simp at h00 h11 h01 h10
  have hdet := det_ent g
  simp only [ent] at hdet
  rw [h00, h11, h01, h10] at hdet
  have ha2 : (a - 1) * (a + 1) = 0 := by push_cast at hdet; linarith
  rcases mul_eq_zero.1 ha2 with h | h
  · apply hg1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply Subtype.ext
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10] <;> linarith
  · apply hg2
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply Subtype.ext
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg, h00, h11, h01, h10] <;>
      linarith

lemma countable_fix {g : Matrix.SpecialLinearGroup (Fin 2) A} (hg1 : g ≠ 1) (hg2 : g ≠ -1) :
    {x | mob g x = x}.Countable := by
  have hne : (slToGL A g).fixpointPolynomial ≠ 0 := by
    rw [Ne, Matrix.GeneralLinearGroup.fixpointPolynomial_eq_zero_iff]
    exact not_scalar hg1 hg2
  have hfin : {x : ℝ | ((slToGL A g).fixpointPolynomial).IsRoot x}.Finite :=
    Polynomial.finite_setOfPred_isRoot hne
  refine Set.Finite.countable (((hfin.image ((↑) : ℝ → OnePoint ℝ)).insert ∞).subset ?_)
  intro p hp
  cases p with
  | infty => exact Set.mem_insert _ _
  | coe x =>
    refine Set.mem_insert_of_mem _ ⟨x, ?_, rfl⟩
    have := (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff
      (c := x) (g := slToGL A g)).2 hp
    simpa [Polynomial.aeval_def] using this

/-- The points with a nontrivial stabilizer in `PSL(2, A)`. -/
def N0 (A : Subring ℝ) : Set (OnePoint ℝ) :=
  {x | ∃ g : Matrix.SpecialLinearGroup (Fin 2) A, g ≠ 1 ∧ g ≠ -1 ∧ mob g x = x}

lemma volP1_N0 (A : Subring ℝ) [Countable A] : volP1 (N0 A) = 0 := by
  apply volP1_of_countable
  have : N0 A ⊆ ⋃ g : Matrix.SpecialLinearGroup (Fin 2) A,
      {x | g ≠ 1 ∧ g ≠ -1 ∧ mob g x = x} := fun x ⟨g, hg⟩ => Set.mem_iUnion.2 ⟨g, hg⟩
  refine Set.Countable.mono this (Set.countable_iUnion fun g => ?_)
  by_cases h : g ≠ 1 ∧ g ≠ -1
  · exact (countable_fix h.1 h.2).mono fun x hx => hx.2.2
  · exact Set.Subsingleton.countable fun x hx => absurd ⟨hx.1, hx.2.1⟩ h

lemma eq_or_eq_neg {x : OnePoint ℝ} (hx : x ∉ N0 A) {g h : Matrix.SpecialLinearGroup (Fin 2) A}
    (hgh : mob g x = mob h x) : g = h ∨ g = -h := by
  by_contra hne
  rw [not_or] at hne
  apply hx
  refine ⟨h⁻¹ * g, fun e => hne.1 ?_, fun e => hne.2 ?_, ?_⟩
  · exact (inv_mul_eq_one.1 e).symm
  · calc g = h * (h⁻¹ * g) := by group
      _ = -h := by rw [e, mul_neg, mul_one]
  · rw [mob_mul, hgh, mob_inv_mob]

lemma mul_mem_of_free {S : Set (Matrix.SpecialLinearGroup (Fin 2) A)}
    (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S) {x : OnePoint ℝ} (hx : x ∉ N0 A)
    {g h : Matrix.SpecialLinearGroup (Fin 2) A} (hgh : mob g x = mob h x)
    (c : Matrix.SpecialLinearGroup (Fin 2) A) (hh : h * c ∈ S) : g * c ∈ S := by
  rcases eq_or_eq_neg hx hgh with rfl | rfl
  · exact hh
  · rwa [neg_mul, hS]

/-! ### The two pointwise inequalities -/

lemma ind_three_le {S : Set (Matrix.SpecialLinearGroup (Fin 2) A)} (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S)
    {b : Matrix.SpecialLinearGroup (Fin 2) A} (hb : ∀ δ ∈ S, δ * b ∉ S ∧ δ * b ^ 2 ∉ S)
    (p : OnePoint ℝ × OnePoint ℝ) (hp : p.1 ∉ N0 A) :
    ind S p + ind {s | s * b⁻¹ ∈ S} p + ind {s | s * (b ^ 2)⁻¹ ∈ S} p ≤ 1 := by
  have d12 : ¬ (p ∈ gr S ∧ p ∈ gr {s | s * b⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * b⁻¹ ∈ S := mul_mem_of_free hS hp (hsp.trans hs'p.symm) _ hs'
    exact (hb _ h1).1 (by rwa [inv_mul_cancel_right])
  have d13 : ¬ (p ∈ gr S ∧ p ∈ gr {s | s * (b ^ 2)⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * (b ^ 2)⁻¹ ∈ S := mul_mem_of_free hS hp (hsp.trans hs'p.symm) _ hs'
    exact (hb _ h1).2 (by rwa [inv_mul_cancel_right])
  have d23 : ¬ (p ∈ gr {s | s * b⁻¹ ∈ S} ∧ p ∈ gr {s | s * (b ^ 2)⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * (b ^ 2)⁻¹ ∈ S := mul_mem_of_free hS hp (hsp.trans hs'p.symm) _ hs'
    have h2 : s * (b ^ 2)⁻¹ * b = s * b⁻¹ := by group
    exact (hb _ h1).1 (by rw [h2]; exact hs)
  rw [ind_apply, ind_apply, ind_apply]
  split_ifs with h1 h2 h3 h3 h2 h3 h3
  · exact absurd ⟨h1, h2⟩ d12
  · exact absurd ⟨h1, h2⟩ d12
  · exact absurd ⟨h1, h3⟩ d13
  · norm_num
  · exact absurd ⟨h2, h3⟩ d23
  all_goals norm_num

lemma one_le_ind_two [Countable A] {S : Set (Matrix.SpecialLinearGroup (Fin 2) A)}
    {a : Matrix.SpecialLinearGroup (Fin 2) A}
    (ha : ∀ δ, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * a ^ m ∈ S) {m : ℤ} (hm : m ≠ 0)
    (p : OnePoint ℝ × OnePoint ℝ) (hp : p ∈ Monod.Dev.CG.orbRel A) :
    1 ≤ ind S p + ind {s | s * (a ^ m)⁻¹ ∈ S} p := by
  obtain ⟨g, hg⟩ := hp
  have h0 : ∀ T : Set (Matrix.SpecialLinearGroup (Fin 2) A), 0 ≤ ind T p := fun T => by
    rw [ind_apply]; split_ifs <;> norm_num
  by_cases hgS : g ∈ S
  · have : ind S p = 1 := by rw [ind_apply, if_pos ⟨g, hgS, hg⟩]
    linarith [h0 {s | s * (a ^ m)⁻¹ ∈ S}]
  · have hmem : g * (a ^ m)⁻¹ ∈ S := by
      rw [← zpow_neg]; exact ha g hgS (-m) (neg_ne_zero.2 hm)
    have : ind {s | s * (a ^ m)⁻¹ ∈ S} p = 1 := by rw [ind_apply, if_pos ⟨g, hmem, hg⟩]
    linarith [h0 S]

end Monod.Dev.CG.A8

namespace Monod.Dev.CG

open MeasureTheory Matrix

theorem chk_not_isAmenableRel_of_pingpong (A : Subring ℝ) [Countable A] (t : A)
    (hnull : ∀ W : Set (OnePoint ℝ), NullMeasurableSet W volP1 →
      (∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (ell t ^ m) ⁻¹' W) = 0) → volP1 W = 0)
    (S : Set (SpecialLinearGroup (Fin 2) A)) (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S)
    (hb : ∀ δ ∈ S, δ * bEl t ∉ S ∧ δ * bEl t ^ 2 ∉ S)
    (ha : ∀ δ, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * ell t ^ m ∈ S) :
    ¬ IsAmenableRel volP1 (orbRel A) := by
  rintro ⟨P, hP⟩
  set u := P (A8.ind S) with hu_def
  set b := bEl t with hb_def
  have hbdd : ∀ T : Set (SpecialLinearGroup (Fin 2) A), IsBddMeasOn (orbRel A) (A8.ind T) :=
    fun T => A8.isBddMeasOn_ind _ T
  -- `u + u ∘ b + u ∘ b² ≤ 1`
  have hE1 : ∀ᵐ x ∂volP1, u x + u (mob b x) + u (mob (b ^ 2) x) ≤ 1 := by
    have hle := A8.ae_le_of_le hP
      (A8.isBddMeasOn_add (A8.isBddMeasOn_add (hbdd S) (hbdd {s | s * b⁻¹ ∈ S}))
        (hbdd {s | s * (b ^ 2)⁻¹ ∈ S}))
      (A8.isBddMeasOn_one _) (A8.volP1_N0 A) (fun p _ hp => A8.ind_three_le hS hb p hp)
    have h1 := hP.add _ _ (A8.isBddMeasOn_add (hbdd S) (hbdd {s | s * b⁻¹ ∈ S}))
      (hbdd {s | s * (b ^ 2)⁻¹ ∈ S})
    have h2 := hP.add _ _ (hbdd S) (hbdd {s | s * b⁻¹ ∈ S})
    have h3 := A8.P_ind_shift hP b S
    have h4 := A8.P_ind_shift hP (b ^ 2) S
    filter_upwards [hle, h1, h2, h3, h4, hP.one] with x hle h1 h2 h3 h4 h5
    simp only [Pi.add_apply, Function.comp_apply, Pi.one_apply] at hle h1 h2 h3 h4 h5
    linarith
  -- `1 ≤ u + u ∘ a^m`
  have hE2 : ∀ m : ℤ, m ≠ 0 → ∀ᵐ x ∂volP1, 1 ≤ u x + u (mob (ell t ^ m) x) := by
    intro m hm
    have hle := A8.ae_le_of_le hP (A8.isBddMeasOn_one _)
      (A8.isBddMeasOn_add (hbdd S) (hbdd {s | s * (ell t ^ m)⁻¹ ∈ S})) (N := ∅) measure_empty
      (fun p hp _ => A8.one_le_ind_two ha hm p hp)
    have h1 := hP.add _ _ (hbdd S) (hbdd {s | s * (ell t ^ m)⁻¹ ∈ S})
    have h3 := A8.P_ind_shift hP (ell t ^ m) S
    filter_upwards [hle, h1, h3, hP.one] with x hle h1 h3 h5
    simp only [Pi.add_apply, Function.comp_apply, Pi.one_apply] at hle h1 h3 h5
    linarith
  -- `{u < 1/2}` is wandering for `a`, hence null
  have hum : AEMeasurable u volP1 := hP.aemeasurable _ (hbdd S)
  set W : Set (OnePoint ℝ) := {x | u x < 1 / 2} with hW_def
  have hWm : NullMeasurableSet W volP1 := hum.nullMeasurableSet_preimage measurableSet_Iio
  have hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (ell t ^ m) ⁻¹' W) = 0 := by
    intro m hm
    refine measure_mono_null ?_ (ae_iff.1 (hE2 m hm))
    rintro x ⟨hx1, hx2⟩
    simp only [hW_def, Set.mem_ofPred_eq, Set.mem_preimage] at hx1 hx2 ⊢
    linarith
  have hW0 : volP1 W = 0 := hnull W hWm hwand
  have hgood : ∀ g : SpecialLinearGroup (Fin 2) A, ∀ᵐ x ∂volP1, 1 / 2 ≤ u (mob g x) := by
    intro g
    rw [ae_iff]
    refine measure_mono_null ?_ (A8.null_preimage_mob g hW0)
    intro x hx
    simp only [Set.mem_ofPred_eq, not_le] at hx
    exact hx
  have hfalse : ∀ᵐ x ∂volP1, False := by
    filter_upwards [hE1, hgood 1, hgood b, hgood (b ^ 2)] with x h1 h2 h3 h4
    rw [A8.mob_one] at h2
    linarith
  rw [ae_iff] at hfalse
  simp only [not_false_eq_true, Set.ofPred_true] at hfalse
  rw [A8.volP1_univ] at hfalse
  exact ENNReal.top_ne_zero hfalse

end Monod.Dev.CG
end

open Monod in
theorem solution (A : Subring ℝ) [Countable A] (hA : Dense (A : Set ℝ)) :
    ¬ IsAmenableRel volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ g : Matrix.SpecialLinearGroup (Fin 2) A, mob g p.1 = p.2} := by
  obtain ⟨t, ht, K, _, σ, h2, h2', hσ⟩ := Monod.Dev.CG.chk_exists_t_ringHom A hA
  obtain ⟨S, hS, hb, ha⟩ := Monod.Dev.CG.chk_exists_pingpong_set t K σ h2 h2' hσ
  exact Monod.Dev.CG.chk_not_isAmenableRel_of_pingpong A t
    (Monod.Dev.CG.chk_null_of_wandering t ht) S hS hb ha
