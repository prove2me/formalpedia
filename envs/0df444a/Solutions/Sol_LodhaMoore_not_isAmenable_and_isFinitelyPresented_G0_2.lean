-- Prove2me | solution 2 for LodhaMoore.not_isAmenable_and_isFinitelyPresented_G0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T12:56:04.031083+00:00
-- url     : https://prove2.me/submissions/0ee1c164-4b7c-48b6-852f-fbfc1290aa5d

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_Garrido_Amenability
import Theorems.Thm_Monod_isAmenableRel_orbit_of_isAmenable
import Theorems.Thm_LodhaMoore_orbit_G0_eq_orbit_K_of_irrational
import Theorems.Thm_LodhaMoore_exists_mulEquiv_G0_G0Seq_and_semiconj_Phi
import Theorems.Thm_LodhaMoore_presentation_G_G0Seq_and_isFinitelyPresented

section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

end LodhaMoore
end

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

end Monod.Dev.CG.A6

namespace Monod.Dev.CG

open Polynomial

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

lemma det_ent (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun x : A => (x : ℝ)) h
  simpa using this

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

/-! ### Measurability on `P¹ × P¹` -/

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

attribute [local instance] secondCountable_P1

theorem countable_SL (A : Subring ℝ) [Countable A] :
    Countable (Matrix.SpecialLinearGroup (Fin 2) A) :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → A // Matrix.det M = 1})

attribute [local instance] countable_SL

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

/-! ### The two pointwise inequalities -/

end Monod.Dev.CG.A8

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG
end

section
/-! # Group S2: statements 1, 3, 6, 7, 8, 10 of the Lodha–Moore development -/

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set

/-! ### Möbius maps over `⊤ : Subring ℝ` -/

/-- The real entries of a matrix of `SL(2, A)`. -/
noncomputable abbrev ent {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    ℝ := ((g i j : A) : ℝ)

lemma slToGL_apply {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    (slToGL A g : GL (Fin 2) ℝ) i j = ent g i j := by
  simp [slToGL]

lemma det_ent {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun x : A => (x : ℝ)) h
  simpa using this

lemma mob_coe {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (t : ℝ) :
    mob g (t : OnePoint ℝ) = if ent g 1 0 * t + ent g 1 1 = 0 then ∞ else
      (((ent g 0 0 * t + ent g 0 1) / (ent g 1 0 * t + ent g 1 1) : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_some_eq_ite]
  simp only [slToGL_apply]

lemma mob_infty {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    mob g ∞ = if ent g 1 0 = 0 then ∞ else ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ) := by
  unfold mob
  rw [OnePoint.smul_infty_eq_ite]
  simp only [slToGL_apply]

lemma mob_mul {A : Subring ℝ} (g h : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (g * h) x = mob g (mob h x) := by
  unfold mob
  rw [map_mul, mul_smul]

lemma mob_one {A : Subring ℝ} (x : OnePoint ℝ) :
    mob (1 : Matrix.SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob
  rw [map_one, one_smul]

lemma mob_inv_mob {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g⁻¹ (mob g x) = x := by
  rw [← mob_mul, inv_mul_cancel, mob_one]

lemma mob_mob_inv {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g (mob g⁻¹ x) = x := by
  rw [← mob_mul, mul_inv_cancel, mob_one]

/-- A matrix of `SL(2, ℝ)` (over `⊤ : Subring ℝ`) from its real entries. -/
noncomputable def mk2 (p q r s : ℝ) (h : p * s - q * r = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  ⟨!![⟨p, trivial⟩, ⟨q, trivial⟩; ⟨r, trivial⟩, ⟨s, trivial⟩], by
    rw [Matrix.det_fin_two_of]
    ext
    simpa using h⟩

@[simp] lemma ent_mk2_00 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 0 = p := rfl
@[simp] lemma ent_mk2_01 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 1 = q := rfl
@[simp] lemma ent_mk2_10 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 0 = r := rfl
@[simp] lemma ent_mk2_11 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 1 = s := rfl

/-! ### Statement 1: `G₀ ≤ H` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Filter Topology Set
open scoped ENNReal

/-! ### Statement 3: `φ` and `Φ` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore MeasureTheory Set
open scoped ENNReal

section Orbit

variable {X : Type*} [MeasurableSpace X] (Γ : Type) [Group Γ] [MulAction Γ X]

variable {Γ}

end Orbit

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2 MeasureTheory Set

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

abbrev SLR := SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)
abbrev PSLR := ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)

/-- The quotient map `SL(2, ℝ) → PSL(2, ℝ)`. -/
noncomputable abbrev pr : SLR →* PSLR := QuotientGroup.mk' _

lemma slr_ext {A B : SLR} (h : ∀ i j, ent A i j = ent B i j) : A = B := by
  ext i j
  exact h i j

lemma ent_mul (A B : SLR) (i j : Fin 2) :
    ent (A * B) i j = ent A i 0 * ent B 0 j + ent A i 1 * ent B 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

lemma ent_one (i j : Fin 2) : ent (1 : SLR) i j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [ent]

@[simp] lemma ent_kTrans_00 : ent kTrans 0 0 = 1 := rfl
@[simp] lemma ent_kTrans_01 : ent kTrans 0 1 = 1 := rfl
@[simp] lemma ent_kTrans_10 : ent kTrans 1 0 = 0 := rfl
@[simp] lemma ent_kTrans_11 : ent kTrans 1 1 = 1 := rfl
@[simp] lemma ent_kInv_00 : ent kInv 0 0 = 0 := rfl
@[simp] lemma ent_kInv_01 : ent kInv 0 1 = 1 := rfl
@[simp] lemma ent_kInv_10 : ent kInv 1 0 = -1 := rfl
@[simp] lemma ent_kInv_11 : ent kInv 1 1 = 0 := rfl
@[simp] lemma ent_kDil_00 : ent kDil 0 0 = Real.sqrt 2 := rfl
@[simp] lemma ent_kDil_01 : ent kDil 0 1 = 0 := rfl
@[simp] lemma ent_kDil_10 : ent kDil 1 0 = 0 := rfl
@[simp] lemma ent_kDil_11 : ent kDil 1 1 = 1 / Real.sqrt 2 := rfl

/-- The upper unipotent `t ↦ t + x`. -/
noncomputable def uu (x : ℝ) : SLR := mk2 1 x 0 1 (by ring)
/-- The lower unipotent `t ↦ t / (x t + 1)`. -/
noncomputable def ll (x : ℝ) : SLR := mk2 1 0 x 1 (by ring)

lemma uu_add (x y : ℝ) : uu x * uu y = uu (x + y) := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ent_mul, uu]
  ring

lemma uu_zero : uu 0 = 1 := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ent_one, uu]

lemma uu_one : uu 1 = kTrans := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [uu]

lemma uu_kDil (x : ℝ) : uu x * kDil = kDil * uu (x / 2) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ent_mul, uu]
  field_simp
  linear_combination (-x) * h2

lemma kInv_uu (y : ℝ) : kInv * uu y = ll (-y) * kInv := by
  apply slr_ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ent_mul, uu, ll]

/-- The preimage of `K` in `SL(2, ℝ)`. -/
noncomputable def Kt : Subgroup SLR := K.comap pr

lemma kTrans_mem : kTrans ∈ Kt := Subgroup.subset_closure (by simp)
lemma kInv_mem : kInv ∈ Kt := Subgroup.subset_closure (by simp)
lemma kDil_mem : kDil ∈ Kt := Subgroup.subset_closure (by simp)

lemma uu_int_mem (n : ℤ) : uu n ∈ Kt := by
  have h : ∀ n : ℤ, uu n = kTrans ^ n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [uu_zero]
    | succ n ih =>
      rw [_root_.zpow_add_one, ← ih, ← uu_one, uu_add]
      push_cast; rfl
    | pred n ih =>
      have e : uu (-1) = kTrans⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← uu_one, uu_add]; norm_num [uu_zero]
      rw [_root_.zpow_sub_one, ← ih, ← e, uu_add]
      push_cast; ring_nf
  rw [h]
  exact Kt.zpow_mem kTrans_mem n

lemma uu_half_mem {x : ℝ} (hx : uu x ∈ Kt) : uu (x / 2) ∈ Kt := by
  have e : uu (x / 2) = kDil⁻¹ * uu x * kDil := by
    rw [mul_assoc, uu_kDil, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e]
  exact Kt.mul_mem (Kt.mul_mem (Kt.inv_mem kDil_mem) hx) kDil_mem

lemma uu_dyadic_mem (n : ℤ) (k : ℕ) : uu (n / 2 ^ k) ∈ Kt := by
  induction k with
  | zero => simpa using uu_int_mem n
  | succ k ih =>
    have := uu_half_mem ih
    rwa [div_div, ← pow_succ] at this

lemma countable_K : Countable K := by
  have : (K : Set PSLR) = Set.range (FreeGroup.lift (fun x : ({QuotientGroup.mk kTrans,
      QuotientGroup.mk kInv, QuotientGroup.mk kDil} : Set PSLR) => (x : PSLR))) := by
    rw [← MonoidHom.coe_range, ← FreeGroup.closure_eq_range]
    rfl
  exact (this ▸ Set.countable_range _ : (K : Set PSLR).Countable).to_subtype

lemma ent_of_mem_center {z : SLR} (hz : z ∈ Subgroup.center SLR) :
    ∃ r : ℝ, r ^ 2 = 1 ∧ ent z 0 0 = r ∧ ent z 1 1 = r ∧ ent z 0 1 = 0 ∧ ent z 1 0 = 0 := by
  obtain ⟨r, hr1, hr2⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have e : ∀ i j, (z : Matrix (Fin 2) (Fin 2) (⊤ : Subring ℝ)) i j =
      (Matrix.scalar (Fin 2) r) i j := fun i j => by rw [hr2]
  refine ⟨(r : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hr1
    simpa using this
  · simp [ent, e 0 0]
  · simp [ent, e 1 1]
  · simp [ent, e 0 1]
  · simp [ent, e 1 0]

lemma mob_of_mem_center {z : SLR} (hz : z ∈ Subgroup.center SLR) (x : OnePoint ℝ) :
    mob z x = x := by
  obtain ⟨r, hr, h00, h11, h01, h10⟩ := ent_of_mem_center hz
  have hr0 : r ≠ 0 := by rintro rfl; norm_num at hr
  cases x with
  | infty => rw [mob_infty, if_pos h10]
  | coe t =>
    rw [mob_coe, h00, h11, h01, h10, if_neg (by simpa using hr0)]
    congr 1
    rw [add_zero, zero_mul, zero_add, mul_comm, mul_div_assoc, div_self hr0, mul_one]

lemma mob_eq_of_pr_eq {A B : SLR} (h : (QuotientGroup.mk A : PSLR) = QuotientGroup.mk B)
    (x : OnePoint ℝ) : mob A x = mob B x := by
  have hz : A⁻¹ * B ∈ Subgroup.center SLR := QuotientGroup.eq.1 h
  have : B = A * (A⁻¹ * B) := by group
  rw [this, mob_mul, mob_of_mem_center hz]

/-! ### Möbius maps are continuous and preserve null sets (from the Monod development) -/

section Mob

variable {A : Subring ℝ}

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

lemma measurable_mob {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    Measurable (mob g) :=
  (continuous_mob g).measurable

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

theorem polishSpace_P1 : PolishSpace (OnePoint ℝ) := by
  have e := onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)
  have : PolishSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.polishSpace
  exact e.isClosedEmbedding.polishSpace

theorem sigmaFinite_volP1 : MeasureTheory.SigmaFinite volP1 :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.sigmaFinite_map

lemma volP1_apply (Z : Set (OnePoint ℝ)) : volP1 Z = MeasureTheory.volume (((↑) : ℝ → OnePoint ℝ) ⁻¹' Z) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply MeasureTheory.volume Z

open MeasureTheory in
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

end Mob

/-- The orbit relation on `P¹` of a subgroup `Γ` of `PSL(2, ℝ)`. -/
def orbRelP (Γ : Subgroup PSLR) : Set (OnePoint ℝ × OnePoint ℝ) :=
  {p | ∃ A : SLR, (QuotientGroup.mk A : PSLR) ∈ Γ ∧ mob A p.1 = p.2}

lemma orbRelP_eq (Γ : Subgroup PSLR) :
    orbRelP Γ = ⋃ γ : Γ, {p | mob (Quotient.out (γ : PSLR)) p.1 = p.2} := by
  ext p
  simp only [orbRelP, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨A, hA, hp⟩
    refine ⟨⟨_, hA⟩, ?_⟩
    rw [mob_eq_of_pr_eq (QuotientGroup.out_eq' _)]
    exact hp
  · rintro ⟨γ, hp⟩
    refine ⟨Quotient.out (γ : PSLR), ?_, hp⟩
    rw [QuotientGroup.out_eq']
    exact γ.2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

lemma equivalence_orbRelP (Γ : Subgroup PSLR) : Equivalence fun x y => (x, y) ∈ orbRelP Γ := by
  refine ⟨fun x => ⟨1, by simpa using Γ.one_mem, mob_one x⟩, ?_, ?_⟩
  · rintro x y ⟨A, hA, hp⟩
    refine ⟨A⁻¹, by simpa using Γ.inv_mem hA, ?_⟩
    simp only at hp ⊢
    rw [← hp, mob_inv_mob]
  · rintro x y z ⟨A, hA, hp⟩ ⟨B, hB, hq⟩
    refine ⟨B * A, by simpa using Γ.mul_mem hB hA, ?_⟩
    simp only at hp hq ⊢
    rw [mob_mul, hp, hq]

lemma countable_orbRelP (Γ : Subgroup PSLR) [Countable Γ] (x : OnePoint ℝ) :
    {y | (x, y) ∈ orbRelP Γ}.Countable := by
  refine (Set.countable_range fun γ : Γ => mob (Quotient.out (γ : PSLR)) x).mono ?_
  intro y hy
  rw [Set.mem_ofPred_eq, orbRelP_eq, Set.mem_iUnion] at hy
  obtain ⟨γ, hγ⟩ := hy
  exact ⟨γ, hγ⟩

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

/-! ### Statement 10: `G₀`- and `K`-orbits of irrational points -/

lemma ll_int_mem (n : ℤ) : ll n ∈ Kt := by
  have e : ll n = kInv * uu (-n : ℤ) * kInv⁻¹ := by
    rw [kInv_uu]; push_cast; rw [neg_neg, mul_assoc, mul_inv_cancel, mul_one]
  rw [e]
  exact Kt.mul_mem (Kt.mul_mem kInv_mem (uu_int_mem _)) (Kt.inv_mem kInv_mem)

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set MeasureTheory

/-! ### The Carrière–Ghys ping-pong argument for a countable subgroup `Λ` of `SL(2, ℝ)`

Monod's development (`Monod.Dev.CG.A8`) runs the argument for the orbit relation of `SL(2, A)`;
here it is run for the orbit relation of any countable subgroup `Λ` containing `a_t`, `b_t` and
a ping-pong set `S ⊆ Λ`. -/

section CGL

variable (Λ : Subgroup SLR)

/-- The orbit relation of `Λ` on `P¹`. -/
def relL : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ g ∈ Λ, mob g p.1 = p.2}

/-- The pairs `(x, s x)` with `s ∈ T`. -/
def grS (T : Set SLR) : Set (OnePoint ℝ × OnePoint ℝ) := {p | ∃ s ∈ T, mob s p.1 = p.2}

/-- `f_T`, the indicator of `grS T`. -/
noncomputable def indS (T : Set SLR) : OnePoint ℝ × OnePoint ℝ → ℝ := (grS T).indicator 1

open Classical in
lemma indS_apply (T : Set SLR) (p : OnePoint ℝ × OnePoint ℝ) :
    indS T p = if p ∈ grS T then 1 else 0 := by
  simp only [indS, Set.indicator_apply, Pi.one_apply]

attribute [local instance] secondCountable_P1

lemma measurableSet_grS {T : Set SLR} (hT : T.Countable) : MeasurableSet (grS T) := by
  have : grS T = ⋃ s ∈ T, {p : OnePoint ℝ × OnePoint ℝ | mob s p.1 = p.2} := by
    ext p; simp [grS]
  rw [this]
  exact MeasurableSet.biUnion hT fun s _ =>
    measurableSet_eq_fun ((measurable_mob s).comp measurable_fst) measurable_snd

lemma isBddMeasOn_indS (R : Set (OnePoint ℝ × OnePoint ℝ)) {T : Set SLR} (hT : T.Countable) :
    IsBddMeasOn R (indS T) := by
  refine ⟨measurable_one.indicator (measurableSet_grS hT), 1, fun p _ => ?_⟩
  rw [indS_apply]
  split_ifs <;> norm_num

variable {Λ}

/-- `x ↦ mob g⁻¹ x` as a measurable equivalence. -/
noncomputable def mobInvE (g : SLR) : OnePoint ℝ ≃ᵐ OnePoint ℝ where
  toFun := mob g⁻¹
  invFun := mob g
  left_inv := mob_mob_inv g
  right_inv := mob_inv_mob g
  measurable_toFun := measurable_mob g⁻¹
  measurable_invFun := measurable_mob g

/-- The partial transformation `x ↦ mob g⁻¹ x` of `relL Λ`, for `g ∈ Λ`. -/
noncomputable def phiL {g : SLR} (hg : g ∈ Λ) : PartialTransformation (relL Λ) where
  dom := univ
  cod := univ
  measurableSet_dom := MeasurableSet.univ
  measurableSet_cod := MeasurableSet.univ
  e := ((MeasurableEquiv.Set.univ _).trans (mobInvE g)).trans (MeasurableEquiv.Set.univ _).symm
  graph_subset _ := ⟨g⁻¹, Λ.inv_mem hg, rfl⟩

lemma shiftRel_phiL {g : SLR} (hg : g ∈ Λ) (f : OnePoint ℝ × OnePoint ℝ → ℝ) :
    (phiL hg).shiftRel f = fun p => f (mob g p.1, p.2) := by
  funext p
  have h : p.1 ∈ (phiL hg).cod := mem_univ _
  simp only [PartialTransformation.shiftRel, dif_pos h]
  rfl

lemma shiftBase_phiL {g : SLR} (hg : g ∈ Λ) (F : OnePoint ℝ → ℝ) :
    (phiL hg).shiftBase F = F ∘ mob g := by
  funext y
  have h : y ∈ (phiL hg).cod := mem_univ _
  simp only [PartialTransformation.shiftBase, dif_pos h, Function.comp_apply]
  rfl

lemma mem_grS_shift (g : SLR) (T : Set SLR) (x y : OnePoint ℝ) :
    (mob g x, y) ∈ grS T ↔ (x, y) ∈ grS {s | s * g⁻¹ ∈ T} := by
  constructor
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s * g, by simpa using hs, ?_⟩
    simp only at hsy ⊢
    rw [mob_mul, hsy]
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s * g⁻¹, hs, ?_⟩
    simp only at hsy ⊢
    rw [mob_mul, mob_inv_mob, hsy]

lemma shiftRel_indS {g : SLR} (hg : g ∈ Λ) (T : Set SLR) :
    (phiL hg).shiftRel (indS T) = indS {s | s * g⁻¹ ∈ T} := by
  rw [shiftRel_phiL]
  funext ⟨x, y⟩
  classical
  simp only [indS, Set.indicator_apply, mem_grS_shift, Pi.one_apply]

lemma P_indS_shift {P : (OnePoint ℝ × OnePoint ℝ → ℝ) → OnePoint ℝ → ℝ}
    (hP : IsLeftInvariantMean volP1 (relL Λ) P) {g : SLR} (hg : g ∈ Λ) {T : Set SLR}
    (hT : T.Countable) :
    P (indS {s | s * g⁻¹ ∈ T}) =ᵐ[volP1] P (indS T) ∘ mob g := by
  have := hP.invariant (phiL hg) (indS T) (isBddMeasOn_indS _ hT)
  rwa [shiftRel_indS, shiftBase_phiL] at this

/-- The points with a nontrivial stabilizer in `Λ / ±1`. -/
def N0L (Λ : Subgroup SLR) : Set (OnePoint ℝ) :=
  {x | ∃ g ∈ Λ, g ≠ 1 ∧ g ≠ -1 ∧ mob g x = x}

lemma volP1_N0L [Countable Λ] : volP1 (N0L Λ) = 0 := by
  apply Monod.Dev.CG.A8.volP1_of_countable
  have : N0L Λ ⊆ ⋃ g : Λ, {x | (g : SLR) ≠ 1 ∧ (g : SLR) ≠ -1 ∧ mob (g : SLR) x = x} := by
    rintro x ⟨g, hg, h⟩
    exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, h⟩
  refine Set.Countable.mono this (Set.countable_iUnion fun g => ?_)
  by_cases h : (g : SLR) ≠ 1 ∧ (g : SLR) ≠ -1
  · exact (Monod.Dev.CG.A8.countable_fix h.1 h.2).mono fun x hx => hx.2.2
  · exact Set.Subsingleton.countable fun x hx => absurd ⟨hx.1, hx.2.1⟩ h

lemma eq_or_eq_negL {x : OnePoint ℝ} (hx : x ∉ N0L Λ) {g h : SLR} (hg : g ∈ Λ) (hh : h ∈ Λ)
    (hgh : mob g x = mob h x) : g = h ∨ g = -h := by
  by_contra hne
  rw [not_or] at hne
  apply hx
  refine ⟨h⁻¹ * g, Λ.mul_mem (Λ.inv_mem hh) hg, fun e => hne.1 ?_, fun e => hne.2 ?_, ?_⟩
  · exact (inv_mul_eq_one.1 e).symm
  · calc g = h * (h⁻¹ * g) := by group
      _ = -h := by rw [e, mul_neg, mul_one]
  · rw [mob_mul, hgh, mob_inv_mob]

lemma mul_mem_of_freeL {S : Set SLR} (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S) {x : OnePoint ℝ}
    (hx : x ∉ N0L Λ) {g h : SLR} (hg : g ∈ Λ) (hh : h ∈ Λ) (hgh : mob g x = mob h x)
    (c : SLR) (hhc : h * c ∈ S) : g * c ∈ S := by
  rcases eq_or_eq_negL hx hg hh hgh with rfl | rfl
  · exact hhc
  · rwa [neg_mul, hS]

lemma indS_three_le {S : Set SLR} (hSL : S ⊆ Λ) (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S) {b : SLR}
    (hbL : b ∈ Λ) (hb : ∀ δ ∈ S, δ * b ∉ S ∧ δ * b ^ 2 ∉ S)
    (p : OnePoint ℝ × OnePoint ℝ) (hp : p.1 ∉ N0L Λ) :
    indS S p + indS {s | s * b⁻¹ ∈ S} p + indS {s | s * (b ^ 2)⁻¹ ∈ S} p ≤ 1 := by
  have memL : ∀ {s c : SLR}, c ∈ Λ → s * c⁻¹ ∈ S → s ∈ Λ := fun {s c} hc h => by
    have := Λ.mul_mem (hSL h) hc
    rwa [inv_mul_cancel_right] at this
  have hb2 : b ^ 2 ∈ Λ := Λ.pow_mem hbL 2
  have d12 : ¬ (p ∈ grS S ∧ p ∈ grS {s | s * b⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * b⁻¹ ∈ S :=
      mul_mem_of_freeL hS hp (hSL hs) (memL hbL hs') (hsp.trans hs'p.symm) _ hs'
    exact (hb _ h1).1 (by rwa [inv_mul_cancel_right])
  have d13 : ¬ (p ∈ grS S ∧ p ∈ grS {s | s * (b ^ 2)⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * (b ^ 2)⁻¹ ∈ S :=
      mul_mem_of_freeL hS hp (hSL hs) (memL hb2 hs') (hsp.trans hs'p.symm) _ hs'
    exact (hb _ h1).2 (by rwa [inv_mul_cancel_right])
  have d23 : ¬ (p ∈ grS {s | s * b⁻¹ ∈ S} ∧ p ∈ grS {s | s * (b ^ 2)⁻¹ ∈ S}) := by
    rintro ⟨⟨s, hs, hsp⟩, ⟨s', hs', hs'p⟩⟩
    have h1 : s * (b ^ 2)⁻¹ ∈ S :=
      mul_mem_of_freeL hS hp (memL hbL hs) (memL hb2 hs') (hsp.trans hs'p.symm) _ hs'
    have h2 : s * (b ^ 2)⁻¹ * b = s * b⁻¹ := by group
    exact (hb _ h1).1 (by rw [h2]; exact hs)
  rw [indS_apply, indS_apply, indS_apply]
  split_ifs with h1 h2 h3 h3 h2 h3 h3
  · exact absurd ⟨h1, h2⟩ d12
  · exact absurd ⟨h1, h2⟩ d12
  · exact absurd ⟨h1, h3⟩ d13
  · norm_num
  · exact absurd ⟨h2, h3⟩ d23
  all_goals norm_num

lemma one_le_indS_two {S : Set SLR} {a : SLR}
    (ha : ∀ δ ∈ Λ, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * a ^ m ∈ S) {m : ℤ} (hm : m ≠ 0)
    (p : OnePoint ℝ × OnePoint ℝ) (hp : p ∈ relL Λ) :
    1 ≤ indS S p + indS {s | s * (a ^ m)⁻¹ ∈ S} p := by
  obtain ⟨g, hgL, hg⟩ := hp
  have h0 : ∀ T : Set SLR, 0 ≤ indS T p := fun T => by
    rw [indS_apply]; split_ifs <;> norm_num
  by_cases hgS : g ∈ S
  · have : indS S p = 1 := by rw [indS_apply, if_pos ⟨g, hgS, hg⟩]
    linarith [h0 {s | s * (a ^ m)⁻¹ ∈ S}]
  · have hmem : g * (a ^ m)⁻¹ ∈ S := by
      rw [← zpow_neg]; exact ha g hgL hgS (-m) (neg_ne_zero.2 hm)
    have : indS {s | s * (a ^ m)⁻¹ ∈ S} p = 1 := by rw [indS_apply, if_pos ⟨g, hmem, hg⟩]
    linarith [h0 S]

/-- The Carrière–Ghys contradiction for the orbit relation of a countable `Λ ≤ SL(2, ℝ)`. -/
theorem not_isAmenableRel_relL [Countable Λ] (a b : SLR) (haL : a ∈ Λ) (hbL : b ∈ Λ)
    (hnull : ∀ W : Set (OnePoint ℝ), NullMeasurableSet W volP1 →
      (∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0) → volP1 W = 0)
    (S : Set SLR) (hSL : S ⊆ Λ) (hS : ∀ γ, -γ ∈ S ↔ γ ∈ S)
    (hb : ∀ δ ∈ S, δ * b ∉ S ∧ δ * b ^ 2 ∉ S)
    (ha : ∀ δ ∈ Λ, δ ∉ S → ∀ m : ℤ, m ≠ 0 → δ * a ^ m ∈ S) :
    ¬ IsAmenableRel volP1 (relL Λ) := by
  rintro ⟨P, hP⟩
  have hLc : (Λ : Set SLR).Countable := Set.countable_coe_iff.1 ‹Countable Λ›
  have hcT : ∀ c ∈ Λ, ({s | s * c⁻¹ ∈ S} : Set SLR).Countable := fun c hc =>
    hLc.mono fun s hs => by
      have := Λ.mul_mem (hSL hs) hc
      rwa [inv_mul_cancel_right] at this
  have hSc : S.Countable := hLc.mono hSL
  set u := P (indS S) with hu_def
  have hbdd : ∀ T : Set SLR, T.Countable → IsBddMeasOn (relL Λ) (indS T) :=
    fun T hT => isBddMeasOn_indS _ hT
  have hb2 : b ^ 2 ∈ Λ := Λ.pow_mem hbL 2
  have hE1 : ∀ᵐ x ∂volP1, u x + u (mob b x) + u (mob (b ^ 2) x) ≤ 1 := by
    have hle := Monod.Dev.CG.A8.ae_le_of_le hP
      (Monod.Dev.CG.A8.isBddMeasOn_add (Monod.Dev.CG.A8.isBddMeasOn_add (hbdd S hSc)
        (hbdd _ (hcT b hbL))) (hbdd _ (hcT _ hb2)))
      (Monod.Dev.CG.A8.isBddMeasOn_one _) volP1_N0L
      (fun p _ hp => indS_three_le hSL hS hbL hb p hp)
    have h1 := hP.add _ _ (Monod.Dev.CG.A8.isBddMeasOn_add (hbdd S hSc) (hbdd _ (hcT b hbL)))
      (hbdd _ (hcT _ hb2))
    have h2 := hP.add _ _ (hbdd S hSc) (hbdd _ (hcT b hbL))
    have h3 := P_indS_shift hP hbL hSc
    have h4 := P_indS_shift hP hb2 hSc
    filter_upwards [hle, h1, h2, h3, h4, hP.one] with x hle h1 h2 h3 h4 h5
    simp only [Pi.add_apply, Function.comp_apply, Pi.one_apply] at hle h1 h2 h3 h4 h5
    linarith
  have hE2 : ∀ m : ℤ, m ≠ 0 → ∀ᵐ x ∂volP1, 1 ≤ u x + u (mob (a ^ m) x) := by
    intro m hm
    have ham : a ^ m ∈ Λ := Λ.zpow_mem haL m
    have hle := Monod.Dev.CG.A8.ae_le_of_le hP (Monod.Dev.CG.A8.isBddMeasOn_one _)
      (Monod.Dev.CG.A8.isBddMeasOn_add (hbdd S hSc) (hbdd _ (hcT _ ham))) (N := ∅)
      measure_empty (fun p hp _ => one_le_indS_two ha hm p hp)
    have h1 := hP.add _ _ (hbdd S hSc) (hbdd _ (hcT _ ham))
    have h3 := P_indS_shift hP ham hSc
    filter_upwards [hle, h1, h3, hP.one] with x hle h1 h3 h5
    simp only [Pi.add_apply, Function.comp_apply, Pi.one_apply] at hle h1 h3 h5
    linarith
  have hum : AEMeasurable u volP1 := hP.aemeasurable _ (hbdd S hSc)
  set W : Set (OnePoint ℝ) := {x | u x < 1 / 2} with hW_def
  have hWm : NullMeasurableSet W volP1 := hum.nullMeasurableSet_preimage measurableSet_Iio
  have hwand : ∀ m : ℤ, m ≠ 0 → volP1 (W ∩ mob (a ^ m) ⁻¹' W) = 0 := by
    intro m hm
    refine measure_mono_null ?_ (ae_iff.1 (hE2 m hm))
    rintro x ⟨hx1, hx2⟩
    simp only [hW_def, Set.mem_ofPred_eq, Set.mem_preimage] at hx1 hx2 ⊢
    linarith
  have hW0 : volP1 W = 0 := hnull W hWm hwand
  have hgood : ∀ g : SLR, ∀ᵐ x ∂volP1, 1 / 2 ≤ u (mob g x) := by
    intro g
    rw [ae_iff]
    refine measure_mono_null ?_ (Monod.Dev.CG.A8.null_preimage_mob g hW0)
    intro x hx
    simp only [Set.mem_ofPred_eq, not_le] at hx
    exact hx
  have hfalse : ∀ᵐ x ∂volP1, False := by
    filter_upwards [hE1, hgood 1, hgood b, hgood (b ^ 2)] with x h1 h2 h3 h4
    rw [mob_one] at h2
    linarith
  rw [ae_iff] at hfalse
  simp only [not_false_eq_true, Set.ofPred_true] at hfalse
  rw [Monod.Dev.CG.A8.volP1_univ] at hfalse
  exact ENNReal.top_ne_zero hfalse

end CGL


/-! ### The Carrière–Ghys argument for `K` -/

lemma neg_one_mem_center : (-1 : SLR) ∈ Subgroup.center SLR :=
  Subgroup.mem_center_iff.2 fun g => by rw [neg_one_mul, mul_neg_one]

lemma neg_mem_Kt {γ : SLR} : -γ ∈ Kt ↔ γ ∈ Kt := by
  have h1 : (-1 : SLR) ∈ Kt := by
    show (QuotientGroup.mk (-1 : SLR) : PSLR) ∈ K
    rw [(QuotientGroup.eq_one_iff (-1 : SLR)).2 neg_one_mem_center]
    exact K.one_mem
  constructor
  · intro h
    have := Kt.mul_mem h1 h
    rwa [neg_one_mul, neg_neg] at this
  · intro h
    have := Kt.mul_mem h1 h
    rwa [neg_one_mul] at this

lemma eq_or_eq_neg_of_pr_eq {γ δ : SLR}
    (h : (QuotientGroup.mk γ : PSLR) = QuotientGroup.mk δ) : δ = γ ∨ δ = -γ := by
  have hz := QuotientGroup.eq.1 h
  obtain ⟨r, hr, h00, h11, h01, h10⟩ := ent_of_mem_center hz
  generalize hz' : γ⁻¹ * δ = z at h00 h11 h01 h10
  have e : δ = γ * z := by rw [← hz']; group
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rw [e]
  have ent_neg : ∀ (A : SLR) (i j : Fin 2), ent (-A) i j = -ent A i j := fun A i j => by
    simp [ent, Matrix.SpecialLinearGroup.coe_neg]
  rcases mul_eq_zero.1 hr' with h | h
  · left
    have hr1 : r = 1 := by linarith
    have hz1 : z = 1 := by
      apply slr_ext; intro i j
      rw [ent_one]
      fin_cases i <;> fin_cases j
      · simpa [hr1] using h00
      · simpa using h01
      · simpa using h10
      · simpa [hr1] using h11
    rw [hz1, mul_one]
  · right
    have hr1 : r = -1 := by linarith
    have hz1 : z = -1 := by
      apply slr_ext; intro i j
      rw [ent_neg, ent_one]
      fin_cases i <;> fin_cases j
      · simpa [hr1] using h00
      · simpa using h01
      · simpa using h10
      · simpa [hr1] using h11
    rw [hz1, mul_neg_one]

lemma countable_comap (Γ : Subgroup PSLR) [Countable Γ] : Countable (Γ.comap pr) := by
  classical
  let f : Γ.comap pr → Γ × Bool := fun γ =>
    (⟨QuotientGroup.mk (γ : SLR), γ.2⟩, decide ((γ : SLR) = Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR)))
  refine Function.Injective.countable (f := f) fun γ δ hfg => ?_
  simp only [f, Prod.mk.injEq] at hfg
  obtain ⟨h1, h2⟩ := hfg
  have h1' : (QuotientGroup.mk (γ : SLR) : PSLR) = QuotientGroup.mk (δ : SLR) :=
    congrArg Subtype.val h1
  apply Subtype.ext
  have ho : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR)) : PSLR) =
      QuotientGroup.mk (γ : SLR) := QuotientGroup.out_eq' _
  have hγ := eq_or_eq_neg_of_pr_eq ho
  have hδ := eq_or_eq_neg_of_pr_eq (ho.trans h1')
  have hout : Quotient.out (QuotientGroup.mk (δ : SLR) : PSLR) =
      Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR) := by rw [h1']
  rw [hout] at h2
  revert h2 hγ hδ
  generalize Quotient.out (QuotientGroup.mk (γ : SLR) : PSLR) = o
  intro h2 hγ hδ
  by_cases hg : (γ : SLR) = o
  · have hd : (δ : SLR) = o := by simpa [hg] using h2
    rw [hg, hd]
  · have hd : (δ : SLR) ≠ o := by simpa [hg] using h2
    have hg' : (γ : SLR) = -o := hγ.resolve_left (Ne.symm hg ∘ Eq.symm)
    have hd' : (δ : SLR) = -o := hδ.resolve_left (Ne.symm hd ∘ Eq.symm)
    rw [hg', hd']

lemma countable_Kt : Countable Kt := by
  have := countable_K
  exact countable_comap K

/-- `t = 2⁻⁵`. -/
noncomputable def tK : (⊤ : Subring ℝ) := ⟨(1 / 2 : ℝ) ^ 5, trivial⟩

lemma ell_tK_mem : Monod.Dev.CG.ell tK ∈ Kt := by
  have e : Monod.Dev.CG.ell tK * kInv = uu ((1 : ℤ) / 2 ^ 5) := by
    apply slr_ext; intro i j
    simp only [ent_mul]
    fin_cases i <;> fin_cases j <;> simp [uu, tK, Monod.Dev.CG.ell, ent]
  have : Monod.Dev.CG.ell tK = uu ((1 : ℤ) / 2 ^ 5) * kInv⁻¹ := by rw [← e, mul_inv_cancel_right]
  rw [this]
  exact Kt.mul_mem (uu_dyadic_mem 1 5) (Kt.inv_mem kInv_mem)

lemma gConj_mem : (Monod.Dev.CG.gConj : SLR) ∈ Kt := by
  have e : (Monod.Dev.CG.gConj : SLR) = ll 1 * uu 1 := by
    apply slr_ext; intro i j
    simp only [ent_mul]
    fin_cases i <;> fin_cases j <;> simp [uu, ll, Monod.Dev.CG.gConj, ent] <;> norm_cast
  rw [e]
  exact Kt.mul_mem (by exact_mod_cast ll_int_mem 1) (by exact_mod_cast uu_int_mem 1)

lemma bEl_tK_mem : Monod.Dev.CG.bEl tK ∈ Kt :=
  Kt.mul_mem (Kt.mul_mem gConj_mem ell_tK_mem) (Kt.inv_mem gConj_mem)

lemma exists_sigma_tK : ∃ σ : Subring.closure ({tK} : Set (⊤ : Subring ℝ)) →+* ℚ_[2],
    σ ⟨tK, Subring.subset_closure rfl⟩ = ((2 : ℚ_[2]))⁻¹ ^ 5 := by
  refine Monod.Dev.CG.A6.exists_hom_closure_real ⊤ tK _ fun p hp => ?_
  set r : ℚ := ((2 : ℚ))⁻¹ ^ 5
  have e1 : ((tK : ℝ)) = algebraMap ℚ ℝ r := by simp [r, tK]
  have e2 : ((2 : ℚ_[2]))⁻¹ ^ 5 = algebraMap ℚ ℚ_[2] r := by simp [r]
  rw [e1, Polynomial.aeval_algebraMap_apply] at hp
  have hr : Polynomial.aeval r p = 0 := (map_eq_zero_iff _ (algebraMap ℚ ℝ).injective).1 hp
  rw [e2, Polynomial.aeval_algebraMap_apply, hr, map_zero]

/-- The orbit relation of `K` on `P¹` has no left invariant mean. -/
theorem not_isAmenableRel_orbRelP_K : ¬ IsAmenableRel volP1 (orbRelP K) := by
  have := countable_Kt
  obtain ⟨σ, hσ⟩ := exists_sigma_tK
  obtain ⟨h2a, h2b⟩ := Monod.Dev.CG.A6.padic_norm_two 2
  have hs : 20 ≤ ‖σ ⟨tK, Subring.subset_closure rfl⟩‖ := by
    rw [hσ, norm_pow, norm_inv]
    have : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
      have := Padic.norm_p (p := 2)
      simpa using this
    rw [this]; norm_num
  obtain ⟨S0, hS0, hb0, ha0⟩ := Monod.Dev.CG.chk_exists_pingpong_set tK ℚ_[2] σ h2a h2b hs
  have ht : |(tK : ℝ)| < 2 := by
    show |(1 / 2 : ℝ) ^ 5| < 2
    norm_num [abs_of_pos]
  have := not_isAmenableRel_relL (Λ := Kt) (Monod.Dev.CG.ell tK) (Monod.Dev.CG.bEl tK)
    ell_tK_mem bEl_tK_mem (Monod.Dev.CG.chk_null_of_wandering tK ht) (S0 ∩ Kt)
    Set.inter_subset_right
    (fun γ => by rw [Set.mem_inter_iff, Set.mem_inter_iff, hS0, SetLike.mem_coe,
      SetLike.mem_coe, neg_mem_Kt])
    (fun δ hδ => ⟨fun h => (hb0 δ hδ.1).1 h.1, fun h => (hb0 δ hδ.1).2 h.1⟩)
    (fun δ hδ hδS m hm => ⟨ha0 δ (fun h => hδS ⟨h, hδ⟩) m hm,
      Kt.mul_mem hδ (Kt.zpow_mem ell_tK_mem m)⟩)
  exact this

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod MeasureTheory

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore
end

section
/-! # Group GoalDirect: Theorem 1.1 without `μ`-amenability

A second proof of the goal. Nonamenability: if `G₀` were amenable, its orbit relation on `P¹`
would be amenable in the sense of Connes–Feldman–Weiss (Monod's published
`isAmenableRel_orbit_of_isAmenable`); by statement 10 it agrees with the orbit relation of `K`
off the `K`-saturation of `P¹ \ (ℝ \ ℚ)`, a countable, hence null, set; so the orbit relation of `K`
would be amenable, which the Carrière–Ghys ping-pong argument (`S2.not_isAmenableRel_orbRelP_K`)
refutes. Finite presentation: statements 12 and 27. -/

namespace LodhaMoore.Dev.GoalDirect

open LodhaMoore Monod MeasureTheory

/-! ### Transfer of amenability across a saturated null set (copied from `CFW4`) -/

section Transfer

variable {X : Type*} [MeasurableSpace X]


/-! ### Transfer of amenability across a saturated null set -/

/-- A partial transformation of `R'` restricted to the complement of an `R'`-saturated set `N`
is a partial transformation of `R`, when `R` and `R'` agree off `N`. -/
def PartialTransformation.restrictCompl {R R' : Set (X × X)} {N : Set X} (hN : MeasurableSet N)
    (hsat : ∀ p ∈ R', p.1 ∈ N ↔ p.2 ∈ N)
    (hagree : ∀ p : X × X, p.1 ∉ N → p.2 ∉ N → (p ∈ R ↔ p ∈ R'))
    (φ : PartialTransformation R') : PartialTransformation R where
  dom := φ.dom ∩ Nᶜ
  cod := φ.cod ∩ Nᶜ
  measurableSet_dom := φ.measurableSet_dom.inter hN.compl
  measurableSet_cod := φ.measurableSet_cod.inter hN.compl
  e :=
    { toFun := fun a => ⟨(φ.e ⟨a, a.2.1⟩ : X), (φ.e ⟨a, a.2.1⟩).2, fun h =>
        a.2.2 ((hsat _ (φ.graph_subset ⟨a, a.2.1⟩)).2 h)⟩
      invFun := fun b => ⟨(φ.e.symm ⟨b, b.2.1⟩ : X), (φ.e.symm ⟨b, b.2.1⟩).2, fun h => by
        have := (hsat _ (φ.graph_subset (φ.e.symm ⟨b, b.2.1⟩))).1 h
        rw [MeasurableEquiv.apply_symm_apply] at this
        exact b.2.2 this⟩
      left_inv := fun a => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, MeasurableEquiv.symm_apply_apply]
      right_inv := fun b => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, MeasurableEquiv.apply_symm_apply]
      measurable_toFun := by
        apply Measurable.subtype_mk
        exact measurable_subtype_coe.comp
          (φ.e.measurable.comp (measurable_subtype_coe.subtype_mk))
      measurable_invFun := by
        apply Measurable.subtype_mk
        exact measurable_subtype_coe.comp
          (φ.e.symm.measurable.comp (measurable_subtype_coe.subtype_mk)) }
  graph_subset a := by
    have h1 := φ.graph_subset ⟨a, a.2.1⟩
    refine (hagree ((a : X), (φ.e ⟨a, a.2.1⟩ : X)) a.2.2 ?_).2 h1
    exact fun h => a.2.2 ((hsat _ h1).2 h)

/-- Transfer of amenability across an invariant null set: if `R` and `R'` agree off
`N × X ∪ X × N`, where `N` is a measurable `μ`-null set saturated for `R'`, and the pairs of `R`
meeting `N` start from a null set, then amenability of `R` gives amenability of `R'`.  Given a
left invariant mean `P` of `R`, the mean `f ↦ P (1_{Nᶜ × Nᶜ} · f)` is one for `R'`. -/
theorem isAmenableRel_of_agree {μ : Measure X} {R R' : Set (X × X)} {N : Set X}
    (hN : MeasurableSet N) (hN0 : μ N = 0)
    (hsat : ∀ p ∈ R', p.1 ∈ N ↔ p.2 ∈ N)
    (hagree : ∀ p : X × X, p.1 ∉ N → p.2 ∉ N → (p ∈ R ↔ p ∈ R'))
    (hRN : RelNull μ R {p | p.1 ∈ N ∨ p.2 ∈ N})
    (hR : IsAmenableRel μ R) : IsAmenableRel μ R' := by
  classical
  obtain ⟨P, hP⟩ := hR
  set S : Set (X × X) := Nᶜ ×ˢ Nᶜ with hS
  have hSm : MeasurableSet S := hN.compl.prod hN.compl
  let T : (X × X → ℝ) → X × X → ℝ := fun f => S.indicator f
  have hT : ∀ f, IsBddMeasOn R' f → IsBddMeasOn R (T f) := by
    rintro f ⟨hfm, C, hC⟩
    refine ⟨hfm.indicator hSm, max C 0, fun p hp => ?_⟩
    by_cases hpS : p ∈ S
    · simp only [T, Set.indicator_of_mem hpS]
      exact (hC p ((hagree p hpS.1 hpS.2).1 hp)).trans (le_max_left _ _)
    · simp only [T, Set.indicator_of_notMem hpS, abs_zero]
      exact le_max_right _ _
  refine ⟨fun f => P (T f), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun f hf => hP.aemeasurable _ (hT f hf)
  · intro f g hf hg hfg
    refine hP.congr _ _ (hT f hf) (hT g hg) (measure_mono_null ?_ hfg)
    rintro _ ⟨p, ⟨hne, hpR⟩, rfl⟩
    have hpS : p ∈ S := by
      by_contra hpS
      simp [T, Set.indicator_of_notMem hpS] at hne
    refine ⟨p, ⟨fun h => hne ?_, (hagree p hpS.1 hpS.2).1 hpR⟩, rfl⟩
    simp only [T, Set.indicator_of_mem hpS, h]
  · intro f g hf hg
    have : T (f + g) = T f + T g := Set.indicator_add S f g
    rw [this]
    exact hP.add _ _ (hT f hf) (hT g hg)
  · intro c f hf
    have : T (c • f) = c • T f := by
      funext p
      by_cases hp : p ∈ S <;> simp [T, hp]
    rw [this]
    exact hP.smul _ _ (hT f hf)
  · intro f hf hpos
    refine hP.nonneg _ (hT f hf) fun p hp => ?_
    by_cases hpS : p ∈ S
    · simp only [T, Set.indicator_of_mem hpS]
      exact hpos p ((hagree p hpS.1 hpS.2).1 hp)
    · simp [T, Set.indicator_of_notMem hpS]
  · have h1 : IsBddMeasOn R (1 : X × X → ℝ) := ⟨measurable_const, 1, fun _ _ => by simp⟩
    have h1' : IsBddMeasOn R' (1 : X × X → ℝ) := ⟨measurable_const, 1, fun _ _ => by simp⟩
    refine (hP.congr _ _ (hT 1 h1') h1 (measure_mono_null ?_ hRN)).trans hP.one
    rintro _ ⟨p, ⟨hne, hpR⟩, rfl⟩
    refine ⟨p, ⟨?_, hpR⟩, rfl⟩
    by_contra hp
    simp only [Set.mem_ofPred_eq, not_or] at hp
    have hpS : p ∈ S := ⟨hp.1, hp.2⟩
    simp [T, Set.indicator_of_mem hpS] at hne
  · intro φ f hf
    let ψ := PartialTransformation.restrictCompl hN hsat hagree φ
    have hshift : T (φ.shiftRel f) = ψ.shiftRel (T f) := by
      funext p
      obtain ⟨y, z⟩ := p
      simp only [T, PartialTransformation.shiftRel, Set.indicator, S, Set.mem_prod,
        Set.mem_compl_iff]
      by_cases hy : y ∈ N
      · have : y ∉ ψ.cod := fun h => h.2 hy
        simp [hy, this]
      by_cases hz : z ∈ N
      · simp [hz]
      by_cases hc : y ∈ φ.cod
      · have hc' : y ∈ ψ.cod := ⟨hc, hy⟩
        have hx : ((φ.e.symm ⟨y, hc⟩ : φ.dom) : X) ∉ N := by
          intro h
          have := (hsat _ (φ.graph_subset (φ.e.symm ⟨y, hc⟩))).1 h
          rw [MeasurableEquiv.apply_symm_apply] at this
          exact hy this
        simp only [hy, hz, not_false_eq_true, and_self, ↓reduceIte, hc, ↓reduceDIte, hc']
        split_ifs with h
        · rfl
        · exact absurd ⟨hx, trivial⟩ h
      · have : y ∉ ψ.cod := fun h => hc h.1
        simp [hy, hz, hc, this]
    show P (T (φ.shiftRel f)) =ᵐ[μ] φ.shiftBase (P (T f))
    rw [hshift]
    refine (hP.invariant ψ _ (hT f hf)).trans ?_
    have : ∀ᵐ y ∂μ, y ∉ N := measure_mono_null (fun y hy => not_not.1 hy) hN0
    filter_upwards [this] with y hy
    simp only [PartialTransformation.shiftBase]
    by_cases hc : y ∈ φ.cod
    · have hc' : y ∈ ψ.cod := ⟨hc, hy⟩
      simp only [hc, hc', ↓reduceDIte]
      rfl
    · have : y ∉ ψ.cod := fun h => hc h.1
      simp [hc, this]

end Transfer

/-! ### Nonamenability of `G₀` -/

section Amen

/-- Homeomorphisms of the projective line act on it by evaluation. -/
abbrev mulActionHomeo : MulAction (OnePoint ℝ ≃ₜ OnePoint ℝ) (OnePoint ℝ) where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] mulActionHomeo

lemma countable_G0 : Countable G0 := by
  have : (G0 : Set (OnePoint ℝ ≃ₜ OnePoint ℝ)) = Set.range (FreeGroup.lift
      (fun x : ({a, b, c} : Set (OnePoint ℝ ≃ₜ OnePoint ℝ)) => (x : OnePoint ℝ ≃ₜ OnePoint ℝ))) := by
    rw [← MonoidHom.coe_range, ← FreeGroup.closure_eq_range]
    rfl
  exact (this ▸ Set.countable_range _ : (G0 : Set (OnePoint ℝ ≃ₜ OnePoint ℝ)).Countable).to_subtype

lemma volP1_countable {Z : Set (OnePoint ℝ)} (hZ : Z.Countable) : volP1 Z = 0 := by
  rw [volP1, OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply]
  exact (hZ.preimage OnePoint.coe_injective).measure_zero _

/-- The irrational points of the projective line. -/
def Irr : Set (OnePoint ℝ) := {x | ∃ t : ℝ, Irrational t ∧ x = (t : OnePoint ℝ)}

lemma countable_compl_Irr : (Irrᶜ : Set (OnePoint ℝ)).Countable := by
  refine ((Set.countable_range fun q : ℚ => ((q : ℝ) : OnePoint ℝ)).insert OnePoint.infty).mono ?_
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact Set.mem_insert _ _
  | coe t =>
    refine Set.mem_insert_of_mem _ ?_
    have : ¬ Irrational t := fun h => hx ⟨t, h, rfl⟩
    unfold Irrational at this
    push Not at this
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, rfl⟩

/-- Statement 10 for a point of `Irr`, in the form of the two orbit relations. -/
lemma orbit_iff {x y : OnePoint ℝ} (hx : x ∈ Irr) :
    (∃ g : G0, g • x = y) ↔ (x, y) ∈ S2.orbRelP K := by
  obtain ⟨t, ht, rfl⟩ := hx
  have := Set.ext_iff.1 (orbit_G0_eq_orbit_K_of_irrational t ht) y
  simp only [Set.mem_ofPred_eq] at this
  simp only [S2.orbRelP, Set.mem_ofPred_eq]
  rw [← this]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, g.2, hg⟩
  · rintro ⟨g, hg, h⟩
    exact ⟨⟨g, hg⟩, h⟩

/-- The elements of `G₀` preserve `volP1`-null sets: off the countable set `P¹ \ Irr` each of
them agrees pointwise with elements of the countable group `K` (statement 10). -/
lemma null_preimage_G0 (l : G0) (s : Set (OnePoint ℝ)) (hs : volP1 s = 0) :
    volP1 ((fun x : OnePoint ℝ => l • x) ⁻¹' s) = 0 := by
  have := S2.countable_Kt
  have hsub : (fun x : OnePoint ℝ => l • x) ⁻¹' s ⊆
      Irrᶜ ∪ ⋃ A : S2.Kt, Monod.mob (A : S2.SLR) ⁻¹' s := by
    intro x hx
    by_cases hxI : x ∈ Irr
    · obtain ⟨A, hA, hAx⟩ := (orbit_iff hxI).1 ⟨l, rfl⟩
      refine Or.inr (Set.mem_iUnion.2 ⟨⟨A, hA⟩, ?_⟩)
      simp only [Set.mem_preimage] at hx ⊢
      rw [hAx]
      exact hx
    · exact Or.inl hxI
  refine measure_mono_null hsub (measure_union_null (volP1_countable countable_compl_Irr) ?_)
  exact measure_iUnion_null fun A => S2.null_preimage_mob _ hs

/-- The `K`-saturation of the non-irrational points: countable, and `K`-invariant. -/
def NK : Set (OnePoint ℝ) := {y | ∃ x ∉ Irr, (x, y) ∈ S2.orbRelP K}

lemma countable_NK : NK.Countable := by
  have := S2.countable_K
  refine (countable_compl_Irr.biUnion fun x _ => S2.countable_orbRelP K x).mono ?_
  rintro y ⟨x, hx, hxy⟩
  exact Set.mem_biUnion hx hxy

theorem not_isAmenable_G0 : ¬ Garrido.IsAmenable G0 := by
  intro hA
  have := S2.sigmaFinite_volP1
  have := countable_G0
  have hE := Monod.isAmenableRel_orbit_of_isAmenable volP1 G0
    (fun l => (l : OnePoint ℝ ≃ₜ OnePoint ℝ).continuous.measurable) null_preimage_G0 hA
  have hequiv := S2.equivalence_orbRelP K
  apply S2.not_isAmenableRel_orbRelP_K
  refine isAmenableRel_of_agree (N := NK) countable_NK.measurableSet
    (volP1_countable countable_NK) ?_ ?_ ?_ hE
  · -- `NK` is `K`-saturated.
    rintro ⟨x, y⟩ hxy
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, hz, hequiv.trans hzx hxy⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨z, hz, hequiv.trans hzy (hequiv.symm hxy)⟩
  · -- Off `NK` the two relations agree (statement 10).
    rintro ⟨x, y⟩ hx -
    have hxI : x ∈ Irr := by
      by_contra h
      exact hx ⟨x, h, hequiv.refl x⟩
    exact orbit_iff hxI
  · -- The pairs of the `G₀`-relation meeting `NK` start from a countable set.
    have hc : (NK ∪ ⋃ l : G0, (fun y : OnePoint ℝ => l⁻¹ • y) '' NK).Countable :=
      countable_NK.union (Set.countable_iUnion fun l => countable_NK.image _)
    refine measure_mono_null ?_ (volP1_countable hc)
    rintro _ ⟨⟨x, y⟩, ⟨hxy, l, hl⟩, rfl⟩
    rcases hxy with h | h
    · exact Or.inl h
    · refine Or.inr (Set.mem_iUnion.2 ⟨l, y, h, ?_⟩)
      simp only at hl ⊢
      rw [← hl, inv_smul_smul]

end Amen

theorem isFinitelyPresented_G0 : Group.IsFinitelyPresented G0 := by
  obtain ⟨e, -⟩ := exists_mulEquiv_G0_G0Seq_and_semiconj_Phi
  have := presentation_G_G0Seq_and_isFinitelyPresented.2.2.2
  exact Group.IsFinitelyPresented.equiv ((MulEquiv.inv' G0).trans e).symm

end LodhaMoore.Dev.GoalDirect

namespace LodhaMoore

open LodhaMoore.Dev.GoalDirect

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.GoalDirect
theorem solution :
    ¬ Garrido.IsAmenable G0 ∧ Group.IsFinitelyPresented G0 :=
  ⟨not_isAmenable_G0, isFinitelyPresented_G0⟩
end
