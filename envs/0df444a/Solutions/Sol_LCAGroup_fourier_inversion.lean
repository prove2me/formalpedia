-- Prove2me | solution 1 for LCAGroup.fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T13:03:07.301484+00:00
-- url     : https://prove2.me/submissions/254d3d87-8614-468b-9388-b0de82516840

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_PlancherelMeasure
import Theorems.Thm_LCAGroup_fourier_convolution

open MeasureTheory Topology

set_option autoImplicit false

namespace Sol_LCAGroup_fourier_inversion

open Filter Set RiemannMasullo
open scoped ENNReal NNReal Pointwise

section General

/-- For an integrable function, a compact subset of a measurable set carries all but an
arbitrarily small part of the integral of its norm, assuming inner regularity on finite sets. -/
theorem exists_isCompact_integral_norm_sdiff_lt
    {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [μ.InnerRegularCompactLTTop] {f : X → E}
    (hf : Integrable f μ) {s : Set X} (hs : MeasurableSet s) {ε : ℝ} (hε : 0 < ε) :
    ∃ K ⊆ s, IsCompact K ∧ (∫ x in s \ K, ‖f x‖ ∂μ) < ε := by
  obtain ⟨t, ht, htZero, htFin⟩ := hf.aefinStronglyMeasurable.exists_set_sigmaFinite
  let : SigmaFinite (μ.restrict t) := htFin
  let A (n : ℕ) := s ∩ (spanningSets (μ.restrict t) n ∩ t)
  have hA n : MeasurableSet (A n) := hs.inter ((measurableSet_spanningSets _ _).inter ht)
  have hAμ n : μ (A n) < ∞ := by
    apply (measure_mono inter_subset_right).trans_lt
    rw [← Measure.restrict_apply (measurableSet_spanningSets _ _)]
    exact measure_spanningSets_lt_top _ _
  have hUnion : ⋃ n, A n = s ∩ t := by
    simp [A, ← iUnion_inter, ← inter_iUnion]
  have hMono : Monotone A := fun i j hij ↦
    inter_subset_inter_right _ (inter_subset_inter_left _ (monotone_spanningSets _ hij))
  have hLim := tendsto_setIntegral_of_monotone (f := fun x ↦ ‖f x‖) hA hMono hf.norm.integrableOn
  rw [hUnion] at hLim
  have hEq : (∫ x in s ∩ t, ‖f x‖ ∂μ) = ∫ x in s, ‖f x‖ ∂μ := by
    symm
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs.nullMeasurableSet inter_subset_left ?_
    filter_upwards [ae_imp_of_ae_restrict htZero] with x hx hxS
    have hxT : x ∈ tᶜ := fun h ↦ hxS.2 ⟨hxS.1, h⟩
    simp [show f x = 0 from hx hxT]
  rw [hEq] at hLim
  have hNear : ∀ᶠ n in atTop, (∫ x in s, ‖f x‖ ∂μ) - ε / 2 < ∫ x in A n, ‖f x‖ ∂μ :=
    hLim (Ioi_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := hNear.exists
  obtain ⟨δ, hδ, hSmall⟩ := exists_pos_setLIntegral_lt_of_measure_lt hf.hasFiniteIntegral.ne
    (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨K, hKA, hK, hm⟩ := (hA n).exists_isCompact_sdiff_lt (hAμ n).ne hδ.ne'
  have hKmeas := hK.isClosed.measurableSet
  have hSmall' : (∫ x in A n \ K, ‖f x‖ ∂μ) < ε / 2 := by
    have h := hSmall (A n \ K) hm
    rw [integral_norm_eq_lintegral_enorm hf.integrableOn.aestronglyMeasurable]
    exact (ENNReal.toReal_lt_toReal h.ne_top ENNReal.ofReal_ne_top).mpr h |>.trans_eq
      (ENNReal.toReal_ofReal (half_pos hε).le)
  have hKs : K ⊆ s := hKA.trans inter_subset_left
  have h₁ := setIntegral_sdiff hKmeas hf.norm.integrableOn hKA
  have h₂ := setIntegral_sdiff hKmeas hf.norm.integrableOn hKs
  exact ⟨K, hKs, hK, by
    change _ < (∫ x in A n, ‖f x‖ ∂μ) at hn
    linarith⟩

section Approx

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [μ.Regular] [NormedSpace ℝ E]

/-- Density of compactly supported continuous functions in `L¹` of a regular measure on a
locally compact Hausdorff space (no normality assumption). -/
theorem exists_compactTest_eLpNorm_sub_le {f : X → E} (hf : Integrable f μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g, eLpNorm (f - g) 1 μ ≤ ε ∧ Continuous g ∧ HasCompactSupport g := by
  classical
  refine (memLp_one_iff_integrable.mpr hf).induction_dense (by simp)
    (fun g : X → E => Continuous g ∧ HasCompactSupport g) ?_ ?_ ?_ hε
  · intro c s hsm hsf δ hδ
    obtain ⟨η, hη, hsmall⟩ := exists_eLpNorm_indicator_le (p := 1) (μ := μ) (by simp) c hδ
    have hη' : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hη.ne')).ne'
    obtain ⟨U, hsU, hU, -, hUs⟩ := hsm.exists_isOpen_sdiff_lt hsf.ne hη'
    obtain ⟨K, hKs, hK, hsK⟩ := hsm.exists_isCompact_sdiff_lt hsf.ne hη'
    obtain ⟨b, hbK, hbU, hbs, hb⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hμ : μ (U \ K) ≤ η := calc
      μ (U \ K) ≤ μ ((U \ s) ∪ (s \ K)) := measure_mono (by
        intro x hx
        by_cases hxs : x ∈ s
        · exact Or.inr ⟨hxs, hx.2⟩
        · exact Or.inl ⟨hx.1, hxs⟩)
      _ ≤ μ (U \ s) + μ (s \ K) := measure_union_le _ _
      _ ≤ η := (add_le_add hUs.le hsK.le).trans_eq (ENNReal.add_halves _)
    let g (x : X) := b x • c
    have hc : Continuous g := b.continuous.smul continuous_const
    have hs : HasCompactSupport g := hbs.comp_left (g := fun t : ℝ ↦ t • c) (zero_smul _ _)
    refine ⟨g, ?_, hc, hs⟩
    refine (eLpNorm_mono (g := (U \ K).indicator (fun _ ↦ c)) ?_).trans
      (hsmall _ hμ)
    intro x
    by_cases hxK : x ∈ K
    · have h1 : b x = 1 := hbK hxK
      simp [g, hxK, hKs hxK, h1]
    by_cases hxs : x ∈ s
    · simp only [Pi.sub_apply, indicator_of_mem hxs, indicator_of_mem
        (show x ∈ U \ K from ⟨hsU hxs, hxK⟩), g]
      rw [show b x • c - c = (b x - 1) • c by rw [sub_smul, one_smul], norm_smul]
      have hle : ‖b x - 1‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb x).1, (hb x).2]
      simpa using mul_le_mul_of_nonneg_right hle (norm_nonneg c)
    · by_cases hxU : x ∈ U
      · simpa [g, hxU, hxK, hxs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb x).1] using
          mul_le_mul_of_nonneg_right (hb x).2 (norm_nonneg c)
      · have h0 : b x = 0 := hbU hxU
        simp [g, hxU, hxs, h0]
  · exact fun _ _ ⟨hc, hs⟩ ⟨hc', hs'⟩ ↦ ⟨hc.add hc', hs.add hs'⟩
  · exact fun g hg ↦ (hg.1.integrable_of_hasCompactSupport hg.2).1

end Approx

/-- Averaging against a probability density: if `u` is within `ε` of `c` wherever the density
`h` does not vanish, then the `h`-average of `u` is within `ε` of `c`. -/
theorem norm_integral_ofReal_mul_sub_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {h : X → ℝ} (hh : Integrable h μ) (h0 : ∀ y, 0 ≤ h y) (h1 : ∫ y, h y ∂μ = 1)
    {u : X → ℂ} (hu : Integrable (fun y ↦ (h y : ℂ) * u y) μ) {c : ℂ} {ε : ℝ}
    (hε : ∀ y, h y ≠ 0 → ‖u y - c‖ ≤ ε) :
    ‖(∫ y, (h y : ℂ) * u y ∂μ) - c‖ ≤ ε := by
  have hhC : Integrable (fun y ↦ (h y : ℂ)) μ := hh.ofReal
  have hc : (∫ y, (h y : ℂ) * c ∂μ) = c := by
    rw [integral_mul_const, integral_complex_ofReal, h1, Complex.ofReal_one, one_mul]
  have hhc : Integrable (fun y ↦ (h y : ℂ) * c) μ := hhC.mul_const c
  calc ‖(∫ y, (h y : ℂ) * u y ∂μ) - c‖
      = ‖∫ y, ((h y : ℂ) * u y - (h y : ℂ) * c) ∂μ‖ := by rw [integral_sub hu hhc, hc]
    _ ≤ ∫ y, h y * ε ∂μ := by
        refine norm_integral_le_of_norm_le (hh.mul_const ε) (.of_forall fun y ↦ ?_)
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 y)]
        by_cases hy : h y = 0
        · simp [hy]
        · exact mul_le_mul_of_nonneg_left (hε y hy) (h0 y)
    _ = ε := by rw [integral_mul_const, h1, one_mul]

/-- Splitting an integral `∫ Φ (a - b)` into a part where `a - b` is small and a tail. -/
theorem norm_integral_mul_sub_integral_mul_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {Φ : X → ℂ} (hΦ : Integrable Φ ν) {C : Set X} (hC : MeasurableSet C) {a b : X → ℂ}
    (ha : Integrable (fun χ ↦ Φ χ * a χ) ν) (hb : Integrable (fun χ ↦ Φ χ * b χ) ν) {ε : ℝ}
    (hε0 : 0 ≤ ε) (h2 : ∀ χ, ‖a χ - b χ‖ ≤ 2) (hε : ∀ χ ∈ C, ‖a χ - b χ‖ ≤ ε) :
    ‖(∫ χ, Φ χ * a χ ∂ν) - ∫ χ, Φ χ * b χ ∂ν‖ ≤
      ε * (∫ χ, ‖Φ χ‖ ∂ν) + 2 * ∫ χ in Cᶜ, ‖Φ χ‖ ∂ν := by
  classical
  have hbd : Integrable (fun χ ↦ ε * ‖Φ χ‖ + 2 * Cᶜ.indicator (fun χ ↦ ‖Φ χ‖) χ) ν :=
    (hΦ.norm.const_mul ε).add ((hΦ.norm.indicator hC.compl).const_mul 2)
  calc ‖(∫ χ, Φ χ * a χ ∂ν) - ∫ χ, Φ χ * b χ ∂ν‖
      = ‖∫ χ, (Φ χ * a χ - Φ χ * b χ) ∂ν‖ := by rw [integral_sub ha hb]
    _ ≤ ∫ χ, (ε * ‖Φ χ‖ + 2 * Cᶜ.indicator (fun χ ↦ ‖Φ χ‖) χ) ∂ν := by
        refine norm_integral_le_of_norm_le hbd (.of_forall fun χ ↦ ?_)
        rw [← mul_sub, norm_mul]
        by_cases hχ : χ ∈ C
        · have h0 : Cᶜ.indicator (fun χ ↦ ‖Φ χ‖) χ = 0 := indicator_of_notMem (by simpa using hχ) _
          rw [h0, mul_zero, add_zero, mul_comm]
          exact mul_le_mul_of_nonneg_right (hε χ hχ) (norm_nonneg _)
        · have h0 : Cᶜ.indicator (fun χ ↦ ‖Φ χ‖) χ = ‖Φ χ‖ := indicator_of_mem hχ _
          rw [h0, mul_comm]
          have h3 := mul_le_mul_of_nonneg_right (h2 χ) (norm_nonneg (Φ χ))
          nlinarith [norm_nonneg (Φ χ)]
    _ = ε * (∫ χ, ‖Φ χ‖ ∂ν) + 2 * ∫ χ in Cᶜ, ‖Φ χ‖ ∂ν := by
        rw [integral_add (hΦ.norm.const_mul ε) ((hΦ.norm.indicator hC.compl).const_mul 2),
          integral_const_mul, integral_const_mul, integral_indicator hC.compl]

/-- A normalised continuous bump function supported in a prescribed neighbourhood. -/
theorem exists_bump {G : Type*} [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {V : Set G} {x : G} (hV : V ∈ 𝓝 x) :
    ∃ k : G → ℝ, Continuous k ∧ HasCompactSupport k ∧ (∀ y, 0 ≤ k y) ∧ ∫ y, k y ∂μ = 1 ∧
      Function.support k ⊆ V := by
  obtain ⟨b, hb1, hb0, hbs, hb⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := x)) (isOpen_interior (s := V)).isClosed_compl
    (Set.disjoint_singleton_left.mpr fun h ↦ h (mem_interior_iff_mem_nhds.mpr hV))
  have hbx : b x = 1 := hb1 (mem_singleton x)
  have hpos : 0 < ∫ y, b y ∂μ :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbs (fun y ↦ (hb y).1)
      (by rw [hbx]; exact one_ne_zero)
  refine ⟨fun y ↦ b y * (∫ y, b y ∂μ)⁻¹, b.continuous.mul continuous_const,
    hbs.mul_right (f' := fun _ ↦ (∫ y, b y ∂μ)⁻¹), fun y ↦ mul_nonneg (hb y).1 (inv_nonneg.mpr hpos.le),
    ?_, ?_⟩
  · rw [integral_mul_const, mul_inv_cancel₀ hpos.ne']
  · intro y hy
    by_contra hyV
    have : b y = 0 := hb0 (fun h ↦ hyV (interior_subset h))
    exact hy (by simp [this])

/-- A continuous function of compact support on a topological group is uniformly continuous
with respect to right translations. -/
theorem exists_nhds_one_forall_norm_mul_sub_lt {G E : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [NormedAddCommGroup E] {φ : G → E}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {η : ℝ} (hη : 0 < η) :
    ∃ V ∈ 𝓝 (1 : G), ∀ z, ∀ v ∈ V, ‖φ (z * v) - φ z‖ < η := by
  obtain ⟨W, hW, hW1⟩ := exists_compact_mem_nhds (1 : G)
  have hQ : IsCompact (tsupport φ * W⁻¹) := hs.isCompact.mul hW.inv
  have hD : Continuous (fun p : G × G ↦ φ (p.1 * p.2) - φ p.1) :=
    (hφ.comp (continuous_fst.mul continuous_snd)).sub (hφ.comp continuous_fst)
  obtain ⟨u, v, -, hv, hQu, h1v, huv⟩ := generalized_tube_lemma hQ
    (isCompact_singleton (x := (1 : G))) (isOpen_lt hD.norm continuous_const) (by
      rintro ⟨z, y⟩ ⟨-, hy⟩
      rw [mem_singleton_iff] at hy
      change y = 1 at hy
      subst hy
      simpa using hη)
  refine ⟨v ∩ W, inter_mem (hv.mem_nhds (h1v rfl)) hW1, fun z w hw ↦ ?_⟩
  by_cases hz : z ∈ tsupport φ * W⁻¹
  · exact huv (mk_mem_prod (hQu hz) hw.1)
  · have h1 : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
      hz ⟨z, h, 1, by simpa using mem_of_mem_nhds hW1, mul_one z⟩
    have h2 : φ (z * w) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
      hz ⟨z * w, h, w⁻¹, by simpa using hw.2, mul_inv_cancel_right z w⟩
    rw [h1, h2, sub_zero, norm_zero]
    exact hη

/-- A compact set of characters of a locally compact group is equicontinuous at `1`. -/
theorem exists_nhds_one_forall_norm_char_sub_one_lt {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    {C : Set (PontryaginDual G)} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ χ ∈ C, ∀ v ∈ V, ‖(χ v : ℂ) - 1‖ < ε := by
  have he : Continuous (fun p : PontryaginDual G × G ↦ p.1 p.2) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_fst).prodMk continuous_snd)
  have hd : Continuous (fun p : PontryaginDual G × G ↦ ((p.1 p.2 : Circle) : ℂ) - 1) :=
    (continuous_subtype_val.comp he).sub continuous_const
  obtain ⟨u, v, -, hv, hCu, h1v, huv⟩ := generalized_tube_lemma hC
    (isCompact_singleton (x := (1 : G))) (isOpen_lt hd.norm continuous_const) (by
      rintro ⟨χ, y⟩ ⟨-, hy⟩
      rw [mem_singleton_iff] at hy
      change y = 1 at hy
      subst hy
      simpa using hε)
  exact ⟨v, hv.mem_nhds (h1v rfl), fun χ hχ y hy ↦ huv (mk_mem_prod (hCu hχ) hy)⟩

end General

section Plancherel

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

variable (μ : Measure G)

/-- Multiplication by a conjugated character preserves integrability. -/
theorem integrable_fourierIntegrand {f : G → ℂ} (hf : Integrable f μ)
    (χ : PontryaginDual G) : Integrable (fun x ↦ f x * star (χ x : ℂ)) μ := by
  exact hf.mul_bdd (c := 1) ((continuous_subtype_val.comp χ.continuous).star.aestronglyMeasurable)
    (.of_forall fun x ↦ by rw [norm_star, Circle.norm_coe])

/-- The Fourier integral is bounded by the integral of the absolute value. -/
theorem norm_lcaFourier_le_integral_norm (f : G → ℂ) (χ : PontryaginDual G) :
    ‖lcaFourier μ f χ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  simpa only [lcaFourier, norm_mul, norm_star, Circle.norm_coe, mul_one] using
    norm_integral_le_integral_norm (μ := μ) (fun x ↦ f x * star (χ x : ℂ))

/-- Linearity of the Fourier transform on integrable functions. -/
theorem lcaFourier_add_smul {F h : G → ℂ} (hF : Integrable F μ) (hh : Integrable h μ) (c : ℂ) :
    lcaFourier μ (F + c • h) = lcaFourier μ F + c • lcaFourier μ h := by
  funext χ
  simp only [lcaFourier, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add (integrable_fourierIntegrand μ hF χ)
    ((integrable_fourierIntegrand μ hh χ).const_mul c), integral_const_mul]

/-- The polarised Plancherel identity for a Plancherel measure. -/
theorem plancherel_inner {ν : Measure (PontryaginDual G)} (hν : LCAGroup.IsPlancherelMeasure μ ν)
    {F h : G → ℂ} (hF : Integrable F μ) (hF2 : MemLp F 2 μ) (hh : Integrable h μ)
    (hh2 : MemLp h 2 μ) :
    ∫ χ, lcaFourier μ F χ * star (lcaFourier μ h χ) ∂ν = ∫ x, F x * star (h x) ∂μ := by
  have hF' := (hν.2.2 F hF hF2).1
  have hh' := (hν.2.2 h hh hh2).1
  have key : ∀ c : ℂ, ‖hh'.toLp _ + c • hF'.toLp _‖ = ‖hh2.toLp h + c • hF2.toLp F‖ := by
    intro c
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_const_smul, ← MemLp.toLp_add,
      Lp.norm_toLp, Lp.norm_toLp, ← lcaFourier_add_smul μ hh hF c,
      (hν.2.2 _ (hh.add (hF.smul c)) (hh2.add (hF2.const_smul c))).2]
  have hinner : inner ℂ (hh'.toLp _) (hF'.toLp _) = inner ℂ (hh2.toLp h) (hF2.toLp F) := by
    rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (hh2.toLp h)]
    have e1 := key 1
    have e2 := key (-1)
    have e3 := key RCLike.I
    have e4 := key (-RCLike.I)
    simp only [one_smul, neg_smul, ← sub_eq_add_neg] at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  rw [L2.inner_def, L2.inner_def] at hinner
  calc ∫ χ, lcaFourier μ F χ * star (lcaFourier μ h χ) ∂ν
      = ∫ χ, inner ℂ ((hh'.toLp _ : PontryaginDual G → ℂ) χ)
          ((hF'.toLp _ : PontryaginDual G → ℂ) χ) ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hh'.coeFn_toLp, hF'.coeFn_toLp] with χ h1 h2
        rw [h1, h2, RCLike.inner_apply]
        rfl
    _ = ∫ x, inner ℂ ((hh2.toLp h : G → ℂ) x) ((hF2.toLp F : G → ℂ) x) ∂μ := hinner
    _ = ∫ x, F x * star (h x) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hh2.coeFn_toLp, hF2.coeFn_toLp] with x h1 h2
        rw [h1, h2, RCLike.inner_apply]
        rfl

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] in
/-- Evaluation at a point is continuous on the dual group. -/
theorem continuous_char_apply (x : G) :
    Continuous (fun χ : PontryaginDual G ↦ (χ x : ℂ)) :=
  continuous_subtype_val.comp ((continuous_eval_const (F := C(G, Circle)) x).comp
    (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous)

/-- Fourier inversion at a point of continuity, for `F ∈ L¹ ∩ L²` with integrable transform. -/
theorem inversion_of_continuousAt [μ.IsHaarMeasure] [μ.Regular]
    {ν : Measure (PontryaginDual G)} (hν : LCAGroup.IsPlancherelMeasure μ ν)
    {F : G → ℂ} (hF : Integrable F μ) (hF2 : MemLp F 2 μ)
    (hF' : Integrable (lcaFourier μ F) ν) {x : G} (hx : ContinuousAt F x) :
    F x = ∫ χ, lcaFourier μ F χ * (χ x : ℂ) ∂ν := by
  have := hν.1
  have := hν.2.1
  have hI : 0 ≤ ∫ χ, ‖lcaFourier μ F χ‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have key : ∀ ε > 0, ‖F x - ∫ χ, lcaFourier μ F χ * (χ x : ℂ) ∂ν‖ ≤
      ε * ((∫ χ, ‖lcaFourier μ F χ‖ ∂ν) + 3) := by
    intro ε hε
    obtain ⟨C, -, hC, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hF' MeasurableSet.univ hε
    rw [← compl_eq_univ_sdiff] at hTail
    obtain ⟨V₁, hV₁, hCV⟩ := exists_nhds_one_forall_norm_char_sub_one_lt hC hε
    have hU : {y | ‖F y - F x‖ < ε} ∈ 𝓝 x :=
      (Metric.tendsto_nhds.mp hx ε hε).mono fun y hy ↦ by rwa [dist_eq_norm] at hy
    have hxV : (fun y ↦ x⁻¹ * y) ⁻¹' V₁ ∈ 𝓝 x :=
      (continuous_mul_left x⁻¹).continuousAt.preimage_mem_nhds (by simpa using hV₁)
    obtain ⟨k, hkc, hks, hk0, hk1, hksupp⟩ := exists_bump μ (inter_mem hU hxV)
    have hki : Integrable k μ := hkc.integrable_of_hasCompactSupport hks
    have hκc : Continuous (fun y ↦ (k y : ℂ)) := Complex.continuous_ofReal.comp hkc
    have hκs : HasCompactSupport (fun y ↦ (k y : ℂ)) := hks.comp_left Complex.ofReal_zero
    have hκi : Integrable (fun y ↦ (k y : ℂ)) μ := hκc.integrable_of_hasCompactSupport hκs
    have hκ2 : MemLp (fun y ↦ (k y : ℂ)) 2 μ := hκc.memLp_of_hasCompactSupport hκs
    have hP := plancherel_inner μ hν hF hF2 hκi hκ2
    have hκn : ∫ y, ‖(k y : ℂ)‖ ∂μ = 1 := by
      rw [← hk1]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk0 y)]
    obtain ⟨M, hM⟩ := hκc.bounded_above_of_compact_support hκs
    have h1 : ‖(∫ y, F y * star ((k y : ℂ)) ∂μ) - F x‖ ≤ ε := by
      have hu : Integrable (fun y ↦ (k y : ℂ) * F y) μ :=
        hF.bdd_mul hκc.aestronglyMeasurable (.of_forall hM)
      have h := norm_integral_ofReal_mul_sub_le hki hk0 hk1 hu (c := F x) (ε := ε)
        (fun y hy ↦ le_of_lt (hksupp hy).1)
      have e : (fun y ↦ F y * star ((k y : ℂ))) = fun y ↦ (k y : ℂ) * F y := by
        funext y
        rw [← starRingEnd_apply, Complex.conj_ofReal, mul_comm]
      rw [e]
      exact h
    have hstar : ∀ χ : PontryaginDual G, star (lcaFourier μ (fun y ↦ (k y : ℂ)) χ) =
        ∫ y, (k y : ℂ) * (χ y : ℂ) ∂μ := by
      intro χ
      unfold lcaFourier
      rw [← starRingEnd_apply, ← integral_conj]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      change (starRingEnd ℂ) ((k y : ℂ) * star (χ y : ℂ)) = _
      rw [map_mul, Complex.conj_ofReal, starRingEnd_apply, star_star]
    have hχi : ∀ χ : PontryaginDual G, Integrable (fun y ↦ (k y : ℂ) * (χ y : ℂ)) μ := fun χ ↦
      hκi.mul_bdd (c := 1) ((continuous_subtype_val.comp χ.continuous).aestronglyMeasurable)
        (.of_forall fun y ↦ by rw [Circle.norm_coe])
    have h2 : ∀ χ : PontryaginDual G,
        ‖star (lcaFourier μ (fun y ↦ (k y : ℂ)) χ) - (χ x : ℂ)‖ ≤ 2 := by
      intro χ
      refine (norm_sub_le _ _).trans ?_
      rw [norm_star, Circle.norm_coe]
      have := norm_lcaFourier_le_integral_norm μ (fun y ↦ (k y : ℂ)) χ
      rw [hκn] at this
      linarith
    have h3 : ∀ χ ∈ C, ‖star (lcaFourier μ (fun y ↦ (k y : ℂ)) χ) - (χ x : ℂ)‖ ≤ ε := by
      intro χ hχ
      rw [hstar]
      refine norm_integral_ofReal_mul_sub_le hki hk0 hk1 (hχi χ) fun y hy ↦ ?_
      have hy' : x⁻¹ * y ∈ V₁ := (hksupp hy).2
      have e : (χ y : ℂ) - (χ x : ℂ) = (χ x : ℂ) * ((χ (x⁻¹ * y) : ℂ) - 1) := by
        rw [mul_sub, mul_one, ← Circle.coe_mul, ← map_mul, mul_inv_cancel_left]
      rw [e, norm_mul, Circle.norm_coe, one_mul]
      exact (hCV χ hχ _ hy').le
    have hm : AEStronglyMeasurable (fun χ ↦ star (lcaFourier μ (fun y ↦ (k y : ℂ)) χ)) ν :=
      (hν.2.2 _ hκi hκ2).1.aestronglyMeasurable.star
    have hΦ1 : Integrable
        (fun χ ↦ lcaFourier μ F χ * star (lcaFourier μ (fun y ↦ (k y : ℂ)) χ)) ν :=
      hF'.mul_bdd (c := 1) hm (.of_forall fun χ ↦ by
        rw [norm_star]
        exact (norm_lcaFourier_le_integral_norm μ _ χ).trans_eq hκn)
    have hΦ2 : Integrable (fun χ : PontryaginDual G ↦ lcaFourier μ F χ * (χ x : ℂ)) ν :=
      hF'.mul_bdd (c := 1) (continuous_char_apply x).aestronglyMeasurable
        (.of_forall fun χ ↦ by rw [Circle.norm_coe])
    have h4 := norm_integral_mul_sub_integral_mul_le hF' hC.measurableSet hΦ1 hΦ2 hε.le h2 h3
    rw [hP] at h4
    calc ‖F x - ∫ χ, lcaFourier μ F χ * (χ x : ℂ) ∂ν‖
        ≤ ‖F x - ∫ y, F y * star ((k y : ℂ)) ∂μ‖ +
          ‖(∫ y, F y * star ((k y : ℂ)) ∂μ) - ∫ χ, lcaFourier μ F χ * (χ x : ℂ) ∂ν‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + (ε * (∫ χ, ‖lcaFourier μ F χ‖ ∂ν) +
            2 * ∫ χ in Cᶜ, ‖lcaFourier μ F χ‖ ∂ν) :=
          add_le_add (by rw [norm_sub_rev]; exact h1) h4
      _ ≤ ε * ((∫ χ, ‖lcaFourier μ F χ‖ ∂ν) + 3) := by linarith
  have hI3 : 0 < (∫ χ, ‖lcaFourier μ F χ‖ ∂ν) + 3 := by linarith
  have h0 : ‖F x - ∫ χ, lcaFourier μ F χ * (χ x : ℂ) ∂ν‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have := key (ε / ((∫ χ, ‖lcaFourier μ F χ‖ ∂ν) + 3)) (div_pos hε hI3)
    rwa [div_mul_cancel₀ _ hI3.ne', ← zero_add ε] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

end Plancherel

section Conv

/-- An integrable bounded function is square integrable. -/
theorem memLp_two_of_integrable_of_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : X → ℂ} (hF : Integrable F μ) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) : MemLp F 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable]
  refine (hF.norm.const_mul B).mono' (hF.aestronglyMeasurable.norm.pow 2) (.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The integrand of a convolution with a bounded continuous function is integrable. -/
theorem integrable_conv_integrand {f : G → ℂ} (hf : Integrable f μ) {κ : G → ℂ}
    (hκc : Continuous κ) {M : ℝ} (hM : ∀ z, ‖κ z‖ ≤ M) (x : G) :
    Integrable (fun y ↦ f y * κ (y⁻¹ * x)) μ :=
  hf.mul_bdd (c := M) (hκc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
    (.of_forall fun y ↦ hM _)

/-- A convolution with a bounded function is bounded. -/
theorem norm_lcaConvolution_le {f : G → ℂ} (hf : Integrable f μ) {κ : G → ℂ} {M : ℝ}
    (hM : ∀ z, ‖κ z‖ ≤ M) (x : G) :
    ‖lcaConvolution μ f κ x‖ ≤ M * ∫ y, ‖f y‖ ∂μ := by
  unfold lcaConvolution
  calc ‖∫ y, f y * κ (y⁻¹ * x) ∂μ‖ ≤ ∫ y, M * ‖f y‖ ∂μ :=
        norm_integral_le_of_norm_le (hf.norm.const_mul M) (.of_forall fun y ↦ by
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
    _ = M * ∫ y, ‖f y‖ ∂μ := integral_const_mul _ _

/-- The convolution of an integrable function with a continuous function of compact support
is continuous. -/
theorem continuous_lcaConvolution {f : G → ℂ} (hf : Integrable f μ) {κ : G → ℂ}
    (hκc : Continuous κ) (hκs : HasCompactSupport κ) :
    Continuous (lcaConvolution μ f κ) := by
  obtain ⟨M, hM⟩ := hκc.bounded_above_of_compact_support hκs
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hI : 0 ≤ ∫ y, ‖f y‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  have hI1 : 0 < (∫ y, ‖f y‖ ∂μ) + 1 := by linarith
  obtain ⟨V, hV, hVφ⟩ := exists_nhds_one_forall_norm_mul_sub_lt hκc hκs (div_pos hη hI1)
  have hxV : (fun y ↦ x⁻¹ * y) ⁻¹' V ∈ 𝓝 x :=
    (continuous_mul_left x⁻¹).continuousAt.preimage_mem_nhds (by simpa using hV)
  filter_upwards [hxV] with x' hx'
  rw [dist_eq_norm]
  unfold lcaConvolution
  rw [← integral_sub (integrable_conv_integrand μ hf hκc hM x')
    (integrable_conv_integrand μ hf hκc hM x)]
  calc ‖∫ y, (f y * κ (y⁻¹ * x') - f y * κ (y⁻¹ * x)) ∂μ‖
      ≤ ∫ y, ‖f y‖ * (η / ((∫ y, ‖f y‖ ∂μ) + 1)) ∂μ := by
        refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (.of_forall fun y ↦ ?_)
        rw [← mul_sub, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have e : y⁻¹ * x' = y⁻¹ * x * (x⁻¹ * x') := by group
        rw [e]
        exact (hVφ _ _ hx').le
    _ = (∫ y, ‖f y‖ ∂μ) * (η / ((∫ y, ‖f y‖ ∂μ) + 1)) := integral_mul_const _ _
    _ < η := by
        rw [mul_div_assoc', div_lt_iff₀ hI1]
        nlinarith

/-- Averaging form of the convolution with a normalised bump: if `f` is within `ε` of `c`
on the set where `y ↦ k (y⁻¹ x)` lives, then `(f * k)(x)` is within `ε` of `c`. -/
theorem norm_conv_bump_sub_le {f : G → ℂ} (hf : Integrable f μ) {k : G → ℝ}
    (hkc : Continuous k) (hks : HasCompactSupport k) (hk0 : ∀ y, 0 ≤ k y)
    (hk1 : ∫ y, k y ∂μ = 1) {x : G} {c : ℂ} {ε : ℝ}
    (h : ∀ y, k (y⁻¹ * x) ≠ 0 → ‖f y - c‖ ≤ ε) :
    ‖lcaConvolution μ f (fun y ↦ (k y : ℂ)) x - c‖ ≤ ε := by
  have hki : Integrable k μ := hkc.integrable_of_hasCompactSupport hks
  have hκc : Continuous (fun y ↦ (k y : ℂ)) := Complex.continuous_ofReal.comp hkc
  have hκs : HasCompactSupport (fun y ↦ (k y : ℂ)) := hks.comp_left Complex.ofReal_zero
  obtain ⟨M, hM⟩ := hκc.bounded_above_of_compact_support hκs
  have e : ∀ y, y⁻¹ * x = x / y := fun y ↦ by rw [div_eq_mul_inv, mul_comm]
  have hh : Integrable (fun y ↦ k (y⁻¹ * x)) μ := by
    simp only [e]
    exact hki.comp_div_left x
  have hh1 : ∫ y, k (y⁻¹ * x) ∂μ = 1 := by
    simp only [e]
    rw [integral_div_left_eq_self]
    exact hk1
  have hu : Integrable (fun y ↦ ((k (y⁻¹ * x) : ℝ) : ℂ) * f y) μ :=
    (integrable_conv_integrand μ hf hκc hM x).congr (.of_forall fun y ↦ mul_comm _ _)
  have h' := norm_integral_ofReal_mul_sub_le hh (fun y ↦ hk0 _) hh1 hu h
  have e2 : lcaConvolution μ f (fun y ↦ (k y : ℂ)) x =
      ∫ y, ((k (y⁻¹ * x) : ℝ) : ℂ) * f y ∂μ :=
    integral_congr_ae (.of_forall fun y ↦ mul_comm _ _)
  rw [e2]
  exact h'

/-- Fourier inversion for the convolution of `f` with a continuous function of compact
support. -/
theorem conv_inversion {ν : Measure (PontryaginDual G)} (hν : LCAGroup.IsPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (hf' : Integrable (lcaFourier μ f) ν)
    {κ : G → ℂ} (hκc : Continuous κ) (hκs : HasCompactSupport κ) (x : G) :
    lcaConvolution μ f κ x =
      ∫ χ, lcaFourier μ f χ * (lcaFourier μ κ χ * (χ x : ℂ)) ∂ν := by
  obtain ⟨M, hM⟩ := hκc.bounded_above_of_compact_support hκs
  have hκi : Integrable κ μ := hκc.integrable_of_hasCompactSupport hκs
  obtain ⟨-, hFi, -, hFf⟩ := LCAGroup.fourier_convolution G μ f κ hf hκi
  have hF2 : MemLp (lcaConvolution μ f κ) 2 μ :=
    memLp_two_of_integrable_of_bound hFi (norm_lcaConvolution_le μ hf hM)
  have hFm : AEStronglyMeasurable (lcaFourier μ (lcaConvolution μ f κ)) ν :=
    (hν.2.2 _ hFi hF2).1.aestronglyMeasurable
  have hF' : Integrable (lcaFourier μ (lcaConvolution μ f κ)) ν := by
    refine (hf'.norm.mul_const (∫ y, ‖κ y‖ ∂μ)).mono' hFm (.of_forall fun χ ↦ ?_)
    rw [hFf χ, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_lcaFourier_le_integral_norm μ κ χ) (norm_nonneg _)
  refine (inversion_of_continuousAt μ hν hFi hF2 hF'
    (continuous_lcaConvolution μ hf hκc hκs).continuousAt).trans ?_
  refine integral_congr_ae (.of_forall fun χ ↦ ?_)
  change lcaFourier μ (lcaConvolution μ f κ) χ * (χ x : ℂ) = _
  rw [hFf χ, mul_assoc]

end Conv

section Approximation

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Inserting the Fourier transform of a normalised bump concentrated near `1` changes the
inversion integral by little, uniformly in the point. -/
theorem exists_nhds_one_inversion_approx {ν : Measure (PontryaginDual G)}
    (hν : LCAGroup.IsPlancherelMeasure μ ν) {f : G → ℂ}
    (hf' : Integrable (lcaFourier μ f) ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ k : G → ℝ, Continuous k → HasCompactSupport k → (∀ y, 0 ≤ k y) →
      ∫ y, k y ∂μ = 1 → Function.support k ⊆ V → ∀ x : G,
        ‖(∫ χ, lcaFourier μ f χ * (lcaFourier μ (fun y ↦ (k y : ℂ)) χ * (χ x : ℂ)) ∂ν) -
          ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν‖ ≤ ε * ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 2) := by
  have := hν.1
  have := hν.2.1
  obtain ⟨C, -, hC, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hf' MeasurableSet.univ hε
  rw [← compl_eq_univ_sdiff] at hTail
  obtain ⟨V, hV, hCV⟩ := exists_nhds_one_forall_norm_char_sub_one_lt hC hε
  refine ⟨V, hV, fun k hkc hks hk0 hk1 hksupp x ↦ ?_⟩
  have hki : Integrable k μ := hkc.integrable_of_hasCompactSupport hks
  have hκc : Continuous (fun y ↦ (k y : ℂ)) := Complex.continuous_ofReal.comp hkc
  have hκs : HasCompactSupport (fun y ↦ (k y : ℂ)) := hks.comp_left Complex.ofReal_zero
  have hκi : Integrable (fun y ↦ (k y : ℂ)) μ := hκc.integrable_of_hasCompactSupport hκs
  have hκ2 : MemLp (fun y ↦ (k y : ℂ)) 2 μ := hκc.memLp_of_hasCompactSupport hκs
  have hκn : ∫ y, ‖(k y : ℂ)‖ ∂μ = 1 := by
    rw [← hk1]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk0 y)]
  have hκm : AEStronglyMeasurable (lcaFourier μ (fun y ↦ (k y : ℂ))) ν :=
    (hν.2.2 _ hκi hκ2).1.aestronglyMeasurable
  have hκ1 : ∀ χ : PontryaginDual G, ‖lcaFourier μ (fun y ↦ (k y : ℂ)) χ‖ ≤ 1 := fun χ ↦
    (norm_lcaFourier_le_integral_norm μ _ χ).trans_eq hκn
  have ha : Integrable (fun χ : PontryaginDual G ↦
      lcaFourier μ f χ * (lcaFourier μ (fun y ↦ (k y : ℂ)) χ * (χ x : ℂ))) ν :=
    hf'.mul_bdd (c := 1) (hκm.mul (continuous_char_apply x).aestronglyMeasurable)
      (.of_forall fun χ ↦ by
        rw [norm_mul, Circle.norm_coe, mul_one]
        exact hκ1 χ)
  have hb : Integrable (fun χ : PontryaginDual G ↦ lcaFourier μ f χ * (χ x : ℂ)) ν :=
    hf'.mul_bdd (c := 1) (continuous_char_apply x).aestronglyMeasurable
      (.of_forall fun χ ↦ by rw [Circle.norm_coe])
  have hsub : ∀ χ : PontryaginDual G,
      ‖lcaFourier μ (fun y ↦ (k y : ℂ)) χ * (χ x : ℂ) - (χ x : ℂ)‖ =
        ‖lcaFourier μ (fun y ↦ (k y : ℂ)) χ - 1‖ := by
    intro χ
    rw [← sub_one_mul, norm_mul, Circle.norm_coe, mul_one]
  have h2 : ∀ χ : PontryaginDual G,
      ‖lcaFourier μ (fun y ↦ (k y : ℂ)) χ * (χ x : ℂ) - (χ x : ℂ)‖ ≤ 2 := by
    intro χ
    rw [hsub]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    linarith [hκ1 χ]
  have h3 : ∀ χ ∈ C,
      ‖lcaFourier μ (fun y ↦ (k y : ℂ)) χ * (χ x : ℂ) - (χ x : ℂ)‖ ≤ ε := by
    intro χ hχ
    rw [hsub]
    refine norm_integral_ofReal_mul_sub_le hki hk0 hk1 (integrable_fourierIntegrand μ hκi χ)
      fun y hy ↦ ?_
    have e : star (χ y : ℂ) - 1 = star ((χ y : ℂ) - 1) := by rw [star_sub, star_one]
    rw [e, norm_star]
    exact (hCV χ hχ y (hksupp hy)).le
  have h4 := norm_integral_mul_sub_integral_mul_le hf' hC.measurableSet ha hb hε.le h2 h3
  linarith

/-- Convolution with a normalised bump concentrated near `1` approximates an integrable
function in `L¹`. -/
theorem exists_nhds_one_integral_norm_conv_sub_le {f : G → ℂ} (hf : Integrable f μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ k : G → ℝ, Continuous k → HasCompactSupport k → (∀ y, 0 ≤ k y) →
      ∫ y, k y ∂μ = 1 → Function.support k ⊆ V →
        ∫ x, ‖lcaConvolution μ f (fun y ↦ (k y : ℂ)) x - f x‖ ∂μ ≤ ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨φ, hφle, hφc, hφs⟩ := exists_compactTest_eLpNorm_sub_le hf
    (ε := ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.mpr hε3).ne'
  have hφi : Integrable φ μ := hφc.integrable_of_hasCompactSupport hφs
  have hfφ : ∫ x, ‖f x - φ x‖ ∂μ ≤ ε / 3 := by
    have h := integral_norm_eq_lintegral_enorm (hf.sub hφi).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm] at hφle
    simp only [Pi.sub_apply] at h hφle
    rw [h]
    exact ENNReal.toReal_le_of_le_ofReal hε3.le hφle
  obtain ⟨W, hW, hW1⟩ := exists_compact_mem_nhds (1 : G)
  have hQ : IsCompact (tsupport φ * W) := hφs.isCompact.mul hW
  have hm : 0 ≤ (μ (tsupport φ * W)).toReal := ENNReal.toReal_nonneg
  have hm1 : 0 < 3 * ((μ (tsupport φ * W)).toReal + 1) := by positivity
  obtain ⟨V', hV', hVφ⟩ := exists_nhds_one_forall_norm_mul_sub_lt hφc hφs (div_pos hε hm1)
  refine ⟨V' ∩ W, inter_mem hV' hW1, fun k hkc hks hk0 hk1 hksupp ↦ ?_⟩
  have hκc : Continuous (fun y ↦ (k y : ℂ)) := Complex.continuous_ofReal.comp hkc
  have hκs : HasCompactSupport (fun y ↦ (k y : ℂ)) := hks.comp_left Complex.ofReal_zero
  have hκi : Integrable (fun y ↦ (k y : ℂ)) μ := hκc.integrable_of_hasCompactSupport hκs
  have hκn : ∫ y, ‖(k y : ℂ)‖ ∂μ = 1 := by
    rw [← hk1]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk0 y)]
  obtain ⟨M, hM⟩ := hκc.bounded_above_of_compact_support hκs
  obtain ⟨-, hci, hcn, -⟩ := LCAGroup.fourier_convolution G μ (f - φ) _ (hf.sub hφi) hκi
  obtain ⟨-, hcf, -, -⟩ := LCAGroup.fourier_convolution G μ f _ hf hκi
  obtain ⟨-, hcφ, -, -⟩ := LCAGroup.fourier_convolution G μ φ _ hφi hκi
  have hlin : ∀ x, lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x =
      lcaConvolution μ f (fun y ↦ (k y : ℂ)) x - lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x := by
    intro x
    unfold lcaConvolution
    rw [← integral_sub (integrable_conv_integrand μ hf hκc hM x)
      (integrable_conv_integrand μ hφi hκc hM x)]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [Pi.sub_apply, sub_mul]
  have hsup : ∀ x, ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖ ≤
      (tsupport φ * W).indicator
        (fun _ ↦ ε / (3 * ((μ (tsupport φ * W)).toReal + 1))) x := by
    intro x
    by_cases hxQ : x ∈ tsupport φ * W
    · rw [indicator_of_mem hxQ]
      refine norm_conv_bump_sub_le μ hφi hkc hks hk0 hk1 fun y hy ↦ ?_
      have h := hVφ y _ (hksupp hy).1
      rw [mul_inv_cancel_left] at h
      rw [norm_sub_rev]
      exact h.le
    · rw [indicator_of_notMem hxQ]
      have h1 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
        hxQ ⟨x, h, 1, mem_of_mem_nhds hW1, mul_one x⟩
      have h2 : lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x = 0 := by
        unfold lcaConvolution
        refine integral_eq_zero_of_ae (.of_forall fun y ↦ ?_)
        by_cases hy : y ∈ tsupport φ
        · have hk : k (y⁻¹ * x) = 0 := by
            by_contra hne
            exact hxQ ⟨y, hy, y⁻¹ * x, (hksupp hne).2, mul_inv_cancel_left y x⟩
          simp [hk]
        · simp [image_eq_zero_of_notMem_tsupport hy]
      rw [h1, h2, sub_zero, norm_zero]
  have hindi : Integrable ((tsupport φ * W).indicator
      (fun _ ↦ ε / (3 * ((μ (tsupport φ * W)).toReal + 1)))) μ :=
    (integrable_indicator_iff hQ.measurableSet).mpr
      (integrableOn_const hQ.measure_lt_top.ne)
  have hφκ : ∫ x, ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖ ∂μ ≤ ε / 3 := by
    calc ∫ x, ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖ ∂μ
        ≤ ∫ x, (tsupport φ * W).indicator
            (fun _ ↦ ε / (3 * ((μ (tsupport φ * W)).toReal + 1))) x ∂μ :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) hindi (.of_forall hsup)
      _ = (μ (tsupport φ * W)).toReal * (ε / (3 * ((μ (tsupport φ * W)).toReal + 1))) := by
          rw [integral_indicator_const _ hQ.measurableSet, smul_eq_mul]
          rfl
      _ ≤ ε / 3 := by
          rw [mul_div_assoc', div_le_div_iff₀ hm1 (by norm_num)]
          nlinarith
  have hfφκ : ∫ x, ‖lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x‖ ∂μ ≤ ε / 3 := by
    rw [hκn, mul_one] at hcn
    exact hcn.trans hfφ
  have hA : Integrable (fun x ↦ ‖lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x‖) μ := hci.norm
  have hB : Integrable (fun x ↦ ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖) μ :=
    (hcφ.sub hφi).norm
  have hD : Integrable (fun x ↦ ‖f x - φ x‖) μ := (hf.sub hφi).norm
  have hAB : Integrable (fun x ↦ ‖lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x‖ +
      ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖) μ := hA.add hB
  have hABD : Integrable (fun x ↦ ‖lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x‖ +
      ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖ + ‖f x - φ x‖) μ := hAB.add hD
  calc ∫ x, ‖lcaConvolution μ f (fun y ↦ (k y : ℂ)) x - f x‖ ∂μ
      ≤ ∫ x, (‖lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x‖ +
          ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖ + ‖f x - φ x‖) ∂μ := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
          hABD (.of_forall fun x ↦ ?_)
        have e : lcaConvolution μ f (fun y ↦ (k y : ℂ)) x - f x =
            lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x +
              (lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x) - (f x - φ x) := by
          rw [hlin x]
          ring
        change ‖lcaConvolution μ f (fun y ↦ (k y : ℂ)) x - f x‖ ≤ _
        rw [e]
        exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (∫ x, ‖lcaConvolution μ (f - φ) (fun y ↦ (k y : ℂ)) x‖ ∂μ) +
          (∫ x, ‖lcaConvolution μ φ (fun y ↦ (k y : ℂ)) x - φ x‖ ∂μ) +
          ∫ x, ‖f x - φ x‖ ∂μ := by
        rw [integral_add hAB hD, integral_add hA hB]
    _ ≤ ε := by linarith

end Approximation

end Sol_LCAGroup_fourier_inversion

open LCAGroup Sol_LCAGroup_fourier_inversion Filter Set RiemannMasullo in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (ν : Measure (PontryaginDual G)) (hν : IsPlancherelMeasure μ ν)
    (f : G → ℂ) (hf : Integrable f μ)
    (hf' : Integrable (RiemannMasullo.lcaFourier μ f) ν) :
    (∀ᵐ x ∂μ, f x = ∫ χ : PontryaginDual G, RiemannMasullo.lcaFourier μ f χ * (χ x : ℂ) ∂ν) ∧
    (Continuous f →
      ∀ x : G, f x = ∫ χ : PontryaginDual G, RiemannMasullo.lcaFourier μ f χ * (χ x : ℂ) ∂ν) := by
  have hI : 0 ≤ ∫ χ, ‖lcaFourier μ f χ‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hI2 : 0 < (∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 2 := by linarith
  constructor
  · -- almost everywhere
    have hex : ∀ n : ℕ, ∃ F : G → ℂ, Integrable F μ ∧
        (∀ x, ‖F x - ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν‖ ≤
          1 / ((n : ℝ) + 1) * ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 2)) ∧
        ∫ x, ‖F x - f x‖ ∂μ ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      obtain ⟨V₁, hV₁, hA⟩ := exists_nhds_one_inversion_approx μ hν hf' hn
      obtain ⟨V₂, hV₂, hB⟩ := exists_nhds_one_integral_norm_conv_sub_le μ hf hn
      obtain ⟨k, hkc, hks, hk0, hk1, hksupp⟩ := exists_bump μ (inter_mem hV₁ hV₂)
      have hκc : Continuous (fun y ↦ (k y : ℂ)) := Complex.continuous_ofReal.comp hkc
      have hκs : HasCompactSupport (fun y ↦ (k y : ℂ)) := hks.comp_left Complex.ofReal_zero
      have hκi : Integrable (fun y ↦ (k y : ℂ)) μ := hκc.integrable_of_hasCompactSupport hκs
      refine ⟨lcaConvolution μ f (fun y ↦ (k y : ℂ)),
        (LCAGroup.fourier_convolution G μ f _ hf hκi).2.1, fun x ↦ ?_,
        hB k hkc hks hk0 hk1 (hksupp.trans inter_subset_right)⟩
      rw [conv_inversion μ hν hf hf' hκc hκs x]
      exact hA k hkc hks hk0 hk1 (hksupp.trans inter_subset_left) x
    choose F hFi hFg hFf using hex
    have hlim : ∀ x, Tendsto (fun n ↦ F n x) atTop
        (𝓝 (∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν)) := by
      intro x
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) *
          ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 2)) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
          ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 2)
      exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ hFg n x) h0
    have hle : ∫⁻ x, ‖(∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν) - f x‖ₑ ∂μ ≤
        liminf (fun n ↦ ∫⁻ x, ‖F n x - f x‖ₑ ∂μ) atTop := by
      calc ∫⁻ x, ‖(∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν) - f x‖ₑ ∂μ
          = ∫⁻ x, liminf (fun n ↦ ‖F n x - f x‖ₑ) atTop ∂μ :=
            lintegral_congr fun x ↦ (((hlim x).sub_const (f x)).enorm.liminf_eq).symm
        _ ≤ liminf (fun n ↦ ∫⁻ x, ‖F n x - f x‖ₑ ∂μ) atTop :=
            lintegral_liminf_le' fun n ↦ ((hFi n).sub hf).aestronglyMeasurable.enorm
    have h0 : Tendsto (fun n ↦ ∫⁻ x, ‖F n x - f x‖ₑ ∂μ) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
        (fun _ ↦ zero_le) fun n ↦ ?_
      have h2 := ofReal_integral_norm_eq_lintegral_enorm ((hFi n).sub hf)
      simp only [Pi.sub_apply] at h2
      rw [← h2]
      exact ENNReal.ofReal_le_ofReal (hFf n)
    have hzero : ∫⁻ x, ‖(∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν) - f x‖ₑ ∂μ = 0 :=
      le_antisymm (hle.trans_eq h0.liminf_eq) zero_le
    have hgm : AEStronglyMeasurable (fun x ↦ ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν) μ :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ (hFi n).aestronglyMeasurable)
        (.of_forall hlim)
    have hae := (lintegral_eq_zero_iff' (hgm.sub hf.aestronglyMeasurable).enorm).mp hzero
    filter_upwards [hae] with x hx
    exact (sub_eq_zero.mp (enorm_eq_zero.mp hx)).symm
  · -- everywhere, for continuous `f`
    intro hfc x
    have key : ∀ ε > 0, ‖f x - ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν‖ ≤
        ε * ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 3) := by
      intro ε hε
      obtain ⟨V₁, hV₁, hA⟩ := exists_nhds_one_inversion_approx μ hν hf' hε
      have hU : {y | ‖f y - f x‖ < ε} ∈ 𝓝 x :=
        (Metric.tendsto_nhds.mp hfc.continuousAt ε hε).mono fun y hy ↦ by
          rwa [dist_eq_norm] at hy
      have hV₂ : (fun v ↦ x * v⁻¹) ⁻¹' {y | ‖f y - f x‖ < ε} ∈ 𝓝 (1 : G) :=
        (continuous_const.mul continuous_inv).continuousAt.preimage_mem_nhds (by simpa using hU)
      obtain ⟨k, hkc, hks, hk0, hk1, hksupp⟩ := exists_bump μ (inter_mem hV₁ hV₂)
      have hκc : Continuous (fun y ↦ (k y : ℂ)) := Complex.continuous_ofReal.comp hkc
      have hκs : HasCompactSupport (fun y ↦ (k y : ℂ)) := hks.comp_left Complex.ofReal_zero
      have h1 : ‖lcaConvolution μ f (fun y ↦ (k y : ℂ)) x - f x‖ ≤ ε := by
        refine norm_conv_bump_sub_le μ hf hkc hks hk0 hk1 fun y hy ↦ ?_
        have h : ‖f (x * (y⁻¹ * x)⁻¹) - f x‖ < ε := (hksupp hy).2
        have e : x * (y⁻¹ * x)⁻¹ = y := by group
        rw [e] at h
        exact h.le
      have h2 := hA k hkc hks hk0 hk1 (hksupp.trans inter_subset_left) x
      rw [← conv_inversion μ hν hf hf' hκc hκs x] at h2
      calc ‖f x - ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν‖
          ≤ ‖f x - lcaConvolution μ f (fun y ↦ (k y : ℂ)) x‖ +
            ‖lcaConvolution μ f (fun y ↦ (k y : ℂ)) x -
              ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + ε * ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 2) :=
            add_le_add (by rw [norm_sub_rev]; exact h1) h2
        _ = ε * ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 3) := by ring
    have hI3 : 0 < (∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 3 := by linarith
    have h0 : ‖f x - ∫ χ, lcaFourier μ f χ * (χ x : ℂ) ∂ν‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      have := key (ε / ((∫ χ, ‖lcaFourier μ f χ‖ ∂ν) + 3)) (div_pos hε hI3)
      rwa [div_mul_cancel₀ _ hI3.ne', ← zero_add ε] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
