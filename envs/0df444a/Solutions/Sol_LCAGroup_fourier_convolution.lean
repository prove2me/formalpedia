-- Prove2me | solution 1 for LCAGroup.fourier_convolution
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:17:56.397751+00:00
-- url     : https://prove2.me/submissions/989a1ffe-8471-4294-9074-a52ed3753163

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace Sol_LCAGroup_fourier_convolution

open Filter Set
open scoped ENNReal NNReal Pointwise

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

/-- An integrable function is an almost-everywhere limit of continuous functions of compact
support. -/
theorem exists_tendsto_ae_compactSupport {u : X → E} (hu : Integrable u μ) :
    ∃ U : ℕ → X → E, (∀ n, HasCompactSupport (U n)) ∧ (∀ n, Continuous (U n)) ∧
      ∀ᵐ z ∂μ, Tendsto (fun n ↦ U n z) atTop (𝓝 (u z)) := by
  obtain ⟨ε, -, hε, hlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1)
  choose U hU hP using fun n ↦ exists_compactTest_eLpNorm_sub_le hu (hε n).1.ne'
  have ht : Tendsto (fun n ↦ eLpNorm (U n - u) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
      (fun n ↦ (eLpNorm_sub_comm _ _ _ _).le.trans (hU n))
  obtain ⟨s, -, hs⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n ↦ ((hP n).1.integrable_of_hasCompactSupport (hP n).2).1)
      hu.aestronglyMeasurable ht).exists_seq_tendsto_ae
  exact ⟨U ∘ s, fun n ↦ (hP (s n)).2, fun n ↦ (hP (s n)).1, hs⟩

end Approx

section Conv

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- A product-measurable representative for the convolution kernel, carried on a
rectangle with σ-finite sides. -/
theorem lcaConvolution_kernel {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∃ (S : Set G) (k : G × G → ℂ), SigmaFinite (μ.restrict S) ∧ StronglyMeasurable k ∧
      Function.support k ⊆ S ×ˢ S ∧
      (∀ x, ∀ᵐ y ∂μ, k (x, y) = f y * g (y⁻¹ * x)) ∧
      (∀ᵐ y ∂μ, ∀ᵐ x ∂μ, k (x, y) = f y * g (y⁻¹ * x)) := by
  obtain ⟨F, hF, cF, tF⟩ := exists_tendsto_ae_compactSupport hf
  obtain ⟨H, hH, cH, tH⟩ := exists_tendsto_ae_compactSupport hg
  let K : ℕ → Set G := fun n => tsupport (F n) ∪ tsupport (F n) * tsupport (H n)
  have hK (n) : IsCompact (K n) := (hF n).isCompact.union ((hF n).isCompact.mul (hH n).isCompact)
  let S : Set G := ⋃ n, K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  have hσ : SigmaFinite (μ.restrict S) := by
    refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hS.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
    · rw [← iUnion_union]
      exact union_compl_self S
  let P : ℕ → G × G → ℂ := fun n p => F n p.2 * H n (p.2⁻¹ * p.1)
  have hP (n) : Function.support (P n) ⊆ K n ×ˢ K n := by
    rintro ⟨x, y⟩ hp
    have hp' : F n y * H n (y⁻¹ * x) ≠ 0 := hp
    have hfy := subset_tsupport (F n) ((mul_ne_zero_iff.mp hp').1)
    have hgy := subset_tsupport (H n) ((mul_ne_zero_iff.mp hp').2)
    exact ⟨Or.inr ⟨y, hfy, y⁻¹ * x, hgy, mul_inv_cancel_left y x⟩, Or.inl hfy⟩
  have mP (n) : StronglyMeasurable (P n) := by
    have hcompact : HasCompactSupport (P n) := HasCompactSupport.intro ((hK n).prod (hK n))
      (fun p hp ↦ Function.notMem_support.mp (fun h ↦ hp (hP n h)))
    exact hcompact.stronglyMeasurable_of_prod ((cF n).comp continuous_snd |>.mul
      ((cH n).comp (continuous_snd.inv.mul continuous_fst)))
  let k : G × G → ℂ := fun p => limUnder atTop (fun n ↦ P n p)
  refine ⟨S, k, hσ, StronglyMeasurable.limUnder mP, ?_, ?_, ?_⟩
  · intro p hp
    by_contra h
    have hz (n) : P n p = 0 := Function.notMem_support.mp fun hn ↦
      h ⟨mem_iUnion.mpr ⟨n, (hP n hn).1⟩, mem_iUnion.mpr ⟨n, (hP n hn).2⟩⟩
    have ht : Tendsto (fun n ↦ P n p) atTop (𝓝 0) := by
      simp only [hz]
      exact tendsto_const_nhds
    exact hp ht.limUnder_eq
  · intro x
    have hmp := (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
    filter_upwards [tF, hmp.quasiMeasurePreserving.tendsto_ae.eventually tH] with y hy hy'
    exact (hy.mul hy').limUnder_eq
  · filter_upwards [tF] with y hy
    have hmp := measurePreserving_mul_left μ y⁻¹
    filter_upwards [hmp.quasiMeasurePreserving.tendsto_ae.eventually tH] with x hx
    exact (hy.mul hx).limUnder_eq

/-- The fibre integrals of two `L¹` functions exist almost everywhere and their convolution is
`L¹` with the product norm bound. -/
theorem lcaConvolution_integrable {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ x ∂μ, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      Integrable (RiemannMasullo.lcaConvolution μ f g) μ ∧
      eLpNorm (RiemannMasullo.lcaConvolution μ f g) 1 μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := by
  obtain ⟨S, k, hσ, hk, hs, hrow, hcol⟩ := lcaConvolution_kernel μ hf hg
  have hzero (p : G × G) (hp : p ∉ S ×ˢ S) : k p = 0 :=
    Function.notMem_support.mp fun h ↦ hp (hs h)
  let N : G → ℝ≥0∞ := fun x => ∫⁻ y in S, ‖k (x, y)‖ₑ ∂μ
  have hN : Measurable N := hk.enorm.lintegral_prod_right'
  have hfull (x) : N x = ∫⁻ y, ‖k (x, y)‖ₑ ∂μ := by
    apply setLIntegral_eq_of_support_subset
    intro y hy
    by_contra h
    exact hy (by simp [hzero (x, y) (fun hp ↦ h hp.2)])
  have hconv (x) : (∫ y in S, k (x, y) ∂μ) = RiemannMasullo.lcaConvolution μ f g x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy ↦ hzero (x, y) (fun hp ↦ hy hp.2))).trans (integral_congr_ae (hrow x))
  have hm : StronglyMeasurable (RiemannMasullo.lcaConvolution μ f g) :=
    (funext hconv) ▸ hk.integral_prod_right'
  -- Tonelli applies on the supporting rectangle, even when Haar measure on G is not σ-finite.
  have hbound : ∫⁻ x, N x ∂μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := calc
    ∫⁻ x, N x ∂μ = ∫⁻ x in S, N x ∂μ := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra h
      exact hx (by simp [N, fun y ↦ hzero (x, y) (fun hp ↦ h hp.1)])
    _ = ∫⁻ y in S, ∫⁻ x in S, ‖k (x, y)‖ₑ ∂μ ∂μ := lintegral_lintegral_swap hk.enorm.aemeasurable
    _ ≤ ∫⁻ y, ∫⁻ x, ‖k (x, y)‖ₑ ∂μ ∂μ :=
      lintegral_mono' Measure.restrict_le_self fun y ↦ setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, ‖f y‖ₑ * eLpNorm g 1 μ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hcol] with y hy
      calc
        ∫⁻ x, ‖k (x, y)‖ₑ ∂μ = ∫⁻ x, ‖f y‖ₑ * ‖g (y⁻¹ * x)‖ₑ ∂μ := lintegral_congr_ae <|
          hy.mono fun x hx ↦ by
            change ‖k (x, y)‖ₑ = ‖f y‖ₑ * ‖g (y⁻¹ * x)‖ₑ
            rw [hx, enorm_mul]
        _ = ‖f y‖ₑ * eLpNorm g 1 μ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_mul_left_eq_self (fun z ↦ ‖g z‖ₑ),
            eLpNorm_one_eq_lintegral_enorm]
    _ = eLpNorm f 1 μ * eLpNorm g 1 μ := by
      rw [lintegral_mul_const'' _ hf.aestronglyMeasurable.enorm,
        eLpNorm_one_eq_lintegral_enorm (f := f)]
  have hfin := hbound.trans_lt (ENNReal.mul_lt_top (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top
    (memLp_one_iff_integrable.2 hg).eLpNorm_lt_top)
  have hle : ∫⁻ x, ‖RiemannMasullo.lcaConvolution μ f g x‖ₑ ∂μ ≤ ∫⁻ x, N x ∂μ :=
    lintegral_mono fun x ↦ hconv x ▸ enorm_integral_le_lintegral_enorm _
  refine ⟨?_, ⟨hm.aestronglyMeasurable, hle.trans_lt hfin⟩, ?_⟩
  · filter_upwards [ae_lt_top hN hfin.ne] with x hx
    have hInt : Integrable (fun y ↦ k (x, y)) μ :=
      ⟨(hk.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        (hfull x).symm.trans_lt hx⟩
    exact hInt.congr (hrow x)
  · rw [eLpNorm_one_eq_lintegral_enorm]
    exact hle.trans hbound

/-- The integral of an `L¹` convolution is the product of the integrals of its factors. -/
theorem integral_lcaConvolution {f g : G → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    (∫ x, RiemannMasullo.lcaConvolution μ f g x ∂μ) = (∫ y, f y ∂μ) * (∫ z, g z ∂μ) := by
  obtain ⟨S, k, hσ, hk, hs, hrow, hcol⟩ := lcaConvolution_kernel μ hf hg
  have hzeroRow (x : G) (hx : x ∉ S) (y : G) : k (x, y) = 0 :=
    Function.notMem_support.mp fun h ↦ hx (hs h).1
  have hzeroCol (y : G) (hy : y ∉ S) (x : G) : k (x, y) = 0 :=
    Function.notMem_support.mp fun h ↦ hy (hs h).2
  -- Fubini applies to the kernel on its σ-finite supporting rectangle.
  have hInt : Integrable k ((μ.restrict S).prod (μ.restrict S)) := by
    refine (integrable_prod_iff' hk.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · apply ae_mono Measure.restrict_le_self
      filter_upwards [hcol] with y hy
      exact (((hg.comp_mul_left y⁻¹).const_mul (f y)).congr
        (hy.mono fun _ hx ↦ hx.symm)).restrict
    · refine (hf.norm.mul_const (∫ z, ‖g z‖ ∂μ)).restrict.congr ?_
      apply ae_mono Measure.restrict_le_self
      filter_upwards [hcol] with y hy
      symm
      calc
        ∫ x in S, ‖k (x, y)‖ ∂μ = ∫ x, ‖k (x, y)‖ ∂μ :=
          setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by simp [hzeroRow x hx])
        _ = ∫ x, ‖f y * g (y⁻¹ * x)‖ ∂μ :=
          integral_congr_ae (hy.mono fun _ hx ↦ congrArg norm hx)
        _ = ‖f y‖ * ∫ z, ‖g z‖ ∂μ := by
          simp only [norm_mul, integral_const_mul, integral_mul_left_eq_self (fun z ↦ ‖g z‖)]
  have hrowIntegral (x : G) :
      (∫ y in S, k (x, y) ∂μ) = RiemannMasullo.lcaConvolution μ f g x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroCol · · x)).trans
      (integral_congr_ae (hrow x))
  calc
    (∫ x, RiemannMasullo.lcaConvolution μ f g x ∂μ)
        = ∫ x in S, ∫ y in S, k (x, y) ∂μ ∂μ := by
      simp_rw [← hrowIntegral]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by simp [hzeroRow x hx])).symm
    _ = ∫ y in S, ∫ x in S, k (x, y) ∂μ ∂μ := integral_integral_swap hInt
    _ = ∫ y, ∫ x, k (x, y) ∂μ ∂μ := by
      have hcolIntegral (y : G) : (∫ x in S, k (x, y) ∂μ) = ∫ x, k (x, y) ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroRow · · y)
      simp_rw [hcolIntegral]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by simp [hzeroCol y hy])
    _ = (∫ y, f y ∂μ) * (∫ z, g z ∂μ) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [hcol] with y hy
      rw [integral_congr_ae hy, integral_const_mul, integral_mul_left_eq_self g]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- Multiplication by a conjugated character preserves integrability. -/
theorem integrable_fourierIntegrand {f : G → ℂ} (hf : Integrable f μ)
    (χ : PontryaginDual G) : Integrable (fun x ↦ f x * star (χ x : ℂ)) μ := by
  exact hf.mul_bdd (c := 1) ((continuous_subtype_val.comp χ.continuous).star.aestronglyMeasurable)
    (.of_forall fun x ↦ by
      change ‖star (χ x : ℂ)‖ ≤ 1
      rw [norm_star, Circle.norm_coe])

end Conv

end Sol_LCAGroup_fourier_convolution

open Sol_LCAGroup_fourier_convolution in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (f g : G → ℂ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ x ∂μ, Integrable (fun y : G => f y * g (y⁻¹ * x)) μ) ∧
    Integrable (RiemannMasullo.lcaConvolution μ f g) μ ∧
    (∫ x, ‖RiemannMasullo.lcaConvolution μ f g x‖ ∂μ ≤ (∫ x, ‖f x‖ ∂μ) * ∫ x, ‖g x‖ ∂μ) ∧
    ∀ χ : PontryaginDual G,
      RiemannMasullo.lcaFourier μ (RiemannMasullo.lcaConvolution μ f g) χ =
        RiemannMasullo.lcaFourier μ f χ * RiemannMasullo.lcaFourier μ g χ := by
  obtain ⟨h1, h2, h3⟩ := lcaConvolution_integrable μ hf hg
  refine ⟨h1, h2, ?_, ?_⟩
  · have e1 : ∫ x, ‖RiemannMasullo.lcaConvolution μ f g x‖ ∂μ
        = (eLpNorm (RiemannMasullo.lcaConvolution μ f g) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact integral_norm_eq_lintegral_enorm h2.aestronglyMeasurable
    have e2 : ∫ x, ‖f x‖ ∂μ = (eLpNorm f 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable
    have e3 : ∫ x, ‖g x‖ ∂μ = (eLpNorm g 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable
    rw [e1, e2, e3, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (memLp_one_iff_integrable.2 hf).eLpNorm_ne_top
      (memLp_one_iff_integrable.2 hg).eLpNorm_ne_top) h3
  · intro χ
    change (∫ x, RiemannMasullo.lcaConvolution μ f g x * star (χ x : ℂ) ∂μ) =
      (∫ x, f x * star (χ x : ℂ) ∂μ) * (∫ x, g x * star (χ x : ℂ) ∂μ)
    rw [← integral_lcaConvolution μ (integrable_fourierIntegrand μ hf χ)
      (integrable_fourierIntegrand μ hg χ)]
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      simp only [RiemannMasullo.lcaConvolution, ← integral_mul_const]
      apply integral_congr_ae
      exact .of_forall fun y ↦ by
        have hχ : (χ x : ℂ) = (χ y : ℂ) * (χ (y⁻¹ * x) : ℂ) := by
          rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel_left]
        simp only [hχ, star_mul]
        ring
