-- Prove2me | solution 1 for LCAGroup.fourier_L1_to_zeroAtInfty_injective
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:25:54.450717+00:00
-- url     : https://prove2.me/submissions/4209e58d-decb-4280-9a21-942121cc3a92

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_locallyCompact

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace Sol_LCAGroup_fourier_L1_to_zeroAtInfty_injective

open Filter Set RiemannMasullo
open scoped ENNReal

section Regular

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

open scoped Pointwise in
/-- An integrable density for a regular measure vanishes if all its integrals against
a point-separating group of continuous circle-valued functions vanish. -/
theorem ae_eq_zero_of_integral_mul_circle_eq_zero
    {X D : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [Group D] {μ : Measure X} [μ.Regular] {f : X → ℂ}
    (e₀ : X → D →* Circle) (he₀ : ∀ d, Continuous (fun x ↦ e₀ x d))
    (hInj : Function.Injective e₀) (hf : Integrable f μ)
    (h : ∀ d, ∫ x, f x * (e₀ x d : ℂ) ∂μ = 0) : f =ᵐ[μ] 0 := by
  classical
  let B : Set (D → Circle) := {b | b 1 = 1 ∧ ∀ d d', b (d * d') = b d * b d'}
  have hB : IsClosed B := by
    rw [show B = {b : D → Circle | b 1 = 1} ∩
      ⋂ d, ⋂ d', {b : D → Circle | b (d * d') = b d * b d'} by ext; simp [B]]
    exact (isClosed_eq (continuous_apply 1) continuous_const).inter
      (isClosed_iInter fun d ↦ isClosed_iInter fun d' ↦
        isClosed_eq (continuous_apply (d * d')) ((continuous_apply d).mul (continuous_apply d')))
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let e (x : X) : B := ⟨e₀ x, map_one _, map_mul _⟩
  have he : Continuous e := (continuous_pi he₀).subtype_mk _
  have heInj : Function.Injective e := fun _ _ hEq ↦
    hInj (DFunLike.coe_injective (congrArg Subtype.val hEq))
  let coord : D →* C(B, ℂ) :=
    { toFun := fun χ ↦ ⟨fun b ↦ (b.1 χ : ℂ),
        continuous_subtype_val.comp ((continuous_apply χ).comp continuous_subtype_val)⟩
      map_one' := ContinuousMap.ext fun b ↦ by
        change (b.1 1 : ℂ) = 1
        rw [b.2.1, Circle.coe_one]
      map_mul' χ ψ := ContinuousMap.ext fun b ↦ by
        change (b.1 (χ * ψ) : ℂ) = (b.1 χ : ℂ) * (b.1 ψ : ℂ)
        rw [b.2.2, Circle.coe_mul] }
  have hStar (χ : D) : star (coord χ) = coord χ⁻¹ := by
    ext b
    have hInv : b.1 χ⁻¹ = (b.1 χ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← b.2.2, inv_mul_cancel, b.2.1]
    change star (b.1 χ : ℂ) = (b.1 χ⁻¹ : ℂ)
    rw [hInv, Circle.coe_inv_eq_conj, Complex.star_def]
  let A := StarAlgebra.adjoin ℂ (Set.range coord)
  have hSep : A.SeparatesPoints := by
    intro a b hab
    obtain ⟨χ, hχ⟩ : ∃ χ, a.1 χ ≠ b.1 χ := by
      by_contra! hEq
      exact hab (Subtype.ext (funext hEq))
    exact ⟨coord χ, ⟨coord χ, StarAlgebra.subset_adjoin _ _ (mem_range_self χ), rfl⟩,
      fun heq ↦ hχ (Circle.ext heq)⟩
  have hSpan : A.toSubalgebra.toSubmodule ≤ Submodule.span ℂ (Set.range coord) := by
    rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_mono
    suffices Submonoid.closure (Set.range coord ∪ star (Set.range coord)) ≤
        MonoidHom.mrange coord from this
    apply Submonoid.closure_le.mpr
    rintro z (hMem | hMem)
    · exact hMem
    · obtain ⟨χ, hχ⟩ := Set.mem_star.mp hMem
      exact ⟨χ⁻¹, (hStar χ).symm.trans (by rw [hχ, star_star])⟩
  let test (u : C(B, ℂ)) (x : X) := f x * u (e x)
  have hBound (u : C(B, ℂ)) (x : X) : ‖test u x‖ ≤ ‖u‖ * ‖f x‖ := by
    change ‖f x * u (e x)‖ ≤ _
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm u _) (norm_nonneg _)
  have hInt (u : C(B, ℂ)) : Integrable (test u) μ :=
    hf.mul_bdd (u.continuous.comp he).aestronglyMeasurable
      (.of_forall fun x ↦ ContinuousMap.norm_coe_le_norm u (e x))
  let L : C(B, ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun u ↦ ∫ x, test u x ∂μ
      map_add' := fun u v ↦ by
        simp only [test, ContinuousMap.add_apply, mul_add]
        exact integral_add (hInt u) (hInt v)
      map_smul' := fun c u ↦ by
        simp only [test, ContinuousMap.smul_apply, mul_smul_comm,
          RingHom.id_apply, integral_smul] }
    (∫ x, ‖f x‖ ∂μ) fun u ↦ by
      change ‖∫ x, test u x ∂μ‖ ≤ (∫ x, ‖f x‖ ∂μ) * ‖u‖
      rw [mul_comm, ← integral_const_mul]
      exact norm_integral_le_of_norm_le (hf.norm.const_mul ‖u‖) (.of_forall (hBound u))
  have hCoord (d : D) : L (coord d) = 0 := h d
  have hL (u : C(B, ℂ)) : L u = 0 := by
    have hDense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hSep
    have hClosed : IsClosed {v | L v = 0} := isClosed_eq L.continuous continuous_const
    refine closure_minimal (s := (A : Set C(B, ℂ))) ?_ hClosed ?_
    · intro v hv
      have hKer : Submodule.span ℂ (Set.range coord) ≤ L.toLinearMap.ker :=
        Submodule.span_le.mpr (fun _ ⟨χ, hχ⟩ ↦ hχ ▸ hCoord χ)
      exact hKer (hSpan hv)
    · have hu : u ∈ A.topologicalClosure := hDense ▸ StarSubalgebra.mem_top
      exact hu
  apply hf.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s hs _
  have hNorm : ‖∫ x in s, f x ∂μ‖ ≤ 0 := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨K₁, hK₁s, hK₁, hTail₁⟩ := exists_isCompact_integral_norm_sdiff_lt hf hs (half_pos hε)
    obtain ⟨K₀, hK₀s, hK₀, hTail₀⟩ :=
      exists_isCompact_integral_norm_sdiff_lt hf hs.compl (half_pos hε)
    have hDisj : Disjoint (e '' K₀) (e '' K₁) := Set.disjoint_left.mpr <| by
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
      exact hK₀s hx (heInj heq ▸ hK₁s hy)
    obtain ⟨u, hu₀, hu₁, hu01⟩ := exists_continuous_zero_one_of_isClosed
      (hK₀.image he).isClosed (hK₁.image he).isClosed hDisj
    let v : C(B, ℂ) := ⟨fun b ↦ (u b : ℂ), Complex.continuous_ofReal.comp u.continuous⟩
    let q (x : X) := s.indicator f x - test v x
    have hEq : (∫ x, q x ∂μ) = ∫ x in s, f x ∂μ := by
      rw [show (∫ x, q x ∂μ) = (∫ x, s.indicator f x ∂μ) - L v from
        integral_sub (hf.indicator hs) (hInt v), hL, sub_zero, integral_indicator hs]
    rw [zero_add, ← hEq]
    let tail₁ := (s \ K₁).indicator (fun x ↦ ‖f x‖)
    let tail₀ := (sᶜ \ K₀).indicator (fun x ↦ ‖f x‖)
    have ht₁ := hs.diff hK₁.isClosed.measurableSet
    have ht₀ := hs.compl.diff hK₀.isClosed.measurableSet
    have hDom (x : X) : ‖q x‖ ≤ tail₁ x + tail₀ x := by
      have hBounds := hu01 (e x)
      by_cases hx : x ∈ s
      · by_cases hk : x ∈ K₁
        · simp [q, test, v, hx, hu₁ (mem_image_of_mem e hk), tail₁, tail₀, hk]
        have hDist : ‖1 - (u (e x) : ℂ)‖ ≤ 1 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hBounds.2)]
          linarith [hBounds.1]
        have hTail : tail₁ x + tail₀ x = ‖f x‖ := by simp [tail₁, tail₀, hx, hk]
        rw [hTail]
        change ‖s.indicator f x - f x * (u (e x) : ℂ)‖ ≤ ‖f x‖
        calc
          _ = ‖f x * (1 - (u (e x) : ℂ))‖ := by rw [indicator_of_mem hx, mul_sub, mul_one]
          _ ≤ _ := by simpa only [norm_mul, mul_one] using
            mul_le_mul_of_nonneg_left hDist (norm_nonneg (f x))
      · by_cases hk : x ∈ K₀
        · simp [q, test, v, hx, hu₀ (mem_image_of_mem e hk), tail₁, tail₀, hk]
        have hNormU : ‖(u (e x) : ℂ)‖ ≤ 1 := by
          simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBounds.1] using hBounds.2
        have hTail : tail₁ x + tail₀ x = ‖f x‖ := by simp [tail₁, tail₀, hx, hk]
        rw [hTail]
        change ‖s.indicator f x - f x * (u (e x) : ℂ)‖ ≤ ‖f x‖
        rw [indicator_of_notMem hx, zero_sub, norm_neg, norm_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hNormU (norm_nonneg (f x))
    have ht₁Int : Integrable tail₁ μ := hf.norm.indicator ht₁
    have ht₀Int : Integrable tail₀ μ := hf.norm.indicator ht₀
    refine (norm_integral_le_of_norm_le (ht₁Int.add ht₀Int) (.of_forall hDom)).trans_lt ?_
    change (∫ x, tail₁ x + tail₀ x ∂μ) < ε
    rw [integral_add ht₁Int ht₀Int, show (∫ x, tail₁ x ∂μ) = _ from integral_indicator ht₁,
      show (∫ x, tail₀ x ∂μ) = _ from integral_indicator ht₀]
    linarith
  exact norm_eq_zero.mp (le_antisymm hNorm (norm_nonneg _))

end Regular

section Polar

/-- There is a radius such that characters mapping any fixed identity neighborhood into
the closed circle ball of that radius form a compact set in the compact-open topology.
Powers give equicontinuity at the identity, and Arzelà–Ascoli gives compactness. -/
theorem exists_isCompact_pontryaginDual_polar {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ r : ℝ, 0 < r ∧ ∀ U ∈ 𝓝 (1 : G),
      IsCompact {χ : PontryaginDual G | MapsTo χ U (Metric.closedBall 1 r)} := by
  classical
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  obtain ⟨r, hr, hBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hArc
  refine ⟨r, hr, fun U hU ↦ ?_⟩
  let W := Metric.closedBall (1 : Circle) r
  let S := {f : G →* Circle | MapsTo f U W}
  have hEqui : Equicontinuous (fun f : S ↦ (f.1 : G → Circle)) := by
    refine equicontinuous_of_equicontinuousAt_one Subtype.val ?_
    apply (Metric.equicontinuousAt_iff_right (α := Circle)).mpr
    intro ε hε
    let T (n : ℕ) := (fun z : Circle ↦ z ^ n) ⁻¹' W
    have hDisj : Disjoint (Metric.ball (1 : Circle) ε)ᶜ (⋂ n, T n) := by
      refine Set.disjoint_left.mpr fun z hz hzT ↦ ?_
      have hz1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (z := z)
        (fun n _ ↦ hBall (mem_iInter.mp hzT n))
      exact hz (hz1.symm ▸ Metric.mem_ball_self hε)
    obtain ⟨N, hN⟩ := (isClosed_compl_iff.mpr Metric.isOpen_ball).isCompact
      |>.elim_finite_subfamily_closed T
        (fun n ↦ Metric.isClosed_closedBall.preimage (continuous_pow n)) hDisj.inter_eq
    have hNear : ∀ᶠ x : G in 𝓝 1, ∀ n ∈ N, x ^ n ∈ U :=
      (eventually_all_finset N).2 fun n _ ↦
        (continuous_pow n).tendsto' 1 1 (one_pow n) hU
    filter_upwards [hNear] with x hx f
    have hPow : f.1 x ∈ ⋂ n ∈ N, T n := by
      simp only [mem_iInter, T, mem_preimage, ← map_pow]
      exact fun n hn ↦ f.2 (hx n hn)
    have hMem : f.1 x ∈ Metric.ball (1 : Circle) ε := by
      by_contra hz
      exact (Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hN)) hz hPow
    simpa [Function.comp_def, map_one, Metric.mem_ball, dist_comm] using hMem
  let A := {f : ContinuousMonoidHom G Circle | MapsTo f U W}
  let C := ContinuousMonoidHom.toContinuousMap '' A
  have hPointwise : ContinuousMap.toFun '' C =
      Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
    ext f
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      exact ⟨hψ, ψ.toMonoidHom, rfl⟩
    · rintro ⟨hf, ψ, rfl⟩
      let ψc : ContinuousMonoidHom G Circle :=
        { toMonoidHom := ψ, continuous_toFun := hEqui.continuous ⟨ψ, hf⟩ }
      exact ⟨ψc.toContinuousMap, ⟨ψc, hf, rfl⟩, rfl⟩
  have hC : IsCompact C := by
    apply ArzelaAscoli.isCompact_of_equicontinuous
    · rw [hPointwise]
      exact ((isClosed_set_pi fun _ _ ↦ Metric.isClosed_closedBall).inter
        (MonoidHom.isClosed_range_coe G Circle)).isCompact
    · refine (equicontinuous_iff_range (F := fun f : C ↦ f.1.toFun)).mpr ?_
      rw [← Set.image_eq_range ContinuousMap.toFun C, hPointwise]
      have hRange : range (fun f : S ↦ (f.1 : G → Circle)) =
          Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
        ext f
        constructor
        · rintro ⟨ψ, rfl⟩
          exact ⟨ψ.2, ψ.1, rfl⟩
        · rintro ⟨hf, ψ, rfl⟩
          exact ⟨⟨ψ, hf⟩, rfl⟩
      rw [← hRange]
      exact equicontinuous_iff_range.mp hEqui
  exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).isCompact_iff.mpr hC

end Polar

section Fourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

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

/-- Uniform convergence of characters on compact sets controls the integral, since
the integral of the norm of an L¹ function outside a suitable compact set is small. -/
theorem continuous_lcaFourier {f : G → ℂ} (hf : Integrable f μ) :
    Continuous (lcaFourier μ f) := by
  rw [continuous_iff_continuousAt]
  intro ψ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, -, hK, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hf
    MeasurableSet.univ (show 0 < ε / 4 by positivity)
  rw [← compl_eq_univ_sdiff] at hTail
  let I := ∫ x, ‖f x‖ ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ ↦ norm_nonneg _
  let δ := ε / 2 / (I + 1)
  have hδ : 0 < δ := div_pos (half_pos hε) (by positivity)
  let d (p : PontryaginDual G × G) : ℂ := star (p.1 p.2 : ℂ) - star (ψ p.2 : ℂ)
  have he : Continuous (fun p : PontryaginDual G × G ↦ p.1 p.2) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_fst).prodMk continuous_snd)
  have hd : Continuous d := (continuous_subtype_val.comp he).star.sub
    ((continuous_subtype_val.comp ψ.continuous).comp continuous_snd).star
  have hNear : ∀ᶠ χ in 𝓝 ψ, ∀ x ∈ K, ‖d (χ, x)‖ < δ :=
    hK.eventually_forall_of_forall_eventually fun x _ ↦
      (isOpen_lt hd.norm continuous_const).mem_nhds (by simpa [d] using hδ)
  filter_upwards [hNear] with χ hχ
  let q (x : G) := f x * d (χ, x)
  have hq : Integrable q μ := by
    refine ((integrable_fourierIntegrand μ hf χ).sub
      (integrable_fourierIntegrand μ hf ψ)).congr (.of_forall fun x ↦ ?_)
    change f x * star (χ x : ℂ) - f x * star (ψ x : ℂ) =
      f x * (star (χ x : ℂ) - star (ψ x : ℂ))
    exact (mul_sub _ _ _).symm
  have hOn : ‖∫ x in K, q x ∂μ‖ ≤ ε / 2 := by
    have hBound := norm_integral_le_of_norm_le (μ := μ.restrict K) (f := q)
      (hf.norm.const_mul δ).integrableOn
      ((ae_restrict_mem hK.isClosed.measurableSet).mono fun x hx ↦ by
        change ‖f x * d (χ, x)‖ ≤ _
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hχ x hx).le (norm_nonneg _))
    rw [integral_const_mul] at hBound
    refine hBound.trans ((mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hf.norm (.of_forall fun _ ↦ norm_nonneg _)) hδ.le).trans ?_)
    calc
      δ * I ≤ δ * (I + 1) := by gcongr; linarith
      _ = ε / 2 := div_mul_cancel₀ _ (by positivity)
  have hOff : ‖∫ x in Kᶜ, q x ∂μ‖ < ε / 2 := by
    have hBound := norm_integral_le_of_norm_le (μ := μ.restrict Kᶜ) (f := q)
      (hf.norm.const_mul 2).integrableOn (.of_forall fun x ↦ by
        change ‖f x * d (χ, x)‖ ≤ _
        rw [norm_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
        rw [norm_star, norm_star, Circle.norm_coe, Circle.norm_coe]
        norm_num)
    rw [integral_const_mul] at hBound
    exact hBound.trans_lt (by linarith)
  have hEq : (∫ x, q x ∂μ) = lcaFourier μ f χ - lcaFourier μ f ψ := by
    simp only [q, d, lcaFourier, mul_sub]
    exact integral_sub (integrable_fourierIntegrand μ hf χ) (integrable_fourierIntegrand μ hf ψ)
  rw [dist_eq_norm, ← hEq, ← integral_add_compl hK.isClosed.measurableSet hq]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Left translation multiplies the Fourier transform by the corresponding character value. -/
theorem lcaFourier_translate (f : G → ℂ) (a : G) (χ : PontryaginDual G) :
    lcaFourier μ (fun x ↦ f (a * x)) χ = (χ a : ℂ) * lcaFourier μ f χ := by
  have hUnit : (χ a : ℂ) * star (χ a : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    simp
  unfold lcaFourier
  rw [← integral_mul_left_eq_self (μ := μ) (fun x ↦ f x * star (χ x : ℂ)) a,
    ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change f (a * x) * star (χ x : ℂ) =
      (χ a : ℂ) * (f (a * x) * star (χ (a * x) : ℂ))
    have hMul : (χ (a * x) : ℂ) = (χ a : ℂ) * (χ x : ℂ) := by
      simp only [map_mul, Circle.coe_mul]
    rw [hMul, star_mul]
    symm
    calc
      _ = ((χ a : ℂ) * star (χ a : ℂ)) * (f (a * x) * star (χ x : ℂ)) := by ring
      _ = _ := by rw [hUnit, one_mul]

/-- A small L¹ translation difference bounds the transform times the displacement
of the character at the translating element. -/
theorem norm_mul_lcaFourier_le_translation {f : G → ℂ} (hf : Integrable f μ)
    (a : G) (χ : PontryaginDual G) :
    ‖(χ a : ℂ) - 1‖ * ‖lcaFourier μ f χ‖ ≤
      ‖Lp.compMeasurePreserving (a * ·) (measurePreserving_mul_left μ a)
        ((memLp_one_iff_integrable.mpr hf).toLp f) - (memLp_one_iff_integrable.mpr hf).toLp f‖ := by
  let f₁ := (memLp_one_iff_integrable.mpr hf).toLp f
  let T := Lp.compMeasurePreserving (a * ·) (measurePreserving_mul_left μ a) f₁
  have hF : (f₁ : G → ℂ) =ᵐ[μ] f := MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)
  have hT : (T : G → ℂ) =ᵐ[μ] fun x ↦ f (a * x) :=
    (Lp.coeFn_compMeasurePreserving f₁ _).trans
      ((measurePreserving_mul_left μ a).quasiMeasurePreserving.ae_eq_comp hF)
  have hDiff : ((T - f₁ : Lp ℂ 1 μ) : G → ℂ) =ᵐ[μ] fun x ↦ f (a * x) - f x :=
    (Lp.coeFn_sub T f₁).trans (hT.sub hF)
  have hTransform : lcaFourier μ (T - f₁ : Lp ℂ 1 μ) χ =
      ((χ a : ℂ) - 1) * lcaFourier μ f χ := by
    unfold lcaFourier at *
    calc
      _ = ∫ x, (f (a * x) - f x) * star (χ x : ℂ) ∂μ :=
        integral_congr_ae (hDiff.mono fun x hx ↦ by rw [hx])
      _ = (∫ x, f (a * x) * star (χ x : ℂ) ∂μ) -
          ∫ x, f x * star (χ x : ℂ) ∂μ := by
        simp_rw [sub_mul]
        exact integral_sub
          (integrable_fourierIntegrand μ
            ((measurePreserving_mul_left μ a).integrable_comp_of_integrable hf) χ) (integrable_fourierIntegrand μ hf χ)
      _ = _ := by
        rw [sub_mul, one_mul]
        exact congrArg (· - _) (lcaFourier_translate μ f a χ)
  rw [← norm_mul, ← hTransform, L1.norm_eq_integral_norm (T - f₁)]
  exact norm_lcaFourier_le_integral_norm μ _ χ

/-- Paper: Lemma D.1.1.2(1), p. 746. The Fourier transform of an L¹ function
is continuous and vanishes at infinity on the dual group. -/
theorem lcaFourier_zeroAtInfty {f : G → ℂ} (hf : Integrable f μ) :
    ∃ F : C₀(PontryaginDual G, ℂ), ∀ χ, F χ = lcaFourier μ f χ := by
  refine ⟨⟨⟨lcaFourier μ f, continuous_lcaFourier μ hf⟩, ?_⟩, fun _ ↦ rfl⟩
  apply NormedAddGroup.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  let f₁ := (memLp_one_iff_integrable.mpr hf).toLp f
  let T (a : G) := Lp.compMeasurePreserving (a * ·) (measurePreserving_mul_left μ a) f₁
  have hc : Continuous T := by
    have hMul : Continuous fun a : G ↦ ContinuousMap.mulLeft (X := G) a :=
      (ContinuousMap.curry
        ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩).continuous
    exact continuous_const.compMeasurePreservingLp hMul _ ENNReal.one_ne_top
  have hOne : T 1 = f₁ := by
    apply Lp.ext
    simpa [T, Function.comp_def] using
      Lp.coeFn_compMeasurePreserving f₁ (measurePreserving_mul_left μ (1 : G))
  let U := {a | ‖T a - f₁‖ < r * ε}
  have hU : U ∈ 𝓝 (1 : G) :=
    (isOpen_lt (hc.sub continuous_const).norm continuous_const).mem_nhds
      (by
        change ‖T 1 - f₁‖ < r * ε
        rw [hOne, sub_self, norm_zero]
        exact mul_pos hr hε)
  refine mem_cocompact.mpr ⟨_, hPolar U hU, fun χ hχ ↦ ?_⟩
  have hOut : ¬ ∀ a ∈ U, χ a ∈ Metric.closedBall 1 r := hχ
  push Not at hOut
  obtain ⟨a, ha, hFar⟩ := hOut
  have hDist : r ≤ ‖(χ a : ℂ) - 1‖ := by
    have hd : r < dist (χ a) 1 := lt_of_not_ge hFar
    change r < dist (χ a : ℂ) ((1 : Circle) : ℂ) at hd
    simpa only [Circle.coe_one, dist_eq_norm] using hd.le
  have hle := norm_mul_lcaFourier_le_translation μ hf a χ
  change _ ≤ ‖T a - f₁‖ at hle
  change ‖T a - f₁‖ < r * ε at ha
  exact (mul_lt_mul_iff_of_pos_left hr).mp
    ((mul_le_mul_of_nonneg_right hDist (norm_nonneg _)).trans_lt (hle.trans_lt ha))

/-- An integrable function whose Fourier transform is zero vanishes almost everywhere. -/
theorem ae_eq_zero_of_lcaFourier_eq_zero {f : G → ℂ} (hf : Integrable f μ)
    (h : ∀ χ, lcaFourier μ f χ = 0) : f =ᵐ[μ] 0 := by
  let e (x : G) : PontryaginDual G →* Circle :=
    { toFun := fun χ ↦ χ x
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hInj : Function.Injective e := by
    intro x y hEq
    by_contra hxy
    have hmem : x / y ∉ (⊥ : Subgroup G) := by
      rw [Subgroup.mem_bot]
      exact div_ne_one.mpr hxy
    obtain ⟨χ, -, hχ⟩ := MasulloGRH.pontryaginDual_separates_of_locallyCompact G ⊥
      (by rw [Subgroup.coe_bot]; exact isClosed_singleton) (x / y) hmem
    apply hχ
    have h1 : χ x = χ y := DFunLike.congr_fun hEq χ
    rw [map_div, h1, div_self']
  refine ae_eq_zero_of_integral_mul_circle_eq_zero e (fun χ ↦ χ.continuous) hInj hf ?_
  intro χ
  have hinv (x : G) : star (χ⁻¹ x : ℂ) = (χ x : ℂ) := by
    change star (((χ x)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  change (∫ x, f x * (χ x : ℂ) ∂μ) = 0
  simpa only [lcaFourier, hinv] using h χ⁻¹

/-- Paper: Lemma D.1.1.2(2), p. 746. The integral formula gives an injective
complex-linear map on L¹ equivalence classes with operator norm at most one. -/
theorem lcaFourier_L1 :
    ∃ F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ),
      (∀ f χ, F f χ = lcaFourier μ (f : G → ℂ) χ) ∧
      Function.Injective F ∧ ∀ f, ‖F f‖ ≤ ‖f‖ := by
  choose transform hTransform using fun f : Lp ℂ 1 μ ↦
    lcaFourier_zeroAtInfty μ (L1.integrable_coeFn f)
  let F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ) :=
    { toFun := transform
      map_add' f g := ZeroAtInftyContinuousMap.ext fun χ ↦ by
        change transform (f + g) χ = transform f χ + transform g χ
        rw [hTransform, hTransform, hTransform]
        unfold lcaFourier
        calc
          _ = ∫ x, (f x + g x) * star (χ x : ℂ) ∂μ :=
            integral_congr_ae ((Lp.coeFn_add f g).mono fun x hx ↦ by rw [hx]; rfl)
          _ = _ := by
            simp_rw [add_mul]
            exact integral_add (integrable_fourierIntegrand μ (L1.integrable_coeFn f) χ)
              (integrable_fourierIntegrand μ (L1.integrable_coeFn g) χ)
      map_smul' c f := ZeroAtInftyContinuousMap.ext fun χ ↦ by
        change transform (c • f) χ = c • transform f χ
        rw [hTransform, hTransform]
        unfold lcaFourier
        calc
          _ = ∫ x, c • (f x * star (χ x : ℂ)) ∂μ :=
            integral_congr_ae ((Lp.coeFn_smul c f).mono fun x hx ↦ by
              rw [hx]
              exact smul_mul_assoc c (f x) _)
          _ = _ := integral_smul c _ }
  refine ⟨F, hTransform, LinearMap.ker_eq_bot.mp ?_, fun f ↦ ?_⟩
  · apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hZero (χ : PontryaginDual G) : lcaFourier μ (f : G → ℂ) χ = 0 := by
      rw [← hTransform f χ]
      exact DFunLike.congr_fun hf χ
    exact Lp.ext ((ae_eq_zero_of_lcaFourier_eq_zero μ (L1.integrable_coeFn f) hZero).trans
      (Lp.coeFn_zero ℂ 1 μ).symm)
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro χ
    change ‖transform f χ‖ ≤ ‖f‖
    rw [hTransform, L1.norm_eq_integral_norm]
    exact norm_lcaFourier_le_integral_norm μ _ χ

end Fourier

end Sol_LCAGroup_fourier_L1_to_zeroAtInfty_injective

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ),
      (∀ (f : Lp ℂ 1 μ) (χ : PontryaginDual G),
        F f χ = RiemannMasullo.lcaFourier μ (f : G → ℂ) χ) ∧
      Function.Injective F ∧
      ∀ f : Lp ℂ 1 μ, ‖F f‖ ≤ ‖f‖ :=
  Sol_LCAGroup_fourier_L1_to_zeroAtInfty_injective.lcaFourier_L1 μ
