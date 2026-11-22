-- Prove2me | solution 1 for LCAGroup.pontryagin_duality
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:42:57.046147+00:00
-- url     : https://prove2.me/submissions/90365173-b15e-40be-b88a-fce5da71d3dd

import Mathlib
import Theorems.Thm_LCAGroup_plancherel

open Topology

set_option autoImplicit false

namespace Sol_LCAGroup_pontryagin_duality

open Filter Set MeasureTheory RiemannMasullo
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

end Regular

section Plancherel

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- The form of the Plancherel theorem used below: a regular Haar measure on the dual and a
unitary operator that is the Fourier transform on `L¹ ∩ L²`. -/
theorem exists_plancherel (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ ν : Measure (PontryaginDual G), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
        ∀ (f : G → ℂ), Integrable f μ → ∀ (h₂ : MemLp f 2 μ),
          (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
  obtain ⟨⟨ν, hν, -⟩, hU⟩ := LCAGroup.plancherel G μ
  obtain ⟨U, hU, -⟩ := hU ν hν
  exact ⟨ν, hν.1, hν.2.1, U, fun f hf h₂ ↦ hU f hf h₂⟩

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace (PontryaginDual G)]
  [BorelSpace (PontryaginDual G)] in
/-- Left translation multiplies the Fourier transform by the corresponding character value. -/
theorem lcaFourier_translate (μ : Measure G) [μ.IsHaarMeasure]
    (f : G → ℂ) (a : G) (χ : PontryaginDual G) :
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

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Multiplying an L² function by a character translates its Plancherel transform. -/
theorem lcaFourier_unitary_modulation (μ : Measure G)
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (f : G → ℂ), Integrable f μ → ∀ (hf : MemLp f 2 μ),
      (U (hf.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f)
    (ψ : PontryaginDual G) (f : Lp ℂ 2 μ) :
    ∃ g : Lp ℂ 2 μ, (g : G → ℂ) =ᵐ[μ] (fun x ↦ (ψ x : ℂ) * f x) ∧
      (U g : PontryaginDual G → ℂ) =ᵐ[ν] (fun χ ↦ U f (ψ⁻¹ * χ)) := by
  let m := measurePreserving_mul_left ν ψ⁻¹
  let c (x : G) : ℂ := ψ x
  have hc : MemLp c ∞ μ := memLp_top_of_bound
    (continuous_subtype_val.comp ψ.continuous).aestronglyMeasurable 1
      (.of_forall fun x ↦ (Circle.norm_coe (ψ x)).le)
  have hMem (v : Lp ℂ 2 μ) : MemLp (fun x ↦ c x * v x) 2 μ :=
    (Lp.memLp v).mul' hc
  let M (v : Lp ℂ 2 μ) := (hMem v).toLp (fun x ↦ c x * v x)
  have hM (v : Lp ℂ 2 μ) : (M v : G → ℂ) =ᵐ[μ] (fun x ↦ c x * v x) :=
    (hMem v).coeFn_toLp
  refine ⟨M f, hM f, ?_⟩
  let T := Lp.compMeasurePreservingₗᵢ ℂ (ψ⁻¹ * ·) m (p := 2) (E := ℂ)
  have hT (v : Lp ℂ 2 ν) : (T v : PontryaginDual G → ℂ) =ᵐ[ν] (fun χ ↦ v (ψ⁻¹ * χ)) :=
    Lp.coeFn_compMeasurePreserving v m
  suffices hEq : U (M f) = T (U f) by
    rw [hEq]
    exact hT (U f)
  have hMc : Continuous M := by
    apply Isometry.continuous
    apply Isometry.of_dist_eq
    intro v w
    simp only [dist_eq_norm]
    have hNorm : ∀ᵐ x ∂μ, ‖(M v - M w) x‖ = ‖(v - w) x‖ := by
      filter_upwards [hM v, hM w, Lp.coeFn_sub (M v) (M w), Lp.coeFn_sub v w]
        with x hv hw h₁ h₂
      simp only [Pi.sub_apply] at h₁ h₂
      rw [h₁, h₂, hv, hw, ← mul_sub, norm_mul, Circle.norm_coe (ψ x), one_mul]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hNorm.mono fun _ h ↦ h.le))
      (Lp.norm_le_norm_of_ae_le (hNorm.mono fun _ h ↦ h.ge))
  refine (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) (p := 2) ENNReal.ofNat_ne_top).induction_on f
    (isClosed_eq (U.continuous.comp hMc) (T.continuous.comp U.continuous)) ?_
  intro s
  let v : Lp ℂ 2 μ := s
  have hv : Integrable (v : G → ℂ) μ :=
    ((SimpleFunc.memLp_iff_integrable two_ne_zero ENNReal.ofNat_ne_top).mp
      (Lp.simpleFunc.memLp s)).congr (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
  have hMv : Integrable (fun x ↦ c x * v x) μ :=
    memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hv).mul' hc)
  have hUv : (U v : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ v := by
    simpa only [Lp.toLp_coeFn] using hU _ hv (Lp.memLp v)
  change U (M v) = T (U v)
  apply Lp.ext
  filter_upwards [hU _ hMv (hMem v), hT (U v), m.quasiMeasurePreserving.ae_eq_comp hUv]
    with χ h₁ h₂ h₃
  rw [h₁, h₂, show U v (ψ⁻¹ * χ) = lcaFourier μ v (ψ⁻¹ * χ) from h₃]
  unfold lcaFourier
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change c x * v x * star (χ x : ℂ) = v x * star (((ψ x)⁻¹ * χ x : Circle) : ℂ)
    rw [Circle.coe_mul, star_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
    change (ψ x : ℂ) * v x * _ = _
    ring

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace (PontryaginDual G)]
  [BorelSpace (PontryaginDual G)] in
/-- A nonzero L² function with orthogonal modulations gives a normalized measure
whose Fourier–Stieltjes coefficients vanish at those modulations. -/
theorem probability_of_l2_orthogonality (μ : Measure G) [μ.InnerRegularCompactLTTop]
    (f : Lp ℂ 2 μ) (hf : f ≠ 0) {V : Set (PontryaginDual G)}
    (hZero : ∀ ψ ∉ V, ∫ x, (ψ x : ℂ) * (‖f x‖ ^ 2 : ℝ) ∂μ = 0) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν.InnerRegular ∧
      ∀ ψ ∉ V, ∫ x, (ψ x : ℂ) ∂ν = 0 := by
  let w (x : G) := ‖f x‖ ^ 2
  have hw : ∀ x, 0 ≤ w x := fun x ↦ sq_nonneg _
  have hSq (x : G) : inner ℂ (f x) (f x) = (w x : ℂ) := by
    change _ = ((‖f x‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
    exact inner_self_eq_norm_sq_to_K (f x)
  have hInt : Integrable w μ := by
    simpa only [hSq, RCLike.re_to_complex, Complex.ofReal_re]
      using (L2.integrable_inner (𝕜 := ℂ) f f).re
  let ρ := μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
  have hρ {s : Set G} (hs : MeasurableSet s) :
      ρ s = ENNReal.ofReal (∫ x in s, w x ∂μ) := by
    rw [withDensity_apply _ hs,
      ofReal_integral_eq_lintegral_ofReal hInt.integrableOn (.of_forall hw)]
  have hMass : ρ univ = ENNReal.ofReal (‖f‖ ^ 2) := by
    rw [hρ MeasurableSet.univ, Measure.restrict_univ]
    congr 1
    have hSelf : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K f
    rw [L2.inner_def] at hSelf
    simp_rw [hSq, integral_complex_ofReal] at hSelf
    exact Complex.ofReal_injective hSelf
  have hFinite : IsFiniteMeasure ρ := ⟨hMass ▸ ENNReal.ofReal_lt_top⟩
  have hPos : ρ univ ≠ 0 := by
    rw [hMass]
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hf))).ne'
  have hRegular : ρ.InnerRegular := by
    constructor
    intro s hs r hr
    have hrTop := hr.ne_top
    have hr' : r.toReal < ∫ x in s, w x ∂μ := by
      rw [hρ hs] at hr
      exact ENNReal.toReal_lt_of_lt_ofReal hr
    obtain ⟨K, hKs, hK, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hInt hs
      (sub_pos.mpr hr')
    simp only [Real.norm_of_nonneg (hw _)] at hTail
    refine ⟨K, hKs, hK, ?_⟩
    rw [hρ hK.isClosed.measurableSet, ← ENNReal.ofReal_toReal hrTop,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
    have hSplit := setIntegral_sdiff hK.isClosed.measurableSet hInt.integrableOn hKs
    linarith
  refine ⟨(ρ univ)⁻¹ • ρ, ⟨?_⟩, inferInstance, fun ψ hψ ↦ ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hPos (measure_ne_top ρ _)]
  · rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀
      hInt.aemeasurable.ennreal_ofReal (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hw _), Complex.real_smul, mul_comm (w _ : ℂ)]
    change _ * (∫ x, (ψ x : ℂ) * (‖f x‖ ^ 2 : ℝ) ∂μ) = 0
    rw [hZero ψ hψ, mul_zero]

end Plancherel

section Pontryagin

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
/-- Evaluating characters at a point gives a continuous homomorphism from the group into its
bidual. -/
noncomputable def pontryaginDual_eval : G →ₜ* PontryaginDual (PontryaginDual G) := by
  have hEval : Continuous (fun p : PontryaginDual G × G ↦ p.1 p.2) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_fst).prodMk continuous_snd)
  let atPoint (x : G) : PontryaginDual (PontryaginDual G) :=
    { toFun := fun χ ↦ χ x
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := hEval.comp (continuous_id.prodMk continuous_const) }
  refine
    { toFun := atPoint
      map_one' := PontryaginDual.ext fun χ ↦ map_one χ
      map_mul' := fun x y ↦ PontryaginDual.ext fun χ ↦ map_mul χ x y
      continuous_toFun := ?_ }
  exact ContinuousMonoidHom.continuous_of_continuous_uncurry atPoint
    (hEval.comp (continuous_snd.prodMk continuous_fst))

omit [T2Space G] [IsTopologicalGroup G] in
theorem pontryaginDual_eval_apply (x : G) (χ : PontryaginDual G) :
    pontryaginDual_eval x χ = χ x := rfl

/-- Every identity neighbourhood of `G` contains the set of points at which all characters of a
suitable compact set of characters are within distance `1 / 4` of `1`.  This is deduced from the
Plancherel theorem applied to the indicator function of a small compact neighbourhood. -/
theorem exists_pontryaginDual_compact_test {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : Set (PontryaginDual G), IsCompact K ∧
      ∀ x : G, (∀ χ ∈ K, dist (χ x) 1 < 1 / 4) → x ∈ U := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  have : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  obtain ⟨ν, hνH, hνR, T, hT⟩ := exists_plancherel μ
  -- a compact neighbourhood `C` of `1` with `C * C⁻¹ ⊆ U`
  obtain ⟨W, hW, -, hWinv, hWU⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨C, ⟨hC₁, hC⟩, hCW⟩ := (compact_basis_nhds (1 : G)).mem_iff.mp hW
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hCfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  have hCpos : μ C ≠ 0 := (μ.measure_pos_of_mem_nhds hC₁).ne'
  -- the indicator of `C`, its translates, and their classes in `L²`
  let g : G → ℂ := C.indicator fun _ ↦ (1 : ℂ)
  have hg₂ : MemLp g 2 μ := memLp_indicator_const 2 hCm 1 (Or.inr hCfin)
  have hg₁ : Integrable g μ :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 hCm 1 (Or.inr hCfin))
  have hgx₂ (x : G) : MemLp (fun y ↦ g (x * y)) 2 μ :=
    hg₂.comp_measurePreserving (measurePreserving_mul_left μ x)
  have hgx₁ (x : G) : Integrable (fun y ↦ g (x * y)) μ := hg₁.comp_mul_left x
  let u : Lp ℂ 2 μ := hg₂.toLp g
  let ux (x : G) : Lp ℂ 2 μ := (hgx₂ x).toLp fun y ↦ g (x * y)
  have hu : (u : G → ℂ) =ᵐ[μ] g := hg₂.coeFn_toLp
  have hux (x : G) : (ux x : G → ℂ) =ᵐ[μ] fun y ↦ g (x * y) := (hgx₂ x).coeFn_toLp
  have huNe : u ≠ 0 := by
    intro hz
    have hn := norm_indicatorConstLp (p := 2) (μ := μ) (hs := hCm) (hμs := hCfin) (c := (1 : ℂ))
      (by norm_num) ENNReal.ofNat_ne_top
    have hp := ENNReal.toReal_pos hCpos hCfin
    change ‖u‖ = _ at hn
    simp only [hz, norm_zero, norm_one, one_mul] at hn
    exact (Real.rpow_pos_of_pos hp _).ne' hn.symm
  -- their Plancherel transforms
  let v : Lp ℂ 2 ν := T u
  have hvx (x : G) : (T (ux x) : PontryaginDual G → ℂ) =ᵐ[ν] fun χ ↦ (χ x : ℂ) * v χ := by
    filter_upwards [hT _ (hgx₁ x) (hgx₂ x), hT g hg₁ hg₂] with χ h₁ h₂
    rw [h₁, lcaFourier_translate μ g x χ]
    change _ = (χ x : ℂ) * T u χ
    rw [h₂]
  let w (χ : PontryaginDual G) : ℝ := ‖v χ‖ ^ 2
  have hw : ∀ χ, 0 ≤ w χ := fun χ ↦ sq_nonneg _
  have hSq (χ : PontryaginDual G) : inner ℂ (v χ) (v χ) = (w χ : ℂ) := by
    change _ = ((‖v χ‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
    exact inner_self_eq_norm_sq_to_K (v χ)
  have hInt : Integrable w ν := by
    simpa only [hSq, RCLike.re_to_complex, Complex.ofReal_re]
      using (L2.integrable_inner (𝕜 := ℂ) v v).re
  set c : ℝ := ‖u‖ ^ 2 with hc
  have hcpos : 0 < c := sq_pos_of_pos (norm_pos_iff.mpr huNe)
  -- total mass of the weight
  have hMass : ∫ χ, w χ ∂ν = c := by
    have hSelf : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K v
    rw [L2.inner_def] at hSelf
    simp_rw [hSq, integral_complex_ofReal] at hSelf
    rw [Complex.ofReal_injective hSelf, hc]
    change ‖T u‖ ^ 2 = _
    rw [LinearIsometryEquiv.norm_map]
  -- a compact set of characters carrying most of the weight
  obtain ⟨K, -, hK, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hInt MeasurableSet.univ
    (show 0 < c / 4 by positivity)
  simp only [Real.norm_of_nonneg (hw _)] at hTail
  rw [← compl_eq_univ_sdiff] at hTail
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  by_contra hxU
  -- the translate by `x` is orthogonal to the indicator
  have hOrth : inner ℂ u (ux x) = 0 := by
    rw [L2.inner_def, ← integral_zero (α := G) (μ := μ) (G := ℂ)]
    apply integral_congr_ae
    filter_upwards [hu, hux x] with y h₁ h₂
    rw [h₁, h₂]
    by_cases hy : y ∈ C
    · have hxy : x * y ∉ C := by
        intro h
        apply hxU
        apply hWU
        refine ⟨x * y, hCW h, y⁻¹, ?_, by simp⟩
        rw [← hWinv]
        exact Set.inv_mem_inv.mpr (hCW hy)
      simp [g, indicator_of_notMem hxy]
    · simp [g, indicator_of_notMem hy]
  have hZero : ∫ χ, (w χ : ℂ) * (χ x : ℂ) ∂ν = 0 := by
    have h := T.inner_map_map u (ux x)
    rw [hOrth, L2.inner_def] at h
    refine (integral_congr_ae ?_).trans h
    filter_upwards [hvx x] with χ hχ
    have hvv : v χ * star (v χ) = (w χ : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hχ, RCLike.inner_apply, starRingEnd_apply]
    change _ = (χ x : ℂ) * v χ * star (v χ)
    rw [mul_assoc, hvv, mul_comm]
  have hEvalCont : Continuous fun χ : PontryaginDual G ↦ (χ x : ℂ) :=
    continuous_subtype_val.comp (pontryaginDual_eval x).continuous
  have hIntw : Integrable (fun χ : PontryaginDual G ↦ (w χ : ℂ)) ν := hInt.ofReal
  have hIntx : Integrable (fun χ : PontryaginDual G ↦ (w χ : ℂ) * (χ x : ℂ)) ν :=
    hIntw.mul_bdd (c := 1) hEvalCont.aestronglyMeasurable
      (.of_forall fun χ ↦ (Circle.norm_coe (χ x)).le)
  have hDiff : (c : ℂ) = ∫ χ, (w χ : ℂ) * (1 - (χ x : ℂ)) ∂ν := by
    simp_rw [mul_sub, mul_one]
    rw [integral_sub hIntw hIntx, hZero, sub_zero, integral_complex_ofReal, hMass]
  have hKc : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have hBound (χ : PontryaginDual G) :
      ‖(w χ : ℂ) * (1 - (χ x : ℂ))‖ ≤ 1 / 4 * w χ + 2 * Kᶜ.indicator w χ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw χ)]
    by_cases hχ : χ ∈ K
    · have hd : ‖1 - (χ x : ℂ)‖ ≤ 1 / 4 := by
        have h₀ : dist (χ x) 1 = ‖1 - (χ x : ℂ)‖ := by
          rw [← dist_eq_norm, dist_comm]
          rfl
        rw [← h₀]
        exact (hx χ hχ).le
      have : Kᶜ.indicator w χ = 0 := indicator_of_notMem (by simpa using hχ) _
      rw [this]
      nlinarith [hw χ]
    · have hd : ‖1 - (χ x : ℂ)‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, Circle.norm_coe]
        norm_num
      have : Kᶜ.indicator w χ = w χ := indicator_of_mem (by simpa using hχ) _
      rw [this]
      nlinarith [hw χ]
  have hLe : c ≤ ∫ χ, (1 / 4 * w χ + 2 * Kᶜ.indicator w χ) ∂ν := by
    have h₁ : c = ‖(c : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    rw [h₁, hDiff]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (.of_forall fun χ ↦ norm_nonneg _) ?_ (.of_forall hBound)
    exact (hInt.const_mul _).add ((hInt.indicator hKc).const_mul _)
  rw [integral_add (hInt.const_mul _) ((hInt.indicator hKc).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator hKc, hMass] at hLe
  linarith

/-- Evaluation embeds the group as a closed subgroup of its bidual. -/
theorem isClosedEmbedding_pontryaginDual_eval :
    IsClosedEmbedding (pontryaginDual_eval (G := G)) := by
  let e := pontryaginDual_eval (G := G)
  have hInducing : IsInducing e := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto e (𝓝 1) (𝓝 (e 1)) := e.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      obtain ⟨K, hK, hTest⟩ := exists_pontryaginDual_compact_test hU
      let V : Set (PontryaginDual (PontryaginDual G)) :=
        {ψ | MapsTo ψ K (Metric.ball 1 (1 / 4))}
      have hV : IsOpen V :=
        (ContinuousMap.isOpen_setOfPred_mapsTo hK Metric.isOpen_ball).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap (PontryaginDual G) Circle).continuous
      refine Filter.mem_comap.mpr ⟨V, hV.mem_nhds ?_, fun x hx ↦ hTest x (fun χ hχ ↦ hx hχ)⟩
      intro χ _
      simp [Metric.mem_ball]
  have hInjective : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    have hU : ({x}ᶜ : Set G) ∈ 𝓝 (1 : G) := isOpen_compl_singleton.mem_nhds (Ne.symm hx1)
    obtain ⟨K, -, hTest⟩ := exists_pontryaginDual_compact_test hU
    refine hTest x (fun χ _ ↦ ?_) rfl
    have hχ : χ x = 1 := by
      have := DFunLike.congr_fun hx χ
      simpa [e, pontryaginDual_eval_apply] using this
    rw [hχ, dist_self]
    norm_num
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : UniformSpace (PontryaginDual (PontryaginDual G)) := IsTopologicalGroup.rightUniformSpace _
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  have : IsUniformGroup (PontryaginDual (PontryaginDual G)) := isUniformGroup_of_commGroup
  have : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  exact (MonoidHom.isUniformEmbedding_of_isEmbedding (f := e)
    ⟨hInducing, hInjective⟩).isClosedEmbedding

open scoped Pointwise in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- If a character of the dual is orthogonal to evaluations against a finite inner
regular measure, it is orthogonal to every character of the dual. Evaluation functions
form a point-separating self-adjoint algebra after taking their complex linear span. -/
theorem pontryaginDual_integral_mul_eq_zero
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (ν : Measure (PontryaginDual G)) [IsFiniteMeasure ν] [ν.InnerRegular]
    (η : PontryaginDual (PontryaginDual G))
    (h : ∀ x : G, ∫ χ, (η χ : ℂ) * (χ x : ℂ) ∂ν = 0)
    (ψ : PontryaginDual (PontryaginDual G)) : ∫ χ, (η χ : ℂ) * (ψ χ : ℂ) ∂ν = 0 := by
  -- The space of abstract characters is compact in the pointwise topology.
  let B : Set (G → Circle) := {f | f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y}
  have hB : IsClosed B := by
    rw [show B = {f : G → Circle | f 1 = 1} ∩
      ⋂ x, ⋂ y, {f : G → Circle | f (x * y) = f x * f y} by ext; simp [B]]
    exact (isClosed_eq (continuous_apply 1) continuous_const).inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        isClosed_eq (continuous_apply (x * y)) ((continuous_apply x).mul (continuous_apply y)))
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let emb : PontryaginDual G → B := fun χ ↦ ⟨χ, map_one χ, map_mul χ⟩
  have hEmb : Continuous emb := by
    apply Continuous.subtype_mk
    exact continuous_pi fun x ↦ (continuous_eval_const (F := C(G, Circle)) x).comp
      (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
  have hInj : Function.Injective emb := fun _ _ hEq ↦
    DFunLike.coe_injective (congrArg Subtype.val hEq)
  let coord : G →* C(B, ℂ) :=
    { toFun := fun x ↦ ⟨fun b ↦ (b.1 x : ℂ),
        continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)⟩
      map_one' := ContinuousMap.ext fun b ↦ by
        show (b.1 1 : ℂ) = 1
        rw [b.2.1, Circle.coe_one]
      map_mul' := fun x y ↦ ContinuousMap.ext fun b ↦ by
        show (b.1 (x * y) : ℂ) = _
        rw [b.2.2, Circle.coe_mul]
        rfl }
  have hStar (x : G) : star (coord x) = coord x⁻¹ := by
    ext b
    change star (b.1 x : ℂ) = (b.1 x⁻¹ : ℂ)
    have hInv : b.1 x⁻¹ = (b.1 x)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← b.2.2, inv_mul_cancel, b.2.1]
    rw [hInv, Circle.coe_inv_eq_conj, Complex.star_def]
  let A := StarAlgebra.adjoin ℂ (Set.range coord)
  have hSep : A.SeparatesPoints := by
    intro a b hab
    obtain ⟨x, hx⟩ : ∃ x, a.1 x ≠ b.1 x := by
      by_contra! hEq
      exact hab (Subtype.ext (funext hEq))
    exact ⟨coord x, ⟨coord x, StarAlgebra.subset_adjoin _ _ (mem_range_self x), rfl⟩,
      fun hEq ↦ hx (Subtype.ext hEq)⟩
  have hSpan : A.toSubalgebra.toSubmodule ≤ Submodule.span ℂ (Set.range coord) := by
    rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_mono
    suffices Submonoid.closure (Set.range coord ∪ star (Set.range coord)) ≤
        MonoidHom.mrange coord from this
    apply Submonoid.closure_le.mpr
    rintro z (hMem | hMem)
    · exact hMem
    · obtain ⟨x, hx⟩ := Set.mem_star.mp hMem
      exact ⟨x⁻¹, (hStar x).symm.trans (by rw [hx, star_star])⟩
  let test (F : C(B, ℂ)) (χ : PontryaginDual G) := (η χ : ℂ) * F (emb χ)
  have hBound (F : C(B, ℂ)) (χ : PontryaginDual G) : ‖test F χ‖ ≤ ‖F‖ := by
    change ‖(η χ : ℂ) * F (emb χ)‖ ≤ ‖F‖
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact ContinuousMap.norm_coe_le_norm F _
  have hInt (F : C(B, ℂ)) : Integrable (test F) ν :=
    Integrable.of_bound ((continuous_subtype_val.comp η.continuous).mul
      (F.continuous.comp hEmb)).aestronglyMeasurable ‖F‖ (.of_forall (hBound F))
  let L : C(B, ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun F ↦ ∫ χ, test F χ ∂ν
      map_add' := fun F H ↦ by
        simp only [test, ContinuousMap.add_apply, mul_add]
        exact integral_add (hInt F) (hInt H)
      map_smul' := fun c F ↦ by
        simp only [test, ContinuousMap.smul_apply, mul_smul_comm,
          RingHom.id_apply, integral_smul] }
    (ν.real univ) fun F ↦ by
      simpa [mul_comm] using norm_integral_le_of_norm_le_const (μ := ν) (.of_forall (hBound F))
  -- Stone–Weierstrass extends the vanishing from evaluations to all continuous tests.
  have hL : ∀ F, L F = 0 := by
    have hDense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hSep
    intro F
    have hClosed : IsClosed {H | L H = 0} := isClosed_eq L.continuous continuous_const
    refine closure_minimal (s := (A : Set C(B, ℂ))) ?_ hClosed ?_
    · intro H hH
      have hKer : Submodule.span ℂ (Set.range coord) ≤ L.toLinearMap.ker :=
        Submodule.span_le.mpr (fun _ ⟨x, hx⟩ ↦ hx ▸ h x)
      exact hKer (hSpan hH)
    · have hF : F ∈ A.topologicalClosure := hDense ▸ StarSubalgebra.mem_top
      exact hF
  let target (χ : PontryaginDual G) : ℂ := ψ χ
  have hTarget : Continuous target := continuous_subtype_val.comp ψ.continuous
  have hTargetNorm (χ : PontryaginDual G) : ‖target χ‖ = 1 := Circle.norm_coe (ψ χ)
  have hTargetInt : Integrable (fun χ ↦ (η χ : ℂ) * target χ) ν :=
    Integrable.of_bound
      ((continuous_subtype_val.comp η.continuous).mul hTarget).aestronglyMeasurable
      1 (.of_forall fun χ ↦ by
        rw [norm_mul, Circle.norm_coe, hTargetNorm, one_mul])
  -- Extend the target from a compact set carrying nearly all the mass of ν.
  by_contra hNe
  let ε := ‖∫ χ, (η χ : ℂ) * target χ ∂ν‖
  have hε : 0 < ε := norm_pos_iff.mpr hNe
  obtain ⟨K, -, hK, hTail⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top ν _) (ENNReal.ofReal_pos.mpr (by positivity : 0 < ε / 3)).ne'
  rw [← compl_eq_univ_sdiff] at hTail
  have hTail' : ν.real Kᶜ < ε / 3 := by
    simpa [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ ε / 3)] using
      (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hTail
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : K → B := emb ∘ Subtype.val
  have hIncl : IsClosedEmbedding incl :=
    (hEmb.comp continuous_subtype_val).isClosedEmbedding (hInj.comp Subtype.val_injective)
  let re : C(K, ℝ) := ⟨fun χ ↦ (target χ.1).re,
    Complex.continuous_re.comp (hTarget.comp continuous_subtype_val)⟩
  let im : C(K, ℝ) := ⟨fun χ ↦ (target χ.1).im,
    Complex.continuous_im.comp (hTarget.comp continuous_subtype_val)⟩
  obtain ⟨R, hR, hRe⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    (BoundedContinuousFunction.mkOfCompact re) hIncl
  obtain ⟨I, hI, hIm⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    (BoundedContinuousFunction.mkOfCompact im) hIncl
  have hR₁ : ‖R‖ ≤ 1 := hR.le.trans <| (BoundedContinuousFunction.norm_le zero_le_one).2
    fun χ ↦ (Complex.abs_re_le_norm (target χ.1)).trans (hTargetNorm _).le
  have hI₁ : ‖I‖ ≤ 1 := hI.le.trans <| (BoundedContinuousFunction.norm_le zero_le_one).2
    fun χ ↦ (Complex.abs_im_le_norm (target χ.1)).trans (hTargetNorm _).le
  let F : C(B, ℂ) := ⟨fun b ↦ (R b : ℂ) + (I b : ℂ) * Complex.I, by fun_prop⟩
  have hF (b : B) : ‖F b‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    simpa [F, norm_mul, one_add_one_eq_two] using add_le_add
      ((BoundedContinuousFunction.norm_coe_le_norm R b).trans hR₁)
      ((BoundedContinuousFunction.norm_coe_le_norm I b).trans hI₁)
  have hAgree : ∀ χ ∈ K, F (emb χ) = target χ := by
    intro χ hχ
    have hr := congrFun hRe ⟨χ, hχ⟩
    have hi := congrFun hIm ⟨χ, hχ⟩
    change R (emb χ) = (target χ).re at hr
    change I (emb χ) = (target χ).im at hi
    simp only [F, ContinuousMap.coe_mk, hr, hi, Complex.re_add_im]
  have hDiff (χ : PontryaginDual G) : ‖(η χ : ℂ) * target χ - test F χ‖ ≤ 3 := by
    change ‖(η χ : ℂ) * target χ - (η χ : ℂ) * F (emb χ)‖ ≤ 3
    rw [← mul_sub, norm_mul, Circle.norm_coe, one_mul]
    calc
      _ ≤ ‖target χ‖ + ‖F (emb χ)‖ := norm_sub_le _ _
      _ ≤ 1 + 2 := add_le_add (hTargetNorm χ).le (hF (emb χ))
      _ = 3 := by norm_num
  let diff (χ : PontryaginDual G) := (η χ : ℂ) * target χ - test F χ
  have hDiffInt : Integrable diff ν := hTargetInt.sub (hInt F)
  have hKZero : ∫ χ in K, diff χ ∂ν = 0 := by
    calc
      _ = ∫ _ in K, (0 : ℂ) ∂ν := by
        exact setIntegral_congr_fun hK.isClosed.measurableSet fun χ hχ ↦ by
          simp [diff, test, hAgree χ hχ]
      _ = 0 := integral_zero _ _
  have hFull : (∫ χ in Kᶜ, diff χ ∂ν) = ∫ χ, (η χ : ℂ) * target χ ∂ν := by
    rw [← zero_add (∫ χ in Kᶜ, diff χ ∂ν), ← hKZero,
      integral_add_compl hK.isClosed.measurableSet hDiffInt]
    change (∫ χ, (η χ : ℂ) * target χ - test F χ ∂ν) = _
    rw [integral_sub hTargetInt (hInt F)]
    change _ - L F = _
    rw [hL, sub_zero]
  have hLe := norm_setIntegral_le_of_norm_le_const (f := diff) (measure_lt_top ν Kᶜ)
    (fun χ _ ↦ hDiff χ)
  rw [hFull] at hLe
  linarith

open scoped Pointwise in
/-- For each identity neighborhood in the dual, there is an inner-regular probability
measure on the group whose Fourier–Stieltjes transform vanishes off that neighborhood. -/
theorem exists_pontryaginDual_localized_integral [MeasurableSpace G] [BorelSpace G]
    {V : Set (PontryaginDual G)} (hV : V ∈ 𝓝 (1 : PontryaginDual G)) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν.InnerRegular ∧
      ∀ ψ ∉ V, ∫ x, (ψ x : ℂ) ∂ν = 0 := by
  let : MeasurableSpace (PontryaginDual G) := borel _
  have : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  obtain ⟨ν, hνH, hνR, U, hU⟩ := exists_plancherel μ
  -- Choose a compact neighborhood whose pairwise quotients lie in V.
  obtain ⟨W, hW, -, hWinv, hWV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  obtain ⟨K, ⟨hK₁, hK⟩, hKW⟩ := (compact_basis_nhds (1 : PontryaginDual G)).mem_iff.mp hW
  have hKm := hK.isClosed.measurableSet
  have hKfin := (hK.measure_lt_top (μ := ν)).ne
  have hKpos := (ν.measure_pos_of_mem_nhds hK₁).ne'
  let a := indicatorConstLp (μ := ν) 2 hKm hKfin (1 : ℂ)
  have ha : (a : PontryaginDual G → ℂ) =ᵐ[ν] K.indicator (fun _ ↦ (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have haNe : a ≠ 0 := by
    intro hz
    have hn := norm_indicatorConstLp (p := 2) (μ := ν) (hs := hKm) (hμs := hKfin) (c := (1 : ℂ))
      (by norm_num) ENNReal.ofNat_ne_top
    have hp := ENNReal.toReal_pos hKpos hKfin
    change ‖a‖ = _ at hn
    simp only [hz, norm_zero, norm_one, one_mul] at hn
    exact (Real.rpow_pos_of_pos hp _).ne' hn.symm
  let f := U.symm a
  have hUf : U f = a := U.apply_symm_apply a
  refine probability_of_l2_orthogonality μ f (U.symm.map_eq_zero_iff.not.mpr haNe) ?_
  intro ψ hψ
  obtain ⟨g, hg, hUg⟩ := lcaFourier_unitary_modulation μ ν U hU ψ f
  -- The transforms of f and g have disjoint supports up to null sets.
  have hUtf : inner ℂ (U f) (U g) = 0 := by
    let m := measurePreserving_mul_left ν ψ⁻¹
    rw [hUf] at hUg
    rw [L2.inner_def, hUf]
    rw [← integral_zero (α := PontryaginDual G) (μ := ν) (G := ℂ)]
    apply integral_congr_ae
    filter_upwards [ha, hUg, m.quasiMeasurePreserving.ae_eq_comp ha] with χ hχ hχ' hShift
    change a χ = _ at hχ
    change U g χ = _ at hχ'
    rw [hχ, hχ', show a (ψ⁻¹ * χ) = _ from hShift]
    by_cases hχK : χ ∈ K
    · have hOutside : ψ⁻¹ * χ ∉ K := by
        intro h
        apply hψ
        apply hWV
        refine ⟨χ, hKW hχK, (ψ⁻¹ * χ)⁻¹, ?_, by simp [mul_comm]⟩
        rw [← hWinv]
        exact Set.inv_mem_inv.mpr (hKW h)
      simp [indicator_of_notMem hOutside]
    · simp [indicator_of_notMem hχK]
  rw [U.inner_map_map, L2.inner_def] at hUtf
  refine (integral_congr_ae (hg.mono fun x hx ↦ ?_)).trans hUtf
  rw [RCLike.inner_apply, starRingEnd_apply, hx, mul_assoc, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- Evaluation gives the canonical topological group isomorphism with the double dual. -/
theorem pontryaginDual_bidual :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),
      ∀ x χ, e x χ = χ x := by
  let e := pontryaginDual_eval (G := G)
  have hEmb := isClosedEmbedding_pontryaginDual_eval (G := G)
  have hSurj : Function.Surjective e := by
    intro η
    by_contra hη
    -- Choose a transform that vanishes on the translate of the evaluation image by η⁻¹.
    let V := ((η * ·) ⁻¹' Set.range e)ᶜ
    have hV : V ∈ 𝓝 (1 : PontryaginDual (PontryaginDual G)) :=
      (hEmb.isClosed_range.preimage (continuous_const.mul continuous_id)).isOpen_compl.mem_nhds
        (by simpa [V] using hη)
    let : MeasurableSpace (PontryaginDual G) := borel _
    have : BorelSpace (PontryaginDual G) := ⟨rfl⟩
    obtain ⟨ν, hν, hReg, hZero⟩ := exists_pontryaginDual_localized_integral hV
    have hTest (x : G) : ∫ χ, (η⁻¹ χ : ℂ) * (χ x : ℂ) ∂ν = 0 := by
      have hx : η⁻¹ * e x ∉ V := by simp [V]
      exact hZero _ hx
    have hz := pontryaginDual_integral_mul_eq_zero ν η⁻¹ hTest η
    have hProd (χ : PontryaginDual G) : (η⁻¹ χ : ℂ) * (η χ : ℂ) = 1 := by
      rw [← Circle.coe_mul]
      change ((η⁻¹ * η) χ : ℂ) = 1
      rw [inv_mul_cancel, PontryaginDual.one_apply, Circle.coe_one]
    simp [hProd] at hz
  let equiv := MulEquiv.ofBijective e.toMonoidHom ⟨hEmb.injective, hSurj⟩
  have hOpen := hEmb.isInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  exact ⟨equiv.toContinuousMulEquiv (fun _ ↦
    (hOpen.isQuotientMap e.continuous hSurj).isCoinducing.isOpen_preimage),
    fun _ _ ↦ rfl⟩

end Pontryagin

end Sol_LCAGroup_pontryagin_duality

open Sol_LCAGroup_pontryagin_duality in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),
      ∀ (x : G) (χ : PontryaginDual G), e x χ = χ x :=
  pontryaginDual_bidual
