-- Prove2me | solution 1 for LCAGroup.plancherel
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:55:40.608407+00:00
-- url     : https://prove2.me/submissions/05e73de0-c283-4a08-a15b-f0f5cff1cde5

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_PlancherelMeasure

open MeasureTheory Topology

set_option autoImplicit false

/-!
# Plancherel theorem for locally compact abelian groups

The argument follows the proof in the open formalization `mccorvie/riemann-masullo`
(Apache-2.0), files `ForMathlib/Topology/Algebra/PontryaginDual/Separation.lean`,
`ForMathlib/MeasureTheory/Integral/{ProdRegular,Bochner/Regular}.lean`,
`ForMathlib/MeasureTheory/Measure/RegularDomination.lean`,
`ForMathlib/MeasureTheory/Function/ContinuousMapDense.lean` and
`AppD_SchwartzBruhat/Sec1a.lean`, adapted to this version of Mathlib.

* Part 1 (`section Bochner`): for a strongly continuous unitary representation `U` of `G` and a
  vector `v`, the coefficient `g ↦ ⟪v, U g v⟫` is the Fourier–Stieltjes transform of a finite
  regular measure on the dual (Gelfand duality for the double commutant + Riesz–Markov–Kakutani).
* Part 2: measure-theoretic and Fourier-analytic auxiliary lemmas.
* Part 3 (`section Plancherel`): construction and uniqueness of the Plancherel measure, and the
  unitary extension of the Fourier transform.
-/

namespace Sol_LCAGroup_plancherel

noncomputable section

open Filter Set RiemannMasullo
open scoped ENNReal NNReal

section Bochner

open WeakDual

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

section Translation

variable [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]

/-- The left regular action on `Lᵖ` by precomposition with inverse translation. -/
def haarTranslation (p : ℝ≥0∞) [Fact (1 ≤ p)] : G →* (Lp ℂ p μ →L[ℂ] Lp ℂ p μ) where
  toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (g⁻¹ * ·)
    (measurePreserving_mul_left μ g⁻¹)).toContinuousLinearMap
  map_one' := ContinuousLinearMap.ext fun f ↦ by
    change Lp.compMeasurePreserving ((1 : G)⁻¹ * ·) _ f = f
    simpa only [inv_one, one_mul, ← Function.id_def] using Lp.compMeasurePreserving_id_apply f
  map_mul' g h := ContinuousLinearMap.ext fun f ↦ by
    have hcomp : (fun x : G ↦ (g * h)⁻¹ * x) = (h⁻¹ * ·) ∘ (g⁻¹ * ·) := by
      ext x
      simp [mul_inv_rev, mul_assoc]
    change Lp.compMeasurePreserving ((g * h)⁻¹ * ·) _ f =
      Lp.compMeasurePreserving (g⁻¹ * ·) _ (Lp.compMeasurePreserving (h⁻¹ * ·) _ f)
    simp only [hcomp]
    exact Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left μ h⁻¹) (measurePreserving_mul_left μ g⁻¹)

omit [T2Space G] [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop] in
theorem haarTranslation_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : G) (f : Lp ℂ p μ) :
    ‖haarTranslation μ p g f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

omit [T2Space G] in
theorem haarTranslation_continuous (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp ℂ p μ) : Continuous fun g : G ↦ haarTranslation μ p g f := by
  have hg : Continuous fun g : G ↦ ContinuousMap.mulLeft (X := G) g⁻¹ :=
    (ContinuousMap.curry
      ⟨fun q : G × G ↦ q.1⁻¹ * q.2, continuous_fst.inv.mul continuous_snd⟩).continuous
  exact continuous_const.compMeasurePreservingLp hg _ hp

end Translation

section Averaging

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [μ.InnerRegularCompactLTTop]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* (H →L[ℂ] H)) (hU : ∀ g v, ‖U g v‖ = ‖v‖)
  (hc : ∀ v, Continuous fun g ↦ U g v)

omit [CommGroup G] [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure]
  [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem aestronglyMeasurableOn_of_finite_measure {f : G → H} (hf : Continuous f)
    {s : Set G} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    AEStronglyMeasurable f (μ.restrict s) := by
  choose K hKs hKc hKcl hμK using fun n : ℕ ↦
    hs.exists_isCompact_isClosed_sdiff_lt hμs (ε := (n + 1 : ℝ≥0∞)⁻¹) (by simp)
  have hnull : μ (s \ ⋃ n, K n) = 0 := by
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun n ↦ ?_)
    calc
      μ (s \ ⋃ n, K n) ≤ μ (s \ K n) :=
        measure_mono (sdiff_subset_sdiff_right (subset_iUnion K n))
      _ ≤ (n + 1 : ℝ≥0∞)⁻¹ := (hμK n).le
      _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
  have hae : (⋃ n, K n : Set G) =ᵐ[μ] s := by
    have hsub : s ≤ᵐ[μ] ⋃ n, K n := ae_le_set.2 hnull
    filter_upwards [hsub] with g hg
    exact propext ⟨fun h ↦ iUnion_subset hKs h, hg⟩
  rw [← Measure.restrict_congr_set hae, aestronglyMeasurable_iUnion_iff]
  exact fun n ↦ hf.continuousOn.aestronglyMeasurable_of_isCompact (hKc n) (hKcl n).measurableSet

include hU hc in
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] [CompleteSpace H] in
theorem integrable_weighted_orbit (f : Lp ℂ 1 μ) (v : H) :
    Integrable (fun g ↦ f g • U g v) μ := by
  have hf := L1.integrable_coeFn f
  have hfinite := hf.aefinStronglyMeasurable
  let s := hfinite.sigmaFiniteSet
  have horbit : AEStronglyMeasurable (fun g ↦ U g v) (μ.restrict s) := by
    let ν := μ.restrict s
    have : SigmaFinite ν := inferInstance
    have hspan (n : ℕ) : AEStronglyMeasurable (fun g ↦ U g v)
        (ν.restrict (spanningSets ν n)) :=
      aestronglyMeasurableOn_of_finite_measure ν (hc v)
        (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top ν n).ne
    change AEStronglyMeasurable _ ν
    rw [← Measure.restrict_univ (μ := ν), ← iUnion_spanningSets ν,
      aestronglyMeasurable_iUnion_iff]
    exact hspan
  refine (hf.norm.mul_const ‖v‖).mono' ?_ (.of_forall fun g ↦ by rw [norm_smul, hU])
  have hzero : AEStronglyMeasurable (fun g ↦ f g • U g v) (μ.restrict sᶜ) := by
    refine (aestronglyMeasurable_const (b := (0 : H))).congr ?_
    filter_upwards [hfinite.ae_eq_zero_compl] with g hg
    change (f : G → ℂ) g = 0 at hg
    rw [hg, zero_smul]
  change AEStronglyMeasurable ((f : G → ℂ) • fun g ↦ U g v) μ
  have hm := aestronglyMeasurable_union_iff.mpr
    ⟨hf.aestronglyMeasurable.restrict.smul horbit, hzero⟩
  simpa only [union_compl_self, Measure.restrict_univ] using hm

/-- Averaging the orbit of each vector gives a bounded operator depending continuously on
the integrable weight. -/
def averageOrbit : Lp ℂ 1 μ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun f v ↦ ∫ g, f g • U g v ∂μ)
      (fun f₁ f₂ v ↦ by
        rw [← integral_add (integrable_weighted_orbit μ U hU hc f₁ v)
          (integrable_weighted_orbit μ U hU hc f₂ v)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f₁ f₂] with g hg
        rw [hg, Pi.add_apply, add_smul])
      (fun c f v ↦ by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with g hg
        rw [hg, Pi.smul_apply, smul_eq_mul, mul_smul])
      (fun f v w ↦ by
        rw [← integral_add (integrable_weighted_orbit μ U hU hc f v)
          (integrable_weighted_orbit μ U hU hc f w)]
        simp_rw [map_add, smul_add])
      (fun c f v ↦ by rw [← integral_smul]; simp_rw [map_smul, smul_comm c]))
    1 fun f v ↦ by
      simp only [one_mul, L1.norm_eq_integral_norm, ← integral_mul_const]
      apply norm_integral_le_of_norm_le
      · exact (L1.integrable_coeFn f).norm.mul_const _
      · exact .of_forall fun g ↦ by rw [norm_smul, hU]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] [CompleteSpace H] in
theorem averageOrbit_apply (f : Lp ℂ 1 μ) (v : H) :
    averageOrbit μ U hU hc f v = ∫ g, f g • U g v ∂μ := rfl

omit [LocallyCompactSpace G] in
theorem averageOrbit_translate (f : Lp ℂ 1 μ) (g : G) :
    U g * averageOrbit μ U hU hc f = averageOrbit μ U hU hc (haarTranslation μ 1 g f) := by
  ext v
  rw [mul_apply_eq_comp, averageOrbit_apply, averageOrbit_apply,
    ← (U g).integral_comp_comm (integrable_weighted_orbit μ U hU hc f v)]
  calc
    _ = ∫ k, f (g⁻¹ * (g * k)) • U (g * k) v ∂μ := by
      simp [map_mul, mul_apply_eq_comp]
    _ = ∫ k, f (g⁻¹ * k) • U k v ∂μ :=
      integral_mul_left_eq_self (fun k ↦ f (g⁻¹ * k) • U k v) g
    _ = _ := integral_congr_ae <| by
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left μ g⁻¹)]
        with k hk
      exact congrArg (· • U k v) hk.symm

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] in
theorem averageOrbit_commutes (f : Lp ℂ 1 μ) (T : H →L[ℂ] H)
    (hT : ∀ g, U g * T = T * U g) :
    T * averageOrbit μ U hU hc f = averageOrbit μ U hU hc f * T := by
  ext v
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    averageOrbit_apply, averageOrbit_apply,
    ← T.integral_comp_comm (integrable_weighted_orbit μ U hU hc f v)]
  simp only [map_smul]
  exact integral_congr_ae <| .of_forall fun g ↦
    congrArg (fun S : H →L[ℂ] H ↦ f g • S v) (hT g).symm

omit [IsTopologicalGroup G] in
/-- Averages of norm at most one approximate each vector. -/
theorem exists_averageOrbit_close (v : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Lp ℂ 1 μ, ‖f‖ ≤ 1 ∧ dist (averageOrbit μ U hU hc f v) v < ε := by
  let s : Set G := {g | ‖U g v - v‖ < ε / 2}
  have hs : s ∈ 𝓝 (1 : G) := by
    have ht : ContinuousAt (fun g ↦ ‖U g v - v‖) (1 : G) :=
      ((hc v).sub continuous_const).norm.continuousAt
    exact ht (by simpa using Iio_mem_nhds (half_pos hε))
  obtain ⟨K, ⟨hKnhds, hK⟩, hKs⟩ := (compact_basis_nhds (1 : G)).mem_iff.mp hs
  have hKpos : 0 < μ.real K := ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds hKnhds).ne'
    hK.measure_lt_top.ne
  let f : G → ℂ := K.indicator (fun _ ↦ 1)
  have hf : Integrable f μ :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hfi : ∫ g in K, U g v ∂μ = averageOrbit μ U hU hc (hf.toL1 f) v := by
    rw [averageOrbit_apply, ← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toL1] with g hg
    change K.indicator (fun x ↦ U x v) g = (hf.toL1 f : G → ℂ) g • U g v
    rw [hg]
    by_cases hgK : g ∈ K <;> simp [f, hgK]
  let a : ℂ := (μ.real K : ℂ)⁻¹
  have hfNorm : ‖hf.toL1 f‖ = μ.real K := by
    rw [L1.norm_eq_integral_norm]
    have h : (fun g ↦ ‖hf.toL1 f g‖) =ᵐ[μ] K.indicator (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [hf.coeFn_toL1] with g hg
      change hf.toL1 f g = f g at hg
      rw [hg]
      by_cases hgK : g ∈ K <;> simp [f, hgK]
    rw [integral_congr_ae h]
    exact integral_indicator_one hK.measurableSet
  refine ⟨a • hf.toL1 f, ?_, ?_⟩
  · rw [norm_smul, hfNorm]
    simp [a, abs_of_pos hKpos, hKpos.ne']
  have hint : IntegrableOn (fun g ↦ U g v) K μ := by
    apply (integrableOn_const (C := ‖v‖) hK.measure_lt_top.ne).mono'
      ((hc v).continuousOn.aestronglyMeasurable_of_isCompact hK hK.measurableSet)
    exact .of_forall fun g ↦ (hU g v).le
  have hnorm : ‖∫ g in K, U g v - v ∂μ‖ ≤ μ.real K * (ε / 2) :=
    (mul_comm (ε / 2) (μ.real K)) ▸
      norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun g hg ↦ (hKs hg).le)
  have havg : averageOrbit μ U hU hc (a • hf.toL1 f) v - v =
      a • (∫ g in K, U g v - v ∂μ) := by
    rw [map_smul, smul_apply, ← hfi, integral_sub hint
      (integrableOn_const hK.measure_lt_top.ne), setIntegral_const, smul_sub,
      ← Complex.coe_smul, smul_smul]
    simp [a, hKpos.ne']
  rw [dist_eq_norm, havg, norm_smul]
  refine (mul_le_mul_of_nonneg_left hnorm (norm_nonneg a)).trans_lt ?_
  simp [a, abs_of_pos hKpos, hKpos.ne', half_lt_self hε]

omit [IsTopologicalGroup G] in
theorem averageOrbit_dense (v : H) :
    v ∈ closure (range fun f ↦ averageOrbit μ U hU hc f v) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨f, -, hf⟩ := exists_averageOrbit_close μ U hU hc v hε
  exact ⟨_, mem_range_self f, by rwa [dist_comm]⟩

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.IsHaarMeasure] in
/-- Haar averaging is contractive as a map from integrable weights to operators. -/
theorem norm_averageOrbit_le (f : Lp ℂ 1 μ) : ‖averageOrbit μ U hU hc f‖ ≤ ‖f‖ := by
  have h : ‖averageOrbit μ U hU hc‖ ≤ 1 := by
    unfold averageOrbit
    exact LinearMap.mkContinuous₂_norm_le _ zero_le_one _
  simpa using (averageOrbit μ U hU hc).le_of_opNorm_le h f

end Averaging

section Spectrum

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [μ.InnerRegularCompactLTTop]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* (H →L[ℂ] H)) (hU : ∀ g v, ‖U g v‖ = ‖v‖)
  (hc : ∀ v, Continuous fun g ↦ U g v)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
include hU in
/-- The adjoint of a unitary group action is the action of the inverse. -/
theorem unitary_apply_star (g : G) : star (U g) = U g⁻¹ := by
  have hh := (U g).norm_map_iff_adjoint_comp_self.mp (hU g)
  change star (U g) * U g = 1 at hh
  calc
    star (U g) = (star (U g) * U g) * U g⁻¹ := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = U g⁻¹ := by rw [hh, one_mul]

include μ hU hc in
open scoped IsMulCommutative Pointwise in
/-- The double commutant of the representation is commutative and contains
the representation and all its Haar averages. -/
theorem exists_commutative_algebra_with_averages :
    ∃ A : StarSubalgebra ℂ (H →L[ℂ] H), IsClosed (A : Set (H →L[ℂ] H)) ∧
      IsMulCommutative A ∧ (∀ g, U g ∈ A) ∧
      (∀ f, averageOrbit μ U hU hc f ∈ A) := by
  let B := H →L[ℂ] H
  let S : Set B := range U
  let A := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set B)
  have hS : S ∪ star S = S := by
    apply union_eq_self_of_subset_right
    intro T hT
    obtain ⟨g, hg⟩ : star T ∈ range U := hT
    exact ⟨g⁻¹, by rw [← unitary_apply_star U hU, hg, star_star]⟩
  have hA : (A : Set B) = S.centralizer.centralizer := by
    rw [StarSubalgebra.coe_centralizer_centralizer, hS]
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := fun _ ha _ hb ↦ by
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := hb
    rw [← map_mul, ← map_mul, mul_comm g k]
  have hCommA : IsMulCommutative A := .of_setLike_mul_comm fun a ha b hb ↦ by
    change a ∈ (A : Set B) at ha
    change b ∈ (A : Set B) at hb
    rw [hA] at ha hb
    exact Set.centralizer_centralizer_comm_of_comm hcomm _ ha _ hb
  refine ⟨A, hA ▸ Set.isClosed_centralizer _, hCommA, fun g ↦ ?_, fun f ↦ ?_⟩
  · change U g ∈ (A : Set B)
    rw [hA]
    exact Set.subset_centralizer_centralizer (mem_range_self _)
  · change averageOrbit μ U hU hc f ∈ (A : Set B)
    rw [hA]
    intro T hT
    exact averageOrbit_commutes μ U hU hc f T (fun g ↦ hT (U g) (mem_range_self g))

end Spectrum

open scoped CompactlySupported in
/-- A positive functional on complex continuous functions on a compact space is integrated
against a finite regular measure. Apply real Riesz–Markov to its real part. -/
theorem exists_measure_of_positive_functional
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (L : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ q, 0 ≤ (L (star q * q)).re)
    (hStar : ∀ q, L (star q) = star (L q)) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧ σ.Regular ∧
      ∀ q : C(X, ℂ), (∫ x, q x ∂σ) = L q := by
  let toComplex (f : C_c(X, ℝ)) : C(X, ℂ) :=
    ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ (L (toComplex f)).re
      map_add' := fun f g ↦ by
        have h : toComplex (f + g) = toComplex f + toComplex g := by
          ext x
          exact Complex.ofReal_add _ _
        rw [h, map_add, Complex.add_re]
      map_smul' := fun r f ↦ by
        have h : toComplex (r • f) = (r : ℂ) • toComplex f := by
          ext x
          exact Complex.ofReal_mul _ _
        rw [h, map_smul, smul_eq_mul]
        simp [Complex.mul_re, smul_eq_mul]
      monotone' := fun f g hfg ↦ by
        let root : C(X, ℂ) := ⟨fun x ↦ (Real.sqrt (g x - f x) : ℂ),
          Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
            (g.continuous.sub f.continuous))⟩
        have h : toComplex g - toComplex f = star root * root := by
          ext x
          change (g x : ℂ) - (f x : ℂ) =
            star ((Real.sqrt (g x - f x) : ℝ) : ℂ) * (Real.sqrt (g x - f x) : ℂ)
          rw [Complex.star_def, Complex.conj_ofReal, ← sq, ← Complex.ofReal_pow,
            Real.sq_sqrt (sub_nonneg.mpr (hfg x)), Complex.ofReal_sub]
        have hpos := hL root
        rw [← h, map_sub, Complex.sub_re] at hpos
        exact sub_nonneg.mp hpos }
  let σ := RealRMK.rieszMeasure Λ
  have hfinite : IsFiniteMeasure σ := ⟨isCompact_univ.measure_lt_top⟩
  refine ⟨σ, hfinite, inferInstance, fun q ↦ ?_⟩
  have hRe (q : C(X, ℂ)) : (∫ x, q x ∂σ).re = (L q).re := by
    let f : C_c(X, ℝ) := ⟨⟨fun x ↦ (q x).re, Complex.continuous_re.comp q.continuous⟩,
      HasCompactSupport.of_compactSpace _⟩
    have hInt := Complex.reCLM.integral_comp_comm
      (q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        (μ := σ))
    calc
      _ = ∫ x, f x ∂σ := hInt.symm
      _ = (L (toComplex f)).re := RealRMK.integral_rieszMeasure Λ f
      _ = _ := by
        have h : (2 : ℂ) • toComplex f = star q + q := by
          ext x
          change 2 * ((q x).re : ℂ) = star (q x) + q x
          simpa only [Complex.star_def, add_comm, Complex.ofReal_mul, Complex.ofReal_ofNat]
            using (Complex.add_conj (q x)).symm
        have hh := congrArg (fun p ↦ (L p).re) h
        simp [map_smul, smul_eq_mul, Complex.mul_re, hStar] at hh
        linarith
  apply Complex.ext (hRe q)
  have h := hRe (Complex.I • q)
  simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, map_smul,
    Complex.I_mul_re, neg_inj] at h
  exact h

open scoped InnerProductSpace in
/-- The vector functional on a commutative algebra of operators has a finite regular
representing measure on its Gelfand spectrum. -/
theorem exists_spectral_measure {A H : Type*} [CommCStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace (characterSpace ℂ A)] [BorelSpace (characterSpace ℂ A)]
    (j : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    ∃ σ : Measure (characterSpace ℂ A), IsFiniteMeasure σ ∧ σ.Regular ∧
      ∀ a : A, (∫ ω, ω a ∂σ) = ⟪v, j a v⟫_ℂ := by
  let Φ := gelfandStarTransform A
  let T := j.comp Φ.symm.toStarAlgHom
  let L : C(characterSpace ℂ A, ℂ) →ₗ[ℂ] ℂ :=
    (innerSL ℂ v).toLinearMap.comp
      ((ContinuousLinearMap.apply ℂ H v).toLinearMap.comp T.toLinearMap)
  have hL (q : C(characterSpace ℂ A, ℂ)) : L q = ⟪v, T q v⟫_ℂ := rfl
  obtain ⟨σ, hFinite, hRegular, hσ⟩ := exists_measure_of_positive_functional L
    (fun q ↦ by
      rw [hL, map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      change 0 ≤ (((‖T q v‖ : ℝ) : ℂ) ^ 2).re
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      positivity)
    (fun q ↦ by
      rw [hL, hL, map_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right, Complex.star_def, inner_conj_symm])
  refine ⟨σ, hFinite, hRegular, fun a ↦ ?_⟩
  change (∫ ω, Φ a ω ∂σ) = _
  rw [hσ, hL]
  change ⟪v, j (Φ.symm (Φ a)) v⟫_ℂ = _
  rw [StarAlgEquiv.symm_apply_apply]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- On the union of the sets where at least one norm-continuous translate is nonzero,
the spectral characters restrict continuously to characters of the group. -/
theorem exists_continuous_dual_of_spectrum {A : Type*} [CommCStarAlgebra A]
    (V : G →* A) (hStar : ∀ g, star (V g) = V g⁻¹) {ι : Type*}
    (a : ι → A) (hTranslate : ∀ i, Continuous fun g ↦ V g * a i) :
    ∃ χ : {ω : characterSpace ℂ A | ∃ i, ω (a i) ≠ 0} → PontryaginDual G,
      Continuous χ ∧ ∀ ω g, (χ ω g : ℂ) = ω.1 (V g) := by
  let S : Set (characterSpace ℂ A) := {ω | ∃ i, ω (a i) ≠ 0}
  let Φ := gelfandTransform ℂ A
  let z (ω : S) (g : G) := ω.1 (V g)
  have hn (ω : S) (g : G) : ‖z ω g‖ = 1 := by
    have h : star (ω.1 (V g)) * ω.1 (V g) = 1 := by
      rw [← map_star, ← map_mul, hStar, ← map_mul, inv_mul_cancel, map_one, map_one]
    have hNorm := congrArg norm h
    rw [norm_mul, norm_star, norm_one, ← sq] at hNorm
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (hNorm.trans (by norm_num))
  have hz : Continuous (Function.uncurry z) := by
    rw [continuous_iff_continuousAt]
    intro p
    obtain ⟨i, hi⟩ := p.1.2
    have hden : Continuous fun q : S × G ↦ Φ (a i) q.1.1 :=
      (Φ (a i)).continuous.comp (continuous_subtype_val.comp continuous_fst)
    have hnum : Continuous fun q : S × G ↦ Φ (V q.2 * a i) q.1.1 :=
      continuous_eval.comp (((gelfandTransform_isometry A).continuous.comp
        ((hTranslate i).comp continuous_snd)).prodMk
        (continuous_subtype_val.comp continuous_fst))
    refine (hnum.continuousAt.div hden.continuousAt hi).congr_of_eventuallyEq ?_
    filter_upwards [hden.continuousAt.eventually_ne hi] with q hq
    change q.1.1 (V q.2) = q.1.1 (V q.2 * a i) / q.1.1 (a i)
    change q.1.1 (a i) ≠ 0 at hq
    rw [map_mul, mul_div_cancel_right₀ _ hq]
  let χ (ω : S) : PontryaginDual G :=
    { toFun g := ⟨z ω g, mem_sphere_zero_iff_norm.mpr (hn ω g)⟩
      map_one' := Subtype.ext (by change ω.1 (V 1) = 1; rw [map_one, map_one])
      map_mul' g k := Circle.ext (by
        change ω.1 (V (g * k)) = ω.1 (V g) * ω.1 (V k)
        rw [map_mul, map_mul])
      continuous_toFun := (hz.comp (continuous_const.prodMk continuous_id)).subtype_mk _ }
  exact ⟨χ, ContinuousMonoidHom.continuous_of_continuous_uncurry χ (hz.subtype_mk _),
    fun _ _ ↦ rfl⟩

open scoped InnerProductSpace in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- If the operators with norm-continuous translates approximate the vector,
its spectral measure is carried by the open set on which they detect continuous
characters of the group. -/
theorem exists_dual_measure_of_operators {A H : Type*} [CommCStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (j : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (V : G →* A) (hStar : ∀ g, star (V g) = V g⁻¹)
    {ι : Type*} (a : ι → A) (hTranslate : ∀ i, Continuous fun g ↦ V g * a i)
    (hApprox : ∀ ε > 0, ∃ i, ‖j (a i) v - v‖ < ε) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ g, (∫ χ, (χ g : ℂ) ∂ρ) = ⟪v, j (V g) v⟫_ℂ := by
  let X := characterSpace ℂ A
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let S : Set X := {ω | ∃ i, ω (a i) ≠ 0}
  have hOpen : IsOpen S := by
    rw [show S = ⋃ i, {ω : X | ω (a i) ≠ 0} by ext; simp [S]]
    exact isOpen_iUnion fun i ↦ isOpen_ne_fun (gelfandTransform ℂ A (a i)).continuous continuous_const
  obtain ⟨σ, hFinite, hRegular, hσ⟩ := exists_spectral_measure j v
  have hBound (b : A) : (∫ ω, ‖ω b‖ ^ 2 ∂σ) = ‖j b v‖ ^ 2 := by
    have hInt : Integrable (fun ω : X ↦ ω (star b * b)) σ :=
      (gelfandTransform ℂ A (star b * b)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      _ = ∫ ω, (ω (star b * b)).re ∂σ := by
        apply integral_congr_ae
        exact .of_forall fun ω ↦ by
          change ‖ω b‖ ^ 2 = (ω (star b * b)).re
          rw [map_mul, map_star, mul_comm, Complex.star_def, Complex.mul_conj,
            Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = (⟪v, j (star b * b) v⟫_ℂ).re := by
        change (∫ ω, Complex.reCLM (ω (star b * b)) ∂σ) = _
        rw [Complex.reCLM.integral_comp_comm hInt, hσ, Complex.reCLM_apply]
      _ = _ := by
        rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
        change (((‖j b v‖ : ℝ) : ℂ) ^ 2).re = _
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hMass : σ.real Sᶜ ≤ 0 := by
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    obtain ⟨i, hi⟩ := hApprox (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    let b := a i - 1
    have hInt : Integrable (fun ω : X ↦ ‖ω b‖ ^ 2) σ :=
      ((gelfandTransform ℂ A b).continuous.norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hInd : Sᶜ.indicator (fun _ ↦ (1 : ℝ)) ≤ fun ω : X ↦ ‖ω b‖ ^ 2 := by
      intro ω
      by_cases hω : ω ∈ Sᶜ
      · have hz : ω (a i) = 0 := by
          by_contra hn
          exact hω ⟨i, hn⟩
        simp [hω, b, map_sub, hz]
      · simp [hω]
    have hle := integral_mono
      ((integrableOn_const (C := (1 : ℝ)) (measure_ne_top σ Sᶜ)).integrable_indicator
        hOpen.measurableSet.compl) hInt hInd
    change (∫ ω, Sᶜ.indicator (1 : X → ℝ) ω ∂σ) ≤ _ at hle
    rw [integral_indicator_one hOpen.measurableSet.compl, hBound] at hle
    refine hle.trans ?_
    rw [show j b v = j (a i) v - v by simp [b], zero_add, ← Real.sq_sqrt hε.le]
    gcongr
  have hFull : σ.restrict S = σ := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply ae_iff.mpr
    exact ((ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hMass ENNReal.toReal_nonneg)).resolve_right (measure_ne_top σ _)
  obtain ⟨χ, hχ, hEval⟩ := exists_continuous_dual_of_spectrum V hStar a hTranslate
  let τ : Measure S := σ.comap Subtype.val
  have hτ : IsFiniteMeasure τ := ⟨by
    rw [hOpen.isOpenEmbedding_subtypeVal.measurableEmbedding.comap_apply]
    exact measure_lt_top σ _⟩
  let : σ.InnerRegular := inferInstance
  let : τ.InnerRegular := Measure.InnerRegular.comap' σ hOpen.isOpenEmbedding_subtypeVal
  let ρ := Measure.map χ τ
  let : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map τ χ
  let : ρ.InnerRegular := Measure.InnerRegular.map_of_continuous hχ
  let : ρ.WeaklyRegular :=
    Measure.InnerRegularWRT.weaklyRegular_of_finite ρ
      Measure.InnerRegular.innerRegularWRT_isClosed_isOpen
  refine ⟨ρ, inferInstance, ⟨Measure.InnerRegular.innerRegular.mono
    (fun _ h ↦ h.measurableSet) (fun _ h ↦ h)⟩, fun g ↦ ?_⟩
  have hCont : Continuous fun ψ : PontryaginDual G ↦ (ψ g : ℂ) :=
    continuous_subtype_val.comp
      ((continuous_eval_const (F := C(G, Circle)) g).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous)
  calc
    _ = ∫ ω : S, ω.1 (V g) ∂τ := by
      rw [integral_map hχ.measurable.aemeasurable hCont.aestronglyMeasurable]
      exact integral_congr_ae (.of_forall fun ω ↦ hEval ω g)
    _ = ∫ ω, ω (V g) ∂σ := by
      exact (integral_subtype_comap hOpen.measurableSet (fun ω : X ↦ ω (V g))).trans
        (by rw [hFull])
    _ = _ := hσ (V g)

open scoped IsMulCommutative InnerProductSpace in
/-- Haar averaging supplies the norm-continuous translates needed by the spectral
representation of a coefficient of a strongly continuous unitary action. -/
theorem exists_dual_measure_of_unitary
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.InnerRegularCompactLTTop] [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : G →* (H →L[ℂ] H)) (hU : ∀ g v, ‖U g v‖ = ‖v‖)
    (hc : ∀ v, Continuous fun g ↦ U g v) (v : H) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ g, (∫ χ, (χ g : ℂ) ∂ρ) = ⟪v, U g v⟫_ℂ := by
  obtain ⟨A, hClosed, hComm, hGroup, hAverage⟩ :=
    exists_commutative_algebra_with_averages μ U hU hc
  let : IsClosed (A : Set (H →L[ℂ] H)) := hClosed
  let : IsMulCommutative A := hComm
  let : CommCStarAlgebra A := { }
  let V : G →* A := U.codRestrict A.toSubmonoid hGroup
  let a (f : Lp ℂ 1 μ) : A := ⟨averageOrbit μ U hU hc f, hAverage f⟩
  have hTranslate (f : Lp ℂ 1 μ) : Continuous fun g ↦ V g * a f := by
    have h : Continuous fun g ↦ U g * averageOrbit μ U hU hc f := by
      simp_rw [averageOrbit_translate]
      exact (averageOrbit μ U hU hc).continuous.comp
        (haarTranslation_continuous μ 1 ENNReal.one_ne_top f)
    exact h.subtype_mk _
  have hApprox (ε : ℝ) (hε : 0 < ε) : ∃ f, ‖A.subtype (a f) v - v‖ < ε := by
    obtain ⟨f, -, hf⟩ := exists_averageOrbit_close μ U hU hc v hε
    refine ⟨f, ?_⟩
    change ‖averageOrbit μ U hU hc f v - v‖ < ε
    simpa only [dist_eq_norm] using hf
  exact exists_dual_measure_of_operators A.subtype v V
    (fun g ↦ Subtype.ext (unitary_apply_star U hU g)) a hTranslate hApprox

/-- The autocorrelation of a square-integrable function is the Fourier–Stieltjes
transform of a finite regular positive measure on the Pontryagin dual. -/
theorem exists_haar_autocorrelation_measure
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.InnerRegularCompactLTTop] [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] {f : G → ℂ} (hf : MemLp f 2 μ) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ x, (∫ χ, (χ x : ℂ) ∂ρ) = ∫ y, f y * star (f (x⁻¹ * y)) ∂μ := by
  let T := haarTranslation μ 2
  let U := T.comp (invMonoidHom (α := G))
  let v := hf.toLp f
  obtain ⟨ρ, hFinite, hRegular, hρ⟩ := exists_dual_measure_of_unitary μ U
    (fun g w ↦ haarTranslation_norm μ 2 g⁻¹ w)
    (fun w ↦ (haarTranslation_continuous μ 2 (by simp) w).comp continuous_inv) v
  refine ⟨ρ, hFinite, hRegular, fun x ↦ (hρ x).trans ?_⟩
  have hTx : ⇑(U x v) =ᵐ[μ] fun y ↦ f ((x⁻¹)⁻¹ * y) :=
    (Lp.coeFn_compMeasurePreserving v (measurePreserving_mul_left μ (x⁻¹)⁻¹)).trans
      ((measurePreserving_mul_left μ (x⁻¹)⁻¹).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)
  rw [L2.inner_def, ← integral_mul_left_eq_self (μ := μ)
    (fun y ↦ f y * star (f (x⁻¹ * y))) x]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hTx] with y hy hxy
  rw [hy, hxy, inv_inv, inv_mul_cancel_left]
  exact RCLike.inner_apply (f y) (f (x * y))

end Bochner

open scoped ZeroAtInfty

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


end Fourier

section ProdRegular

open scoped Pointwise

/-- A finite regular measure is carried by a countable union of compact sets. -/
theorem exists_isSigmaCompact_ae_mem
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] [ν.Regular] :
    ∃ S : Set X, IsSigmaCompact S ∧ ∀ᵐ x ∂ν, x ∈ S := by
  obtain ⟨ε, -, hε, hlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1)
  choose K _ hK hSmall using fun n ↦ MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top ν univ) (hε n).1.ne'
  let S := ⋃ n, K n
  refine ⟨S, ⟨K, hK, rfl⟩, ?_⟩
  rw [ae_iff]
  change ν Sᶜ = 0
  by_contra h
  have ht : ∀ᶠ n in atTop, ε n < ν Sᶜ := hlim (Iio_mem_nhds (pos_iff_ne_zero.mpr h))
  obtain ⟨n, hn⟩ := ht.exists
  have hs : ν Sᶜ ≤ ν (univ \ K n) := measure_mono <|
    fun x hx ↦ ⟨mem_univ x, fun hk ↦ hx (mem_iUnion.mpr ⟨n, hk⟩)⟩
  exact (hs.trans_lt (hSmall n)).not_gt hn

/-- A continuous kernel on a product, set to zero outside a product of σ-compact sets, is
measurable for the product σ-algebra. -/
theorem measurable_indicator_prod_of_isSigmaCompact
    {X Y E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [Zero E] [MeasurableSpace E] [BorelSpace E]
    {k : X × Y → E} (hk : Continuous k) {S : Set X} {T : Set Y}
    (hS : IsSigmaCompact S) (hT : IsSigmaCompact T) :
    Measurable ((S ×ˢ T).indicator k) := by
  classical
  obtain ⟨K, hK, rfl⟩ := hS
  obtain ⟨L, hL, rfl⟩ := hT
  have hRect (n m : ℕ) (U : Set E) (hU : MeasurableSet U) :
      MeasurableSet ((K n ×ˢ L m) ∩ k ⁻¹' U) := by
    let e : K n × L m → X × Y := Prod.map Subtype.val Subtype.val
    have he : MeasurableEmbedding e :=
      (MeasurableEmbedding.subtype_coe (hK n).isClosed.measurableSet).prodMap
        (MeasurableEmbedding.subtype_coe (hL m).isClosed.measurableSet)
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    let : CompactSpace (L m) := isCompact_iff_compactSpace.mp (hL m)
    have hc : Continuous (k ∘ e) :=
      hk.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
    have hm : Measurable (k ∘ e) := (HasCompactSupport.of_compactSpace _).measurable_of_prod hc
    have hr : range e = K n ×ˢ L m := by
      ext ⟨x, y⟩
      constructor
      · rintro ⟨⟨a, b⟩, heq⟩
        rw [← heq]
        exact ⟨a.property, b.property⟩
      · intro h
        exact ⟨(⟨x, h.1⟩, ⟨y, h.2⟩), rfl⟩
    have heq : e '' ((k ∘ e) ⁻¹' U) = (K n ×ˢ L m) ∩ k ⁻¹' U := by
      rw [preimage_comp, image_preimage_eq_inter_range, hr, inter_comm]
    rw [← heq]
    exact he.measurableSet_image' (hm hU)
  let R := (⋃ n, K n) ×ˢ (⋃ m, L m)
  have hR : MeasurableSet R := (MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet).prod
    (MeasurableSet.iUnion fun m ↦ (hL m).isClosed.measurableSet)
  intro U hU
  have hOn : MeasurableSet (R ∩ k ⁻¹' U) := by
    have heq : R ∩ k ⁻¹' U = ⋃ n, ⋃ m, ((K n ×ˢ L m) ∩ k ⁻¹' U) := by
      simp only [R, ← iUnion_prod, iUnion_inter, iUnion_prod']
    rw [heq]
    exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun m ↦ hRect n m U hU
  by_cases h : (0 : E) ∈ U
  · convert hOn.union hR.compl using 1
    ext p
    by_cases hp : p ∈ R <;> change ((R.indicator k p ∈ U) ↔ _)
    all_goals simp [hp, h]
  · convert hOn using 1
    ext p
    by_cases hp : p ∈ R <;> change ((R.indicator k p ∈ U) ↔ _)
    all_goals simp [hp, h]

/-- Haar averaging of a translated nonnegative weight can be computed by integrating
over Haar first. A σ-compact carrier for the weight suffices for Tonelli. -/
theorem lintegral_lintegral_mul_translate
    {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (η τ : Measure H) [η.IsHaarMeasure] [IsFiniteMeasure τ] [τ.Regular]
    {w v : H → ℝ≥0} (hw : Continuous w) (hv : Continuous v)
    {U : Set H} (hU : IsSigmaCompact U) (hW : Function.support w ⊆ U) :
    (∫⁻ a, ∫⁻ b, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂τ ∂η) =
      (∫⁻ a, (w a : ℝ≥0∞) ∂η) * (∫⁻ b, (v b : ℝ≥0∞) ∂τ) := by
  obtain ⟨S, hS, hτ⟩ := exists_isSigmaCompact_ae_mem τ
  obtain ⟨K, hK, rfl⟩ := hU
  obtain ⟨L, hL, rfl⟩ := hS
  let T : Set H := ⋃ p : ℕ × ℕ, K p.1 * (L p.2)⁻¹
  have hC (p : ℕ × ℕ) : IsCompact (K p.1 * (L p.2)⁻¹) := (hK p.1).mul (hL p.2).inv
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun p ↦ (hC p).isClosed.measurableSet
  obtain ⟨B, hB, hBT⟩ := isSigmaCompact_iUnion_of_isCompact _ hC
  let : SigmaFinite (η.restrict T) := by
    refine ⟨⟨⟨fun n ↦ B n ∪ Tᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hB n).isClosed.measurableSet.union hTm.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hB n).measure_lt_top
    · rw [← iUnion_union, hBT]
      exact union_compl_self T
  have hzero (a b : H) (ha : a ∉ T) (hb : b ∈ ⋃ n, L n) : w (a * b) = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hW hne)
    obtain ⟨m, hm⟩ := mem_iUnion.mp hb
    exact ha (mem_iUnion.mpr ⟨(n, m), a * b, hn, b⁻¹, by simpa, mul_inv_cancel_right a b⟩)
  let k (p : H × H) : ℝ≥0∞ := ((w (p.1 * p.2) * v p.2 : ℝ≥0) : ℝ≥0∞)
  have hk : Continuous k := ENNReal.continuous_coe.comp
    ((hw.comp (continuous_fst.mul continuous_snd)).mul (hv.comp continuous_snd))
  let q := (T ×ˢ (⋃ n, L n)).indicator k
  have hq : Measurable q :=
    measurable_indicator_prod_of_isSigmaCompact hk ⟨B, hB, hBT⟩ ⟨L, hL, rfl⟩
  have hrow (a : H) (ha : a ∈ T) :
      (∫⁻ b, q (a, b) ∂τ) = ∫⁻ b, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂τ := by
    apply lintegral_congr_ae
    filter_upwards [hτ] with b hb
    simpa only [q, k, ENNReal.coe_mul] using
      (indicator_of_mem (s := T ×ˢ (⋃ n, L n)) (a := (a, b)) ⟨ha, hb⟩ k)
  have hcol (b : H) (hb : b ∈ ⋃ n, L n) :
      (∫⁻ a in T, q (a, b) ∂η) = ∫⁻ a, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂η := by
    rw [← setLIntegral_eq_of_support_subset (s := T)
      (f := fun a ↦ (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞)) (fun a ha ↦ by
        by_contra h
        exact ha (by simp [hzero a b h hb]))]
    apply setLIntegral_congr_fun hTm
    intro a ha
    simpa only [q, k, ENNReal.coe_mul] using
      (indicator_of_mem (s := T ×ˢ (⋃ n, L n)) (a := (a, b)) ⟨ha, hb⟩ k)
  calc
    _ = ∫⁻ a in T, ∫⁻ b, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂τ ∂η := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro a ha
      by_contra h
      exact ha ((lintegral_congr_ae (hτ.mono fun b hb ↦ by simp [hzero a b h hb])).trans
        (lintegral_zero))
    _ = ∫⁻ a in T, ∫⁻ b, q (a, b) ∂τ ∂η :=
      setLIntegral_congr_fun hTm fun a ha ↦ (hrow a ha).symm
    _ = ∫⁻ b, ∫⁻ a in T, q (a, b) ∂η ∂τ :=
      lintegral_lintegral_swap hq.aemeasurable
    _ = ∫⁻ b, ∫⁻ a, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂η ∂τ :=
      lintegral_congr_ae (hτ.mono hcol)
    _ = _ := by
      have hm : Measurable (fun a : H ↦ (w a : ℝ≥0∞)) :=
        (ENNReal.continuous_coe.comp hw).measurable
      have hinner (b : H) : (∫⁻ a, (w (a * b) : ℝ≥0∞) * (v b : ℝ≥0∞) ∂η) =
          (∫⁻ a, (w a : ℝ≥0∞) ∂η) * (v b : ℝ≥0∞) := by
        have hmb : Measurable (fun a : H ↦ (w (a * b) : ℝ≥0∞)) :=
          hm.comp (continuous_id.mul continuous_const).measurable
        rw [lintegral_mul_const _ hmb]
        rw [lintegral_mul_right_eq_self (fun a ↦ (w a : ℝ≥0∞)) b]
      simp_rw [hinner]
      exact lintegral_const_mul _ (ENNReal.continuous_coe.comp hv).measurable

end ProdRegular

section RegularDomination

/-- A measure dominated by a finite regular measure on a Hausdorff Borel space is regular. -/
theorem regular_of_le_finite_regular {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    [ν.Regular] (h : μ ≤ ν) : μ.Regular := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν h
  have : μ.InnerRegularCompactLTTop := by
    constructor
    intro A hA r hr
    have he : μ A - r ≠ 0 := ne_of_gt (tsub_pos_of_lt hr)
    obtain ⟨K, hKA, hK, hsmall⟩ :=
      hA.1.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top ν A) he
    refine ⟨K, hKA, hK, ?_⟩
    have hd : μ (A \ K) < μ A - r := lt_of_le_of_lt (h (A \ K)) hsmall
    have hsum : μ A = μ K + μ (A \ K) := by
      simpa [union_eq_right.mpr hKA] using
        (measure_add_sdiff (μ := μ) hK.measurableSet.nullMeasurableSet A).symm
    rw [lt_tsub_iff_right] at hd
    rw [hsum] at hd
    exact (ENNReal.add_lt_add_iff_right (measure_ne_top μ (A \ K))).mp
      (by simpa [add_comm] using hd)
  infer_instance


section CompactTests

open scoped CompactlySupported ENNReal NNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A bounded density with a σ-compact carrier over a regular measure is inner regular. -/
theorem innerRegular_withDensity_of_le_of_isSigmaCompact
    (η : Measure X) [η.Regular] {w : X → ℝ≥0∞} {C : ℝ≥0}
    (hBound : ∀ x, w x ≤ C) {S : Set X} (hS : IsSigmaCompact S)
    (hW : Function.support w ⊆ S) : (η.withDensity w).InnerRegular := by
  let ν := η.withDensity w
  obtain ⟨K, hK, rfl⟩ := hS
  let L := accumulate K
  have hL (n : ℕ) : IsCompact (L n) := isCompact_accumulate hK n
  have hLm (n : ℕ) : MeasurableSet (L n) := (hL n).isClosed.measurableSet
  have hUnion : (⋃ n, L n) = ⋃ n, K n := iUnion_accumulate
  have hSm : MeasurableSet (⋃ n, L n) := MeasurableSet.iUnion hLm
  have hSupp : ∀ᵐ x ∂ν, x ∈ ⋃ n, L n := by
    rw [ae_iff]
    change ν (⋃ n, L n)ᶜ = 0
    rw [withDensity_apply _ hSm.compl]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_mem hSm.compl] with x hx
    by_contra hn
    exact hx (hUnion ▸ hW hn)
  have hRestr (n : ℕ) : (ν.restrict (L n)).InnerRegular := by
    let : Fact (η (L n) < ∞) := ⟨(hL n).measure_lt_top⟩
    let : (η.restrict (L n)).Regular :=
      Measure.Regular.restrict_of_measure_ne_top (hL n).measure_lt_top.ne
    let Cη := C • η.restrict (L n)
    let : Cη.Regular := inferInstanceAs (C • η.restrict (L n)).Regular
    have hDom : ν.restrict (L n) ≤ Cη := by
      rw [show ν = η.withDensity w from rfl, restrict_withDensity (hLm n),
        show Cη = (C : ℝ≥0∞) • η.restrict (L n) from rfl, ← withDensity_const]
      exact withDensity_mono (.of_forall hBound)
    let : IsFiniteMeasure (ν.restrict (L n)) := isFiniteMeasure_of_le Cη hDom
    let := regular_of_le_finite_regular _ Cη hDom
    infer_instance
  constructor
  intro s hs r hr
  have hEq : ν s = ⨆ n, ν (s ∩ L n) := by
    conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem hSupp, Measure.restrict_apply hs]
    rw [inter_iUnion, (monotone_const.inter monotone_accumulate).measure_iUnion]
  rw [hEq] at hr
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hr
  let := hRestr n
  rw [← Measure.restrict_apply hs] at hn
  obtain ⟨A, hA, hAc, hAn⟩ := hs.exists_lt_isCompact hn
  exact ⟨A, hA, hAc, hAn.trans_le (Measure.restrict_apply_le _ _)⟩

/-- Nonnegative compactly supported continuous tests determine inner regular measures
when one of the two measures is locally finite. -/
theorem measure_eq_of_lintegral_eq_on_compactlySupported_nnreal
    (μ ν : Measure X) [μ.InnerRegular] [ν.InnerRegular] [IsLocallyFiniteMeasure ν]
    (h : ∀ f : C_c(X, ℝ≥0), (∫⁻ x, (f x : ℝ≥0∞) ∂μ) = ∫⁻ x, (f x : ℝ≥0∞) ∂ν) :
    μ = ν := by
  have hle (m n : Measure X) [n.InnerRegular] [IsLocallyFiniteMeasure n]
      (h' : ∀ f : C_c(X, ℝ≥0), (∫⁻ x, (f x : ℝ≥0∞) ∂m) ≤
        ∫⁻ x, (f x : ℝ≥0∞) ∂n)
      {K : Set X} (hK : IsCompact K) : m K ≤ n K := by
    by_contra! hLt
    obtain ⟨V, hKV, hV, hVn⟩ := hK.exists_isOpen_lt_of_lt (μ := n) (m K) hLt
    obtain ⟨f, hf, hfc, hfs, h01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
    let u := (⟨f, hfc⟩ : C_c(X, ℝ)).nnrealPart
    have huK (x : X) (hx : x ∈ K) : (u x : ℝ≥0∞) = 1 := by
      change ENNReal.ofReal (f x) = 1
      exact ENNReal.ofReal_eq_one.mpr (hf hx)
    have huV (x : X) : (u x : ℝ≥0∞) ≤ V.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
      by_cases hx : x ∈ V
      · rw [indicator_of_mem hx]
        change ENNReal.ofReal (f x) ≤ 1
        exact ENNReal.ofReal_le_one.mpr (h01 x).2
      · have hz := image_eq_zero_of_notMem_tsupport (fun hx' ↦ hx (hfs hx'))
        rw [indicator_of_notMem hx]
        change ENNReal.ofReal (f x) ≤ 0
        simp [hz]
    have hLow : m K ≤ ∫⁻ x, (u x : ℝ≥0∞) ∂m := by
      rw [← setLIntegral_one]
      refine (setLIntegral_congr_fun hK.isClosed.measurableSet
        (fun x hx ↦ (huK x hx).symm)).le.trans (setLIntegral_le_lintegral _ _)
    have hHigh : (∫⁻ x, (u x : ℝ≥0∞) ∂n) ≤ n V :=
      (lintegral_mono huV).trans_eq (by simpa using lintegral_indicator_const (μ := n) hV.measurableSet 1)
    exact hVn.not_ge (hLow.trans ((h' u).trans hHigh))
  have hμν {K : Set X} (hK : IsCompact K) : μ K ≤ ν K := hle μ ν (fun f ↦ (h f).le) hK
  let : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K hK ↦ (hμν hK).trans_lt hK.measure_lt_top⟩
  have hνμ {K : Set X} (hK : IsCompact K) : ν K ≤ μ K := hle ν μ (fun f ↦ (h f).ge) hK
  ext1 s hs
  rw [hs.measure_eq_iSup_isCompact μ, hs.measure_eq_iSup_isCompact ν]
  exact iSup_congr fun K ↦ iSup_congr fun _ ↦ iSup_congr fun hK ↦
    le_antisymm (hμν hK) (hνμ hK)

end CompactTests

end RegularDomination

section CompactSupportApproximation

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal


/-- Approximate the indicator of a finite-measure set by a continuous cutoff with compact
support. The error is bounded by a constant on a measurable set of arbitrarily small mass. -/
theorem exists_continuous_indicator_error_bound
    {X E : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) {s : Set X}
    (hs : MeasurableSet s) (hsfin : ν s < ∞) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ (v : X → E) (t : Set X), Continuous v ∧ HasCompactSupport v ∧ AEStronglyMeasurable v ν ∧
      MeasurableSet t ∧ ν t ≤ η ∧ ∀ x, ‖(s.indicator (fun _ ↦ c) - v) x‖ ≤
        ‖t.indicator (fun _ ↦ ‖c‖ + ‖c‖) x‖ := by
  have he := (ENNReal.half_pos hη).ne'
  obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne he
  obtain ⟨V, hsV, hV, -, hsmallV⟩ := hs.exists_isOpen_sdiff_lt hsfin.ne he
  obtain ⟨b, hbK, hbV, hbc, hbr⟩ := exists_continuous_one_zero_of_isCompact hK
    hV.isClosed_compl (disjoint_compl_right_iff_subset.mpr (hKs.trans hsV))
  let v (x : X) := b x • c
  refine ⟨v, V \ K, b.continuous.smul continuous_const, hbc.smul_right (f' := fun _ ↦ c),
    b.continuous.aestronglyMeasurable.smul aestronglyMeasurable_const,
    hV.measurableSet.diff hK.isClosed.measurableSet, ?_, ?_⟩
  · calc
      _ ≤ ν ((V \ s) ∪ (s \ K)) := measure_mono (by grind)
      _ ≤ ν (V \ s) + ν (s \ K) := measure_union_le _ _
      _ ≤ η := (add_le_add hsmallV.le hsmallK.le).trans_eq (ENNReal.add_halves _)
  · intro x
    by_cases hx : x ∈ K
    · simp [v, hx, hKs hx, hbK hx]
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hx⟩)]
      refine (norm_sub_le _ _).trans ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact add_le_add (by simp [indicator]; split <;> simp) (by
        simpa [v, norm_smul, abs_of_nonneg (hbr x).1] using
          mul_le_mul_of_nonneg_right (hbr x).2 (norm_nonneg c))
    · have hxs : x ∉ s := fun h ↦ hxV (hsV h)
      simp [v, hxV, hxs, hbV hxV]

section Approximation

variable {X E : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compactly supported continuous functions approximate a function simultaneously in
`Lᵖ` and `Lᑫ` for finite exponents at least one. -/
theorem exists_hasCompactSupport_eLpNorm_sub_le_two
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hp' : p ≠ ∞) (hq' : q ≠ ∞)
    {u : X → E} (hup : MemLp u p ν) (huq : MemLp u q ν) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ v : X → E, Continuous v ∧ HasCompactSupport v ∧
      eLpNorm (u - v) p ν ≤ ε ∧ eLpNorm (u - v) q ν ≤ ε := by
  classical
  borelize E
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have he := (ENNReal.half_pos hε).ne'
  have approxSimple (f : SimpleFunc X E) (hf : MemLp f p ν) :
      ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ v : X → E, Continuous v ∧ HasCompactSupport v ∧
        eLpNorm (⇑f - v) p ν ≤ δ ∧ eLpNorm (⇑f - v) q ν ≤ δ := by
    induction f using SimpleFunc.induction with
    | const c hs =>
      intro δ hδ
      rename_i s
      have hcoe : (⇑(SimpleFunc.piecewise s hs (SimpleFunc.const X c)
          (SimpleFunc.const X 0)) : X → E) = s.indicator (fun _ ↦ c) := by
        rw [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_const]
        rfl
      rw [hcoe]
      by_cases hc : c = 0
      · subst c
        exact ⟨0, continuous_const, HasCompactSupport.zero, by simp, by simp⟩
      have hsfin := SimpleFunc.measure_lt_top_of_memLp_indicator hp0 hp' hc hs hf
      obtain ⟨ηp, hηp, hboundp⟩ := exists_eLpNorm_indicator_le (μ := ν) hp' (‖c‖ + ‖c‖) hδ
      obtain ⟨ηq, hηq, hboundq⟩ := exists_eLpNorm_indicator_le (μ := ν) hq' (‖c‖ + ‖c‖) hδ
      obtain ⟨v, t, hv, hvK, hvm, ht, hνt, hbound⟩ :=
        exists_continuous_indicator_error_bound c hs hsfin
          (ENNReal.coe_ne_zero.mpr (lt_min hηp hηq).ne')
      have hm : AEStronglyMeasurable (s.indicator (fun _ ↦ c) - v) ν :=
        (aestronglyMeasurable_const.indicator hs).sub hvm
      exact ⟨v, hv, hvK,
        (eLpNorm_mono hbound).trans (hboundp t (hνt.trans (by exact_mod_cast min_le_left ..))),
        (eLpNorm_mono hbound).trans (hboundq t (hνt.trans (by exact_mod_cast min_le_right ..)))⟩
    | add hdisj ihf ihg =>
      rename_i f g
      intro δ hδ
      rw [SimpleFunc.coe_add,
        memLp_add_of_disjoint hdisj f.stronglyMeasurable g.stronglyMeasurable] at hf
      obtain ⟨v, hv, hvK, hvp, hvq⟩ := ihf hf.1 (δ / 2) (ENNReal.half_pos hδ).ne'
      obtain ⟨w, hw, hwK, hwp, hwq⟩ := ihg hf.2 (δ / 2) (ENNReal.half_pos hδ).ne'
      have hvm : AEStronglyMeasurable (⇑f - v) ν := f.aestronglyMeasurable.sub
        (hv.integrable_of_hasCompactSupport hvK (μ := ν)).aestronglyMeasurable
      have hwm : AEStronglyMeasurable (⇑g - w) ν := g.aestronglyMeasurable.sub
        (hw.integrable_of_hasCompactSupport hwK (μ := ν)).aestronglyMeasurable
      refine ⟨v + w, hv.add hw, hvK.add hwK, ?_, ?_⟩ <;>
        rw [SimpleFunc.coe_add, add_sub_add_comm]
      · exact (eLpNorm_add_le hvm hwm hp).trans
          ((add_le_add hvp hwp).trans_eq (ENNReal.add_halves _))
      · exact (eLpNorm_add_le hvm hwm hq).trans
          ((add_le_add hvq hwq).trans_eq (ENNReal.add_halves _))
  -- The same sequence of simple functions converges in both norms.
  let u' := hup.aestronglyMeasurable.mk u
  have hueq : u =ᵐ[ν] u' := hup.aestronglyMeasurable.ae_eq_mk
  have hum := hup.aestronglyMeasurable.measurable_mk
  let : SeparableSpace (range u' ∪ {0} : Set E) :=
    StronglyMeasurable.separableSpace_range_union_singleton hup.aestronglyMeasurable.stronglyMeasurable_mk
  let a n := SimpleFunc.approxOn u' hum (range u' ∪ {0}) 0 (by simp) n
  have hlim {r : ℝ≥0∞} (hr : r ≠ ∞) (hu : MemLp u r ν) :
      Tendsto (fun n ↦ eLpNorm (⇑(a n) - u') r ν) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm hr hum (hu.ae_eq hueq).eLpNorm_lt_top
  obtain ⟨n, hpδ, hqδ⟩ := (((hlim hp' hup).eventually (gt_mem_nhds he.bot_lt)).and
    ((hlim hq' huq).eventually (gt_mem_nhds he.bot_lt))).exists
  obtain ⟨v, hv, hvK, hvp, hvq⟩ := approxSimple (a n)
    (SimpleFunc.memLp_approxOn_range hum (hup.ae_eq hueq) n) (ε / 2) he
  have heq : (u - v) =ᵐ[ν] (u' - v) := hueq.sub EventuallyEq.rfl
  have hm1 : AEStronglyMeasurable (u' - ⇑(a n)) ν :=
    hup.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable.sub
      (a n).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (⇑(a n) - v) ν := (a n).aestronglyMeasurable.sub
    (hv.integrable_of_hasCompactSupport hvK (μ := ν)).aestronglyMeasurable
  refine ⟨v, hv, hvK, ?_, ?_⟩ <;>
    rw [eLpNorm_congr_ae heq, show u' - v = u' - ⇑(a n) + (⇑(a n) - v) by abel]
  · exact (eLpNorm_add_le hm1 hm2 hp).trans
      ((add_le_add ((eLpNorm_sub_comm _ _ _ _).le.trans hpδ.le) hvp).trans_eq (ENNReal.add_halves _))
  · exact (eLpNorm_add_le hm1 hm2 hq).trans
      ((add_le_add ((eLpNorm_sub_comm _ _ _ _).le.trans hqδ.le) hvq).trans_eq (ENNReal.add_halves _))

end Approximation

end CompactSupportApproximation

section Fourier2

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]


omit [T2Space G] in
/-- Paper: (D.1.1.3), p. 746. Evaluating characters at a point gives a continuous
homomorphism from the group into its bidual. -/
def pontryaginDual_eval : G →ₜ* PontryaginDual (PontryaginDual G) := by
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

variable [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

-- Retain the existing signature, including the unused integrability hypothesis.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: (D.1.1.4), p. 746. At the trivial character the transform is the integral
of the original function. -/
theorem lcaFourier_one (f : G → ℂ) (hf : Integrable f μ) :
    lcaFourier μ f 1 = ∫ x, f x ∂μ := by
  simp [lcaFourier, PontryaginDual.one_apply]


/-- Each fibre of an `L²` convolution is integrable, with the Cauchy–Schwarz bound. -/
lemma integrable_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (x : G) :
    Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ ∧
      ‖lcaConvolution μ f g x‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hpres : MeasurePreserving (fun y : G ↦ x / y) μ μ :=
    Measure.measurePreserving_div_left μ x
  have hfun : (fun y ↦ g (y⁻¹ * x)) = g ∘ fun y ↦ x / y := by
    ext y
    simp [div_eq_mul_inv, mul_comm]
  have hg' : MemLp (fun y ↦ g (y⁻¹ * x)) 2 μ := hfun ▸ hg.comp_measurePreserving hpres
  have hnorm : eLpNorm (fun y ↦ g (y⁻¹ * x)) 2 μ = eLpNorm g 2 μ := by
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hpres
  have hmul : MemLp (fun y ↦ f y * g (y⁻¹ * x)) 1 μ := hg'.mul hf
  have hint : Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ := memLp_one_iff_integrable.mp hmul
  have hprod : eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    have hsmul := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := 2) (q := 2) (r := 1)
      (φ := f) (f := fun y ↦ g (y⁻¹ * x)) hg'.aestronglyMeasurable hf.aestronglyMeasurable
    have hEq : (fun y ↦ f y * g (y⁻¹ * x)) = f • fun y ↦ g (y⁻¹ * x) := by
      ext y
      simp [smul_eq_mul]
    simpa [hEq, hnorm] using hsmul
  refine ⟨hint, ?_⟩
  have hfin : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  have hI : ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    calc
      ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ
          ≤ ∫⁻ y, ‖f y * g (y⁻¹ * x)‖ₑ ∂μ :=
            enorm_integral_le_lintegral_enorm (fun y ↦ f y * g (y⁻¹ * x))
      _ ≤ eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ :=
        eLpNorm_one_eq_lintegral_enorm.ge
      _ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := hprod
  simpa [lcaConvolution, toReal_enorm', ENNReal.toReal_mul] using ENNReal.toReal_mono hfin hI

/-- Translation in `L²` makes the convolution of two `L²` functions continuous. -/
lemma continuous_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Continuous (lcaConvolution μ f g) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let gInv : G → ℂ := fun y ↦ g y⁻¹
  have hgInv : MemLp gInv 2 μ := hg.comp_measurePreserving (Measure.measurePreserving_inv μ)
  let F : Lp ℂ 2 μ := hf.toLp f
  let H : Lp ℂ 2 μ := hgInv.toLp gInv
  let pairing := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  have hshift : Continuous fun x : G ↦ DomMulAct.mk x⁻¹ • H :=
    (continuous_smul (M := Gᵈᵐᵃ) (X := Lp ℂ 2 μ)).comp
      ((DomMulAct.continuous_mk.comp continuous_inv).prodMk continuous_const)
  have hcont : Continuous (fun x : G ↦ pairing F (DomMulAct.mk x⁻¹ • H)) :=
    (pairing F).continuous.comp hshift
  refine hcont.congr fun x ↦ ?_
  rw [ContinuousLinearMap.lpPairing_eq_integral, lcaConvolution]
  simp only [ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  have hF : (F : G → ℂ) =ᵐ[μ] f := hf.coeFn_toLp
  have hH : (H : G → ℂ) =ᵐ[μ] gInv := hgInv.coeFn_toLp
  have hleft : (fun y ↦ (H : G → ℂ) (x⁻¹ * y)) =ᵐ[μ] fun y ↦ gInv (x⁻¹ * y) :=
    (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp hH
  have hAct := DomMulAct.smul_Lp_ae_eq (DomMulAct.mk x⁻¹) H
  simp only [Equiv.symm_apply_apply, smul_eq_mul] at hAct
  have htrans : (DomMulAct.mk x⁻¹ • H : Lp ℂ 2 μ) =ᵐ[μ] fun y ↦ g (y⁻¹ * x) := by
    refine hAct.trans (hleft.trans ?_)
    filter_upwards with y
    simp [gInv, mul_inv_rev, inv_inv]
  filter_upwards [hF, htrans] with y hyF hyT
  simp only [hyF, hyT]


end Fourier2

open scoped ZeroAtInfty

section Plancherel

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]


omit [μ.Regular] in
/-- The Fourier norm of a single nonzero compactly supported test function fixes the
scalar between two regular Haar measures satisfying Plancherel. -/
theorem isLCAPlancherelMeasure_unique
    {ν₁ ν₂ : Measure (PontryaginDual G)}
    (h₁ : LCAGroup.IsPlancherelMeasure μ ν₁) (h₂ : LCAGroup.IsPlancherelMeasure μ ν₂) : ν₁ = ν₂ := by
  let := h₁.1
  let := h₁.2.1
  let := h₂.1
  let := h₂.2.1
  let c := ν₁.haarScalarFactor ν₂
  have hc : ν₁ = c • ν₂ := Measure.isMulLeftInvariant_eq_smul_of_regular _ _
  obtain ⟨g, hgK, -, hg₁⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : G → ℂ := fun x ↦ g x
  have hfC : Continuous f := Complex.continuous_ofReal.comp g.continuous
  have hfK : HasCompactSupport f := hgK.comp_left Complex.ofReal_zero
  have hf₁ := hfC.integrable_of_hasCompactSupport (μ := μ) hfK
  have hf₂ := hfC.memLp_of_hasCompactSupport (μ := μ) (p := 2) hfK
  have hnorm : eLpNorm f 2 μ ≠ 0 := by
    intro hzero
    have hae := (eLpNorm_eq_zero_iff hf₂.aestronglyMeasurable (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero
    have hEq : f = 0 := Measure.eq_of_ae_eq hae hfC continuous_const
    exact hg₁ (Complex.ofReal_eq_zero.mp (congrFun hEq 1))
  have hScale := (h₁.2.2 f hf₁ hf₂).2
  rw [hc, eLpNorm_smul_measure_of_ne_top' (by simp : (2 : ℝ≥0∞) ≠ ⊤) _
    _, (h₂.2.2 f hf₁ hf₂).2] at hScale
  change (↑(c ^ ((2 : ℝ≥0∞).toReal)⁻¹) : ℝ≥0∞) * eLpNorm f 2 μ = eLpNorm f 2 μ at hScale
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)] at hScale
  have hRoot : (c : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 :=
    (ENNReal.mul_left_inj hnorm hf₂.eLpNorm_ne_top).mp (hScale.trans (one_mul _).symm)
  have hc₁ : c = 1 := by
    apply ENNReal.coe_injective
    apply (ENNReal.strictMono_rpow_of_pos (by norm_num : 0 < ((2 : ℝ≥0∞).toReal)⁻¹)).injective
    simpa only [ENNReal.coe_one, ENNReal.one_rpow] using hRoot
  rw [hc, hc₁, one_smul]

/-- A Fourier norm identity for compactly supported continuous functions extends to
integrable square-integrable functions by approximation in both norms. -/
theorem isLCAPlancherelMeasure_of_compactSupport
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (h : ∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
      eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ) :
    LCAGroup.IsPlancherelMeasure μ ν := by
  have hp : 1 ≤ (2 : ℝ≥0∞) := by norm_num
  have hsub {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
      lcaFourier μ (f - g) = lcaFourier μ f - lcaFourier μ g := by
    funext χ
    simp only [lcaFourier, Pi.sub_apply, sub_mul]
    exact integral_sub (integrable_fourierIntegrand μ hf χ) (integrable_fourierIntegrand μ hg χ)
  have hApprox (f : G → ℂ) (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
      ∃ (g : ℕ → G → ℂ), (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
        Tendsto (fun n ↦ eLpNorm (g n - f) 2 μ) atTop (𝓝 0) ∧
        ∀ χ, Tendsto (fun n ↦ lcaFourier μ (g n) χ) atTop (𝓝 (lcaFourier μ f χ)) := by
    let ε (n : ℕ) : ℝ≥0∞ := ((n : ℝ≥0∞) + 1)⁻¹
    have hε : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    choose g hgC hgK hg₁ hg₂ using fun n : ℕ ↦
      exists_hasCompactSupport_eLpNorm_sub_le_two le_rfl hp ENNReal.one_ne_top
        (by simp) (memLp_one_iff_integrable.mpr hf₁) hf₂ (ε := ε n) (by simp [ε])
    have hlim (p : ℝ≥0∞) (hg : ∀ n, eLpNorm (f - g n) p μ ≤ ε n) :
        Tendsto (fun n ↦ eLpNorm (g n - f) p μ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun _ ↦ bot_le)
        (fun n ↦ (eLpNorm_sub_comm _ _ _ _).le.trans (hg n))
    refine ⟨g, fun n ↦ ⟨hgC n, hgK n⟩, hlim 2 hg₂, fun χ ↦ ?_⟩
    have hmem (n : ℕ) := ((hgC n).integrable_of_hasCompactSupport (μ := μ) (hgK n)).sub hf₁
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hlim' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim 1 hg₁)
    simp only [ENNReal.toReal_zero, Function.comp_def] at hlim'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
      (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    have hEq : (eLpNorm (g n - f) 1 μ).toReal = ∫ x, ‖(g n - f) x‖ ∂μ := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm (hmem n),
        ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
    rw [hEq, ← Pi.sub_apply, ← hsub
      ((hgC n).integrable_of_hasCompactSupport (hgK n)) hf₁]
    exact norm_lcaFourier_le_integral_norm μ _ χ
  -- Pointwise convergence of the transforms and Fatou give the bound for arbitrary inputs.
  have hupper (f : G → ℂ) (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
      eLpNorm (lcaFourier μ f) 2 ν ≤ eLpNorm f 2 μ := by
    obtain ⟨g, hg, hlim₂, hlimF⟩ := hApprox f hf₁ hf₂
    have hg₁ (n : ℕ) : Integrable (g n) μ :=
      (hg n).1.integrable_of_hasCompactSupport (hg n).2
    have hg₂ (n : ℕ) : MemLp (g n) 2 μ := (hg n).1.memLp_of_hasCompactSupport (hg n).2
    have hnorm : Tendsto (fun n ↦ eLpNorm (g n) 2 μ) atTop (𝓝 (eLpNorm f 2 μ)) := by
      have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg₂ f hf₂).mpr hlim₂
      simpa only [Lp.enorm_toLp] using ht.enorm
    calc
      eLpNorm (lcaFourier μ f) 2 ν ≤ liminf (fun n ↦ eLpNorm (lcaFourier μ (g n)) 2 ν) atTop :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun n ↦ (continuous_lcaFourier μ (hg₁ n)).aestronglyMeasurable)
          _ (.of_forall hlimF)
      _ = eLpNorm f 2 μ := by
        simp_rw [h _ (hg _).1 (hg _).2]
        exact hnorm.liminf_eq
  refine ⟨inferInstance, inferInstance, fun f hf₁ hf₂ ↦ ?_⟩
  have hfF : MemLp (lcaFourier μ f) 2 ν :=
    ⟨(continuous_lcaFourier μ hf₁).aestronglyMeasurable,
      (hupper f hf₁ hf₂).trans_lt hf₂.eLpNorm_lt_top⟩
  obtain ⟨g, hg, hlim₂, -⟩ := hApprox f hf₁ hf₂
  have hg₁ (n : ℕ) : Integrable (g n) μ :=
    (hg n).1.integrable_of_hasCompactSupport (hg n).2
  have hg₂ (n : ℕ) : MemLp (g n) 2 μ := (hg n).1.memLp_of_hasCompactSupport (hg n).2
  have hgF (n : ℕ) : MemLp (lcaFourier μ (g n)) 2 ν :=
    ⟨(continuous_lcaFourier μ (hg₁ n)).aestronglyMeasurable,
      (h (g n) (hg n).1 (hg n).2).trans_lt (hg₂ n).eLpNorm_lt_top⟩
  -- The bound applied to differences gives convergence of the transformed sequence in L².
  have hlimF : Tendsto (fun n ↦ eLpNorm (lcaFourier μ (g n) - lcaFourier μ f) 2 ν)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim₂
      (fun _ ↦ bot_le) (fun n ↦ ?_)
    rw [← hsub (hg₁ n) hf₁]
    exact hupper _ ((hg₁ n).sub hf₁) ((hg₂ n).sub hf₂)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg₂ f hf₂).mpr hlim₂
  have htF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hgF _ hfF).mpr hlimF
  refine ⟨hfF, tendsto_nhds_unique (l := atTop)
    (f := fun n ↦ eLpNorm (lcaFourier μ (g n)) 2 ν) ?_ ?_⟩
  · simpa only [Lp.enorm_toLp] using htF.enorm
  · simp_rw [h _ (hg _).1 (hg _).2]
    simpa only [Lp.enorm_toLp] using ht.enorm

open scoped CompactlySupported in
/-- The autocorrelation of a continuous compactly supported function is the
Fourier–Stieltjes transform of a finite regular positive measure on the dual.
This is the autocorrelation case of Bochner's theorem. -/
theorem exists_lcaAutocorrelation_measure (f : C_c(G, ℂ)) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
        lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x := by
  obtain ⟨ρ, hFinite, hRegular, hρ⟩ := exists_haar_autocorrelation_measure μ (f := (f : G → ℂ))
    (f.continuous.memLp_of_hasCompactSupport (p := 2) f.hasCompactSupport)
  exact ⟨ρ, hFinite, hRegular, fun x ↦ by
    simpa only [lcaConvolution, mul_inv_rev, inv_inv] using hρ x⟩

open scoped CompactlySupported Pointwise in
/-- The autocorrelation has compact support, and its Fourier integral is the
squared modulus of the Fourier integral of the original function. -/
theorem lcaFourier_autocorrelation (f : C_c(G, ℂ)) :
    HasCompactSupport (lcaConvolution μ f (fun y ↦ star (f y⁻¹))) ∧
    ∀ χ, lcaFourier μ (lcaConvolution μ f (fun y ↦ star (f y⁻¹))) χ =
      (‖lcaFourier μ f χ‖ ^ 2 : ℝ) := by
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  have hout (x y : G) (hx : x ∉ K * K⁻¹) : f y * star (f (x⁻¹ * y)) = 0 := by
    by_contra h
    have hy : y ∈ K := subset_tsupport f fun hy ↦ h (by simp [hy])
    have hz : x⁻¹ * y ∈ K := subset_tsupport f fun hz ↦ h (by simp [hz])
    apply hx
    refine ⟨y, hy, (x⁻¹ * y)⁻¹, by simpa, ?_⟩
    simp [mul_inv_rev]
  constructor
  · refine HasCompactSupport.intro (hK.mul hK.inv) fun x hx ↦ ?_
    simp only [lcaConvolution, mul_inv_rev, inv_inv, hout x _ hx, integral_zero]
  intro χ
  let k (x y : G) := f y * star (f (x⁻¹ * y)) * star (χ x : ℂ)
  have hk : Continuous (Function.uncurry k) :=
    ((f.continuous.comp continuous_snd).mul
      (f.continuous.comp (continuous_fst.inv.mul continuous_snd)).star).mul
      ((continuous_subtype_val.comp χ.continuous).comp continuous_fst).star
  have hkK : HasCompactSupport (Function.uncurry k) := by
    refine HasCompactSupport.intro ((hK.mul hK.inv).prod hK) ?_
    rintro ⟨x, y⟩ h
    change f y * star (f (x⁻¹ * y)) * star (χ x : ℂ) = 0
    by_cases hx : x ∈ K * K⁻¹
    · rw [image_eq_zero_of_notMem_tsupport (fun hy ↦ h ⟨hx, hy⟩), zero_mul, zero_mul]
    · rw [hout x y hx, zero_mul]
  have hrow (x : G) : lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x *
      star (χ x : ℂ) = ∫ y, k x y ∂μ := by
    simp only [k, lcaConvolution, mul_inv_rev, inv_inv, integral_mul_const]
  have hcol (y : G) : (∫ x, k x y ∂μ) =
      f y * star (χ y : ℂ) * star (lcaFourier μ f χ) := by
    calc
      _ = ∫ z, k (y * z⁻¹) y ∂μ := by
        rw [integral_inv_eq_self (fun z ↦ k (y * z) y) μ,
          integral_mul_left_eq_self (fun z ↦ k z y) y]
      _ = ∫ z, (f y * star (χ y : ℂ)) * star (f z * star (χ z : ℂ)) ∂μ := by
        apply integral_congr_ae
        exact .of_forall fun z ↦ by
          have hχ : (χ (y * z⁻¹) : ℂ) = (χ y : ℂ) * star (χ z : ℂ) := by
            simp only [map_mul, Circle.coe_mul, map_inv, Circle.coe_inv_eq_conj, Complex.star_def]
          simp only [k, hχ, mul_inv_rev, inv_inv, inv_mul_cancel_right, star_mul, star_star]
          ring
      _ = _ := (integral_const_mul _ _).trans
        (congrArg (fun z : ℂ ↦ (f y * star (χ y : ℂ)) * z)
          (integral_conj (f := fun z ↦ f z * star (χ z : ℂ))))
  calc
    _ = ∫ x, ∫ y, k x y ∂μ ∂μ := by simp only [lcaFourier, hrow]
    _ = ∫ y, ∫ x, k x y ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hk hkK
    _ = _ := by
      simp only [hcol, integral_mul_const]
      change lcaFourier μ f χ * star (lcaFourier μ f χ) = _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A Fourier density under a finite regular spectral measure corresponds to
convolution with the Fourier–Stieltjes transform of that measure. -/
theorem integral_lcaFourier_mul_char
    (τ : Measure (PontryaginDual G)) [IsFiniteMeasure τ] [τ.Regular]
    {u : G → ℂ} (hu : Continuous u) (huK : HasCompactSupport u) (x : G) :
    (∫ χ, lcaFourier μ u χ * (χ x : ℂ) ∂τ) =
      lcaConvolution μ u (fun z ↦ ∫ χ, (χ z : ℂ) ∂τ) x := by
  obtain ⟨S, hS, hτ⟩ := exists_isSigmaCompact_ae_mem τ
  let K := tsupport u
  have hK : IsCompact K := huK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  let : Fact (μ K < ⊤) := ⟨hK.measure_lt_top⟩
  let k (p : G × PontryaginDual G) := u p.1 * (p.2 (p.1⁻¹ * x) : ℂ)
  have he : Continuous (fun p : G × PontryaginDual G ↦ p.2 (p.1⁻¹ * x)) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_snd).prodMk (continuous_fst.inv.mul continuous_const))
  have hk : Continuous k := (hu.comp continuous_fst).mul (continuous_subtype_val.comp he)
  let q := (K ×ˢ S).indicator k
  have hq : Measurable q := measurable_indicator_prod_of_isSigmaCompact hk hK.isSigmaCompact hS
  obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖u y‖ ≤ C := hu.bounded_above_of_compact_support huK
  have hInt : Integrable q ((μ.restrict K).prod τ) := by
    apply Integrable.of_bound hq.aestronglyMeasurable C
    exact .of_forall fun p ↦ by
      by_cases hp : p ∈ K ×ˢ S
      · have hk1 : ‖k p‖ = ‖u p.1‖ := by
          simp only [k, norm_mul, Circle.norm_coe, mul_one]
        rw [show q p = k p from indicator_of_mem hp k, hk1]
        exact hC p.1
      · simpa [q, hp] using (norm_nonneg (u p.1)).trans (hC p.1)
  have hrow : ∀ᵐ y ∂μ.restrict K, (∫ χ, q (y, χ) ∂τ) =
      u y * ∫ χ, (χ (y⁻¹ * x) : ℂ) ∂τ := by
    filter_upwards [ae_restrict_mem hKm] with y hy
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hτ] with χ hχ
    exact indicator_of_mem (s := K ×ˢ S) (a := (y, χ)) ⟨hy, hχ⟩ k
  have hcol : ∀ᵐ χ ∂τ, (∫ y in K, q (y, χ) ∂μ) = lcaFourier μ u χ * (χ x : ℂ) := by
    filter_upwards [hτ] with χ hχ
    let r (y : G) := u y * star (χ y : ℂ) * (χ x : ℂ)
    calc
      _ = ∫ y in K, r y ∂μ := by
        refine setIntegral_congr_fun hKm fun y hy ↦ ?_
        rw [show q (y, χ) = k (y, χ) from
          indicator_of_mem (s := K ×ˢ S) (a := (y, χ)) ⟨hy, hχ⟩ k]
        simp only [k, r, map_mul, Circle.coe_mul, map_inv, Circle.coe_inv_eq_conj,
          Complex.star_def, mul_assoc]
      _ = ∫ y, r y ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero <| fun y hy ↦ by
        have hz : u y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp only [r, hz, zero_mul]
      _ = _ := integral_mul_const _ _
  calc
    _ = ∫ χ, ∫ y in K, q (y, χ) ∂μ ∂τ := integral_congr_ae (hcol.mono fun _ h ↦ h.symm)
    _ = ∫ y in K, ∫ χ, q (y, χ) ∂τ ∂μ :=
      (integral_integral_swap (f := fun y χ ↦ q (y, χ)) hInt).symm
    _ = _ := (integral_congr_ae hrow).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by simp [image_eq_zero_of_notMem_tsupport hy]))

/-- A finite regular measure on the dual is determined by its integrals against
the evaluation characters. -/
theorem lcaSpectral_measure_ext
    (τ₁ τ₂ : Measure (PontryaginDual G)) [IsFiniteMeasure τ₁] [τ₁.Regular]
    [IsFiniteMeasure τ₂] [τ₂.Regular]
    (h : ∀ x : G, (∫ χ, (χ x : ℂ) ∂τ₁) = ∫ χ, (χ x : ℂ) ∂τ₂) : τ₁ = τ₂ := by
  let τ := τ₁ + τ₂
  let h₁ : τ₁ ≪ τ := Measure.AbsolutelyContinuous.rfl.add_right _
  let h₂ : τ₂ ≪ τ := Measure.AbsolutelyContinuous.rfl.add_right' _
  let : τ.InnerRegular := inferInstanceAs (τ₁ + τ₂).InnerRegular
  let : τ.Regular := inferInstance
  let d₁ (χ : PontryaginDual G) : ℂ := (τ₁.rnDeriv τ χ).toReal
  let d₂ (χ : PontryaginDual G) : ℂ := (τ₂.rnDeriv τ χ).toReal
  have hInt₁ : Integrable d₁ τ := by
    simpa only [d₁, Complex.real_smul, mul_one] using
      (integrable_rnDeriv_smul_iff (f := fun _ ↦ (1 : ℂ)) h₁).2 (integrable_const _)
  have hInt₂ : Integrable d₂ τ := by
    simpa only [d₂, Complex.real_smul, mul_one] using
      (integrable_rnDeriv_smul_iff (f := fun _ ↦ (1 : ℂ)) h₂).2 (integrable_const _)
  have hc (x : G) : Continuous (fun χ : PontryaginDual G ↦ (χ x : ℂ)) :=
    continuous_subtype_val.comp (pontryaginDual_eval (G := G) x).continuous
  have hEq : (d₁ - d₂) =ᵐ[τ] 0 := by
    refine ae_eq_zero_of_integral_mul_circle_eq_zero
      (fun χ : PontryaginDual G ↦ χ.toMonoidHom)
      (fun x ↦ (pontryaginDual_eval (G := G) x).continuous)
      (fun χ ψ heq ↦ PontryaginDual.ext fun x ↦ congrArg (fun e : G →* Circle ↦ e x) heq)
      (hInt₁.sub hInt₂) fun x ↦ ?_
    change (∫ χ, (d₁ χ - d₂ χ) * (χ x : ℂ) ∂τ) = 0
    simp only [sub_mul]
    rw [integral_sub
      (hInt₁.mul_bdd (hc x).aestronglyMeasurable (.of_forall fun χ ↦ (Circle.norm_coe _).le))
      (hInt₂.mul_bdd (hc x).aestronglyMeasurable (.of_forall fun χ ↦ (Circle.norm_coe _).le))]
    simp only [d₁, d₂, ← Complex.real_smul, integral_rnDeriv_smul, h₁, h₂, h,
      sub_self]
  rw [← Measure.withDensity_rnDeriv_eq τ₁ τ h₁, ← Measure.withDensity_rnDeriv_eq τ₂ τ h₂]
  apply withDensity_congr_ae
  filter_upwards [hEq, Measure.rnDeriv_lt_top τ₁ τ, Measure.rnDeriv_lt_top τ₂ τ] with χ he ht₁ ht₂
  have hr := Complex.ofReal_injective (sub_eq_zero.mp he)
  rw [← ENNReal.ofReal_toReal ht₁.ne, ← ENNReal.ofReal_toReal ht₂.ne, hr]

open scoped CompactlySupported in
/-- The translate of one spectral measure and the other spectral measure agree after
weighting each by the squared Fourier magnitude of the other function. -/
theorem lcaAutocorrelation_weighted_translate
    (f g : C_c(G, ℂ)) (ρ σ : Measure (PontryaginDual G))
    [IsFiniteMeasure ρ] [ρ.Regular] [IsFiniteMeasure σ] [σ.Regular]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x)
    (hσ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂σ) =
      lcaConvolution μ g (fun y ↦ star (g y⁻¹)) x)
    (a : PontryaginDual G) :
    (ρ.map (a * ·)).withDensity (fun χ ↦ ‖lcaFourier μ g χ‖ₑ ^ 2) =
      σ.withDensity (fun χ ↦ ‖lcaFourier μ f (a⁻¹ * χ)‖ₑ ^ 2) := by
  let A (h : C_c(G, ℂ)) := lcaConvolution μ h (fun y ↦ star (h y⁻¹))
  have hAc (h : C_c(G, ℂ)) : Continuous (A h) := by
    apply continuous_lcaConvolution_L2 μ (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport)
    exact (h.continuous.comp continuous_inv).star.memLp_of_hasCompactSupport
      ((h.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).comp_left (star_zero ℂ))
  let u (x : G) := (a x : ℂ) * A f x
  have huc : Continuous u := (continuous_subtype_val.comp a.continuous).mul (hAc f)
  have huK : HasCompactSupport u := (lcaFourier_autocorrelation μ f).1.mul_left
  let e := Homeomorph.mulLeft a
  let τ := ρ.map e
  let : IsFiniteMeasure τ := ρ.isFiniteMeasure_map e
  let : τ.Regular := Measure.Regular.map e
  have hτ (x : G) : (∫ χ, (χ x : ℂ) ∂τ) = u x := by
    rw [show τ = Measure.map e.toMeasurableEquiv ρ from rfl,
      integral_map_equiv]
    change (∫ χ, ((a x * χ x : Circle) : ℂ) ∂ρ) = u x
    simp only [Circle.coe_mul, integral_const_mul, hρ, u, A]
  have hF (χ : PontryaginDual G) : lcaFourier μ u χ =
      (‖lcaFourier μ f (a⁻¹ * χ)‖ ^ 2 : ℝ) := by
    rw [← (lcaFourier_autocorrelation μ f).2 (a⁻¹ * χ)]
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      change (a y : ℂ) * A f y * star (χ y : ℂ) =
        A f y * star ((a⁻¹ * χ) y : ℂ)
      have hinv : ((a⁻¹ * χ) y : ℂ) = star (a y : ℂ) * (χ y : ℂ) := by
        change (((a y)⁻¹ * χ y : Circle) : ℂ) = _
        rw [Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.star_def]
      rw [hinv, star_mul, star_star]
      ring
  let w (h : C_c(G, ℂ)) (χ : PontryaginDual G) : ℝ≥0 := ‖lcaFourier μ h χ‖₊ ^ 2
  have hw (h : C_c(G, ℂ)) : Continuous (w h) :=
    (continuous_lcaFourier μ h.integrable).nnnorm.pow 2
  have hw' : Continuous (fun χ ↦ w f (a⁻¹ * χ)) :=
    (hw f).comp (continuous_const.mul continuous_id)
  have hBound (h : C_c(G, ℂ)) (χ : PontryaginDual G) :
      (w h χ : ℝ≥0∞) ≤ ENNReal.ofReal ((∫ x, ‖h x‖ ∂μ) ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (norm_lcaFourier_le_integral_norm μ h χ) 2)
  have hReg (v : Measure (PontryaginDual G)) [IsFiniteMeasure v] [v.Regular]
      (p : PontryaginDual G → ℝ≥0∞) (C : ℝ) (hp : ∀ χ, p χ ≤ ENNReal.ofReal C) :
      IsFiniteMeasure (v.withDensity p) ∧ (v.withDensity p).Regular := by
    let c := Real.toNNReal C
    let cv := c • v
    have hle : v.withDensity p ≤ cv := by
      change _ ≤ (ENNReal.ofReal C) • v
      rw [← withDensity_const]
      exact withDensity_mono (.of_forall hp)
    let : IsFiniteMeasure cv := inferInstanceAs (IsFiniteMeasure (c • v))
    let : cv.Regular := inferInstanceAs (c • v).Regular
    exact ⟨isFiniteMeasure_of_le cv hle, regular_of_le_finite_regular _ cv hle⟩
  obtain ⟨h₁fin, h₁reg⟩ := hReg τ (fun χ ↦ (w g χ : ℝ≥0∞)) _ (hBound g)
  obtain ⟨h₂fin, h₂reg⟩ := hReg σ (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞)) _
    (fun χ ↦ hBound f (a⁻¹ * χ))
  let := h₁fin
  let := h₁reg
  let := h₂fin
  let := h₂reg
  suffices heq : τ.withDensity (fun χ ↦ (w g χ : ℝ≥0∞)) =
      σ.withDensity (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞)) by
    have he : (e : PontryaginDual G → PontryaginDual G) = (a * ·) := rfl
    simpa only [τ, he, w, ENNReal.coe_pow, enorm_eq_nnnorm] using heq
  apply lcaSpectral_measure_ext
  intro x
  rw [integral_withDensity_eq_integral_smul (hw g).measurable,
    integral_withDensity_eq_integral_smul hw'.measurable]
  have hl (χ : PontryaginDual G) :
      w g χ • (χ x : ℂ) = lcaFourier μ (A g) χ * (χ x : ℂ) := by
    rw [(lcaFourier_autocorrelation μ g).2 χ]
    simp [w, NNReal.smul_def, Complex.real_smul]
  have hr (χ : PontryaginDual G) :
      w f (a⁻¹ * χ) • (χ x : ℂ) = lcaFourier μ u χ * (χ x : ℂ) := by
    rw [hF]
    simp [w, NNReal.smul_def, Complex.real_smul]
  simp_rw [hl, hr]
  rw [integral_lcaFourier_mul_char μ τ (hAc g) (lcaFourier_autocorrelation μ g).1,
    integral_lcaFourier_mul_char μ σ huc huK, funext hτ, funext hσ]
  let q (y : G) := A g y * u (y⁻¹ * x)
  have hcomm (y : G) : q (x * y⁻¹) = u y * A g (y⁻¹ * x) := by
    simp only [q, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rw [mul_comm x y⁻¹, mul_comm]
  change (∫ y, q y ∂μ) = ∫ y, u y * A g (y⁻¹ * x) ∂μ
  rw [← integral_mul_left_eq_self q x]
  calc
    (∫ y, q (x * y) ∂μ) = ∫ y, q (x * y⁻¹) ∂μ :=
      (integral_inv_eq_self (fun y ↦ q (x * y)) μ).symm
    _ = _ := integral_congr_ae (.of_forall hcomm)

open scoped CompactlySupported in
/-- Averaging the weighted spectral measures of two autocorrelations over dual
translations gives this identity on each measurable set. For a dual character `a`,
the spectral measure of `f` modulated by `a` is the translate of its spectral
measure by `a`. Weight that translate by the squared Fourier magnitude of `g`,
or weight the spectral measure of `g` by the shifted squared Fourier magnitude
of `f`. The two measures have the same Fourier–Stieltjes transform by
commutativity of convolution. Integrate the resulting identity over `a`
against the fixed Haar measure `η`. -/
theorem lcaAutocorrelation_measure_mul_lintegral
    (η : Measure (PontryaginDual G)) [η.IsHaarMeasure] [η.Regular]
    (f g : C_c(G, ℂ)) (ρ σ : Measure (PontryaginDual G))
    [IsFiniteMeasure ρ] [ρ.Regular] [IsFiniteMeasure σ] [σ.Regular]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x)
    (hσ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂σ) =
      lcaConvolution μ g (fun y ↦ star (g y⁻¹)) x)
    {s : Set (PontryaginDual G)} (hs : MeasurableSet s) :
    (∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ 2 ∂η) * σ s =
      ρ univ * (∫⁻ χ in s, ‖lcaFourier μ g χ‖ₑ ^ 2 ∂η) := by
  let w (h : C_c(G, ℂ)) (χ : PontryaginDual G) : ℝ≥0 := ‖lcaFourier μ h χ‖₊ ^ 2
  have hw (h : C_c(G, ℂ)) : Continuous (w h) :=
    (continuous_lcaFourier μ h.integrable).nnnorm.pow 2
  have hwMeas (h : C_c(G, ℂ)) : Measurable (fun χ ↦ (w h χ : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.comp (hw h)).measurable
  have hCarrier (h : C_c(G, ℂ)) :
      ∃ S : Set (PontryaginDual G), IsSigmaCompact S ∧ Function.support (w h) ⊆ S := by
    obtain ⟨F, hF⟩ := lcaFourier_zeroAtInfty μ h.integrable
    have hlim : Tendsto (w h) (cocompact (PontryaginDual G)) (𝓝 0) := by
      simpa only [w, ← hF, nnnorm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
        (zero_at_infty F).nnnorm.pow 2
    obtain ⟨ε, -, hε, hεlim⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0) < 1)
    let K (n : ℕ) := {χ | ε n ≤ w h χ}
    have hK (n : ℕ) : IsCompact (K n) := by
      obtain ⟨L, hL, hLK⟩ := mem_cocompact.mp (hlim (Iio_mem_nhds (hε n).1))
      exact hL.of_isClosed_subset (isClosed_le continuous_const (hw h)) (by
        intro χ hχ
        by_contra hn
        exact (not_lt_of_ge (show ε n ≤ w h χ from hχ)) (show w h χ < ε n from hLK hn))
    refine ⟨⋃ n, K n, ⟨K, hK, rfl⟩, fun χ hχ ↦ ?_⟩
    have hh : ∀ᶠ n in atTop, ε n < w h χ :=
      hεlim (Iio_mem_nhds (pos_iff_ne_zero.mpr hχ))
    obtain ⟨n, hn⟩ := hh.exists
    exact mem_iUnion.mpr ⟨n, le_of_lt hn⟩
  obtain ⟨S, hS, hfS⟩ := hCarrier f
  obtain ⟨T, hT, hgT⟩ := hCarrier g
  let I := ∫⁻ χ, (w f χ : ℝ≥0∞) ∂η
  let ν₁ := I • σ
  let ν₂ := ρ univ • η.withDensity (fun χ ↦ (w g χ : ℝ≥0∞))
  -- Average the translated identity against each compactly supported continuous test.
  have hTests (p : C_c(PontryaginDual G, ℝ≥0)) :
      (∫⁻ χ, (p χ : ℝ≥0∞) ∂ν₁) = ∫⁻ χ, (p χ : ℝ≥0∞) ∂ν₂ := by
    let v (χ : PontryaginDual G) := w g χ * p χ
    have hv : Continuous v := (hw g).mul p.continuous
    have hvT : Function.support v ⊆ T := fun χ hχ ↦ hgT (mul_ne_zero_iff.mp hχ).1
    have hp : Measurable (fun χ ↦ (p χ : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.comp p.continuous).measurable
    have hpoint (a : PontryaginDual G) :
        (∫⁻ χ, (w f (a⁻¹ * χ) : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂σ) =
          ∫⁻ χ, (v (a * χ) : ℝ≥0∞) ∂ρ := by
      have h := congrArg (fun m : Measure (PontryaginDual G) ↦ ∫⁻ χ, (p χ : ℝ≥0∞) ∂m)
        (lcaAutocorrelation_weighted_translate μ f g ρ σ hρ hσ a).symm
      simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow] at h
      change (∫⁻ χ, (p χ : ℝ≥0∞) ∂σ.withDensity (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞))) =
        ∫⁻ χ, (p χ : ℝ≥0∞) ∂(ρ.map (a * ·)).withDensity (fun χ ↦ (w g χ : ℝ≥0∞)) at h
      have hshift : Measurable (fun χ ↦ (w f (a⁻¹ * χ) : ℝ≥0∞)) :=
        (hwMeas f).comp (continuous_const.mul continuous_id).measurable
      rw [lintegral_withDensity_eq_lintegral_mul _ hshift hp,
        lintegral_withDensity_eq_lintegral_mul _ (hwMeas g) hp] at h
      have hm : Measurable (fun χ ↦ (v χ : ℝ≥0∞)) :=
        (ENNReal.continuous_coe.comp hv).measurable
      calc
        _ = ∫⁻ χ, (v χ : ℝ≥0∞) ∂(ρ.map (a * ·)) := by
          simpa only [Pi.mul_apply, v, ENNReal.coe_mul] using h
        _ = _ := lintegral_map hm (continuous_const.mul continuous_id).measurable
    rw [lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ (hwMeas g) hp]
    calc
      I * (∫⁻ χ, (p χ : ℝ≥0∞) ∂σ) =
          ∫⁻ a, ∫⁻ χ, (w f (a * χ) : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂σ ∂η :=
        (lintegral_lintegral_mul_translate η σ (hw f) p.continuous hS hfS).symm
      _ = ∫⁻ a, ∫⁻ χ, (w f (a⁻¹ * χ) : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂σ ∂η :=
        (lintegral_inv_eq_self (fun a ↦ ∫⁻ χ, (w f (a * χ) : ℝ≥0∞) *
          (p χ : ℝ≥0∞) ∂σ)).symm
      _ = ∫⁻ a, ∫⁻ χ, (v (a * χ) : ℝ≥0∞) ∂ρ ∂η := lintegral_congr hpoint
      _ = ρ univ * ∫⁻ χ, (w g χ : ℝ≥0∞) * (p χ : ℝ≥0∞) ∂η := by
        simpa only [ENNReal.coe_one, mul_one, lintegral_const, one_mul, v, ENNReal.coe_mul] using
          (lintegral_lintegral_mul_translate η ρ hv
            (v := fun _ ↦ (1 : ℝ≥0)) continuous_const hT hvT).trans (mul_comm _ _)
  let C := Real.toNNReal ((∫ x, ‖g x‖ ∂μ) ^ 2)
  have hBound (χ : PontryaginDual G) : (w g χ : ℝ≥0∞) ≤ C := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (norm_lcaFourier_le_integral_norm μ g χ) 2)
  let ν := η.withDensity (fun χ ↦ (w g χ : ℝ≥0∞))
  have hνle : ν ≤ C • η := by
    change _ ≤ (C : ℝ≥0∞) • η
    rw [← withDensity_const]
    exact withDensity_mono (.of_forall hBound)
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK ↦ (hνle K).trans_lt
    (hK.measure_lt_top (μ := C • η))⟩
  let : ν.InnerRegular := innerRegular_withDensity_of_le_of_isSigmaCompact η hBound hT
    (fun χ hχ ↦ hgT (by simpa using hχ))
  let : ν₂.InnerRegular := inferInstanceAs (ρ univ • ν).InnerRegular
  let : IsFiniteMeasureOnCompacts ν₂ := ⟨fun K hK ↦ by
    change (ρ univ • ν) K < ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (measure_lt_top ρ univ) hK.measure_lt_top⟩
  let : IsLocallyFiniteMeasure ν₂ := inferInstance
  let : σ.InnerRegular := inferInstance
  let : ν₁.InnerRegular := inferInstanceAs (I • σ).InnerRegular
  -- Local finiteness of the weighted Haar measure suffices to identify both measures.
  have hEq := congrArg (fun m : Measure (PontryaginDual G) ↦ m s)
    (measure_eq_of_lintegral_eq_on_compactlySupported_nnreal ν₁ ν₂ hTests)
  simpa only [ν₁, ν₂, I, w, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs,
    ENNReal.coe_pow, enorm_eq_nnnorm] using hEq

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
open scoped CompactlySupported in
/-- Evaluating the Fourier–Stieltjes representation at the identity identifies
the total mass with the integral of the squared source norm. -/
theorem lcaAutocorrelation_measure_univ (f : C_c(G, ℂ))
    (ρ : Measure (PontryaginDual G)) [IsFiniteMeasure ρ]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x) :
    ρ univ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have hSqC : Continuous (fun x ↦ ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have hSqK : HasCompactSupport (fun x ↦ ‖f x‖ ^ 2) :=
    f.hasCompactSupport.norm.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hAuto : lcaConvolution μ f (fun y ↦ star (f y⁻¹)) 1 =
      ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [lcaConvolution, ← integral_complex_ofReal]
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h := congrArg Complex.re (hρ 1)
  simp only [map_one, Circle.coe_one, integral_const, Complex.real_smul, mul_one,
    Complex.ofReal_re, hAuto] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
  change ENNReal.ofReal (ρ.real univ) = _
  rw [h, ofReal_integral_eq_lintegral_ofReal (hSqC.integrable_of_hasCompactSupport hSqK)
    (.of_forall fun x ↦ sq_nonneg _)]
  exact lintegral_congr fun x ↦ by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

open scoped CompactlySupported in
/-- A nonnegative compactly supported bump fixes the normalization of Haar measure
on the dual. Its spectral measure gives positive mass to a compact set, so the
averaging identity on that set ensures its squared Fourier integral is finite. -/
theorem exists_lcaFourier_weighted_haar
    (ρ : C_c(G, ℂ) → Measure (PontryaginDual G))
    (hρ : ∀ f, IsFiniteMeasure (ρ f) ∧ (ρ f).Regular ∧
      ∀ x : G, (∫ χ, (χ x : ℂ) ∂(ρ f)) =
        lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x) :
    ∃ ν : Measure (PontryaginDual G), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ f : C_c(G, ℂ), ν.withDensity (fun χ ↦ ‖lcaFourier μ f χ‖ₑ ^ 2) = ρ f := by
  let η : Measure (PontryaginDual G) := MeasureTheory.Measure.haar
  let (g : C_c(G, ℂ)) : IsFiniteMeasure (ρ g) := (hρ g).1
  let (g : C_c(G, ℂ)) : (ρ g).Regular := (hρ g).2.1
  obtain ⟨b, hbK, hb₀, hb₁⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : C_c(G, ℂ) := ⟨⟨fun x ↦ (b x : ℂ), Complex.continuous_ofReal.comp b.continuous⟩,
    hbK.comp_left Complex.ofReal_zero⟩
  let w (g : C_c(G, ℂ)) (χ : PontryaginDual G) := ‖lcaFourier μ g χ‖ₑ ^ 2
  have hf₁ : f 1 ≠ 0 := Complex.ofReal_ne_zero.mpr hb₁
  have hw (g : C_c(G, ℂ)) : Continuous (w g) :=
    ENNReal.continuous_coe.comp ((continuous_lcaFourier μ g.integrable).nnnorm.pow 2)
  have hfSq : Continuous (fun x ↦ ‖f x‖ₑ ^ 2) :=
    ENNReal.continuous_coe.comp (f.continuous.nnnorm.pow 2)
  have hM : ρ f univ ≠ 0 := by
    rw [lcaAutocorrelation_measure_univ μ f (ρ f) (hρ f).2.2]
    apply ne_of_gt
    apply (lintegral_pos_iff_support hfSq.measurable).2
    exact (isOpen_ne_fun hfSq continuous_const).measure_pos μ
      ⟨1, show ‖f 1‖ₑ ^ 2 ≠ 0 by simpa using hf₁⟩
  have hF₁ : lcaFourier μ f 1 ≠ 0 := by
    rw [lcaFourier_one μ f f.integrable]
    change (∫ x, (b x : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr
      (b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbK hb₀ hb₁).ne'
  let I : ℝ≥0∞ := ∫⁻ χ, w f χ ∂η
  have hI₀ : I ≠ 0 := by
    apply ne_of_gt
    apply (lintegral_pos_iff_support (hw f).measurable).2
    exact (isOpen_ne_fun (hw f) continuous_const).measure_pos η
      ⟨1, show w f 1 ≠ 0 by simpa [w] using hF₁⟩
  obtain ⟨K, -, hK, hKpos⟩ := MeasurableSet.univ.exists_lt_isCompact (pos_iff_ne_zero.mpr hM)
  have hI_top : I ≠ ⊤ := by
    intro h
    have hAvg := lcaAutocorrelation_measure_mul_lintegral μ η f f (ρ f) (ρ f)
      (hρ f).2.2 (hρ f).2.2 hK.isClosed.measurableSet
    change I * ρ f K = ρ f univ * (∫⁻ χ in K, w f χ ∂η) at hAvg
    rw [h, ENNReal.top_mul hKpos.ne'] at hAvg
    have hBound (χ : PontryaginDual G) : w f χ ≤ ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) ^ 2 := by
      change ‖lcaFourier μ f χ‖ₑ ^ 2 ≤ _
      rw [← ofReal_norm]
      exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal
        (norm_lcaFourier_le_integral_norm μ f χ)) _
    have hFinite : (∫⁻ χ in K, w f χ ∂η) < ⊤ := by
      refine (lintegral_mono hBound).trans_lt ?_
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hK.measure_lt_top
    exact (ENNReal.mul_lt_top (measure_lt_top (ρ f) univ) hFinite).ne hAvg.symm
  let c := ρ f univ * I⁻¹
  have hc₀ : c ≠ 0 := mul_ne_zero hM (ENNReal.inv_ne_zero.mpr hI_top)
  have hc_top : c ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top (ρ f) univ) (ENNReal.inv_ne_top.mpr hI₀)
  refine ⟨c • η, Measure.IsHaarMeasure.smul η hc₀ hc_top, Measure.Regular.smul hc_top, ?_⟩
  intro g
  ext1 s hs
  have hAvg := lcaAutocorrelation_measure_mul_lintegral μ η f g (ρ f) (ρ g)
    (hρ f).2.2 (hρ g).2.2 hs
  change I * ρ g s = ρ f univ * (∫⁻ χ in s, w g χ ∂η) at hAvg
  change (c • η).withDensity (w g) s = _
  rw [withDensity_apply _ hs, setLIntegral_smul_measure, smul_eq_mul]
  calc
    c * (∫⁻ χ in s, w g χ ∂η) = I⁻¹ * (ρ f univ * (∫⁻ χ in s, w g χ ∂η)) := by
      dsimp [c]
      ac_rfl
    _ = ρ g s := by rw [← hAvg, ← mul_assoc, ENNReal.inv_mul_cancel hI₀ hI_top, one_mul]

open scoped CompactlySupported in
/-- There is a regular Haar measure on the dual for which the Fourier transform
preserves the L² norm of every continuous compactly supported function. It suffices
to construct this measure by Fourier inversion at the identity for autocorrelations
of such functions. -/
theorem exists_lcaFourier_eLpNorm_eq_of_hasCompactSupport :
    ∃ ν : Measure (PontryaginDual G), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ := by
  choose ρ hρ using exists_lcaAutocorrelation_measure μ
  obtain ⟨ν, hHaar, hRegular, hDensity⟩ := exists_lcaFourier_weighted_haar μ ρ hρ
  refine ⟨ν, hHaar, hRegular, fun f hf hs ↦ ?_⟩
  let g : C_c(G, ℂ) := ⟨⟨f, hf⟩, hs⟩
  let : IsFiniteMeasure (ρ g) := (hρ g).1
  have hMass : ρ g univ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ :=
    lcaAutocorrelation_measure_univ μ g (ρ g) (hρ g).2.2
  have hSqEq : (∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ 2 ∂ν) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    have h := congrArg (fun m : Measure (PontryaginDual G) ↦ m univ) (hDensity g)
    change (ν.withDensity (fun χ ↦ ‖lcaFourier μ f χ‖ₑ ^ 2)) univ = ρ g univ at h
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hMass] at h
  have hFourier := continuous_lcaFourier μ (hf.integrable_of_hasCompactSupport (μ := μ) hs)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [hSqEq]

/-- Paper: Lemma D.1.1.2(4), p. 747. There is exactly one Plancherel measure. -/
theorem lcaPlancherelMeasure_existsUnique :
    ∃! ν : Measure (PontryaginDual G), LCAGroup.IsPlancherelMeasure μ ν := by
  obtain ⟨ν, hHaar, hReg, hNorm⟩ := exists_lcaFourier_eLpNorm_eq_of_hasCompactSupport μ
  let := hHaar
  let := hReg
  have hν := isLCAPlancherelMeasure_of_compactSupport μ ν hNorm
  exact ⟨ν, hν, fun ν' hν' ↦ isLCAPlancherelMeasure_unique μ hν' hν⟩

/-- The range of an L² Fourier isometry has trivial orthogonal complement.
Orthogonality to translates of each integrable test function forces the product of its
conjugated transform with the orthogonal vector to vanish almost everywhere. -/
theorem lcaFourier_isometry_surjective
    {ν : Measure (PontryaginDual G)} [ν.Regular]
    (U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (f : G → ℂ), Integrable f μ → ∀ (h₂ : MemLp f 2 μ),
      (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f) :
    Function.Surjective U := by
  classical
  let R := U.toLinearMap.range
  have hClosed : IsClosed (R : Set (Lp ℂ 2 ν)) := U.isometry.isClosedEmbedding.isClosed_range
  let : CompleteSpace R := hClosed.isComplete.completeSpace_coe
  suffices R = ⊤ from LinearMap.range_eq_top.mp this
  refine Submodule.orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr ?_)
  intro g hg
  have hInner (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      ∫ χ, g χ * star (lcaFourier μ f χ) ∂ν = 0 := by
    have hZero := (R.mem_orthogonal g).mp hg _ (U.toLinearMap.mem_range_self (h₂.toLp f))
    change inner ℂ (U (h₂.toLp f)) g = 0 at hZero
    rw [L2.inner_def] at hZero
    refine (integral_congr_ae ((hU f hf h₂).mono fun χ hχ ↦ ?_)).trans hZero
    rw [RCLike.inner_apply, starRingEnd_apply, hχ]
  have hProduct (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      (fun χ ↦ g χ * star (lcaFourier μ f χ)) =ᵐ[ν] 0 := by
    have hInt : Integrable (fun χ ↦ g χ * star (lcaFourier μ f χ)) ν :=
      (L2.integrable_inner (𝕜 := ℂ) (U (h₂.toLp f)) g).congr
        ((hU f hf h₂).mono fun χ hχ ↦ by
          change inner ℂ (U (h₂.toLp f) χ) (g χ) = _
          rw [RCLike.inner_apply, starRingEnd_apply, hχ])
    refine ae_eq_zero_of_integral_mul_circle_eq_zero (X := PontryaginDual G) (D := G)
      (fun χ : PontryaginDual G ↦ χ.toMonoidHom)
      (fun a ↦ (continuous_eval_const (F := C(G, Circle)) a).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous)
      (fun _ _ h ↦ PontryaginDual.ext (fun a ↦ congrArg (fun k : G →* Circle ↦ k a) h))
      hInt ?_
    intro a
    let m := measurePreserving_mul_left μ a⁻¹
    have hZero := hInner (fun x ↦ f (a⁻¹ * x)) (m.integrable_comp_of_integrable hf)
      (h₂.comp_measurePreserving m)
    refine (integral_congr_ae (.of_forall fun χ ↦ ?_)).trans hZero
    change g χ * star (lcaFourier μ f χ) * (χ a : ℂ) = _
    rw [lcaFourier_translate μ f a⁻¹ χ, star_mul, map_inv, Circle.coe_inv_eq_conj,
      ← Complex.star_def, star_star]
    ring
  -- A modulated indicator of a compact neighborhood gives a transform nonzero at each point.
  obtain ⟨K, hK, hK₁⟩ := exists_compact_mem_nhds (1 : G)
  have hKm := hK.isClosed.measurableSet
  have hKfin := (hK.measure_lt_top (μ := μ)).ne
  have hKpos : 0 < μ K := (isOpen_interior.measure_pos μ
    ⟨1, mem_interior_iff_mem_nhds.mpr hK₁⟩).trans_le (measure_mono interior_subset)
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hKfin
  let f (ψ : PontryaginDual G) : G → ℂ := K.indicator fun x ↦ (ψ x : ℂ)
  have hfLp (ψ : PontryaginDual G) (p : ℝ≥0∞) : MemLp (f ψ) p μ :=
    (memLp_indicator_iff_restrict hKm).mpr <|
      MemLp.of_bound (continuous_subtype_val.comp ψ.continuous).aestronglyMeasurable
        1 (.of_forall fun x ↦ (Circle.norm_coe (ψ x)).le)
  have hf (ψ : PontryaginDual G) : Integrable (f ψ) μ :=
    memLp_one_iff_integrable.mp (hfLp ψ 1)
  have hNonzero (ψ : PontryaginDual G) : lcaFourier μ (f ψ) ψ ≠ 0 := by
    unfold lcaFourier
    rw [show (fun x ↦ f ψ x * star (ψ x : ℂ)) = K.indicator (fun _ ↦ (1 : ℂ)) by
      funext x
      by_cases hx : x ∈ K
      · simp only [f, indicator_of_mem hx, Complex.star_def, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow, Complex.ofReal_one]
      · simp [f, hx]]
    rw [integral_indicator hKm, integral_const, Measure.real, Measure.restrict_apply_univ,
      Complex.real_smul, mul_one]
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hKpos.ne' hKfin).ne'
  let O (ψ : PontryaginDual G) := {χ | lcaFourier μ (f ψ) χ ≠ 0}
  have hOpen (ψ : PontryaginDual G) : IsOpen (O ψ) :=
    isOpen_ne_fun (continuous_lcaFourier μ (hf ψ)) continuous_const
  have hLocal (ψ : PontryaginDual G) : ∀ᵐ χ ∂ν.restrict (O ψ), g χ = 0 := by
    filter_upwards [ae_restrict_of_ae (hProduct (f ψ) (hf ψ) (hfLp ψ 2)),
      ae_restrict_mem (hOpen ψ).measurableSet] with χ hχ hmem
    exact (mul_eq_zero.mp hχ).resolve_right (star_ne_zero.mpr hmem)
  have hCompact (L : Set (PontryaginDual G)) (hL : IsCompact L) :
      ∀ᵐ χ ∂ν.restrict L, g χ = 0 := by
    obtain ⟨t, -, ht⟩ := hL.elim_nhds_subcover O (fun ψ _ ↦ (hOpen ψ).mem_nhds (hNonzero ψ))
    exact ae_mono (Measure.restrict_mono ht le_rfl)
      ((ae_restrict_biUnion_finset_iff O t _).mpr (fun ψ _ ↦ hLocal ψ))
  -- Compact approximation of the integrable squared norm avoids a countability assumption.
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [L2.inner_def]
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  let q (χ : PontryaginDual G) := inner ℂ (g χ) (g χ)
  have hq : Integrable q ν := L2.integrable_inner g g
  obtain ⟨L, -, hL, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hq MeasurableSet.univ hε
  have hZero : ∫ χ in L, q χ ∂ν = 0 := by
    have hqZero : q =ᵐ[ν.restrict L] (0 : PontryaginDual G → ℂ) :=
      (hCompact L hL).mono fun χ hχ ↦ by simp [q, hχ]
    rw [integral_congr_ae hqZero, Pi.zero_def, integral_zero]
  have hEq : (∫ χ, q χ ∂ν) = ∫ χ in Lᶜ, q χ ∂ν := by
    rw [← integral_add_compl hL.isClosed.measurableSet hq, hZero, zero_add]
  change ‖∫ χ, q χ ∂ν‖ < 0 + ε
  rw [hEq, zero_add]
  exact (norm_integral_le_integral_norm q).trans_lt (by rwa [← compl_eq_univ_sdiff] at hTail)

/-- Paper: Lemma D.1.1.2(4), p. 747. The Fourier transform on L¹ ∩ L²
extends uniquely to a unitary isomorphism on L². -/
theorem lcaFourier_unitary (ν : Measure (PontryaginDual G))
    (hν : LCAGroup.IsPlancherelMeasure μ ν) :
    ∃! U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
      ∀ (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ),
        (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
  let : ν.Regular := hν.2.1
  let D : Submodule ℂ (Lp ℂ 2 μ) :=
    { carrier := {f | Integrable (f : G → ℂ) μ}
      zero_mem' := (integrable_zero G ℂ μ).congr (Lp.coeFn_zero ℂ 2 μ).symm
      add_mem' := fun {_ _} hf hg ↦ (hf.add hg).congr (Lp.coeFn_add _ _).symm
      smul_mem' := fun c _ hf ↦ (hf.smul c).congr (Lp.coeFn_smul c _).symm }
  have hDense : DenseRange D.subtype := by
    apply (Lp.simpleFunc.dense (E := ℂ) (p := 2) (μ := μ) ENNReal.ofNat_ne_top).mono
    intro f hf
    let g : Lp.simpleFunc ℂ 2 μ := ⟨f, hf⟩
    have hInt : Integrable (Lp.simpleFunc.toSimpleFunc g) μ :=
      (SimpleFunc.memLp_iff_integrable two_ne_zero ENNReal.ofNat_ne_top).mp (Lp.simpleFunc.memLp g)
    exact ⟨⟨f, hInt.congr (Lp.simpleFunc.toSimpleFunc_eq_toFun g)⟩, rfl⟩
  have hPlancherel (f : D) := hν.2.2 f f.2 (Lp.memLp (f : Lp ℂ 2 μ))
  let transform (f : D) : Lp ℂ 2 ν := (hPlancherel f).1.toLp (lcaFourier μ f)
  have hTransform (f : D) : (transform f : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f :=
    MemLp.coeFn_toLp _
  let F : D →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := transform
      map_add' f g := by
        apply Lp.ext
        filter_upwards [hTransform (f + g), hTransform f, hTransform g,
          Lp.coeFn_add (transform f) (transform g)] with χ hfg hf hg hAdd
        change transform (f + g) χ = (transform f + transform g) χ
        rw [hfg, hAdd, Pi.add_apply, hf, hg]
        unfold lcaFourier
        calc
          _ = ∫ x, ((f : Lp ℂ 2 μ) x + (g : Lp ℂ 2 μ) x) * star (χ x : ℂ) ∂μ :=
            integral_congr_ae ((Lp.coeFn_add (f : Lp ℂ 2 μ) g).mono fun x hx ↦ by
              change ((f : Lp ℂ 2 μ) + (g : Lp ℂ 2 μ)) x * _ = _
              rw [hx]
              rfl)
          _ = _ := by
            simp_rw [add_mul]
            exact integral_add (integrable_fourierIntegrand μ f.2 χ)
              (integrable_fourierIntegrand μ g.2 χ)
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [hTransform (c • f), hTransform f, Lp.coeFn_smul c (transform f)]
          with χ hcf hf hSmul
        change transform (c • f) χ = (c • transform f) χ
        rw [hcf, hSmul, Pi.smul_apply, hf]
        unfold lcaFourier
        calc
          _ = ∫ x, c • ((f : Lp ℂ 2 μ) x * star (χ x : ℂ)) ∂μ :=
            integral_congr_ae ((Lp.coeFn_smul c (f : Lp ℂ 2 μ)).mono fun x hx ↦ by
              change ((c • (f : Lp ℂ 2 μ)) : Lp ℂ 2 μ) x * _ = _
              rw [hx, Pi.smul_apply]
              exact smul_mul_assoc _ _ _)
          _ = _ := integral_smul c _ }
  have hNorm (f : D) : ‖F f‖ = ‖D.subtype f‖ := by
    change ‖(hPlancherel f).1.toLp (lcaFourier μ f)‖ = ‖(f : Lp ℂ 2 μ)‖
    rw [Lp.norm_toLp, Lp.norm_def, (hPlancherel f).2]
  let Uc : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν := F.extendOfNorm D.subtype
  have hUeq (x : D) : Uc (D.subtype x) = F x :=
    LinearMap.extendOfNorm_eq hDense ⟨1, fun x ↦ by rw [one_mul, hNorm x]⟩ x
  have hUnorm (x : Lp ℂ 2 μ) : ‖Uc x‖ = ‖x‖ := by
    refine hDense.induction_on (p := fun w ↦ ‖Uc w‖ = ‖w‖) x
      (isClosed_eq Uc.continuous.norm continuous_norm) fun y ↦ ?_
    rw [hUeq, hNorm]
  let U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 ν := ⟨Uc.toLinearMap, hUnorm⟩
  have hU (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
    let x : D := ⟨h₂.toLp f, hf.congr h₂.coeFn_toLp.symm⟩
    have hEq : U (D.subtype x) = F x := hUeq x
    change (U (D.subtype x) : PontryaginDual G → ℂ) =ᵐ[ν] _
    rw [hEq]
    refine (hTransform x).trans (.of_forall fun χ ↦ integral_congr_ae ?_)
    exact h₂.coeFn_toLp.mono fun y hy ↦ by change _ * _ = _ * _; rw [hy]
  let e := LinearIsometryEquiv.ofSurjective U (lcaFourier_isometry_surjective μ U hU)
  refine ⟨e, hU, fun V hV ↦ ?_⟩
  apply LinearIsometryEquiv.ext
  intro f
  refine hDense.induction_on (p := fun w ↦ V w = e w) f
    (isClosed_eq V.continuous e.continuous) fun x ↦ ?_
  have hx := Lp.memLp (x : Lp ℂ 2 μ)
  have hEq : hx.toLp (x : G → ℂ) = D.subtype x := Lp.toLp_coeFn _ hx
  rw [← hEq]
  exact Lp.ext ((hV x x.2 hx).trans (hU x x.2 hx).symm)

-- TODO(paper-gap): Lemma D.1.1.2(5) asserts continuity and pointwise inversion for an
-- arbitrary measurable representative. A nonzero function supported at one point of
-- the real line has zero transform, and its double transform is everywhere zero.

end Plancherel

end

end Sol_LCAGroup_plancherel

open LCAGroup in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    (∃! ν : Measure (PontryaginDual G), IsPlancherelMeasure μ ν) ∧
    ∀ ν : Measure (PontryaginDual G), IsPlancherelMeasure μ ν →
      ∃! U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
        ∀ (f : G → ℂ) (_hf : Integrable f μ) (h₂ : MemLp f 2 μ),
          (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] RiemannMasullo.lcaFourier μ f :=
  ⟨Sol_LCAGroup_plancherel.lcaPlancherelMeasure_existsUnique μ,
    fun ν hν ↦ Sol_LCAGroup_plancherel.lcaFourier_unitary μ ν hν⟩
