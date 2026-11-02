-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exists_signed_compact_scalar_circle_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:09:55.283445+00:00
-- url     : https://prove2.me/submissions/553d80ff-4a9e-4829-b6d2-e8f57d14d2c6

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_FiniteTransfer_exists_countable_mixed_stages
import Theorems.Thm_OAI_CircleDomainRigidity_countable_uncovered_test_endpoints_of_range
import Theorems.Thm_OAI_CircleDomainRigidity_selected_limit_isCircleDomain

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PeriodizedLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Periodizing scalar coarea lengths

A scalar coarea estimate controls the integral of the physical length
of real level sets. Integer translates of `[0,1)` partition the real
line, so the sum of these lengths over all lifts of a mod-one level
has the same integral on `[0,1)`. Countable subadditivity then gives
finite physical length for almost every mod-one level.
-/

open Set MeasureTheory Metric Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- The actual mod-one fiber of any real coordinate is the countable
union of its integer-translated scalar fibers. -/
theorem unitAddCircle_level_eq_iUnion_integer_levels {Z : Type*} (f : Z → ℝ) (t : ℝ) :
    {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, {x | f x = t + (k : ℝ)} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, unitAddCircle_eq_iff_exists_int]

theorem unitAddCircle_level_inter_eq_iUnion_integer_levels
    {Z : Type*} (f : Z → ℝ) (D : Set Z) (t : ℝ) :
    D ∩ {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, D ∩ {x | f x = t + (k : ℝ)} := by
  rw [unitAddCircle_level_eq_iUnion_integer_levels, inter_iUnion]

private theorem iUnion_integer_Ico : (⋃ k : ℤ, Ico (k : ℝ) ((k : ℝ) + 1)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩

private theorem pairwise_disjoint_integer_Ico :
    Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) ((k : ℝ) + 1)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨hxi, hxi'⟩ ⟨hxj, hxj'⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hstep : i + 1 ≤ j := by omega
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hstep
    linarith
  · have hstep : j + 1 ≤ i := by omega
    have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hstep
    linarith

/-- Tonelli and the integer translates of a unit interval give the exact
periodized coarea integral. -/
theorem lintegral_periodizedLevelLength (L : ℝ → ℝ≥0∞) (hL : Measurable L) :
    ∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t = ∫⁻ t, L t := by
  unfold periodizedLevelLength
  have hm (k : ℤ) : AEMeasurable (fun t : ℝ => L (t + (k : ℝ)))
      (volume.restrict (Ico (0 : ℝ) 1)) :=
    (hL.comp (measurable_id.add_const (k : ℝ))).aemeasurable
  rw [lintegral_tsum hm]
  have hshift (k : ℤ) :
      ∫⁻ t in Ico (0 : ℝ) 1, L (t + (k : ℝ)) =
        ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), L t := by
    have h := (measurePreserving_add_right volume (k : ℝ)).setLIntegral_comp_emb
      (Homeomorph.addRight (k : ℝ)).isClosedEmbedding.measurableEmbedding L (Ico 0 1)
    simpa only [image_add_const_Ico, zero_add, add_comm (1 : ℝ) (k : ℝ)] using h
  simp_rw [hshift]
  rw [← lintegral_iUnion (fun _ : ℤ => measurableSet_Ico) pairwise_disjoint_integer_Ico,
    iUnion_integer_Ico, Measure.restrict_univ]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar coarea and its finite-energy consequences

The planar scalar coarea identities specialize
Federer, *Geometric Measure Theory*, Springer (1969), §3.2.11 (coarea)
and §3.2.12 (weighted coarea),
DOI: 10.1007/978-3-642-62010-2. For a `C¹` real function on an open
subset of the Euclidean plane, the integral of the one-dimensional
Hausdorff measures of its fibers equals the integral of the norm of its
differential. The locally Lipschitz version follows from the stated
Lipschitz coarea theorem by a countable relatively compact covering.

`PlanarScalarCoarea` and `WeightedPlanarScalarCoarea` express these
specializations as propositions. They require neither finite energy nor
topological conclusions. The length function need only be Lebesgue
measurable; Borel measurability is unnecessary.

Finite area and finite squared differential imply finite integrated
length, and integer periodization
gives finite physical length for almost every circle-valued level.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace CircleDomainRigidity

/-- The scalar fibers are measurable even though the function is only
assumed continuous on its open domain. -/
theorem measurableSet_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (t : ℝ) :
    MeasurableSet (D ∩ {z | f z = t}) := by
  classical
  have hm : Measurable (D.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | f z = t} =
      D ∩ (D.piecewise f (fun _ => 0)) ⁻¹' {t} := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  rw [heq]
  exact hD.measurableSet.inter (hm (measurableSet_singleton t))

/-- Countable additivity on the disjoint integer lifts is the exact
weighted circle-fiber identity. -/
theorem weightedCircleLevelLength_eq_periodized {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    weightedCircleLevelLength D f q t =
      periodizedLevelLength (weightedScalarLevelLength D f q) t := by
  unfold weightedCircleLevelLength periodizedLevelLength weightedScalarLevelLength
  rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
  apply lintegral_iUnion (fun k : ℤ => measurableSet_scalar_level hD hf (t + (k : ℝ)))
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨_, hzi⟩ ⟨_, hzj⟩
  change f z = t + (i : ℝ) at hzi
  change f z = t + (j : ℝ) at hzj
  apply hij
  exact_mod_cast (show (i : ℝ) = (j : ℝ) by linarith)

theorem lintegral_periodizedLevelLength_of_aemeasurable
    (L : ℝ → ℝ≥0∞) (hL : AEMeasurable L volume) :
    (∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t) = ∫⁻ t, L t := by
  have htranslate (k : ℤ) :
      ∀ᵐ t ∂volume, L (t + (k : ℝ)) = hL.mk L (t + (k : ℝ)) :=
    (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving.ae hL.ae_eq_mk
  have heq : periodizedLevelLength L =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
      periodizedLevelLength (hL.mk L) := by
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr htranslate)] with t ht
    exact tsum_congr ht
  rw [lintegral_congr_ae heq, lintegral_periodizedLevelLength _ hL.measurable_mk,
    ← lintegral_congr_ae hL.ae_eq_mk]

/-- The weighted circle-valued coarea formula follows from the real
one, including the measurability needed for further integration. -/
theorem weighted_circle_coarea {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞)
    (hcoarea : WeightedScalarCoareaIdentity D f q) :
    AEMeasurable (weightedCircleLevelLength D f q)
        (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻ t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) =
        ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := by
  have heq : weightedCircleLevelLength D f q =
      periodizedLevelLength (weightedScalarLevelLength D f q) :=
    funext (weightedCircleLevelLength_eq_periodized hD hf q)
  rw [heq]
  constructor
  · apply AEMeasurable.restrict
    exact AEMeasurable.tsum (fun k : ℤ => hcoarea.1.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving)
  · rw [lintegral_periodizedLevelLength_of_aemeasurable _ hcoarea.1, hcoarea.2]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted regular levels for collar construction, using
Federer's coarea theorem and Sard's theorem. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem ennreal_mul_le_add_squares (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc
      a * b ≤ b * b := mul_le_mul' h le_rfl
      _ ≤ a ^ 2 + b ^ 2 := by rw [← pow_two]; exact le_add_self
  · calc
      a * b ≤ a * a := mul_le_mul' le_rfl h
      _ ≤ a ^ 2 + b ^ 2 := by rw [← pow_two]; exact le_self_add

theorem weighted_scalar_coarea_integral_lt_top
    {D : Set ℂ} {f : ℂ → ℝ} {q : ℂ → ℝ≥0∞}
    (hcoarea : WeightedScalarCoareaIdentity D f q) (hq : Measurable q)
    (hq2 : (∫⁻ z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞) :
    (∫⁻ t, weightedScalarLevelLength D f q t) < ∞ := by
  rw [hcoarea.2]
  have hb : (∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) ≤
      (∫⁻ z in D, q z ^ 2) + ∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2 := by
    calc
      _ ≤ ∫⁻ z in D, (q z ^ 2 + (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) :=
        lintegral_mono fun z => ennreal_mul_le_add_squares _ _
      _ = _ := lintegral_add_left (hq.pow_const 2) _
  exact hb.trans_lt (ENNReal.add_lt_top.mpr ⟨hq2, hf2⟩)

theorem exists_weighted_regular_level
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hcompact : HasCompactSupport f) (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    (hq2 : (∫⁻ z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, IsPlanarRegularValue f t ∧ weightedScalarLevelLength D f q t < ∞ := by
  have hc := hcoarea D hD f (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn q hq
  have hfin := weighted_scalar_coarea_integral_lt_top hc hq hq2 hf2
  have hbad : volume {t | weightedScalarLevelLength D f q t = ∞} = 0 := by
    have ha := ae_lt_top' hc.1 hfin.ne
    rw [ae_iff] at ha
    simpa only [not_lt, top_le_iff] using ha
  have hcrit := hsard f hf hcompact
  have hnull : volume ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞}) = 0 := measure_union_null hcrit hbad
  have hpositive : 0 < volume (Ioo a b \ ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞})) := by
    rw [measure_sdiff_null hnull, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  obtain ⟨t, ht, hgood⟩ := nonempty_of_measure_ne_zero hpositive.ne'
  refine ⟨t, ht, ?_, ?_⟩
  · intro z hz hzero
    exact hgood (Or.inl ⟨z, hzero, hz⟩)
  · exact lt_top_iff_ne_top.mpr (fun ht => hgood (Or.inr ht))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteWeightedCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact cutoffs have finite differential energy, so weighted
coarea and Sard choose finite-cost regular contours without an added
energy hypothesis on the cutoff. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem smooth_compact_differential_energy {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hcompact : HasCompactSupport f) :
    (∫⁻ z, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞ := by
  have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := (↑(⊤ : ℕ∞))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  have hcont : Continuous (fun z => ‖fderiv ℝ f z‖ ^ 2) := hd.norm.pow 2
  have hsupp : HasCompactSupport (fun z => ‖fderiv ℝ f z‖ ^ 2) := by
    apply hcompact.mono'
    intro z hz
    by_contra hzf
    have hd := fderiv_of_notMem_tsupport ℝ hzf
    apply hz
    change ‖fderiv ℝ f z‖ ^ 2 = 0
    rw [hd]
    simp
  have hint : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hfin := (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun z => sq_nonneg ‖fderiv ℝ f z‖))).mp hint.hasFiniteIntegral
  simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using hfin

theorem exists_finite_weighted_regular_superlevel
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {A O : Set ℂ} (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻ z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ O ∧
      IsCompact {z | f z = t} ∧ IsPlanarRegularValue f t ∧
      frontier {z | t < f z} ⊆ {z | f z = t} ∧
      weightedScalarLevelLength univ f q t < ∞ := by
  obtain ⟨f, hf, hcompact, hsupp, hrange, hone⟩ := exists_smooth_planar_cutoff hA hO hAO
  obtain ⟨t, ht, hregular, hfinite⟩ := exists_weighted_regular_level hcoarea hsard isOpen_univ
    hf hcompact q hq (by simpa only [Measure.restrict_univ] using hq2)
    (by simpa only [Measure.restrict_univ] using smooth_compact_differential_energy hf hcompact)
    zero_lt_one
  have hclosure := closure_superlevel_subset_tsupport (f := f) ht.1
  refine ⟨f, t, hf, hcompact, hsupp, hrange, ht, isOpen_lt continuous_const hf.continuous,
    ?_, hcompact.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hsupp,
    isCompact_nonzero_level hf.continuous hcompact ht.1.ne', hregular, ?_, hfinite⟩
  · intro z hz
    change t < f z
    rw [hone.self_of_nhdsSet z hz]
    exact ht.2
  · intro z hz
    exact (frontier_lt_subset_eq continuous_const hf.continuous hz).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartLipschitz
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed physical sphere metric has locally Lipschitz finite charts.
This follows from the explicit smooth inverse stereographic formula in
Mathlib, including the linear coordinates chosen by the sphere homeomorphism. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section

namespace CircleDomainRigidity

theorem contDiff_roundSphere_finite_chart :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) := by
  classical
  have hlin (W : Submodule ℝ RoundAmbient) (e : ℂ ≃L[ℝ] W) :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => (e z : RoundAmbient)) :=
    W.subtypeL.contDiff.comp e.contDiff
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux _ ∘ _)
  apply contDiff_stereoInvFunAux.comp
  exact hlin _ _

attribute [local instance] sphereMetric

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LinearChartWeight
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed linear coordinates in the sphere homeomorphism preserve
the inverse quadratic decay of stereographic derivatives. -/

noncomputable section

namespace CircleDomainRigidity

theorem linear_chart_inverse_quadratic_bound
    {v : RoundAmbient} (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    16 * ‖A.toContinuousLinearMap‖ / (‖A z‖ ^ 2 + 4) ≤
      (16 * ‖A.toContinuousLinearMap‖ * (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2)) /
        (1 + ‖z‖ ^ 2) := by
  have hlin : ‖z‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A z‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      A.symm.toContinuousLinearMap.le_opNorm (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg z) hlin 2
  simp only [mul_pow] at hsq
  have hden : 1 + ‖z‖ ^ 2 ≤
      (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2) * (‖A z‖ ^ 2 + 4) := by
    nlinarith [sq_nonneg ‖A.symm.toContinuousLinearMap‖, sq_nonneg ‖A z‖]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    _ ≤ (16 * ‖A.toContinuousLinearMap‖) *
        ((1 + ‖A.symm.toContinuousLinearMap‖ ^ 2) * (‖A z‖ ^ 2 + 4)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- Actual finite smooth Jordan disks covering a chosen compact part of an
obstacle, with disjoint closures contained in the prescribed physical open
set. Its complement is required connected and unbounded precisely for the
hole-filling containment argument. -/
theorem exists_finite_smooth_jordan_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, _⟩ :=
    exists_regular_superlevel_isolating_obstacle hsard hA hAF hFA hV hAV
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSmoothContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth obstacle-isolating contours whose actual Hausdorff arclength
integral against the prescribed density is finite. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Manifold

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_regular_isolating_obstacle
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻ z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ V ∧
      closure {z | t < f z} ∩ F = A ∧ IsCompact {z | f z = t} ∧
      IsPlanarRegularValue f t ∧ Disjoint {z | f z = t} F ∧
      weightedScalarLevelLength univ f q t < ∞ := by
  let O := V ∩ (F \ A)ᶜ
  have hO : IsOpen O := hV.inter hFA.isOpen_compl
  have hAO : A ⊆ O := fun z hz => ⟨hAV hz, fun hbad => hbad.2 hz⟩
  obtain ⟨f, t, hf, _, hsupp, _, ht, hopen, hAU, hcompact, hclO,
    hlevel, hregular, _, hfinite⟩ :=
    exists_finite_weighted_regular_superlevel hcoarea hsard hA hO hAO q hq hq2
  have hclF : closure {z | t < f z} ∩ F = A := by
    apply Subset.antisymm
    · intro z hz
      by_contra hzA
      exact (hclO hz.1).2 ⟨hz.2, hzA⟩
    · intro z hz
      exact ⟨subset_closure (hAU hz), hAF hz⟩
  have hdisj : Disjoint {z | f z = t} F := by
    apply disjoint_left.mpr
    intro z hz hzF
    have hzSupp : z ∈ tsupport f := subset_tsupport f (by
      change f z ≠ 0
      rw [hz]
      exact ht.1.ne')
    have hzA : z ∈ A := by
      by_contra hnot
      exact (hsupp hzSupp).2 ⟨hzF, hnot⟩
    have hh := hAU hzA
    change t < f z at hh
    rw [hz] at hh
    exact hh.false
  exact ⟨f, t, hf, ht, hopen, hAU, hcompact, fun z hz => (hclO hz).1,
    hclF, hlevel, hregular, hdisj, hfinite⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedJordanCovers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Jordan fillings of finite-weight regular levels. The selected
frontiers retain the original regular-level equation and weighted bound. -/

open Set Filter Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_finite_weighted_jordan_cover
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ V ∧ Disjoint {z | f z = t} F ∧
      (∫⁻z in {z | f z = t}, q z ∂(μH[1] : Measure ℂ)) < ∞ ∧
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F ∧
        frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, hcost⟩ :=
    exists_weighted_regular_isolating_obstacle hcoarea hsard hA hAF hFA hV hAV q hq hq2
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  have hlevelV : {z | f z = t} ⊆ V := fun z hz =>
    hUV (frontier_subset_closure (hUd.symm ▸ hz))
  have hfiniteCost : (∫⁻z in {z | f z = t}, q z ∂(μH[1] : Measure ℂ)) < ∞ := by
    simpa only [weightedScalarLevelLength, univ_inter] using hcost
  refine ⟨f, t, γ, H, s, hf, hregular, hlevelV, havoid, hfiniteCost, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i), hfrontlevel i⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClopenNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a component by a clopen neighborhood

This is the compact-space step before the smooth contour construction:
a neighborhood containing a whole component contains a clopen
neighborhood of that component's base point. Applied in a closed
obstacle set, it isolates a singleton dust component.
-/

open Set

namespace CircleDomainRigidity

theorem exists_clopen_between_component_and_open
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) {O : Set X} (hO : IsOpen O) (hC : connectedComponent x ⊆ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  classical
  have hd : Disjoint Oᶜ (connectedComponent x) :=
    Set.disjoint_left.mpr (fun y hy hyC => hy (hC hyC))
  rw [connectedComponent_eq_iInter_isClopen x] at hd
  obtain ⟨s, hs⟩ := hO.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun V : {V : Set X // IsClopen V ∧ x ∈ V} => V.val)
    (fun V => V.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  refine ⟨⋂ V ∈ s, (V : Set X), isClopen_biInter_finset (fun V _ => V.property.1),
    mem_iInter₂.mpr (fun V _ => V.property.2), ?_⟩
  intro y hy
  by_contra hyO
  exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hyO hy

/-- In particular, singleton components in a compact closed obstacle
have arbitrarily small relatively clopen neighborhoods. -/
theorem exists_clopen_neighborhood_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) (hC : connectedComponent x = {x}) {O : Set X}
    (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O :=
  exists_clopen_between_component_and_open x hO (by simpa only [hC, singleton_subset_iff] using hx)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPhysicalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small physical disks at singleton quotient components

A singleton component of a closed quotient obstacle has a compact relatively
clopen neighborhood inside any prescribed open neighborhood. Pulling it back
and applying the proved smooth contour construction gives actual physical
Jordan disks. The boundaries avoid the entire quotient obstacle, and hence
lie in the physical domain whenever that obstacle contains the collapsed
complementary components.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The compact relatively clopen obstacle piece used before smoothing. -/
theorem exists_compact_piece_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ A : Set X, IsCompact A ∧ x ∈ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  have hcomp : connectedComponent xf = {xf} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hy' : y.val ∈ connectedComponentIn F x := by
        rw [connectedComponentIn_eq_image hx]
        exact ⟨y, hy, rfl⟩
      rw [hcomponent] at hy'
      exact mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hy'))
    · exact singleton_subset_iff.mpr mem_connectedComponent
  obtain ⟨B, hB, hxB, hBV⟩ := exists_clopen_neighborhood_of_singleton_component xf hcomp
    (hV.preimage continuous_subtype_val) hxV
  let A : Set X := Subtype.val '' B
  have hdiff : F \ A = Subtype.val '' Bᶜ := by
    ext y
    constructor
    · rintro ⟨hyF, hyA⟩
      exact ⟨⟨y, hyF⟩, fun h => hyA ⟨⟨y, hyF⟩, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hy (hzy' ▸ hz)
  refine ⟨A, hB.isClosed.isCompact.image continuous_subtype_val,
    ⟨xf, hxB, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · rintro _ ⟨y, hy, rfl⟩
    exact hBV hy
  · rw [hdiff]
    exact hF.isClosedMap_subtype_val _ hB.isOpen.isClosed_compl

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SinglePhysicalDisk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single smooth physical disk about a quotient singleton

Connectedness of the fiber upgrades the finite disjoint cover to a single
disk. The general open-family lemma does not need finiteness.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_member_containing_connected_set
    {X I : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ i, S ⊆ U i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let V : Set X := ⋃ j ∈ ({i}ᶜ : Set I), U j
  have hV : IsOpen V := isOpen_biUnion (fun j _ => hU j)
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro z hz hzV
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzV
    exact Set.disjoint_left.mp (hd (fun h => hj (mem_singleton_iff.mpr h.symm))) hz hzj
  have hSC : S ⊆ U i ∪ V := by
    intro z hz
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, by simpa using hji, hzj⟩)
  rcases hS.isPreconnected.subset_or_subset (hU i) hV hUV hSC with h | h
  · exact ⟨i, h⟩
  · exact (Set.disjoint_left.mp hUV hxi (h hx)).elim

theorem isConnected_finite_fiber
    {X : Type*} (π : Sphere → X) (hfibers : ∀ x, IsConnected (π ⁻¹' {x}))
    {x : X} (hne : π OnePoint.infty ≠ x) :
    IsConnected {z : ℂ | π (z : Sphere) = x} := by
  have heq : ((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x} = π ⁻¹' {x} := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [hne]
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  have hconn : IsConnected (((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x}) :=
    heq.symm ▸ hfibers x
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hconn.isPreconnected⟩
  obtain ⟨p, hp⟩ := hconn.nonempty
  obtain ⟨z, hz, _⟩ := hp
  exact ⟨z, hz⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedPhysicalCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-cost smooth physical collars of an actual collapsed component.
The regular level containing the chosen boundary is retained explicitly. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_small_physical_disk
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (f : ℂ → ℝ) (t : ℝ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      frontier (jordanInterior H) ⊆ {z | f z = t} ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      (∀ z, f z = t → (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) ∧
      (∫⁻z in {z | f z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
  classical
  obtain ⟨hphysical, hunbounded⟩ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      hV hVconn hinfty
  obtain ⟨A, hAc, hxA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_of_singleton_component hF hx hcomponent hV hxV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) := by
    apply isCompact_finite_preimage (hAc.isClosed.preimage hπ)
    exact fun h => hinfty (subset_closure (hAV h))
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hf, hreg, hlevelV, havoid, hcost,
    _, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_weighted_jordan_cover hcoarea hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV)
      hphysical hunbounded g hg hg2
  have hfiber : IsConnected {z : ℂ | π (z : Sphere) = x} := by
    apply isConnected_finite_fiber π (connected_fibers_of_component_collapse G π hsurj hr)
    intro heq
    exact hinfty (subset_closure (heq.symm ▸ hxV))
  have hpair : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hd i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcover : {z : ℂ | π (z : Sphere) = x} ⊆ ⋃ i : s, jordanInterior (H i) := by
    intro z hz
    have hzA : z ∈ q ⁻¹' A := by
      change π (z : Sphere) ∈ A
      rwa [hz]
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hzA)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hfiber
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair hcover
  obtain ⟨hγ, hemb, hfront, _, hfrontlevel⟩ := hcurves i i.property
  refine ⟨H i, γ i, f, t, hi, hinside i i.property, hγ, hemb, hfront,
    hfrontlevel, hf, hreg, hlevelV, ?_, hcost⟩
  intro z hz
  have hnot : π (z : Sphere) ∉ F := fun h => disjoint_left.mp havoid hz h
  refine ⟨?_, hnot⟩
  by_contra h
  exact hnot (hbad _ h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tag-tuple measures. Tuple components retain the label list;
slot weights depend only on the slot number and have finite total mass. -/

open Set MeasureTheory TopologicalSpace Topology
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem slotWeight_pos (k : ℕ) : 0 < slotWeight k := by
  unfold slotWeight
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))

theorem tsum_slotWeight : ∑' k, slotWeight k = 2 := ENNReal.tsum_geometric_two

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Saturation of physical Jordan interiors

A connected quotient fiber cannot cross a boundary consisting of singleton
fibers. Thus physical Jordan interiors whose boundaries lie in the original
domain are saturated, and project to open quotient neighborhoods. This is
the saturation assertion preceding the small-disks lemma in Section 1.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem preimage_image_open_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' U) = U := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    let K : Set X := π ⁻¹' {π p}
    have hpK : p ∈ K := rfl
    have hmiss : Disjoint K (frontier U) := by
      apply Set.disjoint_left.mpr
      intro z hz hzfront
      have hpz : p = z := hsing z hzfront p hz.symm
      have hpfront : p ∈ frontier U := hpz.symm ▸ hzfront
      rw [hU.frontier_eq] at hpfront
      exact hpfront.2 hp
    have hsplit : K ⊆ U ∨ K ⊆ (closure U)ᶜ := by
      apply (hfibers (π p)).subset_or_subset hU isClosed_closure.isOpen_compl
      · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
      · intro z hz
        by_cases hzU : z ∈ U
        · exact Or.inl hzU
        · right
          intro hzcl
          apply Set.disjoint_left.mp hmiss hz
          rw [hU.frontier_eq]
          exact ⟨hzcl, hzU⟩
    rcases hsplit with hin | hout
    · exact hin hpq.symm
    · exact (hout hpK (subset_closure hp)).elim
  · exact subset_preimage_image π U

/-- Physical Jordan disks with boundary in the domain are saturated for
the actual component-collapse quotient. -/
theorem preimage_image_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
  apply preimage_image_open_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

/-- The saturated physical disk projects to an open quotient neighborhood. -/
theorem isOpen_image_jordanInterior_of_component_collapse
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    IsOpen (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  apply (hclosed.isQuotientMap hπ hsurj).isOpen_preimage.mp
  rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary]
  exact OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted collars in the physical plane and their actual open quotient
neighborhoods. Compact containment survives projection. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

theorem isOpen_region (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsOpen D.region :=
  isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr D.disk
    (fun z hz => (D.level_good z (D.frontier_level hz)).1)

theorem point_mem_region (hsurj : Surjective π) (hp : p ≠ π OnePoint.infty) :
    p ∈ D.region := by
  obtain ⟨x, hx⟩ := hsurj p
  cases x using OnePoint.rec with
  | infty => exact (hp hx.symm).elim
  | coe z => exact ⟨z, ⟨z, D.fiber_inside hx, rfl⟩, hx⟩

theorem closure_region_subset_image (hπ : Continuous π) :
    closure D.region ⊆ π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior D.disk)) := by
  apply closure_minimal (image_mono (image_mono subset_closure))
  exact (((isCompact_closure_jordanInterior D.disk).image OnePoint.continuous_coe).image hπ).isClosed

theorem closure_region_subset {V : Set Sphere} (hπ : Continuous π)
    (hV : closure (jordanInterior D.disk) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) :
    closure D.region ⊆ V := by
  intro x hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := D.closure_region_subset_image hπ hx
  exact hV hz

end WeightedCollar

theorem exists_weighted_collar_in_neighborhood
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {O : Set Sphere} (hO : IsOpen O) (hpO : p ∈ O)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : WeightedCollar G π B p g,
      closure D.region ⊆ O ∧ {z | D.function z = D.level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O := by
  obtain ⟨V, hV, hpV, hVO, hVc⟩ := exists_sphere_neighborhood_connected_compl
    (hO.inter isClosed_singleton.isOpen_compl) ⟨hpO, hp⟩
  have hcomponent : connectedComponentIn B p = {p} :=
    (hTD _ (connectedComponentIn_subset B p) isPreconnected_connectedComponentIn).eq_singleton_of_mem
      (mem_connectedComponentIn hpB)
  obtain ⟨H, γ, f, t, hfiber, hinside, hsmooth, hemb, hfront, hfrontlevel,
    hf, hreg, hlevelV, hgood, hcost⟩ :=
    exists_weighted_small_physical_disk hcoarea hsard hsch G π hπ hclosed hsurj hr
      hB hpB hcomponent hV hpV hVc (fun h => (hVO h).2 rfl) hbad g hg hg2
  let D : WeightedCollar G π B p g :=
    ⟨H, γ, f, t, hfiber, hsmooth, hemb, hfront, hfrontlevel, hf, hreg, hgood, hcost⟩
  refine ⟨D, ?_, ?_⟩
  · exact (D.closure_region_subset hπ hinside).trans (fun _ h => (hVO (subset_closure h)).1)
  · exact hlevelV.trans (fun _ h => (hVO (subset_closure h)).1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NestedWeightedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strictly nested actual weighted collars, chosen inside any prescribed
sequence of quotient neighborhoods. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_nested_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (O : ℕ → Set Sphere) (hO : ∀n, IsOpen (O n)) (hpO : ∀n, p ∈ O n)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      (∀n, closure (D n).region ⊆ O n) ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D n).function z = (D n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O n) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) := by
  classical
  obtain ⟨D0, hD0, hL0⟩ := exists_weighted_collar_in_neighborhood hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hpB hp (hO 0) (hpO 0) g hg hg2
  have hstep : ∀ (n : ℕ) (D : WeightedCollar G π B p g),
      ∃ E : WeightedCollar G π B p g,
        closure E.region ⊆ D.region ∩ O (n+1) ∧
        {z | E.function z = E.level} ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' (D.region ∩ O (n+1)) := by
    intro n D
    exact exists_weighted_collar_in_neighborhood hcoarea hsard hsch
      G π hπ hclosed hsurj hr hB hTD hbad hpB hp
      ((D.isOpen_region hπ hclosed hsurj hr).inter (hO (n+1)))
      ⟨D.point_mem_region hsurj hp, hpO (n+1)⟩ g hg hg2
  choose step hstep using hstep
  let D : ℕ → WeightedCollar G π B p g := Nat.rec D0 step
  have hs (n : ℕ) : D (n+1) = step n (D n) := rfl
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hD0
    | succ n => exact fun z hz => ((hstep n (D n)).1 hz).2
  · intro n z hz
    exact ((hstep n (D n)).1 hz).1
  · intro n
    cases n with
    | zero => exact hL0
    | succ n => exact fun z hz => ((hstep n (D n)).2 hz).2
  · intro n z hz
    exact ((hstep n (D n)).2 hz).1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite circle-uniformization input

Conway, *Functions of One Complex Variable II*, GTM 159 (1995),
Theorem 15.7.9, p. 106, gives circle uniformization of nondegenerate
finitely connected regions. `FiniteCircleUniformization` records only
its existence conclusion on the sphere, omitting normalization and
uniqueness. It is an explicit proposition parameter, not an axiom.

The complement components of a finite family of disjoint closed
connected sets are identified below. This checks the finiteness and
nondegeneracy hypotheses for completed surfaces, also after an arbitrary
sphere homeomorphism such as compact metric uniformization.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem connectedComponentIn_finite_disjoint_closed
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    {i : I} {p : X} (hp : p ∈ C i) :
    connectedComponentIn (⋃ j, C j) p = C i := by
  classical
  let R : Set X := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hC j)
  have hCR : Disjoint (C i) R := by
    apply Set.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj
  have hcover : (⋃ j, C j) ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hsub : connectedComponentIn (⋃ j, C j) p ⊆ C i := by
    have hs := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := ⋃ j, C j) (x := p))
      (C i) R (hC i) hR ((connectedComponentIn_subset _ _).trans hcover)
      (by rw [hCR.inter_eq, inter_empty])
    rcases hs with h | h
    · exact h
    · exact fun x hx => (Set.disjoint_left.mp hCR hp
        (h (mem_connectedComponentIn (mem_iUnion.mpr ⟨i, hp⟩)))).elim
  exact hsub.antisymm ((hconn i).subset_connectedComponentIn hp (subset_iUnion C i))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExteriorDecay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform principal remainder estimate

The same coefficient-area input gives decay at infinity, uniformly in
the finite model. This is stronger than a uniform bounded remainder and
preserves the zero constant term when passing to a limit.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem norm_exterior_series_le_two_inv {c : ℕ → ℂ} {z w : ℂ}
    (hc : ∀ n, ‖c n‖ ≤ 1) (hz : 2 ≤ ‖z‖)
    (hw : HasSum (fun n => c n * (z⁻¹) ^ (n + 1)) w) : ‖w‖ ≤ 2 * ‖z‖⁻¹ := by
  let r : ℝ := ‖z‖⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (norm_nonneg z)
  have hrhalf : r ≤ 1 / 2 := by
    dsimp only [r]
    simpa only [one_div] using
      (inv_le_inv₀ (by linarith : 0 < ‖z‖) (by norm_num : (0 : ℝ) < 2)).mpr hz
  have hr1 : r < 1 := by linarith
  have hg : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have hle := hw.norm_le_of_bounded hg (fun n => show ‖c n * (z⁻¹) ^ (n + 1)‖ ≤ r ^ (n + 1) from by
    rw [norm_mul, norm_pow, norm_inv]
    exact mul_le_of_le_one_left (pow_nonneg hr0 _) (hc n))
  refine hle.trans ?_
  change r / (1 - r) ≤ 2 * r
  apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
  nlinarith [mul_nonneg hr0 (show 0 ≤ 1 - 2 * r by linarith)]

theorem ExteriorCoefficientAreaTheorem.exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 1 < ‖z‖}) (hinj : InjOn F {z | 1 < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * ‖z‖⁻¹ := by
  obtain ⟨c, hc, hbound, hseries⟩ := harea F hF hinj hnorm
  intro z hz
  exact norm_exterior_series_le_two_inv (norm_coefficient_le_one hc hbound) hz
    (hseries z (by linarith))

theorem ExteriorCoefficientAreaTheorem.scaled_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem) {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖})
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let H : ℂ → ℂ := fun z => F ((R : ℂ) * z) / (R : ℂ)
  have harg {z : ℂ} (hz : 1 < ‖z‖) : R < ‖(R : ℂ) * z‖ := by
    rw [norm_mul, hnormR]
    nlinarith
  have hH : DifferentiableOn ℂ H {z | 1 < ‖z‖} := by
    intro z hz
    have hfd := (hF _ (harg hz)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (harg hz))
    exact ((hfd.comp z ((differentiableAt_id.const_mul (R : ℂ)))).div_const _).differentiableWithinAt
  have hHi : InjOn H {z | 1 < ‖z‖} := by
    intro z hz w hw heq
    have heq' : F ((R : ℂ) * z) = F ((R : ℂ) * w) := (div_left_inj' hRc).mp heq
    exact mul_left_cancel₀ hRc (hinj (harg hz) (harg hw) heq')
  have hnH := principal_remainder_rescale hRc hnorm
  intro z hz
  have hnormquot : ‖z / (R : ℂ)‖ = ‖z‖ / R := by rw [norm_div, hnormR]
  have hquot : 2 ≤ ‖z / (R : ℂ)‖ := by
    rw [hnormquot]
    exact (le_div_iff₀ hR).mpr (by linarith)
  have hb := harea.exterior_decay hH hHi hnH (z / (R : ℂ)) hquot
  have heq : H (z / (R : ℂ)) - z / (R : ℂ) = (F z - z) / (R : ℂ) := by
    dsimp only [H]
    rw [mul_div_cancel₀ z hRc]
    ring
  rw [heq, norm_div, hnormR, hnormquot] at hb
  have hzn : 0 < ‖z‖ := by linarith
  have hb' := (div_le_iff₀ hR).mp hb
  calc
    ‖F z - z‖ ≤ 2 * (‖z‖ / R)⁻¹ * R := hb'
    _ = 2 * R ^ 2 / ‖z‖ := by field_simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalFamilyInputs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Classical normal-family inputs

The two propositions are classical consequences of Ahlfors,
*Complex Analysis*, third edition (1979):

* Chapter 5, Theorem 15, p. 224 (Montel compactness), in its diagonal
  exhaustion form, with the varying-domain convention of Chapter 5,
  Section 1.1, pp. 176–177. Holomorphy of the locally uniform limit
  follows from Mathlib.
* Chapter 5, Theorem 2, p. 178 (Hurwitz), applied to injective maps as in
  Chapter 6, Section 1.1, p. 231. Discarding finitely many initial terms
  gives the eventually holomorphic and injective formulation.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem holomorphic_limit_on_exhaustion
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n)) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n)) :
    DifferentiableOn ℂ f (⋃ n, D n) := by
  intro z hz
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  have hFm : ∀ᶠ n in atTop, DifferentiableOn ℂ (F (s n)) (D m) := by
    filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
    exact (hF (s n)).mono (hmono hn)
  have hf := (hlim.mono (subset_iUnion D m)).differentiableOn hFm (hD m)
  exact (hf.differentiableAt ((hD m).mem_nhds hm)).differentiableWithinAt

theorem univalent_limit_on_exhaustion
    (hhurwitz : HurwitzUnivalentLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n))
    (hmono : Monotone D) (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFi : ∀ n, InjOn (F n) (D n)) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n))
    (hnonconst : ∀ n, ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c) :
    InjOn f (⋃ n, D n) := by
  have hfm (m : ℕ) : InjOn f (D m) := by
    apply hhurwitz (D m) (fun n => F (s n)) f (hD m) (hconn m)
    · filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
      exact ⟨(hF (s n)).mono (hmono hn), (hFi (s n)).mono (hmono hn)⟩
    · exact hlim.mono (subset_iUnion D m)
    · exact hnonconst m
  intro z hz w hw heq
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hw
  exact hfm (max m n) (hmono (le_max_left _ _) hm) (hmono (le_max_right _ _) hn) heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MarkedDiskLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous limits of marked round disks

Bounded centers and nonnegative bounded radii form a compact parameter
space. A countable family therefore admits one subsequence on which all
parameters converge. The limiting radius may be zero.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_marked_disk_parameter_limits
    {B : Type*} [Countable B] {L : ℝ}
    (c : ℕ → B → ℂ) (r : ℕ → B → ℝ)
    (hc : ∀ n b, ‖c n b‖ ≤ L) (hr : ∀ n b, r n b ∈ Icc 0 L) :
    ∃ (s : ℕ → ℕ) (c₀ : B → ℂ) (r₀ : B → ℝ),
      StrictMono s ∧ (∀ b, ‖c₀ b‖ ≤ L ∧ r₀ b ∈ Icc 0 L) ∧
      (∀ b, Tendsto (fun n => c (s n) b) atTop (𝓝 (c₀ b))) ∧
      (∀ b, Tendsto (fun n => r (s n) b) atTop (𝓝 (r₀ b))) := by
  let P : Set (B → ℂ × ℝ) := pi univ (fun _ => closedBall (0 : ℂ) L ×ˢ Icc 0 L)
  have hP : IsCompact P := isCompact_univ_pi fun _ => (isCompact_closedBall 0 L).prod isCompact_Icc
  let v : ℕ → B → ℂ × ℝ := fun n b => (c n b, r n b)
  have hv : ∀ n, v n ∈ P := by
    intro n b _
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hc n b, hr n b⟩
  obtain ⟨v₀, hv₀, s, hs, hlim⟩ := hP.tendsto_subseq hv
  refine ⟨s, fun b => (v₀ b).1, fun b => (v₀ b).2, hs, ?_, ?_, ?_⟩
  · intro b
    have hb := hv₀ b (mem_univ b)
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hb.1, hb.2⟩
  · intro b
    exact (continuous_fst.tendsto (v₀ b)).comp (tendsto_pi_nhds.mp hlim b)
  · intro b
    exact (continuous_snd.tendsto (v₀ b)).comp (tendsto_pi_nhds.mp hlim b)

theorem exists_closedBall_point_dist_le
    {c d x : ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : x ∈ closedBall c r) :
    ∃ y ∈ closedBall d s, dist x y ≤ dist c d + |r - s| := by
  rw [closedBall_eq_affine_image hr c] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨d + s • u, ?_, ?_⟩
  · rw [closedBall_eq_affine_image hs d]
    exact mem_image_of_mem _ hu
  · have hu' : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
    have heq : c + r • u - (d + s • u) = (c - d) + (r - s) • u := by
      rw [sub_smul]
      abel
    calc
      dist (c + r • u) (d + s • u) = ‖(c - d) + (r - s) • u‖ := by
        rw [dist_eq_norm, heq]
      _ ≤ ‖c - d‖ + ‖(r - s) • u‖ := norm_add_le _ _
      _ ≤ dist c d + |r - s| := by
        rw [norm_smul, Real.norm_eq_abs, dist_eq_norm]
        nlinarith [abs_nonneg (r - s)]

theorem hausdorffDist_closedBall_le_parameters
    {c d : ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    hausdorffDist (closedBall c r) (closedBall d s) ≤ dist c d + |r - s| := by
  refine hausdorffDist_le_of_mem_dist (by positivity)
    (fun _ hx => exists_closedBall_point_dist_le hr hs hx) ?_
  intro y hy
  simpa only [dist_comm d c, abs_sub_comm s r] using
    exists_closedBall_point_dist_le (d := c) hs hr hy

theorem tendsto_hausdorffDist_closedBall
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hlim : Tendsto r atTop (𝓝 r₀)) :
    Tendsto (fun n => hausdorffDist (closedBall (c n) (r n)) (closedBall c₀ r₀))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n => dist (c n) c₀ + |r n - r₀|) atTop (𝓝 0) := by
    simpa only [dist_self, sub_self, abs_zero, add_zero] using
      (hc.dist (tendsto_const_nhds (x := c₀))).add
        ((hlim.sub (tendsto_const_nhds (x := r₀))).abs)
  exact squeeze_zero (fun _ => hausdorffDist_nonneg)
    (fun n => hausdorffDist_closedBall_le_parameters (hr n) hr₀) hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized limits on exhausting retained cores

The uniform finite-model bounds give local boundedness. The common
decaying exterior remainder passes to the limit and prevents a constant
limit on any retained core containing the exterior. Hurwitz then gives
global injectivity. A further subsequence retains all these conclusions
and converges for every marked complementary disk simultaneously.
-/

open Set Filter Function Asymptotics Bornology Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exterior_decay_le_radius {R t : ℝ} (hR : 0 < R) (ht : 2 * R ≤ t) :
    2 * R ^ 2 / t ≤ R := by
  apply (div_le_iff₀ (by linarith : 0 < t)).mpr
  nlinarith

theorem not_constant_of_exterior_decay
    {D : Set ℂ} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hD : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D)
    (hbound : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c := by
  rintro ⟨c, hc⟩
  let t : ℝ := 2 * R + ‖c‖ + 1
  have ht : 0 < t := by dsimp only [t] <;> positivity
  have htn : ‖(t : ℂ)‖ = t := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hlarge : 2 * R ≤ ‖(t : ℂ)‖ := by
    rw [htn]
    dsimp only [t]
    linarith [norm_nonneg c]
  have hb := (hbound (t : ℂ) hlarge).trans (exterior_decay_le_radius hR hlarge)
  rw [hc _ (hD hlarge)] at hb
  have hnorm := norm_le_norm_sub_add (t : ℂ) c
  rw [norm_sub_rev, htn] at hnorm
  dsimp only [t] at hnorm
  linarith

theorem principal_remainder_of_exterior_decay
    {f : ℂ → ℂ} {R : ℝ}
    (hbound : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    (fun z => f z - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  apply isBigO_iff.mpr
  refine ⟨2 * R ^ 2, ?_⟩
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (2 * R)] with z hz
  simpa only [norm_inv, div_eq_mul_inv] using hbound z hz

theorem exists_normalized_univalent_limit
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n))
    (hmono : Monotone D) (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFi : ∀ n, InjOn (F n) (D n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    (hbounded : ∀ n z, z ∈ D n → ‖z‖ ≤ 4 * R → ‖F n z‖ ≤ 5 * R)
    (hdecay : ∀ n z, 2 * R ≤ ‖z‖ → ‖F n z - z‖ ≤ 2 * R ^ 2 / ‖z‖) :
    ∃ (s : ℕ → ℕ) (f : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n) ∧
      DifferentiableOn ℂ f (⋃ n, D n) ∧ InjOn f (⋃ n, D n) ∧
      (fun z => f z - z) =O[cobounded ℂ] (fun z => z⁻¹) ∧
      ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hlocal : ∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
      ∃ M : ℝ, ∀ n z, z ∈ K → z ∈ D n → ‖F n z‖ ≤ M := by
    intro K hK _
    obtain ⟨A, hA⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    refine ⟨A + 5 * R, ?_⟩
    intro n z hzK hzD
    have hzA : ‖z‖ ≤ A := by simpa only [mem_closedBall, dist_zero_right] using hA hzK
    by_cases hz : ‖z‖ ≤ 4 * R
    · linarith [hbounded n z hzD hz, norm_nonneg z]
    · have hlarge : 2 * R ≤ ‖z‖ := by linarith
      have hb := (hdecay n z hlarge).trans (exterior_decay_le_radius hR hlarge)
      have hn := norm_le_norm_sub_add (F n z) z
      linarith
  obtain ⟨s, f, hs, hlim⟩ := hmontel D F hD hmono hF hlocal
  have hlimdecay : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖f z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
    intro z hz
    have hzU : z ∈ ⋃ n, D n := mem_iUnion.mpr ⟨0, hext hz⟩
    exact le_of_tendsto ((hlim.tendsto_at hzU).sub tendsto_const_nhds).norm
      (Eventually.of_forall (fun n => hdecay (s n) z hz))
  have hnonconst (n : ℕ) : ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c :=
    not_constant_of_exterior_decay hR (hext.trans (hmono (Nat.zero_le n))) hlimdecay
  exact ⟨s, f, hs, hlim, holomorphic_limit_on_exhaustion hD hmono hF hs hlim,
    univalent_limit_on_exhaustion hhurwitz hD hconn hmono hF hFi hs hlim hnonconst,
    principal_remainder_of_exterior_decay hlimdecay, hlimdecay⟩

theorem locally_uniform_subsequence
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : ℕ → ℕ}
    (hlim : TendstoLocallyUniformlyOn F f atTop D) (hs : StrictMono s) :
    TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop D := by
  intro u hu z hz
  obtain ⟨O, hO, h⟩ := hlim u hu z hz
  exact ⟨O, hO, hs.tendsto_atTop.eventually h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereModelLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying normalized compactness to sphere models

All complex-plane hypotheses of the compactness theorem are obtained
from actual normalized smooth sphere equivalences and their retained
holomorphic cores. The exterior estimate follows from the univalent
area theorem.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem finite_part_injOn
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V)
    (hinf : OnePoint.infty ∈ Q) (hfix : f OnePoint.infty = OnePoint.infty)
    {D : Set ℂ} (hDQ : ∀ z ∈ D, (z : Sphere) ∈ Q) :
    InjOn (fun z : ℂ => finiteCoord (f (z : Sphere))) D := by
  intro z hz w hw he
  apply OnePoint.coe_injective
  apply heq.bijOn.injOn (hDQ z hz) (hDQ w hw)
  calc
    f (z : Sphere) = ((finiteCoord (f (z : Sphere)) : ℂ) : Sphere) :=
      (coe_finiteCoord (heq.finite_forward hinf hfix (hDQ z hz))).symm
    _ = ((finiteCoord (f (w : Sphere)) : ℂ) : Sphere) := congrArg ((↑) : ℂ → Sphere) he
    _ = f (w : Sphere) := coe_finiteCoord (heq.finite_forward hinf hfix (hDQ w hw))

theorem finite_part_differentiableOn
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V)
    (hinf : OnePoint.infty ∈ Q) (hfix : f OnePoint.infty = OnePoint.infty)
    {D : Set ℂ} (hD : IsOpen D) (hDQ : ∀ z ∈ D, (z : Sphere) ∈ Q)
    (hconf : IsConformalOn f (((↑) : ℂ → Sphere) '' D)) :
    DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (z : Sphere))) D := by
  intro z hz
  exact (analyticAt_finite_map_of_conformal (OnePoint.isOpenMap_coe D hD)
    hconf (mem_image_of_mem _ hz)
    (heq.finite_forward hinf hfix (hDQ z hz))).differentiableAt.differentiableWithinAt

theorem normalized_sphere_model_exterior_decay
    (harea : ExteriorCoefficientAreaTheorem)
    {f fi : Sphere → Sphere} {Q V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi Q V) {R : ℝ} (hR : 0 < R)
    (hsource : ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q)
    (hconf : IsConformalOn f ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : IsPrincipalNormalized f) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ →
      ‖finiteCoord (f (z : Sphere)) - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hinf : OnePoint.infty ∈ Q := hsource (by simp)
  have hDQ : ∀ z : ℂ, z ∈ {z | R < ‖z‖} → (z : Sphere) ∈ Q := by
    intro z hz
    apply hsource
    simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_ball,
      dist_zero_right, mem_compl_iff, not_lt] using hz.le
  apply harea.scaled_exterior_decay hR
  · apply finite_part_differentiableOn heq hinf hnorm.1
      (isOpen_lt continuous_const continuous_norm) hDQ
    apply hconf.mono
    rintro _ ⟨z, hz, rfl⟩
    simpa only [OnePoint.coe_injective.mem_set_image, Metric.mem_closedBall,
      dist_zero_right, mem_compl_iff, not_le] using (show R < ‖z‖ from hz)
  · exact finite_part_injOn heq hinf hnorm.1 hDQ
  · exact hnorm.2

theorem exists_normalized_limit_of_sphere_models
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsOpen (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      DifferentiableOn ℂ F (⋃ n, D n) ∧ InjOn F (⋃ n, D n) ∧
      (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) ∧
      ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖F z - z‖ ≤ 2 * R ^ 2 / ‖z‖ := by
  have hinf (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  apply exists_normalized_univalent_limit hmontel hhurwitz hR hD hconn hmono
    (fun n => finite_part_differentiableOn (heq n) (hinf n) (hnorm n).1
      (hD n) (hDQ n) (hcore n))
    (fun n => finite_part_injOn (heq n) (hinf n) (hnorm n).1 (hDQ n)) hext
  · intro n z hz hzn
    obtain ⟨_, hbound⟩ := normalized_model_uniform_bound harea (heq n) (hV n)
      hR (hsource n) (hconf n) (hnorm n)
    obtain ⟨w, hw, hweq⟩ := hbound z (hDQ n z hz) hzn
    have he : w = finiteCoord (f n (z : Sphere)) := by
      have := congrArg finiteCoord hweq
      simpa only [finiteCoord_coe] using this
    simpa only [Metric.mem_closedBall, dist_zero_right, he] using hw
  · intro n
    exact normalized_sphere_model_exterior_decay harea (heq n) hR
      (hsource n) (hconf n) (hnorm n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LimitSphereExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extending a principally normalized limit across infinity

The uniform principal remainder does more than prevent a constant
limit: it gives continuity on the sphere and chart derivative one at
infinity. This step needs no further analytic input.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuousAt_extendAtInfinity_infty {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ContinuousAt (extendAtInfinity F) OnePoint.infty := by
  rw [OnePoint.continuousAt_infty']
  change Tendsto (fun z : ℂ => (F z : Sphere)) (coclosedCompact ℂ) (𝓝 OnePoint.infty)
  have hcoe : Tendsto ((↑) : ℂ → Sphere) (cobounded ℂ) (𝓝 OnePoint.infty) := by
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  exact hcoe.comp (principal_tendsto_cobounded hF)

theorem hasDerivAt_extendAtInfinity_chart {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    HasDerivAt (fun u => chart OnePoint.infty
      (extendAtInfinity F (chartSymm OnePoint.infty u))) 1 0 := by
  let G : ℂ → ℂ := fun u => chart OnePoint.infty
    (extendAtInfinity F (chartSymm OnePoint.infty u))
  have hG0 : G 0 = 0 := by simp [G, chart, chartSymm, sphereInv, finiteCoord]
  have hGu (u : ℂ) (hu : u ≠ 0) : G u = (F u⁻¹)⁻¹ := by
    simp only [G, chart, chartSymm, ite_true, if_true]
    have hsu : sphereInv (u : Sphere) = (u⁻¹ : ℂ) := by simp [sphereInv, hu]
    rw [hsu, extendAtInfinity_coe, finiteCoord_sphereInv_coe]
  have hid : Tendsto (fun u : ℂ => u) (𝓝[≠] (0 : ℂ)) (𝓝 0) := nhdsWithin_le_nhds
  have he := hid.mul ((principal_remainder_tendsto_zero hF).comp
    (tendsto_inv₀_nhdsNE_zero (α := ℂ)))
  have hprod : Tendsto (fun u : ℂ => u * F u⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))).add he
    simp only [zero_mul, add_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u ≠ 0 := hu
    change 1 + u * (F u⁻¹ - u⁻¹) = u * F u⁻¹
    rw [mul_sub, mul_inv_cancel₀ hu']
    ring
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h := hprod.inv₀ one_ne_zero
  simp only [inv_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u ≠ 0 := hu
  change (u * F u⁻¹)⁻¹ = slope G 0 u
  rw [slope_def_field, hG0, sub_zero, sub_zero, hGu u hu', div_eq_mul_inv, mul_inv_rev]

theorem isConformalAt_extendAtInfinity_infty {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalAt (extendAtInfinity F) OnePoint.infty := by
  refine ⟨continuousAt_extendAtInfinity_infty hF, 1, one_ne_zero, ?_⟩
  simpa only [extendAtInfinity_infty, chart_infty_self] using hasDerivAt_extendAtInfinity_chart hF

theorem isPrincipalNormalized_extendAtInfinity {F : ℂ → ℂ}
    (hF : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsPrincipalNormalized (extendAtInfinity F) :=
  ⟨rfl, by simpa only [extendAtInfinity_coe, finiteCoord_coe] using hF⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_LimitConformality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conformality of the normalized limit

`HurwitzZeroFreeLimit` records the zero-free form of the same published
Hurwitz theorem already used for injective limits: Ahlfors, *Complex
Analysis*, third edition (1979), Chapter 5, Theorem 2, p. 178. Applied
to the derivatives, it gives a nonzero limiting derivative unless the
limit is constant. The latter alternative is ruled out on each core.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem finite_part_deriv_ne_zero
    {f : Sphere → Sphere} {z : ℂ}
    (hf : IsConformalAt f (z : Sphere)) (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    deriv (fun w : ℂ => finiteCoord (f (w : Sphere))) z ≠ 0 := by
  obtain ⟨_, d, hd, hder⟩ := hf
  have he : (fun w => chart (f (z : Sphere)) (f (chartSymm (z : Sphere) w))) =
      (fun w : ℂ => finiteCoord (f (w : Sphere))) := by
    funext w
    simp only [chart, hfinite, ite_false, if_false, chartSymm_coe_apply]
  rw [he, chart_coe_self] at hder
  rwa [hder.deriv]

theorem deriv_ne_zero_of_holomorphic_limits
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ ∀ z ∈ D, deriv (F n) z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hnonconst : ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) :
    ∀ z ∈ D, deriv f z ≠ 0 := by
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D := hF.mono fun _ h => h.1
  have hderdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (deriv (F n)) D ∧ ∀ z ∈ D, deriv (F n) z ≠ 0 := by
    filter_upwards [hF] with n hn
    exact ⟨hn.1.deriv hD, hn.2⟩
  have hderlim := hlim.deriv hdiff hD
  rcases hhurwitz D (fun n => deriv (F n)) (deriv f) hD hconn hderdiff hderlim with hz | hn
  · exact (hnonconst (hD.exists_is_const_of_deriv_eq_zero hconn.isPreconnected
      (hlim.differentiableOn hdiff hD) (fun z hzD => hz z hzD))).elim
  · exact hn

theorem deriv_ne_zero_on_exhaustion
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFn : ∀ n z, z ∈ D n → deriv (F n) z ≠ 0) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n))
    (hnonconst : ∀ n, ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c) :
    ∀ z ∈ ⋃ n, D n, deriv f z ≠ 0 := by
  intro z hz
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  apply deriv_ne_zero_of_holomorphic_limits hhurwitz (hD m) (hconn m) ?_
    (hlim.mono (subset_iUnion D m)) (hnonconst m) z hm
  filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
  exact ⟨(hF (s n)).mono (hmono hn), fun w hw => hFn (s n) w (hmono hn hw)⟩

theorem isConformalOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D) (hF : DifferentiableOn ℂ F D)
    (hd : ∀ z ∈ D, deriv F z ≠ 0)
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp)
  · exact isConformalAt_extendAtInfinity_coe
      ((hF z hz).differentiableAt (hD.mem_nhds hz)) (hd z hz)
  · rw [mem_singleton_iff] at hp
    subst p
    exact isConformalAt_extendAtInfinity_infty hnorm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedLimitEquivalence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized limit as a sphere conformal equivalence

The source includes infinity. The inverse on the image is constructed
by the local inverse theorem, so the limiting map satisfies the same
two-sided conformal predicate as the final circle-domain target.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isOpen_finite_domain_with_infty
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsOpen (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hc : IsCompact Dᶜ := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hD.isClosed_compl
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hz (hext (le_of_lt (lt_of_not_ge hn)))
  apply (OnePoint.isOpen_iff_of_mem' (by simp)).mpr
  simpa only [preimage_union, OnePoint.coe_injective.preimage_image,
    OnePoint.coe_preimage_infty, union_empty] using And.intro hc hD

theorem injOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hF : InjOn F D) :
    InjOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp) q (⟨w, hw, rfl⟩ | hq) he
  · exact congrArg ((↑) : ℂ → Sphere) (hF hz hw (OnePoint.coe_injective he))
  · rw [mem_singleton_iff] at hq
    subst q
    exact (OnePoint.coe_ne_infty (F z) he).elim
  · rw [mem_singleton_iff] at hp
    subst p
    exact (OnePoint.coe_ne_infty (F w) he.symm).elim
  · rw [mem_singleton_iff] at hp hq
    exact hp.trans hq.symm

theorem normalized_limit_conformal_equivalence
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D)
    (hF : DifferentiableOn ℂ F D) (hFi : InjOn F D)
    (hd : ∀ z ∈ D, deriv F z ≠ 0)
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹))
    {R : ℝ} (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConformalEquivalence (extendAtInfinity F)
      (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty})
      (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty})) :=
  isConformalEquivalence_of_injOn (isConformalOn_extendAtInfinity hD hF hd hnorm)
    (isOpen_finite_domain_with_infty hD hext) (injOn_extendAtInfinity hFi)

theorem exists_conformal_limit_of_sphere_models
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsOpen (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F)
        (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})) := by
  obtain ⟨s, F, hs, hlim, hF, hFi, hFnorm, hdecay⟩ :=
    exists_normalized_limit_of_sphere_models harea hmontel hhurwitz f fi Q V heq hV
      hD hconn hmono hDQ hcore hR hsource hconf hnorm hext
  have hinf (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  have hdiff (n : ℕ) :
      DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f n (z : Sphere))) (D n) :=
    finite_part_differentiableOn (heq n) (hinf n) (hnorm n).1 (hD n) (hDQ n) (hcore n)
  have hnonzero (n : ℕ) (z : ℂ) (hz : z ∈ D n) :
      deriv (fun w : ℂ => finiteCoord (f n (w : Sphere))) z ≠ 0 :=
    finite_part_deriv_ne_zero (hcore n _ (mem_image_of_mem _ hz))
      ((heq n).finite_forward (hinf n) (hnorm n).1 (hDQ n z hz))
  have hnonconst (n : ℕ) : ¬ ∃ c : ℂ, ∀ z ∈ D n, F z = c :=
    not_constant_of_exterior_decay hR (hext.trans (hmono (Nat.zero_le n))) hdecay
  have hd := deriv_ne_zero_on_exhaustion hzero hD hconn hmono hdiff hnonzero hs hlim hnonconst
  refine ⟨s, F, hs, hlim, isPrincipalNormalized_extendAtInfinity hFnorm, ?_⟩
  exact normalized_limit_conformal_equivalence (isOpen_iUnion hD) hF hFi hd hFnorm
    (hext.trans (subset_iUnion D 0))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleComponentCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Center and radius coordinates of circle-domain components

If a circle domain contains infinity, every complementary component
is an ordinary closed disk, allowing radius zero. A bound on the whole
complement bounds both parameters. Thus no choice of disk coordinates
is an extra hypothesis in the marked-disk compactness argument.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem closedBall_parameters_bound
    {c : ℂ} {r L : ℝ} (hr : 0 ≤ r)
    (hsub : Metric.closedBall c r ⊆ Metric.closedBall (0 : ℂ) L) :
    ‖c‖ ≤ L ∧ r ≤ L := by
  have hcenter : ‖c‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hsub (Metric.mem_closedBall_self hr)
  have hplus : c + (r : ℂ) ∈ Metric.closedBall c r := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, le_refl]
  have hminus : c - (r : ℂ) ∈ Metric.closedBall c r := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, le_refl]
  have hp : ‖c + (r : ℂ)‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsub hplus
  have hm : ‖c - (r : ℂ)‖ ≤ L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsub hminus
  have hdiam := norm_sub_le (c + (r : ℂ)) (c - (r : ℂ))
  have heq : c + (r : ℂ) - (c - (r : ℂ)) = (2 * r : ℝ) := by push_cast <;> ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hdiam
  exact ⟨hcenter, by linarith⟩

theorem bounded_circleDomain_component_parameters
    {V : Set Sphere} (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {L : ℝ} (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' Metric.closedBall 0 L)
    {p : Sphere} (hp : p ∈ Vᶜ) :
    ∃ (c : ℂ) (r : ℝ), ‖c‖ ≤ L ∧ r ∈ Icc 0 L ∧
      connectedComponentIn Vᶜ p = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  obtain ⟨c, r, hr, he⟩ := circleDomain_component_eq_closedBall hV hinf hp
  have hsub : Metric.closedBall c r ⊆ Metric.closedBall (0 : ℂ) L := by
    intro z hz
    have hzs : (z : Sphere) ∈ connectedComponentIn Vᶜ p := by
      rw [he]
      exact mem_image_of_mem _ hz
    have hb := hbound (connectedComponentIn_subset Vᶜ p hzs)
    exact OnePoint.coe_injective.mem_set_image.mp hb
  obtain ⟨hc, hrL⟩ := closedBall_parameters_bound hr hsub
  exact ⟨c, r, hc, ⟨hr, hrL⟩, he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MarkedComponentLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked complementary-component limits

The center/radius sequences are selected from actual circle-domain
components. Their Hausdorff-convergent subsequence preserves a previously
constructed locally uniform map limit.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

/-- A mark need only be included eventually. Dummy radius-zero disks at
its earlier stages do not affect the simultaneous parameter limits. -/
theorem exists_eventual_marked_component_limits
    {B : Type*} [Countable B] (V : ℕ → Set Sphere)
    (hV : ∀ n, IsCircleDomain (V n)) (hinf : ∀ n, OnePoint.infty ∈ V n)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ n, (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 L)
    (p : ℕ → B → Sphere) (hp : ∀ b, ∀ᶠ n in atTop, p n b ∈ (V n)ᶜ)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn F f atTop D) :
    ∃ (s : ℕ → ℕ) (c : ℕ → B → ℂ) (r : ℕ → B → ℝ)
      (c₀ : B → ℂ) (r₀ : B → ℝ),
      StrictMono s ∧ TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop D ∧
      (∀ n b, ‖c n b‖ ≤ L ∧ r n b ∈ Icc 0 L) ∧
      (∀ b, ‖c₀ b‖ ≤ L ∧ r₀ b ∈ Icc 0 L) ∧
      (∀ b, ∀ᶠ n in atTop,
        connectedComponentIn (V (s n))ᶜ (p (s n) b) =
          ((↑) : ℂ → Sphere) '' closedBall (c n b) (r n b)) ∧
      (∀ b, Tendsto (fun n => c n b) atTop (𝓝 (c₀ b))) ∧
      (∀ b, Tendsto (fun n => r n b) atTop (𝓝 (r₀ b))) := by
  classical
  have hex : ∀ n b, ∃ (c : ℂ) (r : ℝ), ‖c‖ ≤ L ∧ r ∈ Icc 0 L ∧
      (p n b ∈ (V n)ᶜ → connectedComponentIn (V n)ᶜ (p n b) =
        ((↑) : ℂ → Sphere) '' closedBall c r) := by
    intro n b
    by_cases hb : p n b ∈ (V n)ᶜ
    · obtain ⟨c, r, hc, hr, he⟩ :=
        bounded_circleDomain_component_parameters (hV n) (hinf n) (hbound n) hb
      exact ⟨c, r, hc, hr, fun _ => he⟩
    · exact ⟨0, 0, by simpa using hL, ⟨le_rfl, hL⟩, fun h => (hb h).elim⟩
  choose c r hc hr he using hex
  obtain ⟨s, c₀, r₀, hs, hb, hclim, hrlim⟩ :=
    exists_marked_disk_parameter_limits c r hc hr
  refine ⟨s, (fun n => c (s n)), (fun n => r (s n)), c₀, r₀, hs,
    locally_uniform_subsequence hlim hs, (fun n b => ⟨hc (s n) b, hr (s n) b⟩),
    hb, ?_, hclim, hrlim⟩
  intro b
  filter_upwards [hs.tendsto_atTop (hp b)] with n hn
  exact he (s n) b hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_OmittedLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limits of omitted points and disks

Hurwitz applied to `Fₙ - wₙ` keeps every convergent sequence of omitted
points out of a nonconstant locally uniform limit's image. The argument
works on each retained core. Convergence of disk parameters then keeps
the whole limiting closed disk in the complement.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem omitted_point_limit
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {w : ℕ → ℂ} {w₀ : ℂ}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ ∀ z ∈ D, F n z ≠ w n)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hw : Tendsto w atTop (𝓝 w₀))
    (hnonconst : ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) :
    ∀ z ∈ D, f z ≠ w₀ := by
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => w n)
      (fun _ => w₀) atTop D := (hw.tendstoUniformlyOn_const D).tendstoLocallyUniformlyOn
  have hsub : TendstoLocallyUniformlyOn (fun n z => F n z - w n)
      (fun z => f z - w₀) atTop D := by
    exact uniformContinuous_sub.comp_tendstoLocallyUniformlyOn (hlim.prodMk hconst)
  have hsubF : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z => F n z - w n) D ∧ ∀ z ∈ D, F n z - w n ≠ 0 := by
    filter_upwards [hF] with n hn
    exact ⟨hn.1.sub_const _, fun z hz => sub_ne_zero.mpr (hn.2 z hz)⟩
  rcases hhurwitz D (fun n z => F n z - w n) (fun z => f z - w₀)
      hD hconn hsubF hsub with hz | hn
  · exact (hnonconst ⟨w₀, fun z hzD => sub_eq_zero.mp (hz z hzD)⟩).elim
  · exact fun z hz => sub_ne_zero.mp (hn z hz)

/-- The disks may depend on the index, and need be omitted only eventually
on a fixed connected open source set. -/
theorem omitted_closedBall_limit
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧
      ∀ z ∈ D, F n z ∉ Metric.closedBall (c n) (r n))
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hnonconst : ¬ ∃ a : ℂ, ∀ z ∈ D, f z = a) :
    Metric.closedBall c₀ r₀ ⊆ (f '' D)ᶜ := by
  intro w hw
  rw [closedBall_eq_affine_image hr₀ c₀] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  let v : ℕ → ℂ := fun n => c n + r n • u
  have hv (n : ℕ) : v n ∈ Metric.closedBall (c n) (r n) := by
    rw [closedBall_eq_affine_image (hr n) (c n)]
    exact mem_image_of_mem _ hu
  have hvlim : Tendsto v atTop (𝓝 (c₀ + r₀ • u)) :=
    hc.add (hrlim.smul tendsto_const_nhds)
  have hzero : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧
      ∀ z ∈ D, F n z ≠ v n := by
    filter_upwards [hF] with n hn
    exact ⟨hn.1, fun z hz he => hn.2 z hz (he ▸ hv n)⟩
  rintro ⟨z, hz, he⟩
  exact omitted_point_limit hhurwitz hD hconn hzero hlim hvlim hnonconst z hz he

/-- Eventual holomorphy and omission on each retained core suffice;
no single finite map has to be defined on the full union. -/
theorem omitted_closedBall_limit_on_eventual_cores
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hD : ∀ m, IsOpen (D m)) (hconn : ∀ m, IsConnected (D m))
    (hF : ∀ m, ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (D m) ∧
      ∀ z ∈ D m, F n z ∉ Metric.closedBall (c n) (r n))
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hlim : TendstoLocallyUniformlyOn F f atTop (⋃ m, D m))
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hnonconst : ∀ m, ¬ ∃ a : ℂ, ∀ z ∈ D m, f z = a) :
    Metric.closedBall c₀ r₀ ⊆ (f '' (⋃ m, D m))ᶜ := by
  rintro w hw ⟨z, hz, he⟩
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  exact omitted_closedBall_limit hhurwitz (hD m) (hconn m) (hF m) hr hr₀
    (hlim.mono (subset_iUnion D m)) hc hrlim (hnonconst m) hw ⟨z, hm, he⟩

/-- Passing to the normalized sphere extension introduces only infinity,
so a finite omitted disk remains omitted. -/
theorem sphere_disk_omitted_of_plane_disk
    {D : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h : Metric.closedBall c r ⊆ (f '' D)ᶜ) :
    ((↑) : ℂ → Sphere) '' Metric.closedBall c r ⊆
      (extendAtInfinity f '' (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}))ᶜ := by
  rintro _ ⟨w, hw, rfl⟩ ⟨p, hp, he⟩
  rcases hp with ⟨z, hz, rfl⟩ | hp
  · exact h hw ⟨z, hz, OnePoint.coe_injective he⟩
  · rw [mem_singleton_iff] at hp
    subst p
    exact OnePoint.coe_ne_infty w he.symm

/-- Actual complementary components of the approximating circle domains
remain omitted in the normalized limiting sphere image. -/
theorem marked_component_limit_omitted
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {V : ℕ → Set Sphere} {p : ℕ → Sphere}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hD : ∀ m, IsOpen (D m)) (hconn : ∀ m, IsConnected (D m))
    (hF : ∀ m, ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (D m) ∧
      ∀ z ∈ D m, (F n z : Sphere) ∈ V n)
    (he : ∀ᶠ n in atTop, connectedComponentIn (V n)ᶜ (p n) =
      ((↑) : ℂ → Sphere) '' Metric.closedBall (c n) (r n))
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hlim : TendstoLocallyUniformlyOn F f atTop (⋃ m, D m))
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hnonconst : ∀ m, ¬ ∃ a : ℂ, ∀ z ∈ D m, f z = a) :
    ((↑) : ℂ → Sphere) '' Metric.closedBall c₀ r₀ ⊆
      (extendAtInfinity f '' (((↑) : ℂ → Sphere) '' (⋃ m, D m) ∪ {OnePoint.infty}))ᶜ := by
  apply sphere_disk_omitted_of_plane_disk
  apply omitted_closedBall_limit_on_eventual_cores hhurwitz hD hconn ?_
    hr hr₀ hlim hc hrlim hnonconst
  intro m
  filter_upwards [hF m, he] with n hn hen
  refine ⟨hn.1, ?_⟩
  intro z hz hball
  have hcomp : (F n z : Sphere) ∈ connectedComponentIn (V n)ᶜ (p n) := by
    rw [hen]
    exact mem_image_of_mem _ hball
  exact connectedComponentIn_subset (V n)ᶜ (p n) hcomp (hn.2 z hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedMarkedModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized limits with actual marked complementary disks

The marked components may only appear eventually in the finite models.
A common subsequence yields their round Hausdorff limits and a two-sided
conformal sphere limit. Hurwitz puts every limiting disk in the complement
of that image. Assignment to a particular end is a separate geometric step.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem not_constant_on_open_of_conformal_extension
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D) (hne : D.Nonempty)
    (hconf : IsConformalOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D)) :
    ¬ ∃ c : ℂ, ∀ z ∈ D, F z = c := by
  rintro ⟨c, hc⟩
  obtain ⟨z, hz⟩ := hne
  have hd := finite_part_deriv_ne_zero (hconf _ (mem_image_of_mem _ hz))
    (OnePoint.coe_ne_infty (F z))
  have he : F =ᶠ[𝓝 z] (fun _ => c) := by
    filter_upwards [hD.mem_nhds hz] with w hw
    exact hc w hw
  apply hd
  simpa only [extendAtInfinity_coe, finiteCoord_coe, deriv_const] using he.deriv_eq

theorem exists_normalized_marked_sphere_limit_with_parameters
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    {B : Type*} [Countable B] (p : ℕ → B → Sphere)
    (hp : ∀ b, ∀ᶠ n in atTop, p n b ∈ (V n)ᶜ) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ) (c : B → ℂ) (r : B → ℝ),
      StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F)
        (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})) ∧
      (∀ b, ‖c b‖ ≤ 3 * R ∧ r b ∈ Icc 0 (3 * R)) ∧
      (∀ b, Tendsto (fun n => hausdorffDist
        (finiteCoord '' connectedComponentIn (V (s n))ᶜ (p (s n) b))
        (closedBall (c b) (r b))) atTop (𝓝 0)) ∧
      (∀ b, ((↑) : ℂ → Sphere) '' closedBall (c b) (r b) ⊆
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty}))ᶜ) ∧
      ∃ (cn : ℕ → B → ℂ) (rn : ℕ → B → ℝ),
        (∀ n b, ‖cn n b‖ ≤ 3 * R ∧ rn n b ∈ Icc 0 (3 * R)) ∧
        (∀ b, ∀ᶠ n in atTop,
          connectedComponentIn (V (s n))ᶜ (p (s n) b) =
            ((↑) : ℂ → Sphere) '' closedBall (cn n b) (rn n b)) ∧
        (∀ b, Tendsto (fun n => cn n b) atTop (𝓝 (c b))) ∧
        (∀ b, Tendsto (fun n => rn n b) atTop (𝓝 (r b))) := by
  have hinfQ (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  have hinfV (n : ℕ) : OnePoint.infty ∈ V n := by
    simpa only [(hnorm n).1] using (heq n).mapsTo (hinfQ n)
  have hbound (n : ℕ) : (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 (3 * R) :=
    (normalized_model_uniform_bound harea (heq n) (hV n).1 hR
      (hsource n) (hconf n) (hnorm n)).1
  obtain ⟨s, F, hs, hlim, hFnorm, hFeq⟩ :=
    exists_conformal_limit_of_sphere_models harea hmontel hhurwitz hzero f fi Q V heq
      (fun n => (hV n).1) hD hconn hmono hDQ hcore hR hsource hconf hnorm hext
  obtain ⟨t, c, r, c₀, r₀, ht, hlim', hb, hb₀, he, hc, hr⟩ :=
    exists_eventual_marked_component_limits (fun n => V (s n)) (fun n => hV (s n))
      (fun n => hinfV (s n)) (by positivity : 0 ≤ 3 * R) (fun n => hbound (s n))
      (fun n b => p (s n) b) (fun b => hs.tendsto_atTop (hp b)) hlim
  have hnonconst (m : ℕ) : ¬ ∃ a : ℂ, ∀ z ∈ D m, F z = a :=
    not_constant_on_open_of_conformal_extension (hD m) (hconn m).nonempty
      (hFeq.1.mono ((image_mono (subset_iUnion D m)).trans subset_union_left))
  have hmaps (m : ℕ) : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (s (t n)) (z : Sphere))) (D m) ∧
      ∀ z ∈ D m, (finiteCoord (f (s (t n)) (z : Sphere)) : Sphere) ∈ V (s (t n)) := by
    filter_upwards [(hs.comp ht).tendsto_atTop.eventually_ge_atTop m] with n hn
    refine ⟨(finite_part_differentiableOn (heq (s (t n))) (hinfQ (s (t n)))
      (hnorm (s (t n))).1 (hD (s (t n))) (hDQ (s (t n)))
      (hcore (s (t n)))).mono (hmono hn), ?_⟩
    intro z hz
    have hzQ := hDQ (s (t n)) z (hmono hn hz)
    rw [coe_finiteCoord ((heq (s (t n))).finite_forward
      (hinfQ (s (t n))) (hnorm (s (t n))).1 hzQ)]
    exact (heq (s (t n))).mapsTo hzQ
  refine ⟨s ∘ t, F, c₀, r₀, hs.comp ht, hlim', hFnorm, hFeq, hb₀, ?_, ?_, c, r, hb, he, hc, hr⟩
  · intro b
    have hball := tendsto_hausdorffDist_closedBall (fun n => (hb n b).2.1)
      (hb₀ b).2.1 (hc b) (hr b)
    apply hball.congr'
    filter_upwards [he b] with n hn
    simp only [Function.comp_apply, hn, image_image, finiteCoord_coe, image_id']
  · intro b
    exact marked_component_limit_omitted hzero hD hconn hmaps (he b)
      (fun n => (hb n b).2.1) (hb₀ b).2.1 hlim' (hc b) (hr b) hnonconst

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DelayedTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Delaying tags scales their weighted tuple measure, allowing every finite
tuple cost of a fixed allowed path to become arbitrarily small. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem slotWeight_add (N k : ℕ) : slotWeight (N + k) = slotWeight N * slotWeight k :=
  pow_add _ _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PositiveCountableWeights
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive weights of total mass at most one on the prescribed countable
point and tuple-type sets. Their squares have the same upper bound. -/

open Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem sum_slotWeight_succ : (∑' k, slotWeight (k + 1)) = 1 := by
  simp_rw [Nat.add_comm _ 1, slotWeight_add]
  rw [ENNReal.tsum_mul_left, tsum_slotWeight]
  simpa only [slotWeight, pow_one] using
    (ENNReal.inv_mul_cancel (a := 2) (by norm_num) (by norm_num))

theorem exists_positive_summable_weights (D : Type*) [Countable D] :
    ∃ c : D → ℝ≥0∞, (∀ s, 0 < c s) ∧ (∑' s, c s) ≤ 1 := by
  classical
  let := Encodable.ofCountable D
  refine ⟨fun s => slotWeight (Encodable.encode s + 1), fun s => slotWeight_pos _, ?_⟩
  exact (ENNReal.tsum_comp_le_tsum_of_injective Encodable.encode_injective
    (fun k => slotWeight (k + 1))).trans_eq sum_slotWeight_succ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TupleReference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tuple reference measure is a positive weighted sum of Lebesgue
measures on the finite tuple tori, indexed by label type rather than slot. -/

open Set MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_tupleFiber (i : TupleType) : Continuous (tupleFiber i) :=
  continuous_sigmaMk.comp (continuous_const.prodMk continuous_id)

theorem measurable_tupleFiber (i : TupleType) : Measurable (tupleFiber i) :=
  Continuous.measurable (α := Fin (i.1 + 1) → UnitAddCircle) (γ := LevelTuple)
    (continuous_tupleFiber i)

theorem tupleReference_apply (ω : TupleType → ℝ≥0∞)
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    tupleReference ω A = ∑' i, ω i * volume (tupleFiber i ⁻¹' A) := by
  simp only [tupleReference, Measure.sum_apply _ hA, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (measurable_tupleFiber _) hA]

theorem tupleReference_univ (ω : TupleType → ℝ≥0∞) :
    tupleReference ω univ = ∑' i, ω i := by
  rw [tupleReference_apply ω MeasurableSet.univ]
  apply tsum_congr
  intro i
  have hv : (volume : Measure (Fin (i.1 + 1) → UnitAddCircle)) univ = 1 := by
    change (Measure.pi (fun _ : Fin (i.1 + 1) => (volume : Measure UnitAddCircle))) univ = 1
    rw [Measure.pi_univ]
    simp [AddCircle.measure_univ]
  simp only [preimage_univ, hv, mul_one]

theorem finite_tupleReference {ω : TupleType → ℝ≥0∞} (hω : (∑' i, ω i) < ∞) :
    IsFiniteMeasure (tupleReference ω) := ⟨by rwa [tupleReference_univ]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallyFiniteL2Sum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L² control of a pointwise finite sum by the sum of its local error
norms. This applies to the countable partition-of-unity error terms. -/

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem finiteSupport_hasSum_finsum {ι : Type*} (f : ι → ℝ)
    (hf : HasFiniteSupport f) : HasSum f (∑ᶠ i, f i) := by
  rw [← show (∑' i, f i) = ∑ᶠ i, f i from tsum_eq_finsum hf]
  exact (summable_of_hasFiniteSupport hf).hasSum

theorem eLpNorm_finsum_le_tsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    eLpNorm (fun x => ∑ᶠ i, f i x) 2 μ ≤ ∑' i, eLpNorm (f i) 2 μ := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (u := (atTop : Filter (Finset ι)))
    (f := fun s x => ∑ i ∈ s, f i x)
  · apply Eventually.of_forall
    intro s
    have h := eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (f := f) (s := s) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have he : (fun x => ∑ i ∈ s, f i x) = ∑i ∈ s, f i := by
      ext x
      simp only [Finset.sum_apply]
    rw [he]
    exact h.trans (ENNReal.sum_le_tsum s)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSmoothPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth partition functions on an open planar domain. The
family is locally finite in the domain, allowing accumulation at its boundary. -/

open Set Function Filter TopologicalSpace
open scoped Topology Manifold

noncomputable section

namespace CircleDomainRigidity

theorem exists_openPlanePartition
    (Ω : Opens EuclideanPlane) (U : Ω → Set Ω) (hU : ∀x, U x ∈ 𝓝 x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (c : ι → Ω),
      ∀i, tsupport (ρ.weight i) ⊆ Subtype.val '' U (c i) := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨ι, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate
    (𝓘(ℝ, EuclideanPlane)) (M := Ω) isClosed_univ (fun x _ => hU x)
  let : Encodable ι := b.locallyFinite.encodable (fun i => (b i).nonempty_support)
  let ρ := b.toSmoothPartitionOfUnity
  have hc (i : ι) : HasCompactSupport (ρ i) :=
    (b i).hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_mono (b.support_toSmoothPartitionOfUnity_subset i))
  let ψ : ι → EuclideanPlane → ℝ := fun i => Subtype.val.extend (ρ i) 0
  have hon (i : ι) (x : Ω) : ψ i x = ρ i x :=
    congrFun (Function.extend_comp Subtype.val_injective (ρ i) 0) x
  have hsub (i : ι) : tsupport (ψ i) ⊆ Subtype.val '' U (b.c i) := by
    apply ((hc i).tsupport_extend_zero_subset continuous_subtype_val).trans
    exact image_mono (hb.toSmoothPartitionOfUnity i)
  have hin (i : ι) : tsupport (ψ i) ⊆ Ω :=
    (hsub i).trans (image_subset_iff.mpr (fun x _ => x.property))
  have hsmooth (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) := by
    apply contMDiff_iff_contDiff.mp
    exact ContMDiff.extend_zero (hc i) (ρ i).contMDiff
  have hloc : LocallyFinite (fun i => Subtype.val ⁻¹' Function.support (ψ i) :
      ι → Set Ω) := by
    have heq : (fun i => Subtype.val ⁻¹' Function.support (ψ i) : ι → Set Ω) =
        fun i => Function.support (ρ i) := by
      funext i
      ext x
      simp only [mem_preimage, Function.mem_support, hon]
    rw [heq]
    exact ρ.locallyFinite
  have hn (i : ι) (x : EuclideanPlane) : 0 ≤ ψ i x := by
    by_cases hx : x ∈ Ω
    · rw [show x = ((⟨x, hx⟩ : Ω) : EuclideanPlane) from rfl, hon]
      exact ρ.nonneg i _
    · have hz : ψ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hin i h))
      rw [hz]
  refine ⟨ι, inferInstance, ⟨ψ, hsmooth,
    fun i => (hc i).extend_zero continuous_subtype_val, hin, hloc, hn, ?_⟩, b.c, hsub⟩
  intro x
  simp only [hon]
  exact ρ.sum_eq_one (mem_univ x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveMollification
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized smooth mollifiers preserve actual interval bounds and
constant plateaus. These are pointwise bounds on the input neighborhood. -/

open Set MeasureTheory Metric
open scoped Convolution

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem normed_convolution_eq_of_constant
    [HasContDiffBump E] (β : ContDiffBump (0 : E)) {u : E → ℝ} {x : E} {c : ℝ}
    (hc : ∀y ∈ ball x β.rOut, u y = c) :
    ((β.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) = c := by
  rw [β.normed_convolution_eq_right (fun y hy => (hc y hy).trans
    (hc x (mem_ball_self β.rOut_pos)).symm)]
  exact hc x (mem_ball_self β.rOut_pos)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveSobolevApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit positive mollification of a compactly supported planar
Sobolev function. The values and weak derivatives converge in L². -/

open Set Filter MeasureTheory
open scoped ENNReal Topology Convolution

noncomputable section

namespace CircleDomainRigidity

theorem planarMollification_tsupport_subset (u : EuclideanPlane → ℝ) (n : ℕ) :
    tsupport (planarMollification u n) ⊆
      Metric.cthickening (DeGiorgi.shrinkingBump (d := 2) n).rOut (tsupport u) := by
  have hs := support_convolution_subset
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := (DeGiorgi.shrinkingBump (d := 2) n).normed volume) (g := u)
  apply closure_minimal (hs.trans ?_) Metric.isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
  rw [(DeGiorgi.shrinkingBump (d := 2) n).support_normed_eq] at ha
  have ha' : ‖a‖ < (DeGiorgi.shrinkingBump (d := 2) n).rOut := by
    simpa only [Metric.mem_ball, dist_zero_right] using ha
  apply Metric.mem_cthickening_of_dist_le (x := a + b) (y := b)
    (δ := (DeGiorgi.shrinkingBump (d := 2) n).rOut) (tsupport u)
    (subset_tsupport u hb)
  simpa only [dist_eq_norm, add_sub_cancel_right] using ha'.le

theorem planarMollification_support_eventually {u : EuclideanPlane → ℝ}
    (hu : HasCompactSupport u) {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hsub : tsupport u ⊆ Ω) : ∀ᶠ n in atTop, tsupport (planarMollification u n) ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hu.isCompact.exists_cthickening_subset_open hΩ hsub
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn
  exact (planarMollification_tsupport_subset u n).trans
      ((Metric.cthickening_mono hn.le _).trans hδΩ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactMollifierSampling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform sampling control on compact sets, including exact preservation
of constant regions and smooth cutoffs equal to one near a compact set. -/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem planarMollifier_samples_eventually
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n in atTop, ∀x ∈ K,
      ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn x hx y hy
  apply hδV
  exact mem_cthickening_of_dist_le y x δ K hx
    ((mem_ball.1 hy).le.trans hn.le)

theorem planarMollification_eq_on_compact_eventually
    {u : EuclideanPlane → ℝ} {K V : Set EuclideanPlane}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {c : ℝ} (hc : ∀y ∈ V, u y = c) :
    ∀ᶠ n in atTop, ∀x ∈ K, planarMollification u n x = c := by
  filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn x hx
  exact normed_convolution_eq_of_constant volume (DeGiorgi.shrinkingBump n)
    (fun y hy => hc y (hn x hx hy))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactSobolevCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact cutoffs turn local planar Sobolev functions into
global Sobolev functions, to which positive mollification applies. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem compact_cutoff_mem_Icc
    {Ω : Set EuclideanPlane} {u η : EuclideanPlane → ℝ}
    (hu : ∀x ∈ Ω, u x ∈ Icc 0 1) (hη : ∀x, η x ∈ Icc 0 1)
    (hsub : tsupport η ⊆ Ω) (x : EuclideanPlane) : η x * u x ∈ Icc 0 1 := by
  by_cases hx : x ∈ Ω
  · exact ⟨mul_nonneg (hη x).1 (hu x hx).1,
      (mul_le_mul (hη x).2 (hu x hx).2 (hu x hx).1 zero_le_one).trans_eq (one_mul 1)⟩
  · have hzero : η x = 0 := by
      by_contra hn
      exact hx (hsub (subset_tsupport η hn))
    simp only [hzero, zero_mul, mem_Icc, le_rfl, zero_le_one, and_self]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local positive smoothing with errors relative to the original weak
gradient. Compact cutoffs are removed on a neighborhood of the core. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem tendsto_eLpNorm_restrict_zero
    {f : ℕ → EuclideanPlane → ℝ} {V : Set EuclideanPlane}
    (hf : Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
    (fun _ => bot_le) (fun n => eLpNorm_mono_measure (f n) Measure.restrict_le_self)

theorem exists_local_positive_sobolev_smoothing
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hunit : ∀x ∈ Ω, u x ∈ Icc 0 1) :
    ∃ (V : Set EuclideanPlane) (φ : ℕ → EuclideanPlane → ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      (∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n) ∧
        ∀x, φ n x ∈ Icc 0 1) ∧
      (∀ᶠ n in atTop, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
        atTop (𝓝 0) ∧
      (∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
        2 (volume.restrict V)) atTop (𝓝 0)) ∧
      (∀W : Set EuclideanPlane, IsOpen W → K ⊆ W → ∀c : ℝ,
        (∀x ∈ W, u x = c) → ∀ᶠ n in atTop, ∀x ∈ K, φ n x = c) ∧
      (∀ᶠ n in atTop, ∀a b : ℝ, (∀x ∈ Ω, u x ∈ Icc a b) →
        ∀x ∈ K, φ n x ∈ Icc a b) := by
  obtain ⟨η, V, hη, hsη, hηunit, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro x hx
    apply hsub
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨hw⟩ := exists_global_compact_cutoff_witness hΩ hu.memW1p hη hsη hsub
  have hwunit : ∀x, w x ∈ Icc 0 1 := compact_cutoff_mem_Icc hunit hηunit hsub
  have hwLp : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hw_eq : EqOn w u V := fun x hx => by dsimp [w]; rw [hone x hx, one_mul]
  refine ⟨V, planarMollification w, hV, hKV, hVΩ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨planarMollification_smooth (hwLp.locallyIntegrable (by norm_num)) n,
      planarMollification_hasCompactSupport hsη.mul_right n,
      planarMollification_mem_Icc hwLp.aestronglyMeasurable hwunit n⟩
  · exact planarMollification_support_eventually hsη.mul_right hΩ
      (tsupport_mul_subset_left.trans hsub)
  · have hl := tendsto_eLpNorm_restrict_zero (V := V) (planarMollification_tendsto_L2 hwLp)
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [hw_eq hx]
  · intro i
    have hgi := weakGrad_eq_on_cutoff_plateau hV hVΩ hu hw hone i
    have hl := tendsto_eLpNorm_restrict_zero (V := V)
      (planarMollification_tendsto_gradient_L2 hw i)
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hgi] with x hx
    rw [hx]
  · intro W hW hKW c hc
    apply planarMollification_eq_on_compact_eventually hK (hV.inter hW)
      (subset_inter hKV hKW)
    intro x hx
    rw [hw_eq hx.1, hc x hx.2]
  · filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn a b hab x hx
    apply normed_convolution_mem_Icc volume (DeGiorgi.shrinkingBump n) hwLp.aestronglyMeasurable
    intro y hy
    have hyV := hn x hx hy
    rw [hw_eq hyV]
    exact hab y (hVΩ hyV)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSobolevErrors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative error estimates for multiplying local Sobolev
approximations by smooth partition functions. -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_mul_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) (hs : Function.support ψ ⊆ V) :
    AEStronglyMeasurable (fun x => ψ x * f x) volume := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi]
  exact (aestronglyMeasurable_indicator_iff hV).2 (hψ.aestronglyMeasurable.restrict.mul hf)

theorem eLpNorm_mul_le_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) {C : ℝ≥0} (hC : ∀x, ‖ψ x‖ ≤ C)
    (hs : Function.support ψ ⊆ V) :
    eLpNorm (fun x => ψ x * f x) 2 volume ≤ C * eLpNorm f 2 (volume.restrict V) := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi, eLpNorm_indicator_eq_eLpNorm_restrict hV]
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
  exact Eventually.of_forall fun x => by
    have hnn : ‖ψ x‖₊ ≤ C := by exact_mod_cast hC x
    simpa only [Pi.mul_apply, nnnorm_mul] using mul_le_mul' hnn (le_refl ‖f x‖₊)

theorem tendsto_eLpNorm_mul_zero_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f : ℕ → EuclideanPlane → ℝ} (hf : ∀n, AEStronglyMeasurable (f n) (volume.restrict V))
    {ψ : EuclideanPlane → ℝ} (hψ : Continuous ψ) (hsψ : HasCompactSupport ψ)
    (hs : Function.support ψ ⊆ V)
    (hlim : Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ψ x * f n x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := hψ.bounded_above_of_compact_support hsψ
  let C : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  have hC : ∀x, ‖ψ x‖ ≤ C := fun x => (hA x).trans (le_max_left _ _)
  have hl : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f n) 2 (volume.restrict V))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le) (fun n => eLpNorm_mul_le_of_support hV (hf n) hψ hC hs)

theorem tendsto_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {φ : ℕ → EuclideanPlane → ℝ} (hφ : ∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
      atTop (𝓝 0))
    (hg : ∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0))
    {ψ : EuclideanPlane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    Tendsto (fun n => eLpNorm (fun x =>
      ψ x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (φ n x - u x)) 2 volume)
      atTop (𝓝 0) := by
  let dψ : EuclideanPlane → ℝ := fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsdψ : HasCompactSupport dψ := hsψ.fderiv_apply (𝕜 := ℝ) _
  have hsubdψ : Function.support dψ ⊆ V :=
    (subset_tsupport dψ).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)
  have hv' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => (hφ n).continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
    hdψ hsdψ hsubdψ hv
  have hg' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => ((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous hsψ ((subset_tsupport ψ).trans hsub) (hg i)
  have hl := hg'.add hv'
  simp only [zero_add] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le)
  intro n
  have key : ∀ {a b : EuclideanPlane → ℝ}, Function.support a ⊆ V → Continuous a →
      AEStronglyMeasurable b (volume.restrict V) → AEStronglyMeasurable (fun x => a x * b x) volume := by
    intro a b ha hac hb
    have he : (fun x => a x * b x) = V.indicator (fun x => a x * b x) := by
      funext x
      by_cases hx : x ∈ V
      · simp [hx]
      · have : a x = 0 := Function.notMem_support.mp (fun h => hx (ha h))
        simp [hx, this]
    rw [he]
    exact (aestronglyMeasurable_indicator_iff hV.measurableSet).mpr
      (hac.aestronglyMeasurable.restrict.mul hb)
  exact eLpNorm_add_le
    (key ((subset_tsupport ψ).trans hsub) hψ.continuous
      (((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
        |>.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable))
    (key hsubdψ hdψ ((hφ n).continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable))
    (by norm_num)
theorem aestronglyMeasurable_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {v ψ : EuclideanPlane → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    AEStronglyMeasurable (fun x =>
      ψ x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (v x - u x)) volume := by
  have hdv : Continuous (fun x => (fderiv ℝ v x) (EuclideanSpace.single i 1)) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (aestronglyMeasurable_mul_of_support hV.measurableSet
    (hdv.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous ((subset_tsupport ψ).trans hsub)).add
      (aestronglyMeasurable_mul_of_support hV.measurableSet
        (hv.continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
        hdψ ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select one positive local smoothing on each compact partition core,
with prescribed weighted derivative error in both coordinate directions. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_partition_smooth_approximants
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ, ∀j,
      (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j) ∧
        ∀x, v j x ∈ Icc 0 1) ∧
      (∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u x))
        2 volume < ε j) := by
  classical
  suffices H : ∀j, ∃v : EuclideanPlane → ℝ,
      (ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧ ∀x, v x ∈ Icc 0 1) ∧
      (∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v x - u x))
        2 volume < ε j) by
    choose v hv using H
    exact ⟨v, hv⟩
  intro j
  obtain ⟨V, φ, hV, hKV, hVW, hsmooth, _, hvalue, hgrad, _, hinterval⟩ :=
    exists_local_positive_sobolev_smoothing (hW j) (ρ.compact j).isCompact
      (hsub j) (hu j) (hunit j)
  let hw := (hu j).restrict hV hVW
  have hgrad' (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0) := by
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using hgrad i
  have herr (i : Fin 2) := tendsto_partition_derivative_error hV hw
    (fun n => (hsmooth n).1) hvalue hgrad' (ρ.smooth j) (ρ.compact j) hKV i
  have he : ∀ᶠ n in atTop, ∀i : Fin 2, eLpNorm (fun x =>
      ρ.weight j x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
        (hu j).weakGrad x i) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (φ n x - u x))
      2 volume < ε j := by
    apply eventually_all.mpr
    intro i
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using
      (tendsto_order.1 (herr i)).2 (ε j) (hε j)
  obtain ⟨n, hn, hb⟩ := (he.and hinterval).exists
  exact ⟨φ n, hsmooth n, hb, hn⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionMixing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth mixing on an open planar domain. The locally finite sum is
represented by an actual finite sum in a neighborhood of each point. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem mix_mem_Icc (v : ι → EuclideanPlane → ℝ) {x : EuclideanPlane}
    (hx : x ∈ Ω) {a b : ℝ} (hv : ∀i, ρ.weight i x ≠ 0 → v i x ∈ Icc a b) :
    ρ.mix v x ∈ Icc a b := by
  simpa only [mix, smul_eq_mul] using (convex_Icc a b).finsum_mem
    (fun i => ρ.nonneg i x) (ρ.sum_one ⟨x, hx⟩) hv

theorem eventually_finite_weights {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ∀ᶠ y in 𝓝 x, ∀i ∉ s, ρ.weight i y = 0 := by
  classical
  obtain ⟨T, hT, hfin⟩ := ρ.locallyFinite ⟨x, hx⟩
  refine ⟨hfin.toFinset, ?_⟩
  have hsub : ∀ᶠ y : Ω in 𝓝 ⟨x, hx⟩, ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := by
    filter_upwards [hT] with y hy i hi
    by_contra hn
    apply hi
    exact hfin.mem_toFinset.mpr ⟨y, hn, hy⟩
  have hmap : ∀ᶠ y in Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 ⟨x, hx⟩),
      ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := hsub
  have hm : Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 (⟨x, hx⟩ : Ω)) = 𝓝 x :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hx⟩
  rwa [hm] at hmap

theorem mix_eventually_eq_sum (v : ι → EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  refine ⟨s, hs.mono fun y hy => ?_⟩
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change ρ.weight i y * v i y = 0
  rw [hy i his, zero_mul]

theorem mix_contDiffOn (v : ι → EuclideanPlane → ℝ)
    (hv : ∀i, ContDiff ℝ (⊤ : ℕ∞) (v i)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ρ.mix v) Ω := by
  intro x hx
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum v hx
  apply ContDiffAt.contDiffWithinAt
  apply ((ContDiff.sum (fun i _ => (ρ.smooth i).mul (hv i))).contDiffAt).congr_of_eventuallyEq
  exact hs

theorem mix_fderiv (v : ι → EuclideanPlane → ℝ)
    (hv : ∀i, ContDiff ℝ (⊤ : ℕ∞) (v i)) {x : EuclideanPlane} (hx : x ∈ Ω) :
    fderiv ℝ (ρ.mix v) x =
      ∑ᶠ i, fderiv ℝ (fun y => ρ.weight i y * v i y) x := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have hsum : ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
    filter_upwards [hs] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    apply hi
    change ρ.weight i y * v i y = 0
    rw [hy i his, zero_mul]
  rw [hsum.fderiv_eq]
  rw [fderiv_fun_sum (fun i _ =>
    ((ρ.smooth i).mul (hv i)).differentiable (by simp) x)]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change fderiv ℝ (fun y => ρ.weight i y * v i y) x = 0
  have hz : (fun y => ρ.weight i y * v i y) =ᶠ[𝓝 x] (fun _ => 0) :=
    hs.mono fun y hy => by
      change ρ.weight i y * v i y = 0
      rw [hy i his, zero_mul]
  rw [hz.fderiv_eq]
  exact fderiv_const_apply 0

end OpenPlanePartition

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionErrorSum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected local smoothing errors have a globally controlled L²
sum. Finiteness at each point follows from local finiteness of the weights. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem partitionDerivativeError_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (u : EuclideanPlane → ℝ)
    (G : ι → EuclideanPlane → EuclideanPlane) (v : ι → EuclideanPlane → ℝ)
    (i : Fin 2) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => partitionDerivativeError ρ u G v i j x) := by
  classical
  by_cases hx : x ∈ Ω
  · obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
    apply s.finite_toSet.subset
    intro j hj
    by_contra hjs
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hjs
    have hd : fderiv ℝ (ρ.weight j) x = 0 := by
      rw [hz.fderiv_eq]
      exact fderiv_const_apply 0
    simp only [partitionDerivativeError, hz.eq_of_nhds, hd,
      zero_apply, zero_mul, zero_add]
  · apply finite_empty.subset
    intro j hj
    apply False.elim
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    have hnot : x ∉ tsupport (ρ.weight j) := fun h => hx (ρ.inside j h)
    simp only [partitionDerivativeError, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, zero_apply, zero_mul, zero_add]

theorem exists_partition_approximation_with_summed_error
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ,
      (∀j, (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j) ∧
          ∀x, v j x ∈ Icc 0 1) ∧
        ∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
          ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      ∀i : Fin 2, eLpNorm (fun x => ∑ᶠ j,
        partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x)
        2 volume ≤ ∑' j, ε j := by
  obtain ⟨v, hv⟩ := exists_partition_smooth_approximants ρ W hW hsub u hu hunit ε hε
  refine ⟨v, fun j => ⟨(hv j).1, (hv j).2.1⟩, ?_⟩
  intro i
  apply (eLpNorm_finsum_le_tsum_of_pointFinite volume _ ?_
    (partitionDerivativeError_pointFinite ρ u _ v i)).trans
  · exact ENNReal.tsum_le_tsum (fun j => ((hv j).2.2 i).le)
  · intro j
    exact aestronglyMeasurable_partition_derivative_error (hW j) (hu j)
      (hv j).1.1 (ρ.smooth j) (hsub j) i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionGradientIdentity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total selected error is the derivative of the smooth partition
sum minus the corresponding partition of local weak gradients. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem finite_weights_and_derivatives {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι,
      (∀j ∉ s, ρ.weight j x = 0 ∧ fderiv ℝ (ρ.weight j) x = 0) ∧
      (ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y) ∧
      (∑j ∈ s, ρ.weight j x) = 1 ∧ (∑j ∈ s, fderiv ℝ (ρ.weight j) x) = 0 := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have heq : ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y := by
    filter_upwards [hs] with y hy
    simp only [mix, mul_one]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  have hone : (fun y => ∑j ∈ s, ρ.weight j y) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hs, Ω.isOpen.mem_nhds hx] with y hy hyΩ
    rw [← ρ.sum_one ⟨y, hyΩ⟩]
    symm
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  refine ⟨s, ?_, heq, hone.eq_of_nhds, ?_⟩
  · intro j hj
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hj
    refine ⟨hz.eq_of_nhds, ?_⟩
    rw [hz.fderiv_eq]
    exact fderiv_const_apply 0
  · calc
      _ = fderiv ℝ (fun y => ∑j ∈ s, ρ.weight j y) x :=
        (fderiv_fun_sum (fun j _ => (ρ.smooth j).differentiable (by simp) x)).symm
      _ = fderiv ℝ (fun _ : EuclideanPlane => (1 : ℝ)) x := hone.fderiv_eq
      _ = 0 := fderiv_const_apply 1

theorem mix_gradient_error_identity
    (u : EuclideanPlane → ℝ) (G : ι → EuclideanPlane → EuclideanPlane)
    (v : ι → EuclideanPlane → ℝ) (hv : ∀j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    {x : EuclideanPlane} (hx : x ∈ Ω) (i : Fin 2) :
    (fderiv ℝ (ρ.mix v) x) (EuclideanSpace.single i 1) -
      (∑ᶠ j, ρ.weight j x * G j x i) =
      ∑ᶠ j, partitionDerivativeError ρ u G v i j x := by
  classical
  obtain ⟨s, hz, _, _, hd⟩ := ρ.finite_weights_and_derivatives hx
  have hmix := ρ.mix_fderiv v hv hx
  have hzero (j : ι) (hj : j ∉ s) :
      fderiv ℝ (fun y => ρ.weight j y * v j y) x = 0 := by
    rw [fderiv_fun_mul ((ρ.smooth j).differentiable (by simp) x)
      ((hv j).differentiable (by simp) x), (hz j hj).1, (hz j hj).2]
    simp
  have hf : (∑ᶠ j, fderiv ℝ (fun y => ρ.weight j y * v j y) x) =
      ∑j ∈ s, fderiv ℝ (fun y => ρ.weight j y * v j y) x := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hzero j hjs)
  have hG : (∑ᶠ j, ρ.weight j x * G j x i) = ∑j ∈ s, ρ.weight j x * G j x i := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    apply hj
    change ρ.weight j x * G j x i = 0
    rw [(hz j hjs).1, zero_mul]
  have herr : (∑ᶠ j, partitionDerivativeError ρ u G v i j x) =
      ∑j ∈ s, partitionDerivativeError ρ u G v i j x := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    simp only [partitionDerivativeError, (hz j hjs).1, (hz j hjs).2,
      zero_apply, zero_mul, zero_add]
  have hd' : (∑j ∈ s, (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1)) = 0 := by
    simpa only [sum_apply, zero_apply] using
      congrArg (fun A : EuclideanPlane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd
  rw [hmix, hf, hG, herr]
  simp only [sum_apply]
  have hprod (j : ι) :
      (fderiv ℝ (fun y => ρ.weight j y * v j y) x) (EuclideanSpace.single i 1) =
      ρ.weight j x * (fderiv ℝ (v j) x) (EuclideanSpace.single i 1) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * v j x := by
    rw [fderiv_fun_mul ((ρ.smooth j).differentiable (by simp) x)
      ((hv j).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hprod, partitionDerivativeError, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hd']
  ring

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositivePartitionSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive smoothing on an open plane domain with a prescribed sum of
local gradient errors. All approximants and partition weights are constructed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_positive_partition_smoothing
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ (∀x ∈ Ω, v x ∈ Icc 0 1) ∧
      (∀x ∈ Ω, ∀a b : ℝ,
        (∀j, ρ.weight j x ≠ 0 → ∀y ∈ W j, u y ∈ Icc a b) → v x ∈ Icc a b) ∧
      ∀i : Fin 2, eLpNorm (fun x =>
        (fderiv ℝ v x) (EuclideanSpace.single i 1) -
          ∑ᶠ j, ρ.weight j x * (hu j).weakGrad x i) 2 (volume.restrict Ω) ≤ ∑' j, ε j := by
  obtain ⟨v, hv, he⟩ := exists_partition_approximation_with_summed_error
    ρ W hW hsub u hu hunit ε hε
  have hsmooth (j : ι) := (hv j).1.1
  refine ⟨ρ.mix v, ρ.mix_contDiffOn v hsmooth, ?_, ?_, ?_⟩
  · intro x hx
    exact ρ.mix_mem_Icc v hx (fun j _ => (hv j).1.2.2 x)
  · intro x hx a b hab
    exact ρ.mix_mem_Icc v hx (fun j hj =>
      (hv j).2 a b (hab j hj) x (subset_tsupport (ρ.weight j) hj))
  · intro i
    calc
      _ = eLpNorm (fun x => ∑ᶠ j,
          partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x)
          2 (volume.restrict Ω) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
        exact ρ.mix_gradient_error_identity u _ v hsmooth hx i
      _ ≤ eLpNorm (fun x => ∑ᶠ j,
          partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ _ := he i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OpenDomainRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A globally measurable representative of a smooth function on an open
physical plane domain, preserving its actual derivatives there. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem openZeroExtension_eq {D : Set EuclideanPlane} {w : EuclideanPlane → ℝ}
    {x : EuclideanPlane} (hx : x ∈ D) : openZeroExtension D w x = w x := by
  classical
  exact piecewise_eq_of_mem D w (fun _ => 0) hx

theorem openZeroExtension_measurable {D : Set EuclideanPlane} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ} (hw : ContinuousOn w D) : Measurable (openZeroExtension D w) := by
  classical
  exact hw.measurable_piecewise continuousOn_const hD.measurableSet

theorem openZeroExtension_contDiffOn {D : Set EuclideanPlane}
    {w : EuclideanPlane → ℝ} (hw : ContDiffOn ℝ (⊤ : ℕ∞) w D) :
    ContDiffOn ℝ (⊤ : ℕ∞) (openZeroExtension D w) D :=
  hw.congr (fun _ hx => openZeroExtension_eq hx)

theorem openZeroExtension_fderiv {D : Set EuclideanPlane} (hD : IsOpen D)
    (w : EuclideanPlane → ℝ) {x : EuclideanPlane} (hx : x ∈ D) :
    fderiv ℝ (openZeroExtension D w) x = fderiv ℝ w x := by
  have he : openZeroExtension D w =ᶠ[𝓝 x] w := by
    filter_upwards [hD.mem_nhds hx] with y hy
    exact openZeroExtension_eq hy
  exact he.fderiv_eq

theorem openZeroExtension_gradient_memLp {D : Set EuclideanPlane} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ} {i : Fin 2}
    (hw : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict D)) :
    MemLp (fun x => (fderiv ℝ (openZeroExtension D w) x) (EuclideanSpace.single i 1))
      2 (volume.restrict D) := by
  apply hw.ae_eq
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  rw [openZeroExtension_fderiv hD w hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealGradientNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L² preservation for each derivative component under the planar
coordinate change used by finite transfer. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem real_chart_zeroExtension_partial_eLpNorm {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    eLpNorm (fun p =>
        (fderiv ℝ ((openZeroExtension (euclideanPlaneCoordinates ⁻¹' D) w) ∘
          euclideanPlaneCoordinates.symm) p) (if i = 0 then (1, 0) else (0, 1)))
        2 (volume.restrict D) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
  have hΩ := hD.preimage euclideanPlaneCoordinates.continuous
  rw [real_chart_partial_eLpNorm hD (openZeroExtension_contDiffOn hw) i
    (openZeroExtension_gradient_memLp hΩ hi)]
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [openZeroExtension_fderiv hΩ w hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RectangleNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact rectangles form a neighborhood basis inside a planar open
set; countably many of their interiors suffice to patch measurability. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

theorem exists_closed_rectangle_inside_open
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧ p ∈ Ioo a b ×ˢ Ioo c d ∧
      Icc a b ×ˢ Icc c d ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  refine ⟨p.1 - ε/2, p.1 + ε/2, p.2 - ε/2, p.2 + ε/2,
    by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
  intro q hq
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> apply abs_lt.mpr
  · constructor <;> linarith [hq.1.1, hq.1.2]
  · constructor <;> linarith [hq.2.1, hq.2.2]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ShrinkingRectangleCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact coordinate rectangles whose images have diameter controlled
by the distance to the dust. These are the sampling patches for smoothing. -/

open Set Metric

namespace CircleDomainRigidity

theorem dist_le_infDist_of_small_ball
    {X : Type*} [MetricSpace X] (B : Set X) {c x y : X}
    (hx : x ∈ ball c (infDist c B / 4)) (hy : y ∈ ball c (infDist c B / 4)) :
    dist y x ≤ infDist x B := by
  have hxc : dist c x < infDist c B / 4 := by simpa only [mem_ball, dist_comm] using hx
  have hyc : dist y c < infDist c B / 4 := hy
  have hi := infDist_le_infDist_add_dist (x := c) (y := x) (s := B)
  have ht := dist_triangle y c x
  linarith [infDist_nonneg (x := c) (s := B)]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmallShrinkingRectanglePartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking sampling rectangles with uniformly small physical diameter. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem exists_small_closed_coordinate_rectangle_with_diameter
    {X : Type*} [MetricSpace X] {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty)
    {x : EuclideanPlane} (hx : x ∈ Ω) (hqx : q x ∉ B) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧
      euclideanPlaneCoordinates x ∈ Ioo a b ×ˢ Ioo c d ∧
      (euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ Ω) ∧
      (∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        ∀z ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
          dist (q y) (q z) ≤ infDist (q z) B) ∧
      (∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        ∀z ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
          dist (⟨y 0, y 1⟩ : ℂ) (⟨z 0, z 1⟩ : ℂ) ≤ 1) := by
  let f : EuclideanPlane → ℂ := fun y => ⟨y 0, y 1⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp euclideanPlaneCoordinates.continuous
  let V := (Ω ∩ q ⁻¹' ball (q x) (infDist (q x) B / 4)) ∩ f ⁻¹' ball (f x) (1 / 2)
  have hδ : 0 < infDist (q x) B / 4 := div_pos
    ((hB.notMem_iff_infDist_pos hne).1 hqx) (by norm_num)
  have hV : IsOpen V := (hq.isOpen_inter_preimage hΩ isOpen_ball).inter (isOpen_ball.preimage hf)
  have hxV : x ∈ V := ⟨⟨hx, mem_ball_self hδ⟩, mem_ball_self (by norm_num)⟩
  have hVe : IsOpen (euclideanPlaneCoordinates '' V) :=
    euclideanPlaneCoordinates.toHomeomorph.isOpenMap V hV
  obtain ⟨a, b, c, d, hab, hcd, hpoint, hrect⟩ := exists_closed_rectangle_inside_open hVe
    (mem_image_of_mem euclideanPlaneCoordinates hxV)
  have hsub : euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ V := by
    intro y hy
    obtain ⟨z, hz, heq⟩ := hrect hy
    exact euclideanPlaneCoordinates.injective heq ▸ hz
  refine ⟨a, b, c, d, hab, hcd, hpoint, (hsub.trans inter_subset_left).trans inter_subset_left, ?_, ?_⟩
  · intro y hy z hz
    exact dist_le_infDist_of_small_ball B (hsub hz).1.2 (hsub hy).1.2
  · intro y hy z hz
    have h1 : dist (f y) (f x) < 1 / 2 := (hsub hy).2
    have h2' : dist (f z) (f x) < 1 / 2 := (hsub hz).2
    have h2 : dist (f x) (f z) < 1 / 2 := by simpa only [dist_comm] using h2'
    exact (dist_triangle (f y) (f x) (f z)).trans (by linarith)


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalAreaLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local planar square integrability from spherical area. Spherical area
is written in its finite stereographic chart, with density 4/(1+|z|²)². -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_1
theorem lintegral_sphericalArea (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻x, g x ∂sphericalArea =
      ∫⁻z : ℂ, ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) := by
  rw [sphericalArea, lintegral_map hg OnePoint.continuous_coe.measurable]
  exact lintegral_withDensity_eq_lintegral_mul _
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal
    (hg.comp OnePoint.continuous_coe.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalPlaneCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite physical chart in the Euclidean coordinates used for smoothing. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

theorem exists_planeSphere_eq {p : Sphere} (hp : p ≠ OnePoint.infty) :
    ∃x : EuclideanPlane, planeSphere x = p := by
  cases p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z =>
    refine ⟨complexPlaneCoordinates.symm z, ?_⟩
    exact congrArg ((↑) : ℂ → Sphere) (complexPlaneCoordinates.apply_symm_apply z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneQuotientRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Descend a physical planar function through the actual domain homeomorphism. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem quotientPlaneRepresentative_on_domain
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ)
    (p : Sphere) (hp : p ∈ d.physicalDomain) :
    quotientPlaneRepresentative d w (d.domainEquiv ⟨p, hp⟩).val =
      sphereFromPlaneFunction w p := by
  simp only [quotientPlaneRepresentative, dite_eq_left (d.domainEquiv ⟨p, hp⟩).property]
  have he : (⟨(d.domainEquiv ⟨p, hp⟩).val, (d.domainEquiv ⟨p, hp⟩).property⟩ :
      d.quotientDomain) = d.domainEquiv ⟨p, hp⟩ := rfl
  rw [he, Homeomorph.symm_apply_apply]

theorem quotientPlaneRepresentative_plane
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain d.physicalDomain) :
    quotientPlaneRepresentative d w (π (planeSphere x)) = w x := by
  have hp : planeSphere x ∈ d.physicalDomain := hx
  rw [← he ⟨planeSphere x, hp⟩, quotientPlaneRepresentative_on_domain d w _ hp]
  change sphereFromPlaneFunction w (complexPlaneCoordinates x : Sphere) = w x
  rw [sphereFromPlaneFunction_coe, ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealPhysicalRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable, smooth finite-plane representative with the constructed
Sobolev energy and the actual quotient pullback identity. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem exists_real_physical_representative
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (w : EuclideanPlane → ℝ) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain))
    (henergy : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain d.physicalDomain))) :
    ∃v : (ℝ × ℝ) → ℝ,
      Measurable v ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (FiniteTransfer.realChartDomain d.physicalDomain) ∧
      MemLp (FiniteTransfer.planarGradient v) 2
        (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) ∧
      (∀i : Fin 2, eLpNorm (fun p => (fderiv ℝ v p)
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain))) ∧
      ∀z : ℂ, (z : Sphere) ∈ d.physicalDomain →
        v (Complex.equivRealProdCLM z) = quotientPlaneRepresentative d w (π z) := by
  let Ω := physicalPlaneDomain d.physicalDomain
  let D := FiniteTransfer.realChartDomain d.physicalDomain
  have hΩ : IsOpen Ω := isOpen_physicalPlaneDomain hG
  have hD : IsOpen D := FiniteTransfer.isOpen_realChartDomain hG
  let w₀ := openZeroExtension Ω w
  let v : (ℝ × ℝ) → ℝ := w₀ ∘ euclideanPlaneCoordinates.symm
  have hmeas : Measurable w₀ := openZeroExtension_measurable hΩ hw.continuousOn
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) w₀ (euclideanPlaneCoordinates ⁻¹' D) :=
    openZeroExtension_contDiffOn hw
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) v D := by
    apply hs.comp euclideanPlaneCoordinates.symm.contDiff.contDiffOn
    intro p hp
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hgrad : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w₀ x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) :=
    fun i => openZeroExtension_gradient_memLp hΩ (henergy i)
  refine ⟨v, hmeas.comp euclideanPlaneCoordinates.symm.continuous.measurable, hsm,
    real_chart_gradient_memLp hD hs hgrad, ?_, ?_⟩
  · intro i
    exact real_chart_zeroExtension_partial_eLpNorm hD hw i (henergy i)
  intro z hz
  let x := euclideanPlaneCoordinates.symm (Complex.equivRealProdCLM z)
  have heq : planeSphere x = (z : Sphere) := by
    apply congrArg ((↑) : ℂ → Sphere)
    change Complex.equivRealProdCLM.symm
      (euclideanPlaneCoordinates (euclideanPlaneCoordinates.symm (Complex.equivRealProdCLM z))) = z
    simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hx : x ∈ Ω := by
    change planeSphere x ∈ d.physicalDomain
    rwa [heq]
  change openZeroExtension Ω w x = quotientPlaneRepresentative d w (π z)
  rw [openZeroExtension_eq hx, ← heq]
  exact (quotientPlaneRepresentative_plane d w π he hx).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneRepresentativeBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and unit bounds for the descended physical representative. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem sphereFromPlaneFunction_mem_Icc {G : Set Sphere} {w : EuclideanPlane → ℝ}
    (hw : ∀x ∈ physicalPlaneDomain G, w x ∈ Icc 0 1) :
    ∀p ∈ G, sphereFromPlaneFunction w p ∈ Icc 0 1 := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply hw
    change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExtendedWeightedCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted level estimate allows extended nonnegative densities.
Finite squared energy suffices; no pointwise finiteness is imposed. -/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace CircleDomainRigidity

theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ∞
  · simp [ha]
  by_cases hb : b = ∞
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have h : (a : ℝ) * (b : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ)), sq_nonneg (a : ℝ), sq_nonneg (b : ℝ)]
  exact_mod_cast h

theorem weighted_circle_coarea_extended_finite_energy
    (hcoarea : WeightedPlanarScalarCoarea) {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    (hq2 : (∫⁻z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞) :
    AEMeasurable (weightedCircleLevelLength D f q) (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) =
        (∫⁻z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) ∧
      ∀ᵐt ∂volume.restrict (Ico (0 : ℝ) 1), weightedCircleLevelLength D f q t < ∞ := by
  obtain ⟨hmeas, heq⟩ := weighted_circle_coarea hD hf.continuousOn q (hcoarea D hD f hf q hq)
  have hfinite : (∫⁻t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) < ∞ := by
    rw [heq]
    calc
      _ ≤ ∫⁻z in D, (q z ^ 2 + ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) := by
        apply lintegral_mono
        intro z
        simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using
          ennreal_mul_le_sq_add_sq (q z) (ENNReal.ofReal ‖fderiv ℝ f z‖)
      _ = (∫⁻z in D, q z ^ 2) + ∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) :=
        lintegral_add_left (hq.pow_const 2) _
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hq2, hf2⟩
  exact ⟨hmeas, heq, ae_lt_top' hmeas hfinite.ne⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CircleNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null images of local circle-valued traces

Projection modulo one preserves real outer-null sets. A countable family
of null real branches therefore gives a null image in the circle with
its Haar measure of total mass one.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem volume_addCircle_image_eq_zero {A : Set ℝ} (hA : volume A = 0) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' A) = 0 := by
  have hpiece (a : ℝ) :
      volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1))) = 0 := by
    let e := AddCircle.measurableEquivIoc (1 : ℝ) a
    let S : Set (Ioc a (a + 1)) := Subtype.val ⁻¹' A
    have he : MeasurePreserving e volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    have hset : e ⁻¹' S = ((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1)) := by
      ext y
      constructor
      · intro hy
        refine ⟨(e y).val, ⟨hy, (e y).property⟩, ?_⟩
        exact AddCircle.coe_equivIoc
      · rintro ⟨x, hx, rfl⟩
        change (AddCircle.equivIoc (1 : ℝ) a (x : AddCircle (1 : ℝ))).val ∈ A
        rw [AddCircle.equivIoc_coe_eq hx.2]
        exact hx.1
    rw [← hset, he.measure_preimage_equiv S,
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    apply measure_mono_null _ hA
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hcover : ((↑) : ℝ → AddCircle (1 : ℝ)) '' A ⊆
      ⋃ k : ℤ, ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        (A ∩ Ioc ((k : ℝ) - 1) ((k : ℝ) - 1 + 1)) := by
    rintro y ⟨x, hx, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨⌈x⌉, x, ⟨hx, ?_⟩, rfl⟩
    have hlo := Int.ceil_lt_add_one x
    have hhi := Int.le_ceil x
    constructor <;> linarith
  apply measure_mono_null hcover
  exact measure_iUnion_null (fun k => hpiece ((k : ℝ) - 1))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_BoundaryTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unique traces outside the countable band support

For a bounded real coordinate the interval band is the actual interval
between the lower and upper boundary limits. A zero band budget forces
these limits to agree and gives convergence from the physical domain.
Square summability of the budgets makes all exceptions countable.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem countable_band_support {X : Type*} {a : X → ℝ}
    (ha : Summable (fun x => a x ^ 2)) : {x | a x ≠ 0}.Countable := by
  simpa only [Function.support, ne_eq, sq_eq_zero_iff] using ha.countable_support

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarDifferentialEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-transfer gradient energy controls the norm of the scalar
real differential in the complex coarea chart. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem norm_complex_real_linear_le (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L 1| + |L Complex.I| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hsplit : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    ‖L z‖ = ‖z.re • L 1 + z.im • L Complex.I‖ := by
      conv_lhs => rw [hsplit, map_add, map_smul, map_smul]
    _ ≤ ‖z.re • L 1‖ + ‖z.im • L Complex.I‖ := norm_add_le _ _
    _ = |z.re| * |L 1| + |z.im| * |L Complex.I| := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖z‖ * |L 1| + ‖z‖ * |L Complex.I| :=
      add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _))
    _ = (|L 1| + |L Complex.I|) * ‖z‖ := by ring

theorem complex_chart_differential_energy_finite
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {f : (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f D)
    (henergy : MemLp (FiniteTransfer.planarGradient f) 2 (volume.restrict D)) :
    (∫⁻z in Complex.equivRealProdCLM ⁻¹' D,
      ENNReal.ofReal (‖fderiv ℝ (f ∘ Complex.equivRealProdCLM) z‖ ^ 2)) < ∞ := by
  let e := Complex.equivRealProdCLM
  let μ : Measure ℂ := volume.restrict (e ⁻¹' D)
  have hmp : MeasurePreserving e μ (volume.restrict D) :=
    Complex.volume_preserving_equiv_real_prod.restrict_preimage hD.measurableSet
  have hx := henergy.fst.comp_measurePreserving hmp
  have hy := henergy.snd.comp_measurePreserving hmp
  have hi : Integrable (fun z : ℂ =>
      2 * ((fderiv ℝ f (e z)) (1, 0) ^ 2 + (fderiv ℝ f (e z)) (0, 1) ^ 2)) μ := by
    simpa only [FiniteTransfer.planarGradient, Function.comp_apply, Pi.add_apply] using
      (hx.integrable_sq.add hy.integrable_sq).const_mul 2
  have hfinite : (∫⁻z, ENNReal.ofReal
      (2 * ((fderiv ℝ f (e z)) (1, 0) ^ 2 + (fderiv ℝ f (e z)) (0, 1) ^ 2)) ∂μ) < ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => by positivity)).2 hi |>.lt_top
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) hfinite
  filter_upwards [ae_restrict_mem (hD.preimage e.continuous).measurableSet] with z hz
  apply ENNReal.ofReal_le_ofReal
  have hdiff : DifferentiableAt ℝ f (e z) :=
    (hf.differentiableOn (by norm_num) _ hz).differentiableAt (hD.mem_nhds hz)
  have heq : fderiv ℝ (f ∘ e) z = (fderiv ℝ f (e z)).comp e.toContinuousLinearMap := by
    rw [fderiv_comp z hdiff e.differentiableAt, e.fderiv]
  have hn := norm_complex_real_linear_le ((fderiv ℝ f (e z)).comp e.toContinuousLinearMap)
  have hnorm : ‖fderiv ℝ (f ∘ e) z‖ ≤
      |(fderiv ℝ f (e z)) (1, 0)| + |(fderiv ℝ f (e z)) (0, 1)| := by
    rw [heq]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    e, Complex.equivRealProdCLM_apply, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im] using hn
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_abs ((fderiv ℝ f (e z)) (1, 0)), sq_abs ((fderiv ℝ f (e z)) (0, 1)),
    sq_nonneg (|(fderiv ℝ f (e z)) (1, 0)| - |(fderiv ℝ f (e z)) (0, 1)|)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedHausdorffImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Hausdorff-measure estimates for the finite sphere chart.
The estimates are proved from the library's Lipschitz Hausdorff bound. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

theorem lipschitzOn_hausdorff_restrict_le_map
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) {K : ℝ≥0} {S : Set X}
    (hK : LipschitzOnWith K f S) :
    (μH[1] : Measure Y).restrict (f '' S) ≤
      (K : ℝ≥0∞) • ((μH[1] : Measure X).restrict S).map f := by
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.restrict_apply hT, Measure.smul_apply, Measure.map_apply hf hT,
    Measure.restrict_apply (hf hT)]
  have heq : T ∩ f '' S = f '' (f ⁻¹' T ∩ S) := by
    ext y
    constructor
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxS⟩, rfl⟩
      exact ⟨hx, x, hxS, rfl⟩
  rw [heq]
  simpa only [ENNReal.rpow_one, smul_eq_mul] using
    (hK.mono inter_subset_right).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)

theorem lipschitzOn_lintegral_hausdorff_image_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) {K : ℝ≥0} {S : Set X}
    (hK : LipschitzOnWith K f S) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in f '' S, g y ∂(μH[1] : Measure Y)) ≤
      (K : ℝ≥0∞) * ∫⁻x in S, g (f x) ∂(μH[1] : Measure X) := by
  calc
    _ ≤ ∫⁻y, g y ∂((K : ℝ≥0∞) • ((μH[1] : Measure X).restrict S).map f) :=
      lintegral_mono' (lipschitzOn_hausdorff_restrict_le_map hf hK) le_rfl
    _ = _ := by rw [lintegral_smul_measure, lintegral_map hg hf, smul_eq_mul]

theorem lintegral_hausdorff_image_le_of_partition
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) (A : ℕ → Set X)
    (hA : ∀n, MeasurableSet (A n)) (hdisj : Pairwise (Disjoint on A))
    (hcover : ⋃n, A n = univ) (K : ℕ → ℝ≥0)
    (hK : ∀n, LipschitzOnWith (K n) f (A n))
    (w : X → ℝ≥0∞)
    (hweight : ∀n x, x ∈ A n → (K n : ℝ≥0∞) ≤ w x)
    {S : Set X} (hS : MeasurableSet S) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in f '' S, g y ∂(μH[1] : Measure Y)) ≤
      ∫⁻x in S, w x * g (f x) ∂(μH[1] : Measure X) := by
  have hsets : ⋃n, S ∩ A n = S := by rw [← inter_iUnion, hcover, inter_univ]
  calc
    _ = ∫⁻y in ⋃n, f '' (S ∩ A n), g y ∂(μH[1] : Measure Y) := by
      rw [← image_iUnion, hsets]
    _ ≤ ∑'n, ∫⁻y in f '' (S ∩ A n), g y ∂(μH[1] : Measure Y) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑'n, ∫⁻x in S ∩ A n, w x * g (f x) ∂(μH[1] : Measure X) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ (K n : ℝ≥0∞) * ∫⁻x in S ∩ A n, g (f x) ∂(μH[1] : Measure X) :=
          lipschitzOn_lintegral_hausdorff_image_le hf ((hK n).mono inter_subset_right) g hg
        _ = ∫⁻x in S ∩ A n, (K n : ℝ≥0∞) * g (f x) ∂(μH[1] : Measure X) :=
          (lintegral_const_mul _ (hg.comp hf)).symm
        _ ≤ _ := setLIntegral_mono' (hS.inter (hA n)) fun x hx =>
          mul_le_mul' (hweight n x hx.2) le_rfl
    _ = _ := by
      rw [← lintegral_iUnion (fun n => hS.inter (hA n))
        (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right), hsets]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GlobalSphericalDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The decaying finite-chart density is globally square integrable.
No compact restriction is needed after inserting the spherical factor. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem spherical_weight_sq_le_areaDensity (z : ℂ) :
    (1 / (1 + ‖z‖ ^ 2)) ^ 2 ≤ sphericalAreaDensity z := by
  rw [div_pow, one_pow, sphericalAreaDensity]
  exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_StereographicDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decay of the derivative of the fixed inverse stereographic map.
This supplies the spherical weight missing from a compact-chart bound. -/

open Set Function
open scoped RealInnerProductSpace

noncomputable section

namespace CircleDomainRigidity

theorem stereoInvFunAux_eq_centered (v w : RoundAmbient) :
    stereoInvFunAux v w =
      v + (4 / (‖w‖ ^ 2 + 4)) • (w - (2 : ℝ) • v) := by
  have hn : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have h1 : (‖w‖ ^ 2 + 4)⁻¹ * 4 = 4 / (‖w‖ ^ 2 + 4) := by ring
  have h2 : (‖w‖ ^ 2 + 4)⁻¹ * (‖w‖ ^ 2 - 4) =
      1 - (4 / (‖w‖ ^ 2 + 4)) * 2 := by
    field_simp
    ring
  simp only [stereoInvFunAux, smul_add, smul_smul, h1, h2]
  module

theorem stereographic_scalar_bound {r : ℝ} (hr : 0 ≤ r) :
    4 / (r ^ 2 + 4) + 8 * r * (r + 2) / (r ^ 2 + 4) ^ 2 ≤
      16 / (r ^ 2 + 4) := by
  have hD : 0 < r ^ 2 + 4 := by positivity
  have hpoly : 4 * (r ^ 2 + 4) + 8 * r * (r + 2) ≤ 16 * (r ^ 2 + 4) := by
    nlinarith [sq_nonneg (r - 2)]
  calc
    _ = (4 * (r ^ 2 + 4) + 8 * r * (r + 2)) / (r ^ 2 + 4) ^ 2 := by
      field_simp
    _ ≤ (16 * (r ^ 2 + 4)) / (r ^ 2 + 4) ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2 hpoly
    _ = _ := by field_simp

theorem stereoInvFunAux_fderiv_apply (v w h : RoundAmbient) :
    (fderiv ℝ (stereoInvFunAux v) w) h =
      (4 / (‖w‖ ^ 2 + 4)) • h -
        (8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v) := by
  let D : ℝ := ‖w‖ ^ 2 + 4
  have hD : D ≠ 0 := by dsimp [D] <;> positivity
  have hQ := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const (4 : ℝ)
  have ha : HasFDerivAt (fun z : RoundAmbient => 4 / (‖z‖ ^ 2 + 4))
      ((-8 / D ^ 2) • innerSL ℝ w) w := by
    convert ((hasFDerivAt_inv hD).comp w hQ).const_mul (4 : ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    · funext z
      simp only [Function.comp_apply, div_eq_mul_inv]
    · ext z
      simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
        smul_eq_mul]
      dsimp [D]
      ring
  have hF := (hasFDerivAt_const v w).add
    (ha.smul ((hasFDerivAt_id w).sub_const ((2 : ℝ) • v)))
  have heq : stereoInvFunAux v =
      fun z : RoundAmbient => v + (4 / (‖z‖ ^ 2 + 4)) • (z - (2 : ℝ) • v) :=
    funext (stereoInvFunAux_eq_centered v)
  have hd := hF.fderiv
  change fderiv ℝ (fun z : RoundAmbient =>
    v + (4 / (‖z‖ ^ 2 + 4)) • (z - (2 : ℝ) • v)) w = _ at hd
  rw [heq, hd]
  simp only [zero_add, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  dsimp [D]
  module

theorem norm_stereoInvFunAux_fderiv_apply (v w h : RoundAmbient) (hv : ‖v‖ ≤ 1) :
    ‖(fderiv ℝ (stereoInvFunAux v) w) h‖ ≤
      (16 / (‖w‖ ^ 2 + 4)) * ‖h‖ := by
  have hD : 0 < ‖w‖ ^ 2 + 4 := by positivity
  have hc : |8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2| ≤
      8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2 := by
    calc
      _ = 8 * |inner ℝ w h| / (‖w‖ ^ 2 + 4) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hD)]
        norm_num
      _ ≤ 8 * (‖w‖ * ‖h‖) / (‖w‖ ^ 2 + 4) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm w h) (by norm_num))
          (sq_nonneg _)
      _ = _ := by ring
  have hvect : ‖w - (2 : ℝ) • v‖ ≤ ‖w‖ + 2 := by
    calc
      _ ≤ ‖w‖ + ‖(2 : ℝ) • v‖ := norm_sub_le _ _
      _ = ‖w‖ + 2 * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]; norm_num
      _ ≤ _ := by linarith
  have hfirst : ‖(4 / (‖w‖ ^ 2 + 4)) • h‖ = (4 / (‖w‖ ^ 2 + 4)) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hD)]
  have hsecond : ‖(8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v)‖ ≤
      (8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2) * (‖w‖ + 2) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hvect (norm_nonneg _) (by positivity)
  rw [stereoInvFunAux_fderiv_apply]
  calc
    _ ≤ ‖(4 / (‖w‖ ^ 2 + 4)) • h‖ +
        ‖(8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v)‖ := norm_sub_le _ _
    _ ≤ (4 / (‖w‖ ^ 2 + 4)) * ‖h‖ +
        (8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2) * (‖w‖ + 2) :=
      add_le_add hfirst.le hsecond
    _ = (4 / (‖w‖ ^ 2 + 4) + 8 * ‖w‖ * (‖w‖ + 2) / (‖w‖ ^ 2 + 4) ^ 2) * ‖h‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (stereographic_scalar_bound (norm_nonneg w)) (norm_nonneg h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartDerivativeDecay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global inverse-quadratic derivative bound for the chosen finite sphere chart. -/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem norm_stereoInvFunAux_fderiv (v w : RoundAmbient) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (stereoInvFunAux v) w‖ ≤ 16 / (‖w‖ ^ 2 + 4) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  exact norm_stereoInvFunAux_fderiv_apply v w h hv

theorem norm_linearSphereChartMap (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) :
    ‖linearSphereChartMap v A‖ ≤ ‖A.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (linearSphereChartMap v A)
    (norm_nonneg A.toContinuousLinearMap)
  intro h
  exact A.toContinuousLinearMap.le_opNorm h

theorem linear_stereo_fderiv (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z =
      (fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)).comp (linearSphereChartMap v A) := by
  have hA : HasFDerivAt (fun z : ℂ => (A z : RoundAmbient)) (linearSphereChartMap v A) z :=
    (ℝ ∙ v)ᗮ.subtypeL.hasFDerivAt.comp z A.hasFDerivAt
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux v) := contDiff_stereoInvFunAux
  have hD : DifferentiableAt ℝ (stereoInvFunAux v) (A z : RoundAmbient) :=
    (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  have hFD : HasFDerivAt (stereoInvFunAux v)
      (fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)) (A z : RoundAmbient) :=
    hD.hasFDerivAt
  have heq := (hFD.comp z hA).fderiv
  exact heq

theorem linear_stereo_derivative_decay
    (v : RoundAmbient) (hv : ‖v‖ ≤ 1) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    ‖fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z‖ ≤
      (16 * ‖A.toContinuousLinearMap‖ * (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2)) /
        (1 + ‖z‖ ^ 2) := by
  rw [linear_stereo_fderiv]
  calc
    _ ≤ ‖fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)‖ *
        ‖linearSphereChartMap v A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (16 / (‖A z‖ ^ 2 + 4)) * ‖A.toContinuousLinearMap‖ :=
      mul_le_mul (norm_stereoInvFunAux_fderiv v _ hv) (norm_linearSphereChartMap v A)
        (norm_nonneg _) (by positivity)
    _ = 16 * ‖A.toContinuousLinearMap‖ / (‖A z‖ ^ 2 + 4) := by ring
    _ ≤ _ := linear_chart_inverse_quadratic_bound A z

theorem finite_sphere_chart_derivative_decay :
    ∃C : ℝ, 0 ≤ C ∧ ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2) := by
  classical
  have hlin (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (hv : ‖v‖ ≤ 1) :
      ∃C : ℝ, 0 ≤ C ∧ ∀z : ℂ,
        ‖fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z‖ ≤
          C / (1 + ‖z‖ ^ 2) :=
    ⟨_, by positivity, linear_stereo_derivative_decay v hv A⟩
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  apply hlin
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereChartSmallSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative finite-chart Lipschitz constants on small convex sets. -/

open Set Metric
open scoped NNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem quadratic_weight_compare {x y : ℂ} (hxy : dist x y ≤ 1) :
    1 + ‖x‖ ^ 2 ≤ 3 * (1 + ‖y‖ ^ 2) := by
  have hnorm : ‖x‖ ≤ ‖y‖ + 1 := by
    have hn := norm_sub_norm_le x y
    rw [← dist_eq_norm] at hn
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg x) hnorm 2
  nlinarith [sq_nonneg (‖y‖ - 1)]

theorem decay_weight_compare {x y : ℂ} (hxy : dist x y ≤ 1) {C : ℝ} (hC : 0 ≤ C) :
    C / (1 + ‖y‖ ^ 2) ≤ 3 * C / (1 + ‖x‖ ^ 2) := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hy : 0 < 1 + ‖y‖ ^ 2 := by positivity
  apply (div_le_div_iff₀ hy hx).2
  nlinarith [mul_le_mul_of_nonneg_left (quadratic_weight_compare hxy) hC]

theorem finite_sphere_chart_lipschitz_on_small_convex
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {K : Set ℂ} (hK : Convex ℝ K) (hne : K.Nonempty)
    (hdiam : ∀x ∈ K, ∀y ∈ K, dist x y ≤ 1) :
    ∃L : ℝ≥0, LipschitzOnWith L ((↑) : ℂ → Sphere) K ∧
      ∀z ∈ K, (L : ℝ) ≤ 9 * C / (1 + ‖z‖ ^ 2) := by
  obtain ⟨c, hc⟩ := hne
  let L : ℝ≥0 := ⟨3 * C / (1 + ‖c‖ ^ 2), by positivity⟩
  let F : ℂ → RoundAmbient := fun z => roundSphereEquiv (z : Sphere)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := contDiff_roundSphere_finite_chart
  have hLip : LipschitzOnWith L F K :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun _ _ => (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt)
      (fun z hz => by
        change ‖fderiv ℝ F z‖₊ ≤ L
        exact_mod_cast (hderiv z).trans (decay_weight_compare (hdiam c hc z hz) hC)) hK
  refine ⟨L, ?_, ?_⟩
  · intro z hz w hw
    exact hLip hz hw
  · intro z hz
    change 3 * C / (1 + ‖c‖ ^ 2) ≤ _
    have h := decay_weight_compare (hdiam z hz c hc) (show 0 ≤ 3 * C by positivity)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SphericalWeightedLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spherical metric contributes its decay factor to weighted level
length. No pointwise finiteness of the nonnegative density is required. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r60a8cf_1 : BorelSpace Sphere := ⟨rfl⟩
theorem finite_sphere_chart_weighted_length_le
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {S : Set ℂ} (hS : MeasurableSet S) (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in ((↑) : ℂ → Sphere) '' S, g y ∂(μH[1] : Measure Sphere)) ≤
      ∫⁻z in S, ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
        ∂(μH[1] : Measure ℂ) := by
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq ℂ
  let V : ℕ → Set ℂ := fun n => closedBall (c n) (1 / 2)
  have hV (n : ℕ) : MeasurableSet (V n) := isClosed_closedBall.measurableSet
  have hcover : ⋃n, V n = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := hc.exists_dist_lt z (by norm_num : (0 : ℝ) < 1 / 2)
    exact mem_iUnion.mpr ⟨n, hn.le⟩
  have hsmall (n : ℕ) : ∀x ∈ V n, ∀y ∈ V n, dist x y ≤ 1 := by
    intro x hx y hy
    have h1 : dist x (c n) ≤ 1 / 2 := hx
    have h2 : dist (c n) y ≤ 1 / 2 := by
      change dist y (c n) ≤ 1 / 2 at hy
      simpa only [dist_comm] using hy
    exact (dist_triangle x (c n) y).trans (by linarith)
  choose K hK hweight using fun n => finite_sphere_chart_lipschitz_on_small_convex
    hC hderiv (convex_closedBall (c n) (1 / 2))
      (nonempty_closedBall.mpr (by norm_num)) (hsmall n)
  apply lintegral_hausdorff_image_le_of_partition OnePoint.continuous_coe.measurable
    (disjointed V) (MeasurableSet.disjointed hV) (disjoint_disjointed V)
    (by rw [iUnion_disjointed, hcover]) K
    (fun n => (hK n).mono (disjointed_subset V n))
    (fun z => ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)))
    (fun n z hz => ?_) hS g hg
  have hw := ENNReal.ofReal_le_ofReal (hweight n z (disjointed_subset V n hz))
  simpa using hw

theorem spherical_weighted_density_sq_finite
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z : ℂ, (ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * g (z : Sphere)) ^ 2) < ∞ := by
  rw [lintegral_sphericalArea _ (hg.pow_const 2)] at he
  apply lt_of_le_of_lt (lintegral_mono fun z => ?_) he
  rw [mul_pow, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 / (1 + ‖z‖ ^ 2))]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (spherical_weight_sq_le_areaDensity z)) le_rfl

theorem spherical_weighted_length_le_chart
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (A : Set Sphere) (hA : MeasurableSet (((↑) : ℂ → Sphere) ⁻¹' A))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in A, g y ∂(μH[1] : Measure Sphere)) ≤
      ∫⁻z in ((↑) : ℂ → Sphere) ⁻¹' A,
        ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
          ∂(μH[1] : Measure ℂ) := by
  let : NullSingletonClass (μH[1] : Measure Sphere) :=
    Measure.nullSingletonClass_hausdorff Sphere (by norm_num)
  have hcover : A ⊆ ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A) ∪
      {OnePoint.infty} := by
    intro y hy
    cases y using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z => exact Or.inl ⟨z, hy, rfl⟩
  calc
    _ ≤ ∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A) ∪
        {OnePoint.infty}, g y ∂(μH[1] : Measure Sphere) := lintegral_mono_set hcover
    _ ≤ (∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A),
        g y ∂(μH[1] : Measure Sphere)) +
        ∫⁻y in ({OnePoint.infty} : Set Sphere), g y ∂(μH[1] : Measure Sphere) :=
      lintegral_union_le _ _ _
    _ = ∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A),
        g y ∂(μH[1] : Measure Sphere) := by simp
    _ ≤ _ := finite_sphere_chart_weighted_length_le hC hderiv hA g hg

theorem scaled_spherical_weighted_density_sq_finite
    (C : ℝ) (hC : 0 ≤ C) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z : ℂ, (ENNReal.ofReal (C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)) ^ 2) < ∞ := by
  have heq (z : ℂ) : ENNReal.ofReal (C / (1 + ‖z‖ ^ 2)) =
      ENNReal.ofReal C * ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) := by
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    ring
  simp_rw [heq, mul_assoc, mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  apply ENNReal.mul_lt_top (by finiteness)
  simpa only [mul_pow] using spherical_weighted_density_sq_finite g hg he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleAlmostEverywhere
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-everywhere assertions on the unit circle from their real
representatives. No measurability of the asserted property is required. -/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem ae_circle_of_ae_unit_interval (P : UnitAddCircle → Prop)
    (hP : ∀ᵐ(r : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1), P (r : UnitAddCircle)) :
    ∀ᵐ(t : UnitAddCircle) ∂volume, P t := by
  rw [restrict_Ico_eq_restrict_Ioc] at hP
  have hnull : volume ({r : ℝ | ¬P (r : UnitAddCircle)} ∩ Ioc 0 1) = 0 := by
    simpa only [ae_iff, Measure.restrict_apply' measurableSet_Ioc] using hP
  have hcircle := volume_addCircle_image_eq_zero hnull
  rw [ae_iff]
  apply measure_mono_null _ hcircle
  intro t ht
  let r := AddCircle.equivIoc (1 : ℝ) 0 t
  have hr : (r.val : UnitAddCircle) = t := AddCircle.coe_equivIoc
  refine ⟨r.val, ⟨?_, by simpa using r.property⟩, hr⟩
  change ¬P (r.val : UnitAddCircle)
  change ¬P t at ht
  rwa [hr]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalWeightedCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical weighted length of almost every circle-valued level,
from exactly the published scalar planar coarea input. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r60a8cf_2 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_finite_spherical_weighted_levels
    (hcoarea : WeightedPlanarScalarCoarea)
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞)
    (A : UnitAddCircle → Set Sphere)
    (hA : ∀t : UnitAddCircle, ((↑) : ℂ → Sphere) ⁻¹' A t =
      D ∩ {z | (f z : UnitAddCircle) = t})
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐt ∂volume, (∫⁻y in A t, g y ∂(μH[1] : Measure Sphere)) < ∞ := by
  let q : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
  have hq : Measurable q := by
    apply Measurable.mul
    · apply Measurable.ennreal_ofReal
      apply Continuous.measurable
      exact continuous_const.div (continuous_const.add (continuous_norm.pow 2))
        (fun z => ne_of_gt (by positivity))
    · exact hg.comp OnePoint.continuous_coe.measurable
  have hq2 : (∫⁻z in D, q z ^ 2) < ∞ :=
    (lintegral_mono_set (subset_univ D)).trans_lt (by
      simpa only [Measure.restrict_univ] using
        scaled_spherical_weighted_density_sq_finite (9 * C) (by positivity) g hg henergy)
  have hfinite := (weighted_circle_coarea_extended_finite_energy hcoarea hD hf q hq hq2 hf2).2.2
  apply ae_circle_of_ae_unit_interval
  filter_upwards [hfinite] with t ht
  have hS : MeasurableSet (((↑) : ℂ → Sphere) ⁻¹' A (t : UnitAddCircle)) := by
    rw [hA, unitAddCircle_level_inter_eq_iUnion_integer_levels]
    exact MeasurableSet.iUnion fun k => measurableSet_scalar_level hD hf.continuousOn _
  apply lt_of_le_of_lt (spherical_weighted_length_le_chart hC hderiv _ hS g hg)
  simpa only [hA, weightedCircleLevelLength, q] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoordinateCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply weighted coarea to the actual smooth physical representative
of a quotient coordinate. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r60a8cf_3 : BorelSpace Sphere := ⟨rfl⟩
theorem physicalRealCoordinate_ae_finite_weighted_levels
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → X)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (Q : PhysicalRealCoordinate d π)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐt ∂volume,
      (∫⁻y in d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
        circleBandGraph d.quotientDomain Q.quotient},
        g y ∂(μH[1] : Measure Sphere)) < ∞ := by
  let e := Complex.equivRealProdCLM
  let D := ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hDc : D = e ⁻¹' FiniteTransfer.realChartDomain d.physicalDomain := by
    ext z
    change (z : Sphere) ∈ d.physicalDomain ↔
      (e.symm (e z) : Sphere) ∈ d.physicalDomain
    rw [e.symm_apply_apply]
  have hreal : IsOpen (FiniteTransfer.realChartDomain d.physicalDomain) :=
    hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)
  have hs : ContDiffOn ℝ 1 Q.physical (FiniteTransfer.realChartDomain d.physicalDomain) :=
    Q.physical_smooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf : ContDiffOn ℝ 1 (Q.physical ∘ e) D := by
    rw [hDc]
    exact hs.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2)) < ∞ := by
    rw [hDc]
    exact complex_chart_differential_energy_finite hreal hs Q.physical_energy
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  apply ae_finite_spherical_weighted_levels hcoarea hC hderiv hD hf hf2
    (fun t => d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
      circleBandGraph d.quotientDomain Q.quotient}) _ g hg henergy
  intro t
  ext z
  have hzU (hz : (z : Sphere) ∈ d.physicalDomain) : π z ∈ d.quotientDomain := by
    rw [he ⟨z, hz⟩]
    exact (d.domainEquiv ⟨z, hz⟩).property
  constructor
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t
    rw [Q.pullback z hz]
    exact (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mp ht
  · rintro ⟨hz, ht⟩
    refine ⟨hz, (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mpr ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t at ht
    rwa [Q.pullback z hz] at ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GreedyOpenSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable selection of compatible open barriers

A basis enumeration selects one admissible candidate at each finite stage.
If removing previous candidates allows a candidate with the same or larger open set,
every candidate
admissible for the final family has its open set covered by that family.
This is the selection step only; countability of unavailable ends is separate.
-/

open Set Function

noncomputable section

namespace CircleDomainRigidity

variable {X C : Type*}

private theorem greedyStep_contains (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) (A : Set C) :
    A ⊆ greedyStep B U Allowed n A := by
  classical
  unfold greedyStep
  split
  · exact subset_insert _ _
  · exact Subset.refl _

private theorem greedyStep_finite (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) {A : Set C} (hA : A.Finite) :
    (greedyStep B U Allowed n A).Finite := by
  classical
  unfold greedyStep
  split
  · exact hA.insert _
  · exact hA

private theorem greedyStep_new_subsingleton (B : ℕ → Set X) (U : C → Set X)
    (Allowed : Set C → C → Prop) (n : ℕ) (A : Set C) :
    (greedyStep B U Allowed n A \ A).Subsingleton := by
  classical
  unfold greedyStep
  split
  · intro c hc d hd
    exact (hc.1.resolve_right hc.2).trans (hd.1.resolve_right hd.2).symm
  · intro c hc
    exact (hc.2 hc.1).elim

/-- Select a countable compatible family whose union covers every finally
admissible candidate. The stage condition retains the actual order of selection. -/
theorem exists_countable_open_selection [TopologicalSpace X] [SecondCountableTopology X]
    (U : C → Set X) (hU : ∀ c, IsOpen (U c))
    (Allowed : Set C → C → Prop)
    (hrestrict : ∀ {A D : Set C}, A ⊆ D → ∀ c, Allowed D c →
      ∃ d, Allowed A d ∧ U c ⊆ U d) :
    ∃ A : ℕ → Set C,
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → Allowed (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, Allowed (⋃ n, A n) c → U c ⊆ ⋃ d ∈ ⋃ n, A n, U d := by
  classical
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis X
  let A : ℕ → Set C := Nat.rec ∅ (fun n D => greedyStep B U Allowed n D)
  have hstep (n : ℕ) : A (n + 1) = greedyStep B U Allowed n (A n) := rfl
  have hmono : Monotone A := monotone_nat_of_le_succ fun n =>
    greedyStep_contains B U Allowed n (A n)
  have hfin (n : ℕ) : (A n).Finite := by
    induction n with
    | zero => exact finite_empty
    | succ n ih => exact greedyStep_finite B U Allowed n ih
  refine ⟨A, rfl, hfin, hmono, fun n => greedyStep_new_subsingleton B U Allowed n (A n),
    ?_, countable_iUnion fun n => (hfin n).countable, ?_⟩
  · intro n c hc
    rw [hstep] at hc
    unfold greedyStep at hc
    split at hc
    · rename_i h
      have he : c = h.choose := hc.1.resolve_right hc.2
      subst c
      exact h.choose_spec.1
    · exact (hc.2 hc.1).elim
  · intro c hc x hx
    obtain ⟨V, hV, hxV, hVU⟩ := hB.exists_subset_of_mem_open hx (hU c)
    obtain ⟨n, rfl⟩ := hV
    obtain ⟨d, hd, hcd⟩ := hrestrict (subset_iUnion A n) c hc
    have hn : ∃ d, Allowed (A n) d ∧ B n ⊆ U d := ⟨d, hd, hVU.trans hcd⟩
    have hchosen : hn.choose ∈ A (n + 1) := by
      rw [hstep]
      simp only [greedyStep, dite_eq_left hn, mem_insert_iff, true_or]
    exact mem_iUnion₂.mpr ⟨hn.choose, mem_iUnion.mpr ⟨n + 1, hchosen⟩, hn.choose_spec.2 hxV⟩
/-- The open-set selection can impose every countably indexed accuracy demand
at once, retaining compatibility across different accuracies. -/
theorem exists_countable_graded_open_selection
    [TopologicalSpace X] [SecondCountableTopology X]
    (U : C → Set X) (hU : ∀ c, IsOpen (U c)) (grade : C → ℕ)
    (Allowed : Set C → C → Prop)
    (hrestrict : ∀ {A D : Set C}, A ⊆ D → ∀ c, Allowed D c →
      ∃ d, Allowed A d ∧ grade d = grade c ∧ U c ⊆ U d) :
    ∃ A : ℕ → Set C,
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → Allowed (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, Allowed (⋃ n, A n) c → ∀ x ∈ U c,
        ∃ d ∈ ⋃ n, A n, grade d = grade c ∧ x ∈ U d := by
  let V : C → Set (ℕ × X) := fun c => {grade c} ×ˢ U c
  have hV (c : C) : IsOpen (V c) := (isOpen_discrete _).prod (hU c)
  have hres {A D : Set C} (hAD : A ⊆ D) (c : C) (hc : Allowed D c) :
      ∃ d, Allowed A d ∧ V c ⊆ V d := by
    obtain ⟨d, hd, hg, hcd⟩ := hrestrict hAD c hc
    refine ⟨d, hd, ?_⟩
    intro p hp
    exact ⟨by simpa only [V, mem_prod, mem_singleton_iff, hg] using hp.1, hcd hp.2⟩
  obtain ⟨A, h0, hfin, hmono, hsingle, hnew, hcount, hcover⟩ :=
    exists_countable_open_selection V hV Allowed hres
  refine ⟨A, h0, hfin, hmono, hsingle, hnew, hcount, ?_⟩
  intro c hc x hx
  obtain ⟨d, hd, hp⟩ := mem_iUnion₂.mp (hcover c hc (show (grade c, x) ∈ V c from ⟨rfl, hx⟩))
  exact ⟨d, hd, hp.1.symm, hp.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real tests used by the countable selection. Compatibility is
with every finite sublist of previously selected tests, retaining repetitions. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace UngatedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

theorem open_openEnds (c : UngatedRealTest d π EStar) : IsOpen c.openEnds :=
  c.region_open.preimage continuous_subtype_val

theorem CompatibleWith.mono {c : UngatedRealTest d π EStar}
    {A B : Set (UngatedRealTest d π EStar)} (h : c.CompatibleWith B) (hAB : A ⊆ B) :
    c.CompatibleWith A :=
  ⟨fun a ha => h.1 a (hAB ha), fun n q hq => h.2 n q (fun i => hAB (hq i))⟩

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem freeComponentFailure_congr_selected
    {X T I J K : Type*} [TopologicalSpace X]
    (F : Set X) (N : Set (X × T)) (R : I → Set (X × T)) (S : J → Set (X × T))
    (a : K → I) (b : K → J) (h : ∀ k, R (a k) = S (b k)) :
    freeComponentFailure F N R a = freeComponentFailure F N S b := by
  have he : finiteLevelUnionGraph R a = finiteLevelUnionGraph S b := by
    unfold finiteLevelUnionGraph
    apply iUnion_congr
    intro k
    rw [h k]
  unfold freeComponentFailure
  rw [he]

end UngatedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ShrinkingWeightedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen collar closures and all their joining levels shrink to the
actual quotient point. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_shrinking_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {W : Set Sphere} (hW : IsOpen W) (hpW : p ∈ W)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      closure (D 0).region ⊆ W ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) ∧
      (∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, closure (D n).region ⊆ V ∧
        {z | (D n).function z = (D n).level} ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' V) := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r] <;> positivity
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let O : ℕ → Set Sphere := fun n => W ∩ ball p (r n)
  obtain ⟨D, hD, hnested, hlevel, hlevelNested⟩ := exists_nested_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hTD hbad hpB hp O
    (fun _ => hW.inter isOpen_ball) (fun n => ⟨hpW, mem_ball_self (hrpos n)⟩) g hg hg2
  refine ⟨D, (hD 0).trans inter_subset_left, hnested, hlevelNested, ?_⟩
  intro V hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrzero.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro n hn
  have hsub : O n ⊆ V := inter_subset_right.trans ((ball_subset_ball (hN n hn).le).trans hball)
  exact ⟨(hD n).trans hsub, (hlevel n).trans (preimage_mono hsub)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ScalarPairNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing prescribed real scalar trace pairs to their unit-circle levels
preserves planar outer-nullity. No measurability of the trace image is needed. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem volume_scalarPairModOne_image_eq_zero {A : Set (ℝ × ℝ)}
    (hA : volume A = 0) :
    ((volume : Measure UnitAddCircle).prod volume) (scalarPairModOne '' A) = 0 := by
  have hpiece (a b : ℝ) :
      ((volume : Measure UnitAddCircle).prod volume)
        (scalarPairModOne '' (A ∩ (Ioc a (a + 1) ×ˢ Ioc b (b + 1)))) = 0 := by
    let e₁ := AddCircle.measurableEquivIoc (1 : ℝ) a
    let e₂ := AddCircle.measurableEquivIoc (1 : ℝ) b
    let e := e₁.prodCongr e₂
    let g : (Ioc a (a + 1)) × (Ioc b (b + 1)) → ℝ × ℝ :=
      Prod.map Subtype.val Subtype.val
    have he₁ : MeasurePreserving e₁ volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    have he₂ : MeasurePreserving e₂ volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    let : SFinite (volume.comap (Subtype.val : Ioc a (a + 1) → ℝ)) := he₁.sfinite
    let : SFinite (volume.comap (Subtype.val : Ioc b (b + 1) → ℝ)) := he₂.sfinite
    have he : MeasurePreserving e (volume.prod volume)
        ((volume.comap (Subtype.val : Ioc a (a + 1) → ℝ)).prod
          (volume.comap (Subtype.val : Ioc b (b + 1) → ℝ))) := he₁.prod he₂
    have hg₁ : MeasurePreserving (Subtype.val : Ioc a (a + 1) → ℝ)
        (volume.comap Subtype.val) (volume.restrict (Ioc a (a + 1))) :=
      ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Ioc volume⟩
    have hg₂ : MeasurePreserving (Subtype.val : Ioc b (b + 1) → ℝ)
        (volume.comap Subtype.val) (volume.restrict (Ioc b (b + 1))) :=
      ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Ioc volume⟩
    have hg : MeasurePreserving g
        ((volume.comap (Subtype.val : Ioc a (a + 1) → ℝ)).prod
          (volume.comap (Subtype.val : Ioc b (b + 1) → ℝ)))
        ((volume.restrict (Ioc a (a + 1))).prod (volume.restrict (Ioc b (b + 1)))) :=
      hg₁.prod hg₂
    have hnull : ((volume.restrict (Ioc a (a + 1))).prod
        (volume.restrict (Ioc b (b + 1)))) A = 0 := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact le_antisymm (hA ▸ Measure.restrict_apply_le _ _) bot_le
    have hset : (g ∘ e) ⁻¹' A =
        scalarPairModOne '' (A ∩ (Ioc a (a + 1) ×ˢ Ioc b (b + 1))) := by
      ext y
      constructor
      · intro hy
        refine ⟨g (e y), ⟨hy, (e₁ y.1).property, (e₂ y.2).property⟩, ?_⟩
        exact Prod.ext AddCircle.coe_equivIoc AddCircle.coe_equivIoc
      · rintro ⟨x, ⟨hx, hx₁, hx₂⟩, rfl⟩
        change ((AddCircle.equivIoc (1 : ℝ) a (x.1 : UnitAddCircle)).val,
          (AddCircle.equivIoc (1 : ℝ) b (x.2 : UnitAddCircle)).val) ∈ A
        rw [AddCircle.equivIoc_coe_eq hx₁, AddCircle.equivIoc_coe_eq hx₂]
        exact hx
    rw [← hset]
    exact (hg.comp he).preimage_null hnull
  have hcover : scalarPairModOne '' A ⊆ ⋃ k : ℤ × ℤ,
      scalarPairModOne '' (A ∩
        (Ioc ((k.1 : ℝ) - 1) ((k.1 : ℝ) - 1 + 1) ×ˢ
          Ioc ((k.2 : ℝ) - 1) ((k.2 : ℝ) - 1 + 1))) := by
    rintro y ⟨x, hx, rfl⟩
    refine mem_iUnion.mpr ⟨(⌈x.1⌉, ⌈x.2⌉), x, ⟨hx, ?_, ?_⟩, rfl⟩
    · constructor <;> linarith [Int.ceil_lt_add_one x.1, Int.le_ceil x.1]
    · constructor <;> linarith [Int.ceil_lt_add_one x.2, Int.le_ceil x.2]
  exact measure_mono_null hcover (measure_iUnion_null fun k => hpiece _ _)

 theorem scalar_trace_pair_null_mod_one {X : Type*} (B : Set X) (u v : X → ℝ)
    (h : volume ((fun x => (u x, v x)) '' B) = 0) :
    ((volume : Measure UnitAddCircle).prod volume)
      ((fun x => ((u x : UnitAddCircle), (v x : UnitAddCircle))) '' B) = 0 := by
  simpa only [image_image, comp_def, scalarPairModOne] using
    volume_scalarPairModOne_image_eq_zero h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SamplingTraceContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking sampling sets preserve the exact continuous boundary trace
of a partition smoothing. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem boundaryPaste_continuous
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : ContinuousOn v Ω)
    (hsmall : ∀ x ∈ Ω, ∀ j, ρ.weight j x ≠ 0 → ∀ y ∈ W j,
      dist y x ≤ infDist x (Ω : Set EuclideanPlane)ᶜ)
    (hband : ∀ x ∈ Ω, ∀ a b : ℝ,
      (∀ j, ρ.weight j x ≠ 0 → ∀ y ∈ W j, u y ∈ Icc a b) → v x ∈ Icc a b) :
    Continuous (boundaryPaste Ω u v) := by
  classical
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ (Ω : Set EuclideanPlane)
  · apply (hv.continuousAt (Ω.isOpen.mem_nhds hp)).congr
    filter_upwards [Ω.isOpen.mem_nhds hp] with x hx
    simp only [boundaryPaste, ite_eq_left hx]
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, huc⟩ := Metric.continuousAt_iff.mp (hu.continuousAt (x := p))
      (ε / 2) (by linarith)
    refine ⟨δ / 2, by linarith, ?_⟩
    intro x hx
    simp only [boundaryPaste, ite_eq_right hp]
    by_cases hxΩ : x ∈ (Ω : Set EuclideanPlane)
    · rw [ite_eq_left hxΩ]
      have hrange : v x ∈ Icc (u p - ε / 2) (u p + ε / 2) := by
        apply hband x hxΩ
        intro j hj y hy
        have hxy := hsmall x hxΩ j hj y hy
        have hdist : dist y p < δ := by
          have hi : infDist x (Ω : Set EuclideanPlane)ᶜ ≤ dist x p := infDist_le_dist_of_mem hp
          calc
            dist y p ≤ dist y x + dist x p := dist_triangle _ _ _
            _ ≤ 2 * dist x p := by linarith
            _ < δ := by linarith
        have he : |u y - u p| < ε / 2 := by
          simpa only [Real.dist_eq] using huc hdist
        have hh := abs_lt.mp he
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [Real.dist_eq]
      have ha : |v x - u p| ≤ ε / 2 := abs_le.mpr
        ⟨by linarith [hrange.1], by linarith [hrange.2]⟩
      linarith
    · rw [ite_eq_right hxΩ]
      exact (huc (by linarith : dist x p < δ)).trans (by linarith)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RefinedShrinkingRectanglePartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shrinking rectangle construction can respect specified open sampling neighborhoods. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem exists_small_shrinking_partition_refining_neighborhoods
    {X : Type*} [MetricSpace X] (Ω : TopologicalSpace.Opens EuclideanPlane)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty) (hqB : ∀x ∈ Ω, q x ∉ B)
    (N : Ω → Set EuclideanPlane) (hN : ∀x, IsOpen (N x)) (hxN : ∀x : Ω, x.val ∈ N x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (center : ι → Ω)
      (a b c d : ι → ℝ),
      (∀j, a j < b j ∧ c j < d j) ∧
      (∀j, euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) ⊆ Ω ∩ N (center j)) ∧
      (∀j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (q y) (q x) ≤ Metric.infDist (q x) B) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (⟨x 0, x 1⟩ : ℂ) (⟨y 0, y 1⟩ : ℂ) ≤ 1) := by
  choose a b c d hab hcd hpoint hrect hpair hdiam using
    fun x : Ω => exists_small_closed_coordinate_rectangle_with_diameter
      (Ω.isOpen.inter (hN x)) q (hq.mono inter_subset_left) B hB hne
      (show x.val ∈ (Ω : Set EuclideanPlane) ∩ N x from ⟨x.property, hxN x⟩)
      (hqB x x.property)
  let U : Ω → Set Ω := fun x => (fun y : Ω => euclideanPlaneCoordinates y) ⁻¹'
    (Ioo (a x) (b x) ×ˢ Ioo (c x) (d x))
  have hU (x : Ω) : U x ∈ 𝓝 x := by
    apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.prod isOpen_Ioo).preimage
        (euclideanPlaneCoordinates.continuous.comp continuous_subtype_val)
    · exact hpoint x
  obtain ⟨ι, hι, ρ, center, hsub⟩ := exists_openPlanePartition Ω U hU
  refine ⟨ι, hι, ρ, center, a ∘ center, b ∘ center, c ∘ center, d ∘ center,
    fun j => ⟨hab (center j), hcd (center j)⟩, fun j => hrect (center j), ?_, ?_, ?_⟩
  · intro j x hx
    obtain ⟨y, hy, rfl⟩ := hsub j hx
    exact hy
  · intro j x hx y hy
    exact hpair (center j) y hy x hx

  · intro j x hx y hy
    exact hdiam (center j) x hx y hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExactTraceSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth the original continuous Sobolev test on its open domain while
retaining every boundary value exactly. The derivative error can be prescribed. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_exact_trace_smoothing
    (Ω : TopologicalSpace.Opens EuclideanPlane) (hne : (Ω : Set EuclideanPlane)ᶜ.Nonempty)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (hunit : ∀ x, u x ∈ Icc 0 1) (hw : DeGiorgi.MemW1pWitness 2 u Ω)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ v : EuclideanPlane → ℝ, Continuous v ∧ HasCompactSupport v ∧
      ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ (∀ x, v x ∈ Icc 0 1) ∧
      EqOn v u (Ω : Set EuclideanPlane)ᶜ ∧
      ∀ i : Fin 2, MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) 2
        (volume.restrict Ω) ∧
        eLpNorm (fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Ω) < ε := by
  classical
  let N : Ω → Set EuclideanPlane := fun x => ball x.val (1 / 2)
  obtain ⟨ι, hι, ρ, center, a, b, c, d, _, hrect, hsub, hsmall, _⟩ :=
    exists_small_shrinking_partition_refining_neighborhoods Ω id continuousOn_id
      (Ω : Set EuclideanPlane)ᶜ Ω.isOpen.isClosed_compl hne
      (fun x hx hn => hn hx) N (fun _ => isOpen_ball) (fun x => mem_ball_self (by norm_num))
  let : Countable ι := hι
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))
  have hW (j : ι) : IsOpen (W j) :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
  have hclosed (j : ι) : W j ⊆
      euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) := by
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩
  have hWU (j : ι) : W j ⊆ Ω := fun _ hx => (hrect j (hclosed j hx)).1
  let H (j : ι) := hw.restrict (hW j) (hWU j)
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  obtain ⟨w, hws, hwu, hband, herr⟩ := exists_positive_partition_smoothing
    ρ W hW hsub u H (fun _ x _ => hunit x) δ hδ
  let v := boundaryPaste Ω u w
  have hvc : Continuous v := boundaryPaste_continuous ρ W hu hws.continuousOn
    (by
      intro x hx j hj y hy
      exact hsmall j x (hclosed j (hsub j (subset_tsupport _ hj))) y (hclosed j hy)) hband
  have hvon : EqOn v w Ω := by
    intro x hx
    simp only [v, boundaryPaste, ite_eq_left hx]
  have hvoff : EqOn v u (Ω : Set EuclideanPlane)ᶜ := by
    intro x hx
    simp only [v, boundaryPaste, ite_eq_right hx]
  have hvd : ContDiffOn ℝ (⊤ : ℕ∞) v Ω := hws.congr hvon
  have hvgrad (x : EuclideanPlane) (hx : x ∈ Ω) : fderiv ℝ v x = fderiv ℝ w x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact hvon hy
  have hvs : HasCompactSupport v := by
    apply HasCompactSupport.intro' (K := cthickening 1 (tsupport u)) (hs.isCompact.cthickening)
      isClosed_cthickening
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hvon hxΩ]
      have hrange : w x ∈ Icc 0 0 := by
        apply hband x hxΩ
        intro j hj y hy
        have hxj := hclosed j (hsub j (subset_tsupport _ hj))
        have hyj := hclosed j hy
        have hxy : dist x y ≤ 1 := by
          have hxC : dist x (center j).val < 1 / 2 := (hrect j hxj).2
          have hyC : dist y (center j).val < 1 / 2 := (hrect j hyj).2
          calc
            dist x y ≤ dist x (center j).val + dist (center j).val y := dist_triangle _ _ _
            _ ≤ 1 := by rw [dist_comm (center j).val y]; linarith
        have huy : u y = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hyu
          exact hx (mem_cthickening_of_dist_le x y 1 (tsupport u) hyu hxy)
        simp only [huy, mem_Icc, le_refl, and_self]
      exact le_antisymm hrange.2 hrange.1
    · rw [hvoff hxΩ]
      apply image_eq_zero_of_notMem_tsupport
      intro hxu
      exact hx (self_subset_cthickening (δ := 1) (tsupport u) hxu)
  refine ⟨v, hvc, hvs, hvd, ?_, hvoff, ?_⟩
  · intro x
    by_cases hx : x ∈ Ω
    · rw [hvon hx]
      exact hwu x hx
    · rw [hvoff hx]
      exact hunit x
  · intro i
    have hsumG (x : EuclideanPlane) (hx : x ∈ Ω) :
        (∑ᶠ j, ρ.weight j x * (H j).weakGrad x i) = hw.weakGrad x i := by
      change (∑ᶠ j, ρ.weight j x * hw.weakGrad x i) = _
      rw [← finsum_mul, ρ.sum_one ⟨x, hx⟩, one_mul]
    have he : eLpNorm (fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i)
        2 (volume.restrict Ω) < ε := by
      apply lt_of_le_of_lt _ hsum
      convert herr i using 1
      all_goals try with_reducible_and_instances rfl
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [hvgrad x hx, hsumG x hx]
    have hE : MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i)
        2 (volume.restrict Ω) :=
      ⟨(measurable_fderiv_apply_const ℝ v _).aestronglyMeasurable.sub
        (hw.weakGrad_component_memLp i).aestronglyMeasurable, he.trans_le le_top⟩
    have hL := hE.add (hw.weakGrad_component_memLp i)
    refine ⟨?_, he⟩
    convert hL using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact (sub_add_cancel _ _).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExactTraceSobolevError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact-trace smoothing has a global Sobolev difference. Thus changing
a test to its smooth representative preserves its original boundary trace
and changes its global gradient by an arbitrarily small amount. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem zeroTraceWitness_component_eLpNorm
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    eLpNorm (fun x => (zeroTraceWitness hU hu hs hz hw).weakGrad x i) 2 volume =
      eLpNorm (fun x => hw.weakGrad x i) 2 (volume.restrict U) := by
  have he : (fun x => (zeroTraceWitness hU hu hs hz hw).weakGrad x i) =ᵐ[volume]
      U.indicator (fun x => hw.weakGrad x i) := by
    have hl := zeroTraceWitness_gradient_on hU hu hs hz hw i
    change ∀ᵐ x ∂volume.restrict U, (zeroTraceWitness hU hu hs hz hw).weakGrad x i = hw.weakGrad x i at hl
    have hl' := (ae_restrict_iff' hU.measurableSet).mp hl
    filter_upwards [hl'] with x hx
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
      exact hx hxU
    · rw [indicator_of_notMem hxU]
      exact zeroTraceWitness_zero hU hu hs hz hw i hxU
  rw [eLpNorm_congr_ae he, eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrescribedPlaneCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a point-complement source the physical representative retains the
entire prescribed continuous sphere function, including every dust value.
The zero extension used for its derivatives does not change those values. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_prescribed_plane_coordinate
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = x.val)
    (v : EuclideanPlane → ℝ) (hv : Continuous v) (hs : HasCompactSupport v)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) v (physicalPlaneDomain d.physicalDomain))
    (hunit : ∀ x, v x ∈ Icc 0 1)
    (hgrad : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain d.physicalDomain))) :
    ∃ Q : PhysicalRealCoordinate d id,
      Q.quotient = sphereFromPlaneFunction v ∧ Continuous Q.quotient ∧
      ∀ i : Fin 2, eLpNorm (fun p => fderiv ℝ Q.physical p
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) := by
  obtain ⟨w, hm, hws, hwe, hn, hp⟩ :=
    exists_real_physical_representative d hG id he v hsm hgrad
  have hvc : Continuous (sphereFromPlaneFunction v) := by
    apply continuousOn_univ.mp
    exact sphereFromPlaneFunction_continuousOn isOpen_univ hv.continuousOn hs.isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  let Q : PhysicalRealCoordinate d id := {
    quotient := sphereFromPlaneFunction v
    quotient_continuous := hvc.continuousOn
    quotient_unit := fun p => sphereFromPlaneFunction_mem_Icc (G := univ)
      (fun x _ => hunit x) p (mem_univ p)
    physical := w
    physical_measurable := hm
    physical_smooth := hws
    physical_energy := hwe
    pullback := by
      intro z hz
      refine (hp z hz).trans ?_
      change quotientPlaneRepresentative d v (z : Sphere) = sphereFromPlaneFunction v z
      exact (congrArg (quotientPlaneRepresentative d v) (he ⟨(z : Sphere), hz⟩).symm).trans
        (quotientPlaneRepresentative_on_domain d v (z : Sphere) hz) }
  exact ⟨Q, rfl, hvc, hn⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExactTraceTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth replacements of the original scalar tests. Their full
boundary traces, continuous representatives and global Sobolev errors
are retained together for the circle-model construction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_exact_trace_test
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = x.val)
    (hne : (physicalPlaneDomain d.physicalDomain)ᶜ.Nonempty)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (hunit : ∀ x, u x ∈ Icc 0 1)
    (H : DeGiorgi.MemW1pWitness 2 u (physicalPlaneDomain d.physicalDomain))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ExactTraceTest d u, ∀ i : Fin 2,
      eLpNorm (fun x => T.error.weakGrad x i) 2 volume < ε := by
  let Ω : TopologicalSpace.Opens EuclideanPlane :=
    ⟨physicalPlaneDomain d.physicalDomain, isOpen_physicalPlaneDomain hG⟩
  obtain ⟨v, hvc, hvs, hvsm, hvunit, hvtrace, hvgrad⟩ :=
    exists_exact_trace_smoothing Ω hne hu hs hunit H hε
  let V := smoothPlaneSobolevWitness Ω.isOpen (hvsm.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hvc.memLp_of_hasCompactSupport hvs).restrict Ω) (fun i => (hvgrad i).1)
  let D := H.sub V
  have hz : ∀ x ∉ (Ω : Set EuclideanPlane), u x - v x = 0 := by
    intro x hx
    rw [hvtrace hx, sub_self]
  let K := zeroTraceWitness Ω.isOpen (hu.sub hvc) (hs.sub hvs) hz D
  obtain ⟨Q, hQ, hQc, _⟩ := exists_prescribed_plane_coordinate d hG he v hvc hvs hvsm hvunit
    (fun i => (hvgrad i).1)
  refine ⟨⟨v, hvc, hvs, hvsm, hvunit, (fun i => (hvgrad i).1), hvtrace, Q, hQ, hQc, K⟩, ?_⟩
  intro i
  change eLpNorm (fun x => K.weakGrad x i) 2 volume < ε
  rw [zeroTraceWitness_component_eLpNorm]
  have hd : (fun x => D.weakGrad x i) =
      -(fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - H.weakGrad x i) := by
    funext x
    change H.weakGrad x i + (-1) * fderiv ℝ v x (EuclideanSpace.single i 1) = _
    simp only [Pi.neg_apply]
    ring
  rw [hd, eLpNorm_neg]
  exact (hvgrad i).2

namespace ExactTraceTest
variable {d : PathCodeData Sphere Sphere} {u : EuclideanPlane → ℝ}
  (T : ExactTraceTest d u)

 theorem trace_on_sphere {p : Sphere} (hp : p ∈ d.physicalDomainᶜ) :
    T.coordinate.quotient p = sphereFromPlaneFunction u p := by
  change p ∉ d.physicalDomain at hp
  rw [T.coordinate_eq]
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    simp only [sphereFromPlaneFunction_coe]
    apply T.trace
    change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∉ d.physicalDomain
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp

end ExactTraceTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanFillLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upper containment for limits of Jordan fills

Uniform convergence of boundary parametrizations traps the approximating
closed fills in every neighborhood of the limiting closed fill. The proof
uses Jordan nesting and radial enlargement.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_jordan_fill_subset_open
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∀ᶠ n in atTop, closure (jordanInterior (J n)) ⊆ O := by
  obtain ⟨r, hr, hrO, _⟩ := exists_disjoint_jordan_enlargements
    (fun _ : Unit => H) (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fun _ => O) (fun _ => hO) (fun _ => hHO)
  let K := dilatedJordan H (r Unit.unit) (by linarith [hr Unit.unit])
  have hK : jordanInterior K = H '' ball (0 : ℂ) (r Unit.unit) :=
    jordanInterior_dilated H _
  have hγK : range γ ⊆ jordanInterior K := by
    rw [hfront, frontier_jordanInterior, hK]
    apply image_mono
    intro z hz
    simpa only [mem_ball, mem_sphere, dist_zero_right] using
      (show ‖z‖ < r Unit.unit by
        have hz' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
        linarith [hr Unit.unit])
  obtain ⟨δ, hδ, hδK⟩ := (isCompact_range hγ).exists_thickening_subset_open
    (jordanInterior_isOpen K) hγK
  have hclose := Metric.tendstoUniformly_iff.mp hlim δ hδ
  filter_upwards [hclose, hfrontn] with n hn hnfront
  apply (closed_jordanInterior_subset_of_frontier_subset (J n) K ?_).trans
    (show jordanInterior K ⊆ O by
      rw [hK]
      exact (image_mono ball_subset_closedBall).trans (hrO Unit.unit))
  rw [← hnfront]
  rintro _ ⟨t, rfl⟩
  apply hδK
  apply mem_thickening_iff.mpr
  exact ⟨γ t, mem_range_self t, by simpa only [dist_comm] using hn t⟩

theorem mem_jordan_fill_of_tendsto
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {z : ℂ} {zn : ℕ → ℂ} (hz : Tendsto zn atTop (𝓝 z))
    (hzn : ∀ᶠ n in atTop, zn n ∈ closure (jordanInterior (J n))) :
    z ∈ closure (jordanInterior H) := by
  by_contra hnot
  have hnorm : 1 < ‖H.symm z‖ := by
    have hn : H.symm z ∉ closedBall (0 : ℂ) 1 := by
      intro h
      apply hnot
      rw [closure_jordanInterior]
      exact ⟨H.symm z, h, H.apply_symm_apply z⟩
    simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  obtain ⟨r, hr, hrz⟩ := exists_between hnorm
  let K := dilatedJordan H r (by linarith)
  have hK : jordanInterior K = H '' ball (0 : ℂ) r := jordanInterior_dilated H _
  have hHK : closure (jordanInterior H) ⊆ jordanInterior K := by
    rw [closure_jordanInterior, hK]
    exact image_mono (closedBall_subset_ball hr)
  have hevent := eventually_jordan_fill_subset_open H J γ γn hγ hfront hfrontn hlim
    (jordanInterior_isOpen K) hHK
  have hzK : z ∈ closure (jordanInterior K) :=
    isClosed_closure.mem_of_tendsto hz (by
      filter_upwards [hevent, hzn] with n hn hnz
      exact subset_closure (hn hnz))
  rw [hK, ← H.image_closure, closure_ball 0 (by linarith : r ≠ 0)] at hzK
  obtain ⟨w, hw, hwz⟩ := hzK
  have hw' : w = H.symm z := H.injective (hwz.trans (H.apply_symm_apply z).symm)
  have hwle : ‖H.symm z‖ ≤ r := by simpa only [hw', mem_closedBall, dist_zero_right] using hw
  exact (not_le_of_gt hrz) hwle

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected retained-core exhaustions

Compact exhaustion and paths in an open plane domain give nested connected
open cores with compact closure in that domain. Adjoining one fixed exterior
then gives the cofinite cores required by normalized model compactness.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {z₀ : ℂ} (hz₀ : z₀ ∈ G) :
    ∃ U : ℕ → Set ℂ,
      (∀ n, IsOpen (U n)) ∧ (∀ n, IsConnected (U n)) ∧ Monotone U ∧
      (∀ n, IsCompact (closure (U n)) ∧ closure (U n) ⊆ G) ∧
      (⋃ n, U n) = G ∧ z₀ ∈ U 0 := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let : LocallyPathConnectedSpace G := hG.locallyPathConnectedSpace
  let C := CompactExhaustion.choice G
  let x₀ : G := ⟨z₀, hz₀⟩
  obtain ⟨k₀, hk₀⟩ := C.exists_mem x₀
  let A : ℕ → Set G := fun n => connectedComponentIn (interior (C (n + k₀ + 1))) x₀
  have hxA (n : ℕ) : x₀ ∈ A n := by
    apply mem_connectedComponentIn
    apply C.subset_interior (by omega : k₀ < n + k₀ + 1)
    exact hk₀
  have hAo (n : ℕ) : IsOpen (A n) := isOpen_interior.connectedComponentIn
  have hAc (n : ℕ) : IsConnected (A n) :=
    ⟨⟨x₀, hxA n⟩, isPreconnected_connectedComponentIn⟩
  have hAm : Monotone A := by
    intro m n hmn
    exact connectedComponentIn_mono _ (interior_mono (C.subset (by omega)))
  let U : ℕ → Set ℂ := fun n => Subtype.val '' A n
  have hUclosed (n : ℕ) : closure (U n) ⊆ Subtype.val '' C (n + k₀ + 1) := by
    apply closure_minimal _ ((C.isCompact _).image continuous_subtype_val).isClosed
    exact image_mono ((connectedComponentIn_subset _ _).trans interior_subset)
  refine ⟨U, fun n => hG.isOpenMap_subtype_val _ (hAo n),
    fun n => (hAc n).image _ continuous_subtype_val.continuousOn,
    fun m n hmn => image_mono (hAm hmn), ?_, ?_, ⟨x₀, hxA 0, rfl⟩⟩
  · intro n
    exact ⟨((C.isCompact _).image continuous_subtype_val).of_isClosed_subset
      isClosed_closure (hUclosed n), (hUclosed n).trans (by rintro _ ⟨x, _, rfl⟩; exact x.property)⟩
  · apply Subset.antisymm
    · exact iUnion_subset fun n => by rintro _ ⟨x, _, rfl⟩; exact x.property
    · intro z hz
      let x : G := ⟨z, hz⟩
      have hj : Joined x₀ x := (hG.isConnected_iff_isPathConnected.mp hconn).joinedIn
        z₀ hz₀ z hz |>.joined_subtype
      let γ := hj.somePath
      obtain ⟨k, hk⟩ := C.exists_superset_of_isCompact (isCompact_range γ.continuous)
      have hrange : range γ ⊆ interior (C (k + k₀ + 1)) :=
        hk.trans (C.subset_interior (by omega : k < k + k₀ + 1))
      have hx : x ∈ A k :=
        (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
          (by exact ⟨0, γ.source⟩) hrange (by exact ⟨1, γ.target⟩)
      exact mem_iUnion.mpr ⟨k, x, hx, rfl⟩

/-- The cofinite cores retain a full fixed exterior, while the closure
of every core stays in the original domain. -/
theorem exists_cofinite_connected_plane_exhaustion
    {G : Set ℂ} (hG : IsOpen G) (hconn : IsConnected G)
    {R : ℝ} (hR : 0 < R) (hext : {z : ℂ | R ≤ ‖z‖} ⊆ G) :
    ∃ D : ℕ → Set ℂ,
      (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, closure (D n) ⊆ G) ∧ (⋃ n, D n) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 := by
  let z₀ : ℂ := (2 * R : ℝ)
  have hnorm : ‖z₀‖ = 2 * R := by
    simp only [z₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
  have hz₀ : z₀ ∈ G := hext (by change R ≤ ‖z₀‖; rw [hnorm]; linarith)
  obtain ⟨U, hUo, hUc, hUm, hUcl, hUunion, hbase⟩ :=
    exists_connected_plane_exhaustion hG hconn hz₀
  let E : Set ℂ := (closedBall (0 : ℂ) R)ᶜ
  have hEo : IsOpen E := isClosed_closedBall.isOpen_compl
  have hEc : IsConnected E := isConnected_complex_exterior_closedBall hR.le
  have hzE : z₀ ∈ E := by
    simpa only [E, mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hnorm] using
      (by linarith : R < 2 * R)
  have hEcl : closure E ⊆ G := by
    rw [closure_compl, interior_closedBall (0 : ℂ) hR.ne']
    intro z hz
    apply hext
    change R ≤ ‖z‖
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz
  refine ⟨fun n => U n ∪ E, fun n => (hUo n).union hEo,
    fun n => (hUc n).union ⟨z₀, hUm (Nat.zero_le n) hbase, hzE⟩ hEc,
    fun m n hmn => union_subset_union_left E (hUm hmn), ?_, ?_, ?_⟩
  · intro n
    rw [closure_union]
    exact union_subset (hUcl n).2 hEcl
  · ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨n, hz | hz⟩
      · exact (hUcl n).2 (subset_closure hz)
      · exact hEcl (subset_closure hz)
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hUunion.symm ▸ hz)
      exact ⟨n, Or.inl hn⟩
  · intro z hz
    right
    have hz' : 2 * R ≤ ‖z‖ := hz
    change z ∉ closedBall (0 : ℂ) R
    rw [mem_closedBall, dist_zero_right, not_le]
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereCoreExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual source cores for domains containing infinity

The open connected cores exhaust the given domain. Their finite closures,
with infinity added, are compact subsets of the domain and can therefore
be prescribed in the finite-transfer construction.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isClosed_finite_set_with_infty {C : Set ℂ} (hC : IsClosed C) :
    IsClosed (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty}) := by
  have he : (((↑) : ℂ → Sphere) '' C ∪ {OnePoint.infty})ᶜ =
      ((↑) : ℂ → Sphere) '' Cᶜ := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp
    | coe z => simp only [mem_compl_iff, mem_union, OnePoint.coe_injective.mem_set_image,
        mem_singleton_iff, OnePoint.coe_ne_infty, or_false]
  rw [← isOpen_compl_iff, he]
  exact OnePoint.isOpen_image_coe.mpr hC.isOpen_compl

theorem exists_sphere_connected_core_exhaustion
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ (R : ℝ) (D : ℕ → Set ℂ) (K : ℕ → Set Sphere),
      0 < R ∧ (∀ n, IsOpen (D n)) ∧ (∀ n, IsConnected (D n)) ∧ Monotone D ∧
      (∀ n, K n = ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}) ∧
      (∀ n, IsCompact (K n) ∧ K n ⊆ G) ∧
      (∀ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ interior (K n)) ∧
      (⋃ n, ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}) = G ∧
      {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0 ∧
      ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ G := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hA : IsOpen A := hG.preimage OnePoint.continuous_coe
  have hAc : IsCompact Aᶜ := ((OnePoint.isOpen_iff_of_mem hinf).mp hG).2
  obtain ⟨R, hR, hbound⟩ := hAc.isBounded.exists_pos_norm_lt
  have hext : {z : ℂ | R ≤ ‖z‖} ⊆ A := by
    intro z hz
    by_contra hzA
    exact (not_lt_of_ge hz) (hbound z hzA)
  have hAn : A.Nonempty := by
    refine ⟨(R : ℂ), hext ?_⟩
    change R ≤ ‖(R : ℂ)‖
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, le_refl]
  have hconnA : IsConnected A := ⟨hAn,
    (finite_part_connected_unbounded hconn.isPreconnected (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1⟩
  obtain ⟨D, hDo, hDc, hDm, hDcl, hDunion, hDexterior⟩ :=
    exists_cofinite_connected_plane_exhaustion hA hconnA hR hext
  let K : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' closure (D n) ∪ {OnePoint.infty}
  have hDG (n : ℕ) : ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ G := by
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n (subset_closure hz)
    · exact mem_singleton_iff.mp hp ▸ hinf
  have hDE (n : ℕ) : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D n :=
    hDexterior.trans (hDm (Nat.zero_le n))
  refine ⟨R, D, K, hR, hDo, hDc, hDm, fun _ => rfl, ?_, ?_, ?_, hDexterior, ?_⟩
  · intro n
    refine ⟨(isClosed_finite_set_with_infty isClosed_closure).isCompact, ?_⟩
    rintro p (⟨z, hz, rfl⟩ | hp)
    · exact hDcl n hz
    · exact mem_singleton_iff.mp hp ▸ hinf
  · intro n
    apply interior_maximal ?_ (isOpen_finite_domain_with_infty (hDo n) (hDE n))
    exact union_subset_union_left _ (image_mono subset_closure)
  · apply Subset.antisymm (iUnion_subset hDG)
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact mem_iUnion.mpr ⟨0, Or.inr rfl⟩
    | coe z =>
      have hz : z ∈ A := hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hDunion.symm ▸ hz)
      exact mem_iUnion.mpr ⟨n, Or.inl ⟨z, hn, rfl⟩⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply hext
      change R ≤ ‖z‖
      simpa only [OnePoint.coe_injective.mem_set_image, mem_compl_iff, mem_ball,
        dist_zero_right, not_lt] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedCoreNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact connected neighborhoods inside the source

A compact subset of a domain containing infinity lies strictly inside a
compact connected subset of that domain which also contains a neighborhood
of infinity. This lets successive finite Jordan cores retain earlier ones.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem closure_finite_domain_with_infty (D : Set ℂ) :
    closure (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) =
      ((↑) : ℂ → Sphere) '' closure D ∪ {OnePoint.infty} := by
  apply Subset.antisymm
  · exact closure_minimal (union_subset_union_left _ (image_mono subset_closure))
      (isClosed_finite_set_with_infty isClosed_closure)
  · apply union_subset
    · exact (image_closure_subset_closure_image OnePoint.continuous_coe).trans
        (closure_mono subset_union_left)
    · exact subset_union_right.trans subset_closure

theorem isConnected_finite_domain_with_infty
    {D : Set ℂ} (hD : IsConnected D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConnected (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hunbounded : ¬ Bornology.IsBounded D := by
    intro h
    have hc := (isBounded_closedBall (x := (0 : ℂ)) (r := R)).union h
    apply NormedSpace.unbounded_univ ℝ ℂ
    apply hc.subset
    intro z _
    by_cases hz : ‖z‖ ≤ R
    · exact Or.inl (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    · exact Or.inr (hext (le_of_lt (lt_of_not_ge hz)))
  have hinf := infty_mem_closure_image_of_unbounded hunbounded
  apply (hD.image _ OnePoint.continuous_coe.continuousOn).subset_closure subset_union_left
  exact union_subset subset_closure (singleton_subset_iff.mpr hinf)

theorem exists_compact_connected_core_neighborhood
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ P : Set Sphere, IsCompact P ∧ IsConnected P ∧ P ⊆ G ∧
      S ⊆ interior P ∧ OnePoint.infty ∈ interior P := by
  obtain ⟨R, D, K, hR, hDo, hDc, hDm, hKdef, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  let U : ℕ → Set Sphere := fun n => ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty}
  have hUo (n : ℕ) : IsOpen (U n) :=
    isOpen_finite_domain_with_infty (hDo n) (hext.trans (hDm (Nat.zero_le n)))
  have hUm : Monotone U := fun _ _ h => union_subset_union_left _ (image_mono (hDm h))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover U hUo
    (fun p hp => hcover.symm ▸ hSG hp) hUm.directed_le
  refine ⟨K n, (hK n).1, ?_, (hK n).2, hn.trans (hDK n), hDK n (Or.inr rfl)⟩
  rw [hKdef n, ← closure_finite_domain_with_infty]
  exact (isConnected_finite_domain_with_infty (hDc n)
    (hext.trans (hDm (Nat.zero_le n)))).closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem interior_finite_disjoint_closed
    {I : Type*} [Finite I] (C : I → Set Sphere)
    (hC : ∀ i, IsClosed (C i)) (hd : Pairwise (Disjoint on C)) :
    interior (⋃ i, C i) = ⋃ i, interior (C i) := by
  classical
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hp)
    let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
    have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hC j
    have hpB : p ∉ B := by
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hd j.property.symm) hi hj
    have hsub : interior (⋃ j, C j) ∩ Bᶜ ⊆ C i := by
      rintro q ⟨hq, hqB⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hq)
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hqB (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    exact mem_iUnion.mpr ⟨i, interior_maximal hsub (isOpen_interior.inter hB.isOpen_compl) ⟨hp, hpB⟩⟩
  · exact iUnion_subset fun i => interior_mono (subset_iUnion C i)

theorem closure_interior_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    closure (interior (closedJordanCore H)) = closedJordanCore H := by
  rw [interior_closedJordanCore, openCompletedRegion, closure_compl,
    interior_finite_disjoint_closed (fun i => closedTerminalCap (H i))
      (fun i => (isCompact_closedTerminalCap (H i)).isClosed) (disjoint_closedTerminalCaps H hd)]
  simp only [interior_closedTerminalCap, closedJordanCore]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PrescribedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite smooth Jordan core retaining a prescribed connected set

Sard, compact one-manifold classification and Schoenflies produce disjoint
smooth filled contours around the complement. Their common exterior stays
in the original domain and retains the prescribed compact set in its interior.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_prescribed_jordan_core
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G P : Set Sphere} (hG : IsOpen G) (hP : IsCompact P) (hPG : P ⊆ G)
    (hconn : IsPreconnected P) (hinf : OnePoint.infty ∈ interior P) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ),
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      closedJordanCore H ⊆ G ∧ P ⊆ interior (closedJordanCore H) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i)) := by
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Gᶜ
  let V : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Pᶜ
  have hinfG : OnePoint.infty ∈ G := hPG (interior_subset hinf)
  have hAc : IsCompact A := isCompact_finite_preimage hG.isClosed_compl
    (by simpa only [mem_compl_iff, not_not] using hinfG)
  have hVo : IsOpen V := hP.isClosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hAV : A ⊆ V := preimage_mono (compl_subset_compl.mpr hPG)
  have hVc : IsPreconnected Vᶜ ∧ ¬ Bornology.IsBounded Vᶜ := by
    simpa only [V, ← preimage_compl, compl_compl] using
      finite_part_connected_unbounded hconn hinf
  obtain ⟨f, t, γ₀, H₀, s, hs, hcover, hdisj, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAc (Subset.refl A)
      (by simp only [sdiff_self, isClosed_empty]) hVo hAV hVc.1 hVc.2
  let : Fintype s := hs.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let H : Fin (Fintype.card s) → ℂ ≃ₜ ℂ := fun i => H₀ (e.symm i)
  let γ : Fin (Fintype.card s) → Circle → ℂ := fun i => γ₀ (e.symm i)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hdisj (e.symm i).property (e.symm j).property
      (fun h => hij (e.symm.injective (Subtype.ext h)))
  have hcover' : A ⊆ ⋃ i, jordanInterior (H i) := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hcover hz)
    refine mem_iUnion.mpr ⟨e ⟨j, hj⟩, ?_⟩
    simpa only [H, e.symm_apply_apply] using hzj
  have hinside' (i : Fin (Fintype.card s)) : closure (jordanInterior (H i)) ⊆ V :=
    hinside _ (e.symm i).property
  refine ⟨Fintype.card s, H, γ, hd, ?_, ?_, ?_⟩
  · intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinfG
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover' hpG)
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  · rw [interior_closedJordanCore]
    intro p hp hbad
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hbad
    exact hinside' i hz hp
  · intro i
    obtain ⟨hsm, hemb, hfront, _⟩ := hcurves _ (e.symm i).property
    exact ⟨hsm, hemb, hfront⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A strict exhaustion by finite smooth Jordan cores

Every prescribed compact subset is retained in the interior of a finite
Jordan core. Recursive application retains the preceding core and the next
compact exhaustion set. The construction uses Sard, one-manifold
classification, and Schoenflies.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace SmoothJordanCore

variable {G : Set Sphere} (C : SmoothJordanCore G)

theorem regular : closure (interior C.carrier) = C.carrier :=
  closure_interior_closedJordanCore C.disk C.disjoint

theorem connected_interior : IsConnected (interior C.carrier) := by
  rw [carrier, interior_closedJordanCore]
  exact isConnected_openCompletedRegion C.disk C.disjoint

theorem infty_interior : OnePoint.infty ∈ interior C.carrier := by
  rw [carrier, interior_closedJordanCore]
  intro h
  obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
  exact OnePoint.coe_ne_infty z hz

end SmoothJordanCore

theorem exists_smooth_jordan_core_containing
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ C : SmoothJordanCore G, S ⊆ interior C.carrier := by
  obtain ⟨P, hPc, hPconn, hPG, hSP, hinfP⟩ :=
    exists_compact_connected_core_neighborhood hG hconn hinf hS hSG
  obtain ⟨n, H, γ, hd, hKG, hPK, hcurves⟩ :=
    exists_prescribed_jordan_core hsard hschoenflies hG hPc hPG hPconn.isPreconnected hinfP
  let C : SmoothJordanCore G := ⟨n, H, γ, hd, hKG,
    fun i => (hcurves i).1, fun i => (hcurves i).2.1, fun i => (hcurves i).2.2⟩
  exact ⟨C, (hSP.trans interior_subset).trans hPK⟩

theorem exists_smooth_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ C : ℕ → SmoothJordanCore G,
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G := by
  classical
  obtain ⟨R, D, K, _, _, _, _, _, hK, hDK, hcover, _, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  have hex (S : Set Sphere) (hS : IsCompact S) (hSG : S ⊆ G) :=
    exists_smooth_jordan_core_containing hsard hschoenflies hG hconn hinf hS hSG
  let initial : SmoothJordanCore G := Classical.choose (hex (K 0) (hK 0).1 (hK 0).2)
  have hinitial : K 0 ⊆ interior initial.carrier :=
    Classical.choose_spec (hex (K 0) (hK 0).1 (hK 0).2)
  let next (n : ℕ) (C : SmoothJordanCore G) : SmoothJordanCore G :=
    Classical.choose (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  have hnext (n : ℕ) (C : SmoothJordanCore G) :
      C.carrier ∪ K (n + 1) ⊆ interior (next n C).carrier :=
    Classical.choose_spec (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  let C : ℕ → SmoothJordanCore G := fun n => Nat.rec initial next n
  have hstep (n : ℕ) : C (n + 1) = next n (C n) := rfl
  have hretain (n : ℕ) : K n ⊆ interior (C n).carrier := by
    cases n with
    | zero => exact hinitial
    | succ n => exact subset_union_right.trans (hnext n (C n))
  refine ⟨C, fun n => subset_union_left.trans (hnext n (C n)), ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun n => interior_subset.trans (C n).subset
  · intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
    exact mem_iUnion.mpr ⟨n, hretain n (interior_subset (hDK n hn))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Images of compact retained cores

A conformal injection on an open neighborhood carries a compact core's
interior and boundary to the interior and boundary of its image. Regular
closed cores remain regular closed. These facts use local openness, not a
boundary extension of the conformal map.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem frontier_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, interior_image_of_continuous_open hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

theorem closure_image_interior_of_continuous
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : ContinuousOn f G) (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K) :
    closure (f '' interior K) = f '' K := by
  have hc : ContinuousOn f K := hf.mono hKG
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hK.image_of_continuousOn hc).isClosed
  · have hci : ContinuousOn f (closure (interior K)) := hregular.symm ▸ hc
    simpa only [hregular] using hci.image_closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanCoreRecognition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognizing the exterior bounded by a finite Jordan family

A regular closed sphere set with connected interior containing infinity
and with finitely many disjoint Jordan boundary curves is exactly their
common closed exterior. The filled disks are disjoint. This supplies the
image-side identification of retained cores without assuming orientation
or a boundary extension theorem.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem unbounded_preconnected_subset_jordan_exterior
    {T : Set ℂ} (hT : IsPreconnected T) (hunbounded : ¬ Bornology.IsBounded T)
    (H : ℂ ≃ₜ ℂ) (havoid : Disjoint T (frontier (jordanInterior H))) :
    T ⊆ (closure (jordanInterior H))ᶜ := by
  have hsplit : T ⊆ jordanInterior H ∨ T ⊆ (closure (jordanInterior H))ᶜ := by
    apply hT.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        exact Set.disjoint_left.mp havoid hz (by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hc, hi⟩)
  rcases hsplit with h | h
  · exact (hunbounded ((isCompact_closure_jordanInterior H).isBounded.subset
      (h.trans subset_closure))).elim
  · exact h

theorem sphere_jordan_core_recognition
    {I : Type*} [Finite I] {A : Set Sphere}
    (hregular : closure (interior A) = A)
    (hconn : IsPreconnected (interior A)) (hinf : OnePoint.infty ∈ interior A)
    (H : I → ℂ ≃ₜ ℂ)
    (hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))))
    (hfront : frontier A = ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) :
    Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      Aᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hAclosed : IsClosed A := hregular ▸ isClosed_closure
  let T : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' interior A
  have hT := finite_part_connected_unbounded hconn (by
    simpa only [interior_interior] using hinf)
  have hfrontA (i : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) ⊆ frontier A := by
    rw [hfront]
    exact subset_iUnion (fun j : I => ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j))) i
  have hTout (i : I) : T ⊆ (closure (jordanInterior (H i)))ᶜ := by
    apply unbounded_preconnected_subset_jordan_exterior hT.1 hT.2 (H i)
    apply Set.disjoint_left.mpr
    intro z hz hzfront
    have hzf := hfrontA i (mem_image_of_mem _ hzfront)
    exact hzf.2 hz
  have hAout (i : I) : A ⊆ (((↑) : ℂ → Sphere) '' jordanInterior (H i))ᶜ := by
    rw [← hregular]
    apply closure_minimal ?_ (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))).isClosed_compl
    intro p hp hinside
    obtain ⟨z, hz, rfl⟩ := hinside
    exact hTout i hp (subset_closure hz)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    rcases disjoint_or_nested_jordanInteriors (H i) (H j) (hpair hij) with hd | hn | hn
    · exact hd
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA i (mem_image_of_mem _ hz))
      exact (hAout j hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H j)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA j (mem_image_of_mem _ hz))
      exact (hAout i hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
  let U : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Aᶜ
  have hUo : IsOpen U := hAclosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hUb : Bornology.IsBounded U := by
    have hc := ((OnePoint.isOpen_iff_of_mem hinf).mp isOpen_interior).2
    apply hc.isBounded.subset
    intro z hz hzint
    exact hz (interior_subset hzint)
  have hprefront : frontier U = ((↑) : ℂ → Sphere) ⁻¹' frontier A := by
    change frontier (((↑) : ℂ → Sphere) ⁻¹' Aᶜ) = _
    rw [← OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe, frontier_compl]
  have hcover : frontier U ⊆ ⋃ i, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hprefront] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront ▸ hz)
    have hzi : z ∈ frontier (jordanInterior (H i)) := OnePoint.coe_injective.mem_set_image.mp hi
    exact mem_iUnion.mpr ⟨i, frontier_subset_closure hzi⟩
  have hselected (i : I) : frontier (jordanInterior (H i)) ⊆ frontier U := by
    intro z hz
    rw [hprefront]
    exact hfrontA i (mem_image_of_mem _ hz)
  have hUfill := open_subset_finite_jordanInteriors_of_frontier_subset H hd hUo hUb hcover hselected
  refine ⟨hd, Subset.antisymm ?_ ?_⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact (hp (interior_subset hinf)).elim
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hUfill hp)
      exact mem_iUnion.mpr ⟨i, z, hi, rfl⟩
  · intro p hp hpA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hAout i hpA hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Jordan disks bounded by an image core

Schoenflies is applied only to the images of the given boundary circles.
The image-core theorem then proves that their filled sides are pairwise
disjoint and exhaust the complement of the image core.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_jordan_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hG : IsOpen G) (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K)
    (hconn : IsPreconnected (interior K)) (hinf : OnePoint.infty ∈ interior K)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {I : Type*} [Finite I] (γ : I → Circle → ℂ)
    (hγ : ∀ i, Continuous (γ i)) (hγinj : ∀ i, Injective (γ i))
    (hγpair : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))))
    (hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i)) :
    ∃ H : I → ℂ ≃ₜ ℂ,
      (∀ i, frontier (jordanInterior (H i)) =
        range (fun t => finiteCoord (f ((γ i t : ℂ) : Sphere)))) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      (f '' K)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hγK (i : I) (t : Circle) : ((γ i t : ℂ) : Sphere) ∈ K := by
    apply hK.isClosed.closure_eq ▸ frontier_subset_closure
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, γ i t, ⟨t, rfl⟩, rfl⟩
  have hinfG : OnePoint.infty ∈ G := hKG (interior_subset hinf)
  have hfinite (i : I) (t : Circle) : f ((γ i t : ℂ) : Sphere) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinfG hfix (hKG (hγK i t))
  let δ : I → Circle → ℂ := fun i t => finiteCoord (f ((γ i t : ℂ) : Sphere))
  have hcoords (i : I) (t : Circle) : (δ i t : Sphere) = f ((γ i t : ℂ) : Sphere) :=
    CannonMobius.coe_coordinate (hfinite i t)
  have hδ (i : I) : Continuous (δ i) := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ i = f ∘ ((↑) : ℂ → Sphere) ∘ γ i :=
      funext (hcoords i)
    rw [he]
    exact hf.comp_continuous (OnePoint.continuous_coe.comp (hγ i))
      (fun t => hKG (hγK i t))
  have hδinj (i : I) : Injective (δ i) := by
    intro x y hxy
    apply hγinj i
    apply OnePoint.coe_injective
    apply hi (hKG (hγK i x)) (hKG (hγK i y))
    exact (hcoords i x).symm.trans ((congrArg ((↑) : ℂ → Sphere) hxy).trans (hcoords i y))
  choose H hH using fun i => hschoenflies (δ i) (hδ i) (hδinj i)
  have hHfront (i : I) : frontier (jordanInterior (H i)) = range (δ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (δ i) (hH i)
  have hHp : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    rw [hHfront i, hHfront j]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have he : ((γ i x : ℂ) : Sphere) = ((γ j y : ℂ) : Sphere) := by
      apply hi (hKG (hγK i x)) (hKG (hγK j y))
      exact (hcoords i x).symm.trans
        ((congrArg ((↑) : ℂ → Sphere) (hx.trans hy.symm)).trans (hcoords j y))
    exact Set.disjoint_left.mp (hγpair hij) ⟨x, rfl⟩ ⟨y, OnePoint.coe_injective he.symm⟩
  have himages (i : I) : f '' (((↑) : ℂ → Sphere) '' range (γ i)) =
      ((↑) : ℂ → Sphere) '' range (δ i) := by
    ext p
    constructor
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨δ i t, ⟨t, rfl⟩, hcoords i t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨((γ i t : ℂ) : Sphere), ⟨γ i t, ⟨t, rfl⟩, rfl⟩, (hcoords i t).symm⟩
  have htargetfront : frontier (f '' K) =
      ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := by
    rw [frontier_image_of_continuous_open hf ho hG hi hK hKG, hfront, image_iUnion]
    congr 1
    funext i
    rw [hHfront i]
    exact himages i
  have htargetint := interior_image_of_continuous_open hf ho hG hi hKG
  have htargetregular : closure (interior (f '' K)) = f '' K := by
    rw [htargetint]
    exact closure_image_interior_of_continuous hf hK hKG hregular
  have htargetconn : IsPreconnected (interior (f '' K)) := by
    rw [htargetint]
    exact hconn.image f (hf.mono (interior_subset.trans hKG))
  have htargetinf : OnePoint.infty ∈ interior (f '' K) := by
    rw [htargetint]
    exact ⟨OnePoint.infty, hinf, hfix⟩
  obtain ⟨hd, he⟩ := sphere_jordan_core_recognition htargetregular htargetconn htargetinf H hHp htargetfront
  exact ⟨H, hHfront, hd, he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanIntersectionConnectivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connectivity on the inside of a retained Jordan boundary

A radial clamp onto a slightly smaller disk fixes any prescribed pair of
interior points and maps the whole domain into its intersection with the
disk. The inner circle stays in the domain by compactness of the retained
boundary. This proves the connectedness needed to track source and image
sides under refinement.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_radialClamp {r : ℝ} (hr : 0 < r) : Continuous (radialClamp r) := by
  apply (continuous_const.div (continuous_const.max continuous_norm) ?_).smul continuous_id
  intro z
  exact ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))

theorem radialClamp_eq_self {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    radialClamp r z = z := by
  simp only [radialClamp, max_eq_left hz, div_self hr.ne', one_smul]

theorem norm_radialClamp_of_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖radialClamp r z‖ = r := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hz)
  rw [radialClamp, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (norm_nonneg z)), div_mul_cancel₀ _ hn]

theorem inner_circle_subset_of_retained_boundary
    {W : Set ℂ} (hW : IsOpen W) (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < 1 → 1 - r < δ → sphere (0 : ℂ) r ⊆ W := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hW hboundary
  refine ⟨δ, hδ, ?_⟩
  intro r hr hr1 hnear z hz
  have hzn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  let w : ℂ := r⁻¹ • z
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hzn,
      inv_mul_cancel₀ hr.ne']
  have hzw : z = r • w := by simp only [w, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  apply hsub
  apply mem_cthickening_of_dist_le z w δ (sphere (0 : ℂ) 1)
    (mem_sphere_zero_iff_norm.mpr hwn)
  calc
    dist z w = ‖(r - 1) • w‖ := by rw [hzw, dist_eq_norm, sub_smul, one_smul]
    _ = 1 - r := by rw [norm_smul, Real.norm_eq_abs, hwn, mul_one, abs_of_neg (sub_neg.mpr hr1)]; ring
    _ ≤ δ := hnear.le

theorem isPreconnected_inter_unitDisk
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    IsPreconnected (W ∩ ball 0 1) := by
  obtain ⟨δ, hδ, hcircle⟩ := inner_circle_subset_of_retained_boundary hW hboundary
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hxn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx.2
  have hyn : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy.2
  have hmax : max (max ‖x‖ ‖y‖) (1 - δ) < 1 :=
    max_lt (max_lt hxn hyn) (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hmax
  have hxr : ‖x‖ < r := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hyr : ‖y‖ < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hr : 0 < r := (norm_nonneg x).trans_lt hxr
  have hnear : 1 - r < δ := by linarith [le_max_right (max ‖x‖ ‖y‖) (1 - δ)]
  have hmap : radialClamp r '' W ⊆ W ∩ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzr : ‖z‖ ≤ r
    · rw [radialClamp_eq_self hr hzr]
      exact ⟨hz, by simpa only [mem_ball, dist_zero_right] using hzr.trans_lt hrhi⟩
    · have he := norm_radialClamp_of_le hr (le_of_lt (lt_of_not_ge hzr))
      exact ⟨hcircle r hr hrhi hnear (mem_sphere_zero_iff_norm.mpr he), by
        simpa only [mem_ball, dist_zero_right, he] using hrhi⟩
  refine ⟨radialClamp r '' W, hmap, ?_, ?_, hconn.image _ (continuous_radialClamp hr).continuousOn⟩
  · exact ⟨x, hx.1, radialClamp_eq_self hr hxr.le⟩
  · exact ⟨y, hy.1, radialClamp_eq_self hr hyr.le⟩

theorem isPreconnected_inter_jordanInterior
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (H : ℂ ≃ₜ ℂ) (hboundary : frontier (jordanInterior H) ⊆ W) :
    IsPreconnected (W ∩ jordanInterior H) := by
  have hpre : IsPreconnected (H ⁻¹' W) := H.isPreconnected_preimage.mpr hconn
  have hbd : sphere (0 : ℂ) 1 ⊆ H ⁻¹' W := by
    intro z hz
    apply hboundary
    rw [frontier_jordanInterior]
    exact mem_image_of_mem _ hz
  have hi := isPreconnected_inter_unitDisk (hW.preimage H.continuous) hpre hbd
  have he : H '' ((H ⁻¹' W) ∩ ball 0 1) = W ∩ jordanInterior H := by
    rw [image_preimage_inter]
    rfl
  exact he ▸ hi.image H H.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanSideCorrespondence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correspondence of the source and image sides of a core boundary

Connectivity of the source on a disk's inside, together with local openness
at its retained boundary, determines which target Jordan disk it maps into.
This tracks the labels of boundary curves without extending the conformal
map across any omitted component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem isPreconnected_sphere_jordan_intersection
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hW : IsPreconnected W := (finite_part_connected_unbounded hconn
    (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1
  have hi := isPreconnected_inter_jordanInterior (hG.preimage OnePoint.continuous_coe) hW H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  have he : ((↑) : ℂ → Sphere) '' (W ∩ jordanInterior H) =
      G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := image_preimage_inter _ _ _
  exact he ▸ hi.image _ OnePoint.continuous_coe.continuousOn

theorem open_image_jordan_side_subset
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (J i) := by
  classical
  let S : Set Sphere := G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))
  let O : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior (J i)
  have hOo : IsOpen O := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (J i))
  have hKclosed : IsClosed (closedJordanCore H) :=
    (isOpen_iUnion fun j => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).isClosed_compl
  have hsrcboundary (j : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j)) ⊆ G := by
    intro q hq
    apply hKG
    have hfq : q ∈ frontier (closedJordanCore H) := by
      rw [frontier_closedJordanCore H hd]
      exact mem_iUnion.mpr ⟨j, hq⟩
    simpa only [hKclosed.closure_eq] using frontier_subset_closure hfq
  have hS : IsPreconnected S :=
    isPreconnected_sphere_jordan_intersection hG hconn.isPreconnected hinf (H i) (hsrcboundary i)
  have hfrontO : frontier O = ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) :=
    frontier_sphere_image_jordanInterior (J i)
  have havoid : Disjoint (f '' S) (frontier O) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ hq
    rw [hfrontO, ← hboundary i] at hq
    obtain ⟨y, hy, he⟩ := hq
    have hyx : y = x := hi (hsrcboundary i hy) hx.1 he
    rw [hyx] at hy
    obtain ⟨z, hz, hez⟩ := hy
    obtain ⟨w, hw, hew⟩ := hx.2
    have hwz : w = z := OnePoint.coe_injective (hew.trans hez.symm)
    exact hz.2 ((jordanInterior_isOpen (H i)).interior_eq.symm ▸ (hwz ▸ hw))
  obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
  let x : Sphere := (z : Sphere)
  have hxfront : x ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := ⟨z, hz, rfl⟩
  let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, closedTerminalCap (H j)
  have hBclosed : IsClosed B := isClosed_iUnion_of_finite fun j =>
    (isCompact_closedTerminalCap (H j)).isClosed
  have hxB : x ∉ B := by
    intro h
    obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp h
    have hwz : w = z := OnePoint.coe_injective he
    exact Set.disjoint_left.mp (hd j.property.symm) (frontier_subset_closure hz) (hwz ▸ hw)
  let N : Set Sphere := G ∩ Bᶜ
  have hN : IsOpen N := hG.inter hBclosed.isOpen_compl
  have hxN : x ∈ N := ⟨hsrcboundary i hxfront, hxB⟩
  have hfN : IsOpen (f '' N) := ho _ hN inter_subset_left
  have hfxfront : f x ∈ frontier O := by
    rw [hfrontO, ← hboundary i]
    exact mem_image_of_mem _ hxfront
  obtain ⟨y, hyN, hyO⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hfxfront)
    (f '' N) (hfN.mem_nhds (mem_image_of_mem _ hxN))
  obtain ⟨w, hwN, rfl⟩ := hyN
  have hwK : w ∉ closedJordanCore H := by
    intro hw
    have htarget : f w ∈ (f '' closedJordanCore H)ᶜ := by
      rw [himage]
      exact mem_iUnion.mpr ⟨i, hyO⟩
    exact htarget (mem_image_of_mem _ hw)
  have hwS : w ∈ S := by
    refine ⟨hwN.1, ?_⟩
    have hwU : w ∈ ⋃ j, ((↑) : ℂ → Sphere) '' jordanInterior (H j) := not_not.mp hwK
    obtain ⟨j, v, hv, he⟩ := mem_iUnion.mp hwU
    by_cases hji : j = i
    · exact hji ▸ ⟨v, hv, he⟩
    · exact (hwN.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, v, subset_closure hv, he⟩)).elim
  have hmeet : (f '' S ∩ O).Nonempty := ⟨f w, mem_image_of_mem _ hwS, hyO⟩
  have hcover : f '' S ⊆ O ∪ (closure O)ᶜ := by
    intro q hq
    by_cases hqo : q ∈ O
    · exact Or.inl hqo
    · right
      intro hqc
      exact Set.disjoint_left.mp havoid hq ⟨hqc, by
        simpa only [hOo.interior_eq] using hqo⟩
  exact (hS.image f (hf.mono inter_subset_left)).subset_left_of_subset_union
    hOo isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hcover hmeet


theorem open_image_jordan_side_eq
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (hJd : Pairwise (Disjoint on fun i => closure (jordanInterior (J i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsides := open_image_jordan_side_subset H J hd hG hconn hinf hKG hf ho hi hboundary himage
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem _ hx.1, hsides i (mem_image_of_mem _ hx)⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hnotK : x ∉ closedJordanCore H := by
      intro hxK
      have hnot : f x ∈ (f '' closedJordanCore H)ᶜ := by
        rw [himage]
        exact mem_iUnion.mpr ⟨i, hy⟩
      exact hnot (mem_image_of_mem _ hxK)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (not_not.mp hnotK)
    have hj' := hsides j (mem_image_of_mem f ⟨hx, hj⟩)
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps J hJd hne)
        (by obtain ⟨z, hz, he⟩ := hj'; exact ⟨z, subset_closure hz, he⟩)
        (by obtain ⟨z, hz, he⟩ := hy; exact ⟨z, subset_closure hz, he⟩)
    exact ⟨x, ⟨hx, hji ▸ hj⟩, rfl⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedImageCores
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched source and target Jordan cores

The actual mapped boundary parametrizations identify each target disk's
label. Both inclusions of the corresponding source/target side equality
are proved, so refinement can carry those labels to end components.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_matched_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) (C : SmoothJordanCore G) :
    ∃ J : Fin C.count → ℂ ≃ₜ ℂ,
      Pairwise (Disjoint on fun i => closure (jordanInterior (J i))) ∧
      (f '' C.carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i) ∧
      (∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (C.disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsrcfront : frontier C.carrier = ⋃ i, ((↑) : ℂ → Sphere) '' range (C.curve i) := by
    rw [SmoothJordanCore.carrier, frontier_closedJordanCore C.disk C.disjoint]
    simp only [C.boundary]
  have hcurvesG (i : Fin C.count) (t : Circle) : ((C.curve i t : ℂ) : Sphere) ∈ G := by
    apply C.subset
    have hfront : ((C.curve i t : ℂ) : Sphere) ∈ frontier C.carrier := by
      rw [hsrcfront]
      exact mem_iUnion.mpr ⟨i, C.curve i t, ⟨t, rfl⟩, rfl⟩
    simpa only [C.isCompact.isClosed.closure_eq] using frontier_subset_closure hfront
  obtain ⟨J, hJfront, hJd, hJe⟩ := exists_jordan_image_core_of_continuous_open hschoenflies hG hf ho hi
    C.isCompact C.subset C.regular C.connected_interior.isPreconnected C.infty_interior hfix
    C.curve (fun i => (C.embedding i).continuous) (fun i => (C.embedding i).injective)
    (by
      intro i j hij
      apply (C.disjoint hij).mono
      · rw [← C.boundary i]
        exact frontier_subset_closure
      · rw [← C.boundary j]
        exact frontier_subset_closure) hsrcfront
  have hboundary (i : Fin C.count) :
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) := by
    rw [C.boundary i, hJfront i, image_image, ← range_comp, ← range_comp]
    congr 1
    funext t
    exact (CannonMobius.coe_coordinate
      (finite_image_of_fixes_infty hi hinf hfix (hcurvesG i t))).symm
  refine ⟨J, hJd, hJe, hboundary, ?_⟩
  exact open_image_jordan_side_eq C.disk J C.disjoint hJd hG hconn hinf C.subset
    hf ho hi hboundary hJe


theorem exists_matched_jordan_exhaustion_of_continuous_open
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i)))) ∧
      (∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i)) ∧
      (∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i))) ∧
      ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)) := by
  classical
  obtain ⟨C, hs, hc⟩ := exists_smooth_jordan_exhaustion hsard hschoenflies hG hconn hinf
  choose J hd he hb hi' using fun n => exists_matched_image_core_of_continuous_open hschoenflies hG hconn hinf hf ho hi hfix (C n)
  exact ⟨C, J, hs, hc, hd, he, hb, hi'⟩

theorem exists_matched_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (J n i)))) ∧
      (∀ n, (f '' (C n).carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J n i)) ∧
      (∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i))) ∧
      ∀ n i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J n i)) :=
  exists_matched_jordan_exhaustion_of_continuous_open hsard hschoenflies hG hconn hinf
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi hfix


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MarkedEndTrapping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Passing marked finite disks to their prescribed ends

The finite-stage geometric containment and uniform convergence on each
fixed boundary curve imply containment in the whole limiting end component.
No winding-number or boundary-extension hypothesis is used.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem limit_disk_subset_jordan_fill
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (htrap : ∀ᶠ n in atTop, closedBall (c n) (r n) ⊆ closure (jordanInterior (J n))) :
    closedBall c₀ r₀ ⊆ closure (jordanInterior H) := by
  intro z hz
  rw [closedBall_eq_affine_image hr₀ c₀] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  apply mem_jordan_fill_of_tendsto H J γ γn hγ hfront hfrontn hlim
    (hc.add (hrlim.smul_const u))
  filter_upwards [htrap] with n hn
  apply hn
  rw [closedBall_eq_affine_image (hr n) (c n)]
  exact mem_image_of_mem _ hu

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedComponentSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trapping a corresponding component by any retained contour

The source end need only lie inside the chosen contour. Compactness places
a sufficiently late source collar there, and the matched side equality
places its target collar inside the target contour.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem SmoothJordanCore.omitted_point_mem_side
    {G : Set Sphere} (A : SmoothJordanCore G) {q : Sphere} (hq : q ∈ Gᶜ)
    {j : Fin A.count} (hqj : q ∈ closedTerminalCap (A.disk j)) :
    q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) := by
  have hnot : q ∉ A.carrier := fun h => hq (A.subset h)
  have hqunion : q ∈ ⋃ k, ((↑) : ℂ → Sphere) '' jordanInterior (A.disk k) :=
    not_not.mp hnot
  obtain ⟨k, z, hz, he⟩ := mem_iUnion.mp hqunion
  by_cases hkj : k = j
  · exact hkj ▸ ⟨z, hz, he⟩
  · exact (Set.disjoint_left.mp (disjoint_closedTerminalCaps A.disk A.disjoint hkj)
      ⟨z, subset_closure hz, he⟩ hqj).elim

theorem matched_component_subset_retained_side
    {G : Set Sphere} {f : Sphere → Sphere}
    (C : ℕ → SmoothJordanCore G) (J : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ)
    (b : (n : ℕ) → Fin (C n).count)
    (hsourceNest : Antitone (fun n => closedTerminalCap ((C n).disk (b n))))
    (hboundary : ∀ n i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n i)))
    {S E : Set Sphere}
    (hsource : S = ⋂ n, closedTerminalCap ((C n).disk (b n)))
    (htarget : E = ⋂ n, closedTerminalCap (J n (b n)))
    (H L : ℂ ≃ₜ ℂ)
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior L))
    (hS : S ⊆ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    E ⊆ ((↑) : ℂ → Sphere) '' jordanInterior L := by
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap ((C n).disk (b n))).isClosed)
    hsourceNest (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)) (hsource ▸ hS)
  have hfrontG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n))) ⊆ G := by
    intro x hx
    apply (C n).subset
    have hxf : x ∈ frontier (C n).carrier := by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      exact mem_iUnion.mpr ⟨b n, hx⟩
    simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hxf
  have hfront : frontier (jordanInterior (J n (b n))) ⊆ jordanInterior L := by
    intro z hz
    have hzimage : (z : Sphere) ∈
        f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n)))) := by
      rw [hboundary n (b n)]
      exact mem_image_of_mem _ hz
    obtain ⟨x, hx, hxe⟩ := hzimage
    have hxcap : x ∈ closedTerminalCap ((C n).disk (b n)) := by
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, frontier_subset_closure hw, rfl⟩
    have hzside : (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior L := by
      have hmem : (z : Sphere) ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :=
        ⟨x, ⟨hfrontG hx, hn hxcap⟩, hxe⟩
      rw [hside] at hmem
      exact hmem.2
    exact OnePoint.coe_injective.mem_set_image.mp hzside
  rw [htarget]
  exact (iInter_subset _ n).trans
    (image_mono (closed_jordanInterior_subset_of_frontier_subset (J n (b n)) L hfront))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_EndCluster
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cluster values at a specified end

The matched side identity places images of a sequence approaching the
source end eventually in every target collar. A convergent image sequence
therefore limits in the full target component, without extending the map
across that component.
-/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

open FiniteTransfer

theorem cluster_mem_matched_end
    {G : Set Sphere} {f : Sphere → Sphere}
    (H J : ℕ → ℂ ≃ₜ ℂ)
    (hside : ∀ j, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H j))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)))
    {q p : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q)) (hxG : ∀ᶠ n in atTop, x n ∈ G)
    (hy : Tendsto (f ∘ x) atTop (𝓝 p)) :
    p ∈ ⋂ j, closedTerminalCap (J j) := by
  apply mem_iInter.mpr
  intro j
  have hevent : ∀ᶠ n in atTop, x n ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j) :=
    hx.eventually ((OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).mem_nhds (hq j))
  apply (isCompact_closedTerminalCap (J j)).isClosed.mem_of_tendsto hy
  filter_upwards [hevent, hxG] with n hn hnG
  have hfn : f (x n) ∈ f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)) := by
    rw [← hside j]
    exact mem_image_of_mem _ ⟨hnG, hn⟩
  obtain ⟨z, hz, he⟩ := hfn.2
  exact ⟨z, subset_closure hz, he⟩

theorem cluster_mem_corresponding_component
    {G : Set Sphere} {f : Sphere → Sphere}
    (H J : ℕ → ℂ ≃ₜ ℂ)
    (hside : ∀ j, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H j))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j)))
    {q p p₀ : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (H j))
    (hcomponent : connectedComponentIn (f '' G)ᶜ p₀ = ⋂ j, closedTerminalCap (J j))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q)) (hxG : ∀ᶠ n in atTop, x n ∈ G)
    (hy : Tendsto (f ∘ x) atTop (𝓝 p)) :
    p ∈ connectedComponentIn (f '' G)ᶜ p₀ := by
  rw [hcomponent]
  exact cluster_mem_matched_end H J hside hq hx hxG hy

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteModelEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Terminal components of an actual finite circle model

Every physical terminal disk determines a target complementary component.
The assignment exhausts all target components and respects every retained
Jordan contour. Only the existing topological inputs are used.
-/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem jordan_address_eq_of_common_point
    {I : ℕ → Type*} (C : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (C n i))))
    {b d : (n : ℕ) → I n} {x : Sphere}
    (hb : x ∈ ⋂ n, closedTerminalCap (C n (b n)))
    (hd' : x ∈ ⋂ n, closedTerminalCap (C n (d n))) : b = d := by
  funext n
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (C n) (hd n) hne)
    (mem_iInter.mp hb n) (mem_iInter.mp hd' n)

theorem exists_finite_model_terminal_assignment
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsOpen V) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ p : I → Sphere,
      (∀ i, p i ∈ Vᶜ) ∧
      Pairwise (Disjoint on fun i => connectedComponentIn Vᶜ (p i)) ∧
      (∀ y ∈ Vᶜ, ∃ i, connectedComponentIn Vᶜ y = connectedComponentIn Vᶜ (p i)) ∧
      (∀ i q, q ∈ closedTerminalCap (T i) → ∀ x : ℕ → Sphere,
        Tendsto x Filter.atTop (𝓝 q) → (∀ᶠ n in Filter.atTop, x n ∈ openCompletedRegion T) →
        ∀ y, Tendsto (f ∘ x) Filter.atTop (𝓝 y) → y ∈ connectedComponentIn Vᶜ (p i)) ∧
      ∀ A : SmoothJordanCore (openCompletedRegion T),
        ∃ L : Fin A.count → ℂ ≃ₜ ℂ,
          (∀ j, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
            ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L j))) ∧
          ∀ i j, closedTerminalCap (T i) ⊆
            ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) →
            connectedComponentIn Vᶜ (p i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L j) := by
  classical
  let Q := openCompletedRegion T
  have hQ : IsOpen Q := isOpen_openCompletedRegion T
  have hQc : IsConnected Q := isConnected_openCompletedRegion T hTd
  have hQcomp : Qᶜ = ⋃ j, closedTerminalCap (T j) := compl_compl _
  have hinf : OnePoint.infty ∈ Q := by
    intro h
    obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
    exact OnePoint.coe_ne_infty z hz
  have hcont : ContinuousOn f Q := fun x hx => (hf.smooth x hx).1.continuousWithinAt
  have hopen : ∀ S, IsOpen S → S ⊆ Q → IsOpen (f '' S) :=
    fun _ hS hSQ => hf.isOpen_image hV hS hSQ
  have hi : InjOn f Q := hf.bijOn.injOn
  have himage : f '' Q = V := hf.bijOn.image_eq
  have hcomponent {i : I} {q : Sphere} (hq : q ∈ closedTerminalCap (T i)) :
      connectedComponentIn Qᶜ q = closedTerminalCap (T i) := by
    rw [hQcomp]
    exact connectedComponentIn_finite_disjoint_closed _
      (fun j => (isCompact_closedTerminalCap (T j)).isClosed)
      (fun j => isPreconnected_closedTerminalCap (T j)) (disjoint_closedTerminalCaps T hTd) hq
  obtain ⟨C, J, hs, hc, hd, he, hb, hside⟩ :=
    exists_matched_jordan_exhaustion_of_continuous_open hsard hschoenflies
      hQ hQc hinf hcont hopen hi hfix
  have hex (i : I) : ∃ (b : (n : ℕ) → Fin (C n).count) (p : Sphere),
      p ∈ Vᶜ ∧ closedTerminalCap (T i) = ⋂ n, closedTerminalCap ((C n).disk (b n)) ∧
      connectedComponentIn Vᶜ p = ⋂ n, closedTerminalCap (J n (b n)) ∧
      Antitone (fun n => closedTerminalCap ((C n).disk (b n))) := by
    obtain ⟨q, hq⟩ := (nontrivial_closedTerminalCap (T i)).nonempty
    have hqQ : q ∈ Qᶜ := by
      rw [hQcomp]
      exact mem_iUnion.mpr ⟨i, hq⟩
    obtain ⟨b, p, hp, hsrc, htgt, hnest⟩ :=
      corresponding_target_end_of_source_of_continuous_open hQ hcont hopen hi
        C J hs hc hd he hb hside hqQ
    rw [hcomponent hq] at hsrc
    rw [himage] at hp htgt
    refine ⟨b, p, hp, hsrc, htgt, ?_⟩
    apply antitone_nat_of_succ_le
    intro n x hx
    have hn := (matched_jordan_disk_subset_iff hi
      ((C n).disk (b n)) ((C (n + 1)).disk (b (n + 1)))
      (J n (b n)) (J (n + 1) (b (n + 1)))
      ((C (n + 1)).boundary_subset_domain _) (hb _ _) (hside _ _)).mpr (hnest n)
    obtain ⟨z, hz, hez⟩ := hn hx
    exact ⟨z, subset_closure hz, hez⟩
  choose b p hp hsrc htgt hanti using hex
  refine ⟨p, hp, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change x ∈ connectedComponentIn Vᶜ (p i) at hxi
    change x ∈ connectedComponentIn Vᶜ (p j) at hxj
    have hbij : b i = b j := jordan_address_eq_of_common_point J hd
      (htgt i ▸ hxi) (htgt j ▸ hxj)
    have hcaps : closedTerminalCap (T i) = closedTerminalCap (T j) := by
      rw [hsrc i, hsrc j, hbij]
    obtain ⟨z, hz⟩ := (nontrivial_closedTerminalCap (T i)).nonempty
    have hzj : z ∈ closedTerminalCap (T j) := by rwa [← hcaps]
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps T hTd hij) hz hzj
  · intro y hy
    have hy' : y ∈ (f '' Q)ᶜ := himage.symm ▸ hy
    obtain ⟨d, q, hq, hqsrc, hytgt, _⟩ :=
      corresponding_source_end_of_target_of_continuous_open hQ hcont hopen hi
        C J hs hc hd he hb hside hy'
    rw [hQcomp] at hq
    obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
    rw [hcomponent hqi] at hqsrc
    have hbd : b i = d := jordan_address_eq_of_common_point
      (fun n => (C n).disk) (fun n => (C n).disjoint)
      (hsrc i ▸ hqi) (hqsrc ▸ hqi)
    refine ⟨i, ?_⟩
    rw [← himage, hytgt, himage, htgt i, hbd]
  · intro i q hqi x hx hxQ y hy
    have hqQ : q ∈ Qᶜ := by
      rw [hQcomp]
      exact mem_iUnion.mpr ⟨i, hqi⟩
    have hqside (n : ℕ) : q ∈ ((↑) : ℂ → Sphere) '' jordanInterior ((C n).disk (b i n)) :=
      (C n).omitted_point_mem_side hqQ (mem_iInter.mp (hsrc i ▸ hqi) n)
    have htgt' : connectedComponentIn (f '' Q)ᶜ (p i) = ⋂ n, closedTerminalCap (J n (b i n)) := by
      simpa only [himage] using htgt i
    simpa only [himage] using cluster_mem_corresponding_component
      (fun n => (C n).disk (b i n)) (fun n => J n (b i n))
      (fun n => hside n (b i n)) hqside htgt' hx hxQ hy
  · intro A
    obtain ⟨L, _, _, hboundary, hsideA⟩ :=
      exists_matched_image_core_of_continuous_open hschoenflies hQ hQc hinf
        hcont hopen hi hfix A
    refine ⟨L, hboundary, ?_⟩
    intro i j hij
    exact matched_component_subset_retained_side C J (b i) (hanti i) hb
      (hsrc i) (htgt i) (A.disk j) (L j) (hsideA j) hij

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteMarkedTrapping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked-disk trapping for the actual finite terminal assignment

The assignment is constructed from a finite model. Once a fixed source
core is retained, a terminal inside one of its holes has its target disk
inside the corresponding image contour. Uniform convergence on that
contour passes this containment to the limiting closed disk.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_terminal_component_assignment
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsOpen V) (hfix : f OnePoint.infty = OnePoint.infty) :
    Nonempty (TerminalComponentAssignment T f V) := by
  obtain ⟨p, hp, hd, hc, hcl, hr⟩ := exists_finite_model_terminal_assignment
    hsard hschoenflies T hTd hf hV hfix
  exact ⟨⟨p, hp, hd, hc, hcl, hr⟩⟩

theorem range_finite_image_boundary
    {f : Sphere → Sphere} {γ : Circle → ℂ} {H L : ℂ ≃ₜ ℂ}
    (hγ : frontier (jordanInterior H) = range γ)
    (hb : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior L))
    (hfinite : ∀ t, f ((γ t : ℂ) : Sphere) ≠ OnePoint.infty) :
    range (fun t => finiteCoord (f ((γ t : ℂ) : Sphere))) = frontier (jordanInterior L) := by
  apply OnePoint.coe_injective.image_injective
  rw [← hb, hγ, image_image, ← range_comp, ← range_comp]
  congr 1
  funext t
  exact coe_finiteCoord (hfinite t)

theorem marked_limit_subset_retained_fill
    {I : ℕ → Type*} (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (ha : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (A : SmoothJordanCore G) (j : Fin A.count)
    (hret : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (t : (n : ℕ) → I n)
    (hphysical : ∀ᶠ n in atTop, closedTerminalCap (T n (t n)) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))
    (F : ℂ → ℂ) (H : ℂ ≃ₜ ℂ)
    (hF : Continuous (F ∘ A.curve j))
    (hH : range (F ∘ A.curve j) = frontier (jordanInterior H))
    (hlim : TendstoUniformly (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere)))
      (F ∘ A.curve j) atTop)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hdisks : ∀ᶠ n in atTop,
      connectedComponentIn (V n)ᶜ ((ha n).point (t n)) =
        ((↑) : ℂ → Sphere) '' closedBall (c n) (r n)) :
    closedBall c₀ r₀ ⊆ closure (jordanInterior H) := by
  classical
  have hex (n : ℕ) : ∃ L : Fin A.count → ℂ ≃ₜ ℂ,
      A.carrier ⊆ openCompletedRegion (T n) →
        (∀ k, f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk k))) =
          ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L k))) ∧
        ∀ i k, closedTerminalCap (T n i) ⊆
          ((↑) : ℂ → Sphere) '' jordanInterior (A.disk k) →
          connectedComponentIn (V n)ᶜ ((ha n).point i) ⊆
            ((↑) : ℂ → Sphere) '' jordanInterior (L k) := by
    by_cases hn : A.carrier ⊆ openCompletedRegion (T n)
    · obtain ⟨L, hL⟩ := (ha n).retained (A.inDomain hn)
      exact ⟨L, fun _ => hL⟩
    · exact ⟨fun _ => H, fun h => (hn h).elim⟩
  choose L hL using hex
  have hfront : ∀ᶠ n in atTop,
      range (fun s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) =
        frontier (jordanInterior (L n j)) := by
    filter_upwards [hret] with n hn
    apply range_finite_image_boundary (A.boundary j) ((hL n hn).1 j)
    intro s
    apply finite_image_of_fixes_infty (heq n).bijOn.injOn
      ((A.inDomain hn).subset (interior_subset A.infty_interior)) (hfix n)
    apply (A.inDomain hn).boundary_subset_domain j
    refine ⟨A.curve j s, ?_, rfl⟩
    dsimp only [SmoothJordanCore.inDomain]
    rw [A.boundary j]
    exact mem_range_self s
  have htrap : ∀ᶠ n in atTop, closedBall (c n) (r n) ⊆ closure (jordanInterior (L n j)) := by
    filter_upwards [hret, hphysical, hdisks] with n hn hpn hdn
    intro z hz
    have hzcomp : (z : Sphere) ∈ connectedComponentIn (V n)ᶜ ((ha n).point (t n)) := by
      rw [hdn]
      exact mem_image_of_mem _ hz
    have hzside := (hL n hn).2 (t n) j hpn hzcomp
    exact subset_closure (OnePoint.coe_injective.mem_set_image.mp hzside)
  exact limit_disk_subset_jordan_fill H (fun n => L n j) _ _ hF hH hfront hlim
    hr hr₀ hc hrlim htrap

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TerminalContainment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Retained cores localize every marked terminal

A connected terminal disk disjoint from a retained core lies in one of
that core's holes. A point of the terminal identifies which hole it is.
Thus retaining the core and retaining a mark already imply the physical
containment needed for the target trapping argument.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem terminal_subset_retained_side
    {I : Type*} (T : I → ℂ ≃ₜ ℂ) {G : Set Sphere} (A : SmoothJordanCore G)
    (hret : A.carrier ⊆ openCompletedRegion T)
    {i : I} {q : Sphere} (hq : q ∈ closedTerminalCap (T i))
    {j : Fin A.count} (hqside : q ∈ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j)) :
    closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) := by
  have hopenCover : closedTerminalCap (T i) ⊆
      ⋃ k, ((↑) : ℂ → Sphere) '' jordanInterior (A.disk k) := by
    intro x hx
    have hnot : x ∉ A.carrier := by
      intro hxa
      exact hret hxa (mem_iUnion.mpr ⟨i, hx⟩)
    exact not_not.mp hnot
  have hclosedCover : closedTerminalCap (T i) ⊆ ⋃ k, closedTerminalCap (A.disk k) := by
    intro x hx
    obtain ⟨k, z, hz, he⟩ := mem_iUnion.mp (hopenCover hx)
    exact mem_iUnion.mpr ⟨k, z, subset_closure hz, he⟩
  have hqcap : q ∈ closedTerminalCap (A.disk j) := by
    obtain ⟨z, hz, he⟩ := hqside
    exact ⟨z, subset_closure hz, he⟩
  have hpiece := connectedComponentIn_subset_finite_closed_piece
    (fun k => closedTerminalCap (A.disk k))
    (fun k => (isCompact_closedTerminalCap (A.disk k)).isClosed)
    (disjoint_closedTerminalCaps A.disk A.disjoint) hclosedCover hq hqcap
  have hTi := (isPreconnected_closedTerminalCap (T i)).subset_connectedComponentIn hq (Subset.refl _)
  intro x hx
  have hxj := hpiece (hTi hx)
  obtain ⟨k, z, hz, he⟩ := mem_iUnion.mp (hopenCover hx)
  by_cases hkj : k = j
  · exact hkj ▸ ⟨z, hz, he⟩
  · exact (Set.disjoint_left.mp (disjoint_closedTerminalCaps A.disk A.disjoint hkj)
      ⟨z, subset_closure hz, he⟩ hxj).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrescribedMarkedEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked disk limits lie in their prescribed complementary components

Local uniform convergence on the source gives uniform convergence on each
retained circle. The finite terminal assignment and the nested target end
description then place the entire limiting round disk in the prescribed
component, including a zero-radius limit.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem marked_limit_subset_corresponding_component
    {I : ℕ → Type*} (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (ha : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (C : ℕ → SmoothJordanCore G)
    (b : (j : ℕ) → Fin (C j).count) (H : ℕ → ℂ ≃ₜ ℂ)
    (hret : ∀ j, ∀ᶠ n in atTop, (C j).carrier ⊆ openCompletedRegion (T n))
    (t : (n : ℕ) → I n)
    {q : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk (b j)))
    (hmark : ∀ᶠ n in atTop, q ∈ closedTerminalCap (T n (t n)))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (hboundary : ∀ j, extendAtInfinity F ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C j).disk (b j)))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j)))
    {p : Sphere}
    (hcomponent : connectedComponentIn (extendAtInfinity F '' G)ᶜ p =
      ⋂ j, closedTerminalCap (H j))
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hdisks : ∀ᶠ n in atTop,
      connectedComponentIn (V n)ᶜ ((ha n).point (t n)) =
        ((↑) : ℂ → Sphere) '' closedBall (c n) (r n)) :
    ((↑) : ℂ → Sphere) '' closedBall c₀ r₀ ⊆
      connectedComponentIn (extendAtInfinity F '' G)ᶜ p := by
  have hphysical (j : ℕ) : ∀ᶠ n in atTop, closedTerminalCap (T n (t n)) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk (b j)) := by
    filter_upwards [hret j, hmark] with n hn hqn
    exact terminal_subset_retained_side (T n) (C j) hn hqn (hq j)
  have hcurveG (j : ℕ) (s : Circle) : ((C j).curve (b j) s : Sphere) ∈ G := by
    apply (C j).boundary_subset_domain (b j)
    refine ⟨(C j).curve (b j) s, ?_, rfl⟩
    rw [(C j).boundary (b j)]
    exact mem_range_self s
  have hcontain (j : ℕ) : closedBall c₀ r₀ ⊆ closure (jordanInterior (H j)) := by
    have hγ : Continuous ((C j).curve (b j)) := ((C j).embedding (b j)).continuous
    have hFγ : Continuous (F ∘ (C j).curve (b j)) :=
      hF.comp_continuous hγ (hcurveG j)
    have hγlim : TendstoUniformly
        (fun n s => finiteCoord (f n (((C j).curve (b j) s : ℂ) : Sphere)))
        (F ∘ (C j).curve (b j)) atTop := by
      apply tendstoUniformlyOn_univ.mp
      apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
      exact hlim.comp ((C j).curve (b j)) (fun s _ => hcurveG j s) hγ.continuousOn
    have hfront : range (F ∘ (C j).curve (b j)) = frontier (jordanInterior (H j)) := by
      simpa only [extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
        range_finite_image_boundary ((C j).boundary (b j)) (hboundary j)
          (fun s => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    exact marked_limit_subset_retained_fill T f fi V ha heq hfix (C j) (b j)
      (hret j) t (hphysical j) F (H j) hFγ hfront hγlim hr hr₀ hc hrlim hdisks
  rw [hcomponent]
  rintro _ ⟨z, hz, rfl⟩
  exact mem_iInter.mpr fun j => ⟨z, hcontain j hz, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealMarkedModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assign the actual countable real-model terminals to their original source ends. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem CountableRealCoordinates.sourceMark_outside
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (s : S) : d.sourceMark s ∈ Gᶜ :=
  (Classical.choose_spec (d.labels_dust s)).1

theorem CountableRealCoordinates.sourceMark_image
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (s : S) : π (d.sourceMark s) = σ s :=
  (Classical.choose_spec (d.labels_dust s)).2

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem eventually_markIndex (s : S) :
    ∀ᶠ n in atTop, (M.markIndex n s : S) = s := by
  classical
  filter_upwards [M.marks s] with n hn
  simp [markIndex, hn]

end RealModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ShrinkingRealModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing transfer errors and shrinking physical marked neighborhoods. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem modelError_pos (n : ℕ) : 0 < modelError n := by
  unfold modelError
  positivity

attribute [local instance] sphereMetric

theorem markedNeighborhoods_nhds {S : Type*} (σ : S → Sphere) (n : ℕ) (s : S) :
    markedNeighborhoods σ n s ∈ 𝓝 (σ s) :=
  ball_mem_nhds _ (modelError_pos n)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OrderedSelectionSlots
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selection which adds at most one object per step has an enumeration in
its original order. Empty steps are retained as `none`, so every earlier
object occurs at a strictly earlier index. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

theorem exists_ordered_selection_slots {C : Type*} (A : ℕ → Set C)
    (hzero : A 0 = ∅) (hmono : Monotone A)
    (hsingle : ∀ n, (A (n + 1) \ A n).Subsingleton) :
    ∃ q : ℕ → Option C,
      (∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n) ∧
      (∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c) := by
  classical
  let q (n : ℕ) : Option C :=
    if h : (A (n + 1) \ A n).Nonempty then some h.choose else none
  have hq (n : ℕ) (c : C) : q n = some c ↔ c ∈ A (n + 1) \ A n := by
    dsimp only [q]
    split_ifs with h
    · constructor
      · intro hc
        have he := Option.some.inj hc
        exact he ▸ h.choose_spec
      · intro hc
        exact congrArg some (hsingle n h.choose_spec hc)
    · constructor
      · intro hc
        exact hc.elim
      · intro hc
        exact (h ⟨c, hc⟩).elim
  refine ⟨q, hq, ?_⟩
  intro n c
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      constructor
      · intro hc
        by_cases hprev : c ∈ A n
        · obtain ⟨k, hk, he⟩ := ih.mp hprev
          exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), he⟩
        · exact ⟨n, Nat.lt_succ_self n, (hq n c).mpr ⟨hc, hprev⟩⟩
      · rintro ⟨k, hk, he⟩
        by_cases hkn : k < n
        · exact hmono (Nat.le_succ n) (ih.mpr ⟨k, hkn, he⟩)
        · have hke : k = n := Nat.eq_of_lt_succ_of_not_lt hk hkn
          subst k
          exact ((hq n c).mp he).1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FreeLevelSections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique level traces away from the countable flags provide the null
circle sections required by the whole-image atomless test. -/

open Set MeasureTheory Filter

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

theorem unitAddCircle_volume_singleton (t : UnitAddCircle) : volume ({t} : Set UnitAddCircle) = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
  simpa only [Set.image_singleton] using
    (volume_addCircle_image_eq_zero (show volume ({x} : Set ℝ) = 0 from measure_singleton x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ZeroRealCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A zero coordinate occupies unused selection slots. Its new-level failure
event is contained in the single zero circle level, hence has zero measure. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem circleBandGraph_zero_subset (U : Set Sphere) :
    circleBandGraph U (fun _ => 0) ⊆ {p : Sphere × UnitAddCircle | p.2 = 0} := by
  rintro _ ⟨⟨x, t⟩, ht, rfl⟩
  obtain ⟨a, b, s, ha, hb, _, he⟩ := mem_intervalFiberHull_iff.mp ht
  have hza : a = 0 := clusterGraph_fiber_eq_of_continuousAt continuousAt_const ha
  have hzb : b = 0 := clusterGraph_fiber_eq_of_continuousAt continuousAt_const hb
  have ht0 : t = 0 := by simpa only [hza, hzb, mul_zero, add_zero] using he
  change (t : UnitAddCircle) = 0
  rw [ht0]
  rfl

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem zero_coordinate_compatibility (U F : Set Sphere) {I : Type*}
    (R : I → Set (Sphere × UnitAddCircle)) (n : ℕ) (labels : Fin n → I) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph U (fun _ => 0)) R labels) = 0 := by
  apply measure_mono_null (t := ({0} : Set UnitAddCircle) ×ˢ univ)
  · rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
    exact ⟨circleBandGraph_zero_subset U hx.2.1, mem_univ _⟩
  · simp only [Measure.prod_prod, unitAddCircle_volume_singleton, zero_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealTestLevelData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected real tests supply the actual level graphs and their
square-summable incidence weights for the next positive-law application. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace realTestLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
  (c : ℕ → UngatedRealTest d π EStar)

theorem level_relation (i : ℕ) :
    levelRelation (realTestLevelData d c).levels i =
      circleBandGraph d.quotientDomain (c i).coordinate.quotient := by
  ext p
  rfl

end realTestLevelData

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem OrderedLevelNullCompatibility.mono {H : ℕ → Set (UnitAddCircle × Sphere)}
    {F K : Set Sphere} (h : OrderedLevelNullCompatibility H K) (hFK : F ⊆ K) :
    OrderedLevelNullCompatibility H F := by
  intro j n labels hlt
  apply measure_mono_null _ (h j n labels hlt)
  rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
  exact ⟨(x, t, θ), ⟨hFK hx.1, hx.2⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TuplePairCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent tuples satisfy every ordered compatibility test and have
no equal levels carrying the same label across the two tuples. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundDiskDistance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distance weight in the Stokes estimate: it is smooth off
the closed round disk and equals the offset on a concentric circle. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_of_dist_gt (c z : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hz : r < dist z c) :
    infDist z (closedBall c r) = dist z c - r := by
  have hd : 0 < dist z c := hr.trans_lt hz
  have hne : dist z c ≠ 0 := hd.ne'
  let a := r / dist z c
  let p := c + a • (z - c)
  have ha : 0 ≤ a := div_nonneg hr hd.le
  have ha1 : a ≤ 1 := (div_le_one hd).mpr hz.le
  have hp : p ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    dsimp only [p]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    rw [← dist_eq_norm, div_mul_cancel₀ r hne]
  have hdist : dist z p = dist z c - r := by
    have heq : z - p = (1 - a) • (z - c) := by dsimp only [p]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ha1), ← dist_eq_norm]
    dsimp only [a]
    rw [sub_mul, one_mul, div_mul_cancel₀ r hne]
  apply le_antisymm
  · exact (infDist_le_dist_of_mem hp).trans_eq hdist
  · apply (le_infDist ⟨c, mem_closedBall_self hr⟩).mpr
    intro y hy
    have htri := dist_triangle z y c
    have hy' := mem_closedBall.mp hy
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundBoundaryStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative persistence of the fixed-source boundary integral under
uniform changes of the map and center-radius changes of the target disk. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_eq_max (c z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    infDist z (closedBall c r) = max (dist z c - r) 0 := by
  by_cases hz : dist z c ≤ r
  · rw [infDist_zero_of_mem (mem_closedBall.mpr hz), max_eq_right (sub_nonpos.mpr hz)]
  · rw [infDist_closedBall_of_dist_gt c z hr (lt_of_not_ge hz),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hz))]

 theorem round_disk_distance_change (c d z w : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |infDist z (closedBall c r) - infDist w (closedBall d s)| ≤
      dist z w + dist c d + |r - s| := by
  rw [infDist_closedBall_eq_max c z hr, infDist_closedBall_eq_max d w hs]
  calc
    _ ≤ max |(dist z c - r) - (dist w d - s)| |(0 : ℝ) - 0| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = |(dist z c - dist w d) - (r - s)| := by
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      congr 1
      ring
    _ ≤ |dist z c - dist w d| + |r - s| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (dist z c - dist w d) (-(r - s))
    _ ≤ dist z w + dist c d + |r - s| := by
      exact add_le_add (by simpa only [Real.dist_eq] using dist_dist_dist_le z c w d) le_rfl

 theorem roundDiskBoundaryPairing_stability
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (c d : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {e M : ℝ} (he : 0 ≤ e)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, dist (f t) (g t) ≤ e)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, |deriv v t| ≤ M) :
    |roundDiskBoundaryPairing f c r v - roundDiskBoundaryPairing g d s v| ≤
      (e + dist c d + |r - s|) * M := by
  have hdv : Continuous (deriv v) := hv.continuous_deriv (by simp)
  have hfi : IntervalIntegrable (fun t => infDist (f t) (closedBall c r) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hf).mul hdv |>.intervalIntegrable 0 1
  have hgi : IntervalIntegrable (fun t => infDist (g t) (closedBall d s) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hg).mul hdv |>.intervalIntegrable 0 1
  unfold roundDiskBoundaryPairing
  rw [← intervalIntegral.integral_sub hfi hgi]
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖infDist (f t) (closedBall c r) * deriv v t -
        infDist (g t) (closedBall d s) * deriv v t‖ ≤
      (e + dist c d + |r - s|) * M := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hweight := (round_disk_distance_change c d (f t) (g t) hr hs).trans
      (add_le_add (add_le_add (hclose t ht') le_rfl) le_rfl)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right hweight (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hderiv t ht') (by positivity))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun t ht => hb t (by simpa only [uIoc_of_le zero_le_one] using ht))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryPairNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open exclusion neighborhoods use the actual fixed-source boundary
functional. Its continuity is proved from the disk-distance estimate;
no stability or exclusion assertion is assumed. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

 theorem boundaryPairFunctional_lipschitz (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ∃ L : ℝ≥0, LipschitzWith L (boundaryPairFunctional v) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (hv.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  refine ⟨⟨3 * M, by positivity⟩, LipschitzWith.of_dist_le_mul ?_⟩
  intro p q
  have h := roundDiskBoundaryPairing_stability
    (p.1 ∘ projIcc 0 1 zero_le_one) (q.1 ∘ projIcc 0 1 zero_le_one)
    (p.1.continuous.comp continuous_projIcc) (q.1.continuous.comp continuous_projIcc)
    p.2.1 q.2.1 p.2.2.property q.2.2.property v hv (dist_nonneg (x := p.1) (y := q.1))
    (fun t _ => ContinuousMap.dist_apply_le_dist (projIcc 0 1 zero_le_one t))
    (fun t ht => by simpa only [Real.norm_eq_abs] using hM t ht)
  have hf : dist p.1 q.1 ≤ dist p q := by
    exact le_max_left _ _
  have hc : dist p.2.1 q.2.1 ≤ dist p q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hr : |(p.2.2 : ℝ) - q.2.2| ≤ dist p q := by
    change dist p.2.2 q.2.2 ≤ dist p q
    exact (le_max_right _ _).trans (le_max_right _ _)
  change |boundaryPairFunctional v p - boundaryPairFunctional v q| ≤ 3 * M * dist p q
  have hs : dist p.1 q.1 + dist p.2.1 q.2.1 + |(p.2.2 : ℝ) - q.2.2| ≤ 3 * dist p q := by
    linarith
  exact h.trans ((mul_le_mul_of_nonneg_right hs hM0).trans_eq (by ring))

 theorem continuous_boundaryPairFunctional (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : Continuous (boundaryPairFunctional v) :=
  (boundaryPairFunctional_lipschitz v hv).choose_spec.continuous

 theorem isOpen_boundaryExclusionSet (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (budget : ℝ) :
    IsOpen (boundaryExclusionSet v budget) :=
  isOpen_lt continuous_const (continuous_boundaryPairFunctional v hv).abs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_MixedMarkedModels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original marked ends in the common mixed model. These constructions
use the actual terminal fibers; no transport of dependent terminal types
from the real subfamily is necessary. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}

namespace MixedModelExhaustion

variable (M : MixedModelExhaustion d data retained O ε ρ)

 theorem eventually_markIndex (s : S) : ∀ᶠ n in atTop, (M.markIndex n s : S) = s :=
  M.real.eventually_markIndex s

 theorem core_model (n : ℕ) : M.real.cores n ⊆ openCompletedRegion (M.stages n).terminals.H := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (M.stages n).core_model (infty_mem_sphericalCore (M.stages n).core)
  | coe z =>
    apply (M.stages n).core_model
    apply (coe_mem_sphericalCore _ _).mpr
    apply interior_subset ((M.stages n).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ M.real.cores n
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp

 theorem eventually_sourceMark_captured (s : S) :
    ∀ᶠ n in atTop, d.sourceMark s ∈
      closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) := by
  have hinf : OnePoint.infty ∈ G :=
    M.real.core_source 0 (M.real.plane_core 0 (Or.inr rfl))
  have hq : d.sourceMark s ≠ OnePoint.infty := by
    intro he
    exact d.sourceMark_outside s (he ▸ hinf)
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hq
  filter_upwards [M.eventually_markIndex s] with n hn
  refine ⟨z, subset_closure ((M.stages n).terminals.fiber_subset (M.markIndex n s) ?_), hz⟩
  change π (z : Sphere) = σ (M.markIndex n s)
  rw [hn, hz]
  exact d.sourceMark_image s

end MixedModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_AssignedParameterLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized finite models retaining marked disk parameters

This assembles the published normal-family inputs, the constructed finite
terminal assignment, the actual smooth Jordan exhaustion, and marked-disk
trapping. Every marked limit is attached to its source component.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_normalized_limit_with_assigned_parameters
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ openCompletedRegion (T n))
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ openCompletedRegion (T n))
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    {G : Set Sphere} (hG : IsOpen G) (hGc : IsConnected G)
    (hGdef : ((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty} = G)
    {B : Type*} [Countable B] (q : B → Sphere) (hq : ∀ b, q b ∈ Gᶜ)
    (t : (n : ℕ) → B → I n)
    (hmark : ∀ b, ∀ᶠ n in atTop, q b ∈ closedTerminalCap (T n (t n b))) :
    ∃ (a : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
      (s : ℕ → ℕ) (F : ℂ → ℂ) (c : B → ℂ) (r : B → ℝ)
      (C : ℕ → SmoothJordanCore G) (J : (j : ℕ) → Fin (C j).count → ℂ ≃ₜ ℂ),
      StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (((↑) : ℂ → Sphere) ⁻¹' G) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) ∧
      (∀ b, ‖c b‖ ≤ 3 * R ∧ r b ∈ Icc 0 (3 * R)) ∧
      (∀ j, (C j).carrier ⊆ interior (C (j + 1)).carrier) ∧
      (⋃ j, interior (C j).carrier) = G ∧
      (∀ j i, extendAtInfinity F ''
        (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C j).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J j i))) ∧
      (∀ j, Pairwise (Disjoint on fun i => closure (jordanInterior (J j i)))) ∧
      (∀ j, (extendAtInfinity F '' (C j).carrier)ᶜ =
        ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J j i)) ∧
      (∀ j i, extendAtInfinity F '' (G ∩
        (((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk i))) =
        (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j i))) ∧
      (∀ b, ∃ (d : (j : ℕ) → Fin (C j).count) (p : Sphere), p ∈ (extendAtInfinity F '' G)ᶜ ∧
        connectedComponentIn Gᶜ (q b) = ⋂ j, closedTerminalCap ((C j).disk (d j)) ∧
        connectedComponentIn (extendAtInfinity F '' G)ᶜ p = ⋂ j, closedTerminalCap (J j (d j)) ∧
        ((↑) : ℂ → Sphere) '' closedBall (c b) (r b) ⊆
          connectedComponentIn (extendAtInfinity F '' G)ᶜ p ∧
        Tendsto (fun n => hausdorffDist
          (finiteCoord '' connectedComponentIn (V (s n))ᶜ ((a (s n)).point (t (s n) b)))
          (closedBall (c b) (r b))) atTop (𝓝 0)) ∧
      ∃ (cn : ℕ → B → ℂ) (rn : ℕ → B → ℝ),
        (∀ n b, ‖cn n b‖ ≤ 3 * R ∧ rn n b ∈ Icc 0 (3 * R)) ∧
        (∀ b, ∀ᶠ n in atTop, connectedComponentIn (V (s n))ᶜ ((a (s n)).point (t (s n) b)) =
          ((↑) : ℂ → Sphere) '' closedBall (cn n b) (rn n b)) ∧
        (∀ b, Tendsto (fun n => cn n b) atTop (𝓝 (c b))) ∧
        (∀ b, Tendsto (fun n => rn n b) atTop (𝓝 (r b))) := by
  classical
  have hex (n : ℕ) : Nonempty (TerminalComponentAssignment (T n) (f n) (V n)) :=
    exists_terminal_component_assignment hsard hschoenflies (T n) (hTd n)
      (heq n) (hV n).1 (hnorm n).1
  let a (n : ℕ) := Classical.choice (hex n)
  obtain ⟨s, F, c, r, hs, hl, hn, he, hb, hh, _, cn, rn, hbn, hdisks, hc, hr⟩ :=
    exists_normalized_marked_sphere_limit_with_parameters harea hmontel hhurwitz hzero
      f fi (fun n => openCompletedRegion (T n)) V heq hV hD hconn hmono hDQ hcore
      hR hsource hconf hnorm hext (fun n b => (a n).point (t n b))
      (fun b => Eventually.of_forall fun n => (a n).outside (t n b))
  rw [hGdef] at he
  have hchart : ((↑) : ℂ → Sphere) ⁻¹' G = ⋃ n, D n := by
    rw [← hGdef]
    ext z
    simp
  rw [← hchart] at hl
  have hinf : OnePoint.infty ∈ G := hGdef ▸ Or.inr rfl
  have hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G) := by
    intro z hz
    have hh' := continuousAt_finite_part_of_conformalAt (he.1 _ hz)
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using hh'.continuousWithinAt
  obtain ⟨C, J, hstrict, hcover, hJd, hJe, hboundary, hside⟩ :=
    exists_matched_jordan_exhaustion hsard hschoenflies hG hGc hinf
      he.1 he.bijOn.injOn hn.1
  refine ⟨a, s, F, c, r, C, J, hs, hl, hn, he, hb, hstrict, hcover, hboundary,
    hJd, hJe, hside, ?_, cn, rn, hbn, hdisks, hc, hr⟩
  intro b
  obtain ⟨d, p, hp, hsrc, htgt, _⟩ := corresponding_target_end_of_source
    hG he.1 he.bijOn.injOn C J hstrict hcover hJd hJe hboundary hside (hq b)
  have hqd (j : ℕ) : q b ∈ ((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk (d j)) := by
    apply (C j).omitted_point_mem_side (hq b)
    exact mem_iInter.mp (hsrc ▸ mem_connectedComponentIn (hq b)) j
  have hretain (j : ℕ) : ∀ᶠ n in atTop, (C j).carrier ⊆ openCompletedRegion (T (s n)) := by
    have hret := eventually_compact_subset_model hD hmono hDQ hsource (C j).isCompact
      ((C j).subset.trans (by rw [hGdef]))
    exact hs.tendsto_atTop hret
  refine ⟨d, p, hp, hsrc, htgt, ?_, hh b⟩
  exact marked_limit_subset_corresponding_component
    (fun n => T (s n)) (fun n => f (s n)) (fun n => fi (s n)) (fun n => V (s n))
    (fun n => a (s n)) (fun n => heq (s n)) (fun n => (hnorm (s n)).1)
    C d (fun j => J j (d j)) hretain (fun n => t (s n) b) hqd
    (hs.tendsto_atTop (hmark b)) F hF hl (fun j => hboundary j (d j)) htgt
    (fun n => (hbn n b).2.1) (hb b).2.1 (hc b) (hr b) (hdisks b)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_MixedAssignedLimit
attribute [-instance] _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned normal limits of the actual mixed stages, retaining the
convergent center and radius sequences used by Stokes. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.exists_assigned_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {S : Type*} [Countable S] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {C : Type*} [LinearOrder C] {data : C → MaskedCoordinateData G d.source π σ}
    {retained : ℕ → C} {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ) (hG : IsOpen G) (hconn : IsConnected G) :
    Nonempty (AssignedMixedModelLimit M) := by
  let _ : ∀ n, Fintype (M.stages n).indices := fun n => (M.stages n).indices_finite.fintype
  have hconf (n : ℕ) : IsConformalOn (M.stages n).model.forward (M.real.cores n) := by
    rw [M.same_forward n]
    exact M.real.core_conformal n
  obtain ⟨a, s, F, c, r, K, J, hs, hl, hn, he, hb, hnest, hcover, hboundary,
      hdisj, himage, hside, hmark, cn, rn, hbn, hdisks, hcl, hrl⟩ :=
    exists_normalized_limit_with_assigned_parameters harea hmontel hhurwitz hzero hsard hsch
      (fun n => (M.stages n).terminals.H) (fun n => (M.stages n).terminals.disjoint_closures)
      (fun n => (M.stages n).model.forward) (fun n => (M.stages n).model.inverse)
      (fun n => (M.stages n).model.domain) (fun n => (M.stages n).model.equivalence)
      (fun n => (M.stages n).model.circle_domain) M.real.plane_open M.real.plane_connected
      M.real.plane_monotone
      (fun n z hz => M.core_model n (M.real.plane_core n (Or.inl ⟨z, hz, rfl⟩)))
      (fun n => (hconf n).mono (fun _ hp => M.real.plane_core n (Or.inl hp)))
      M.real.radius_pos (fun n => (M.real.exterior_core n).trans (M.core_model n))
      (fun n => (hconf n).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.real.exterior_core n)))
      (fun n => (M.stages n).model.principal) M.real.exterior_plane hG hconn M.real.exhausts
      d.sourceMark d.sourceMark_outside M.markIndex M.eventually_sourceMark_captured
  exact ⟨⟨a, s, F, c, r, K, J, hs, hl, hn, he, hb, hnest, hcover, hboundary,
    hdisj, himage, hside, hmark, cn, rn, hbn, hdisks, hcl, hrl⟩⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RestrictedCoordinateMarks
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable selected family uses only countably many nonzero bands.
Restricting to these marks preserves the actual graph, physical function
and masks; every discarded marked fiber is already a singleton. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.countable_band_support
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) :
    {s | C.upper s - C.lower s ≠ 0}.Countable :=
  CircleDomainRigidity.countable_band_support C.width_summable

 theorem exists_common_countable_coordinate_marks
    {I S : Type*} [Countable I] {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : I → MaskedCoordinateData G U π σ) (B : Set S) (hB : B.Countable) :
    ∃ A : Set S, A.Countable ∧ B ⊆ A ∧
      (∀ i, (C i).singular ∈ A) ∧
      ∀ i s, (C i).upper s - (C i).lower s ≠ 0 → s ∈ A := by
  let A := B ∪ range (fun i => (C i).singular) ∪ ⋃ i, {s | (C i).upper s - (C i).lower s ≠ 0}
  refine ⟨A, (hB.union (countable_range _)).union
    (countable_iUnion fun i => (C i).countable_band_support), ?_, ?_, ?_⟩
  · intro s hs
    exact Or.inl (Or.inl hs)
  · intro i
    exact Or.inl (Or.inr (mem_range_self i))
  · intro i s hs
    exact Or.inr (mem_iUnion.mpr ⟨i, hs⟩)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLevelData
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual marked band widths supply the level weights for the next
endpoint-law construction. This uses the full dust as a temporary label
set; the common countable mark restriction is performed after selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

namespace maskedLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
    (fun x : d.dust => x.val))

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_21
theorem exists_countable_flags (B₀ : Set Sphere) (hB₀ : B₀.Countable)
    (hB₀B : B₀ ⊆ d.dust) :
    ∃ flags : Set Sphere, flags.Countable ∧ B₀ ⊆ flags ∧ flags ⊆ d.dust ∧
      (∀ i, ((C i).singular : Sphere) ∈ flags) ∧
      ∀ i, support ((maskedLevelData d π C).levelWeights i) ⊆ flags := by
  obtain ⟨A, hA, hBA, hs, hw⟩ := exists_common_countable_coordinate_marks C
    (Subtype.val ⁻¹' B₀) (hB₀.preimage Subtype.val_injective)
  refine ⟨Subtype.val '' A, hA.image _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hB₀B hx⟩, hBA hx, rfl⟩
  · rintro x ⟨s, _, rfl⟩
    exact s.property
  · intro i
    exact ⟨(C i).singular, hs i, rfl⟩
  · intro i x hx
    change (C i).dustWeight x ≠ 0 at hx
    by_cases hxB : x ∈ d.dust
    · refine ⟨⟨x, hxB⟩, hw i ⟨x, hxB⟩ ?_, rfl⟩
      intro he
      exact hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_left hxB, he,
        ENNReal.ofReal_zero])
    · exact (hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_right hxB])).elim

end maskedLevelData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectableMaskedCoordinate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected coordinate retains the precise level and flag data needed
for a later endpoint-law construction. Weighted coarea is proved for the
actual physical mean before placing it in this interface. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

theorem CompatibleWith.mono {c : SelectableMaskedCoordinate d π}
    {A B : Set (SelectableMaskedCoordinate d π)}
    (h : c.CompatibleWith B) (hAB : A ⊆ B) : c.CompatibleWith A :=
  ⟨fun a ha => h.1 a (hAB ha), fun n q hq => h.2 n q (fun i => hAB (hq i))⟩

end SelectableMaskedCoordinate

namespace SelectableMaskedCoordinate

 local instance localInst_r60a8cf_4 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_of_real
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (Q : PhysicalRealCoordinate d π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val))
    (hgraph : C.graph = circleBandGraph d.quotientDomain Q.quotient)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust) :
    ∃ c : SelectableMaskedCoordinate d π, c.coordinate = C ∧ flags ⊆ c.flags := by
  obtain ⟨Z, hZ, hfZ, hZB, hsing, hweights⟩ :=
    maskedLevelData.exists_countable_flags (fun _ => C) flags hflags hflagsB
  refine ⟨{
    coordinate := C
    flags := Z
    flags_countable := hZ
    flags_dust := hZB
    weight_support := hweights 0
    singular_marked := hsing 0
    domain_unique := ?_
    weighted := ?_ }, rfl, hfZ⟩
  · intro x hx a ha b hb
    rw [hgraph] at ha hb
    exact ((circleBandGraph_on_open hU Q.quotient_continuous hx).mp ha).symm.trans
      ((circleBandGraph_on_open hU Q.quotient_continuous hx).mp hb)
  · intro g hg henergy
    rw [hgraph]
    exact physicalRealCoordinate_ae_finite_weighted_levels hcoarea d hU hG π
      (fun x => (he x).symm) Q g hg henergy

end SelectableMaskedCoordinate

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_OrderedMaskedSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected mixed family retains the complete seed before the new
coordinates. Empty selection steps use the seed zero coordinate. The
resulting order has type omega plus omega, not a rearranged natural order. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem freeComponentFailure_mono_free {X T I J : Type*} [TopologicalSpace X]
    {F K : Set X} (hFK : F ⊆ K) (N : Set (X × T)) (R : I → Set (X × T)) (labels : J → I) :
    freeComponentFailure F N R labels ⊆ freeComponentFailure K N R labels := by
  rintro _ ⟨⟨x, t, θ⟩, h, rfl⟩
  exact ⟨(x, t, θ), ⟨hFK h.1, h.2⟩, rfl⟩

 theorem orderedSelectedCoordinates_compatibility
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (hzero : (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0))
    (hseed : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
          (fun k => (seed k).coordinate.graph) labels) = 0)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (A : ℕ → Set T) (q : ℕ → Option T)
    (hq : ∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n)
    (hpref : ∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c)
    (hnew : ∀ n c, c ∈ A (n + 1) \ A n →
      (data c).CompatibleWith (range seed ∪ data '' A n)) :
    let D := orderedSelectedCoordinates seed data q
    ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0 := by
  let D := orderedSelectedCoordinates seed data q
  have hseedflags : (⋃ k, (seed k).flags) ⊆ ⋃ k, (D k).flags := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨Sum.inlₗ k, hk⟩
  dsimp only
  intro j n labels hlt
  change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
    (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
      (fun k => (D k).coordinate.graph) labels) = 0
  induction j using Lex.rec with
  | h j =>
    cases j with
    | inl j =>
      let inds (i : Fin n) : ℕ := (ofLex (labels i)).elim id (fun _ => 0)
      have hind (i : Fin n) : inds i < j ∧ D (labels i) = seed (inds i) := by
        cases h : ofLex (labels i) with
        | inl k =>
          have hlabel : labels i = Sum.inlₗ k := by
            simpa only [toLex_ofLex] using congrArg toLex h
          have hk : k < j := Sum.Lex.inl_lt_inl_iff.mp (by simpa only [hlabel] using hlt i)
          exact ⟨by simpa only [inds, h, Sum.elim_inl, id_eq] using hk, by simp only [D, orderedSelectedCoordinates, inds, hlabel, ofLex_toLex, Sum.elim_inl, id_eq]⟩
        | inr k =>
          have hlabel : labels i = Sum.inrₗ k := by
            simpa only [toLex_ofLex] using congrArg toLex h
          exact (Sum.Lex.not_inr_lt_inl (by simpa only [hlabel] using hlt i)).elim
      have hz := hseed j n inds (fun i => (hind i).1)
      rw [UngatedRealTest.freeComponentFailure_congr_selected
        (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
        (fun k => (seed k).coordinate.graph) (fun k => (D k).coordinate.graph)
        inds labels (fun i => congrArg (fun c => c.coordinate.graph) (hind i).2.symm)] at hz
      exact measure_mono_null (freeComponentFailure_mono_free
        (show d.dust \ (⋃ k, (D k).flags) ⊆ d.dust \ (⋃ k, (seed k).flags) from
          fun _ hx => ⟨hx.1, fun hm => hx.2 (hseedflags hm)⟩) _ _ labels) hz
    | inr j =>
      cases hj : q j with
      | none =>
        change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (D k).flags)
            ((q j).elim (seed 0) data).coordinate.graph (fun k => (D k).coordinate.graph) labels) = 0
        rw [hj, Option.elim_none, hzero]
        exact zero_coordinate_compatibility _ _ _ n labels
      | some b =>
        have hb := hnew j b ((hq j b).mp hj)
        have hprev (i : Fin n) : D (labels i) ∈ range seed ∪ data '' A j := by
          cases hi : ofLex (labels i) with
          | inl k =>
            have hlabel : labels i = Sum.inlₗ k := by
              simpa only [toLex_ofLex] using congrArg toLex hi
            exact Or.inl ⟨k, by simp only [D, orderedSelectedCoordinates, hlabel, ofLex_toLex]⟩
          | inr k =>
            have hlabel : labels i = Sum.inrₗ k := by
              simpa only [toLex_ofLex] using congrArg toLex hi
            have hk : k < j := Sum.Lex.inr_lt_inr_iff.mp (by simpa only [hlabel] using hlt i)
            cases hqk : q k with
            | none =>
              apply Or.inl
              exact ⟨0, by simp only [D, orderedSelectedCoordinates, hlabel, ofLex_toLex,
                hqk, Option.elim_none]⟩
            | some a =>
              apply Or.inr
              refine ⟨a, (hpref j a).mpr ⟨k, hk, hqk⟩, ?_⟩
              simp only [D, orderedSelectedCoordinates, hlabel, ofLex_toLex, hqk, Option.elim_some]
        have hz := hb.2 n (fun i => D (labels i)) hprev
        have hbf : (data b).flags ⊆ ⋃ k, (D k).flags := by
          intro x hx
          apply mem_iUnion.mpr
          refine ⟨Sum.inrₗ j, ?_⟩
          simpa only [D, orderedSelectedCoordinates, ofLex_toLex, hj, Option.elim_some] using hx
        change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (D k).flags)
            ((q j).elim (seed 0) data).coordinate.graph (fun k => (D k).coordinate.graph) labels) = 0
        rw [hj, Option.elim_some]
        apply measure_mono_null (freeComponentFailure_mono_free
          (show d.dust \ (⋃ k, (D k).flags) ⊆ d.dust \ (data b).flags from
            fun _ hx => ⟨hx.1, fun hm => hx.2 (hbf hm)⟩) _ _ labels)
        exact hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectableRealFamily
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The already selected real barriers become the seed of mixed selection.
All their physical functions and band endpoints are kept, while the temporary
label set is the entire dust. Compatibility is kept on the original free set. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_selectable_real_family
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (p : d.dust) (EStar : Set Sphere)
    (c : ℕ → UngatedRealTest d π EStar)
    (hc0 : (c 0).coordinate.quotient = fun _ => 0)
    (M : Set Sphere) (hM : M.Countable) (hMB : M ⊆ d.dust)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M)) :
    ∃ seed : ℕ → SelectableMaskedCoordinate d π,
      (∀ i, M ⊆ (seed i).flags) ∧
      (∀ i, (seed i).coordinate.graph = circleBandGraph d.quotientDomain (c i).coordinate.quotient) ∧
      (∀ i x, (seed i).coordinate.physical x = ((c i).coordinate.physical x : UnitAddCircle)) ∧
      (∀ i s, (seed i).coordinate.lower s = liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] s.val) ∧
        (seed i).coordinate.upper s = limsup (c i).coordinate.quotient (𝓝[d.quotientDomain] s.val)) ∧
      (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0) ∧
      (∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
            (fun k => (seed k).coordinate.graph) labels) = 0) ∧
      Nonempty (RealCoordinateSubfamily (fun i => (seed i).coordinate) id) := by
  have hempty (j n : ℕ) (labels : Fin n → ℕ) (_ : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ d.dust)
          (circleBandGraph d.quotientDomain (c j).coordinate.quotient)
          (fun k => circleBandGraph d.quotientDomain (c k).coordinate.quotient) labels) = 0 := by
    simp [freeComponentFailure]
  let F := realCoordinateFamily d hU hdense π he hB (fun i => (c i).coordinate)
    d.dust (Subset.refl _) (fun i => (c i).weight) (fun i => (c i).weight_finite)
    (fun _ _ hx _ => hx) (fun i => (c i).band_bound) hempty
  let C (i : ℕ) : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val) := F.maskedCoordinate hG p i
  have hex (i : ℕ) : ∃ q : SelectableMaskedCoordinate d π,
      q.coordinate = C i ∧ M ⊆ q.flags :=
    SelectableMaskedCoordinate.exists_of_real hcoarea d hU hG π he (c i).coordinate
      (C i) rfl M hM hMB
  let seed (i : ℕ) := (hex i).choose
  have hC (i : ℕ) : (seed i).coordinate = C i := (hex i).choose_spec.1
  have hmark (i : ℕ) : M ⊆ (seed i).flags := (hex i).choose_spec.2
  have hgraph (i : ℕ) : (seed i).coordinate.graph =
      circleBandGraph d.quotientDomain (c i).coordinate.quotient := by rw [hC]; rfl
  refine ⟨seed, hmark, hgraph, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    rw [hC]
    rfl
  · intro i s
    rw [hC]
    exact ⟨rfl, rfl⟩
  · rw [hgraph, hc0]
  · intro j n labels hlt
    have hz := hcompat j n labels hlt
    have hrel : levelRelation (realTestLevelData d c).levels =
        fun i => (seed i).coordinate.graph := by
      funext i
      rw [realTestLevelData.level_relation, hgraph]
    rw [hrel] at hz
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ labels) hz
    intro x hx
    exact ⟨hx.1, fun hm => hx.2 (mem_iUnion.mpr ⟨0, hmark 0 hm⟩)⟩
  · have heq : (fun i => (seed i).coordinate) = C := funext hC
    rw [heq]
    exact ⟨F.realSubfamily hG p⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PresentedRealSeed
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real seed carries the exact presentations needed by the later mixed selection. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_presented_real_seed
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (p : d.dust) (EStar : Set Sphere)
    (hinfty : π OnePoint.infty ∈ interior EStar)
    (c : ℕ → UngatedRealTest d π EStar)
    (hc0 : (c 0).coordinate.quotient = fun _ => 0)
    (M : Set Sphere) (hM : M.Countable) (hMB : M ⊆ d.dust)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M)) :
    ∃ seed : ℕ → SelectableMaskedCoordinate d π,
      (∀ i, M ⊆ (seed i).flags) ∧
      (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0) ∧
      (∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
            (fun k => (seed k).coordinate.graph) labels) = 0) ∧
      ∃ P : ∀ i, RealCoordinatePresentation d π (seed i).coordinate,
        ∀ i, (P i).coordinate = (c i).coordinate := by
  obtain ⟨seed, hflags, hgraph, hphysical, hbands, hzero, hcomp, ⟨hR⟩⟩ :=
    exists_selectable_real_family hcoarea d hU hG hdense π he hB p EStar c hc0 M hM hMB hcompat
  refine ⟨seed, hflags, hzero, hcomp, ?_⟩
  let P (i : ℕ) : RealCoordinatePresentation d π (seed i).coordinate :=
    (c i).levelPresentation hπ hinfty (seed i).coordinate (hgraph i) ?_
      (fun x => (hphysical i x).symm) ?_
  · refine ⟨P, fun _ => rfl⟩
  · exact hR.full_mask i
  · intro s
    rw [(hbands i s).1, (hbands i s).2]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SeededGradedRealSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graded selection retaining a prescribed family of real tests. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace GradedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

theorem AllowedWith.mono {S : Set (UngatedRealTest d π EStar)}
    {A B : Set (GradedRealTest d π EStar)} {c : GradedRealTest d π EStar}
    (h : AllowedWith S B c) (hAB : A ⊆ B) : AllowedWith S A c :=
  UngatedRealTest.CompatibleWith.mono h (union_subset_union_right _ (image_mono hAB))

theorem exists_countable_selection_with (S : Set (UngatedRealTest d π EStar)) :
    ∃ A : ℕ → Set (GradedRealTest d π EStar),
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧
      (∀ n, (A (n + 1) \ A n).Subsingleton) ∧
      (∀ n c, c ∈ A (n + 1) \ A n → AllowedWith S (A n) c) ∧
      (⋃ n, A n).Countable ∧
      ∀ c, AllowedWith S (⋃ n, A n) c → ∀ x ∈ c.toUngatedRealTest.openEnds,
        ∃ e ∈ ⋃ n, A n, e.grade = c.grade ∧ x ∈ e.toUngatedRealTest.openEnds := by
  apply exists_countable_graded_open_selection
    (fun c : GradedRealTest d π EStar => c.toUngatedRealTest.openEnds)
    (fun c => c.toUngatedRealTest.open_openEnds) grade (AllowedWith S)
  intro A B hAB c hc
  exact ⟨c, hc.mono hAB, rfl, Subset.rfl⟩

end GradedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteSeededRealFamily
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate a prescribed finite prefix before the greedily selected tests,
retaining the actual functions and their ordered level compatibility. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

theorem finiteSeededRealFamily_prefix
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (q : ℕ → Option (GradedRealTest d π EStar)) (i : Fin (m + 1)) :
    finiteSeededRealFamily seed q i.val = seed i := by
  simp only [finiteSeededRealFamily, dite_eq_left i.isLt]

theorem finiteSeededRealFamily_tail
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (q : ℕ → Option (GradedRealTest d π EStar)) (n : ℕ) :
    finiteSeededRealFamily seed q (n + (m + 1)) =
      (q n).elim (seed 0) GradedRealTest.toUngatedRealTest := by
  simp only [finiteSeededRealFamily, show ¬n + (m + 1) < m + 1 by omega,
    dite_false, Nat.add_sub_cancel]

theorem exists_finite_seeded_real_family
    (d : PathCodeData Sphere Sphere) {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (hzero : seed 0 = UngatedRealTest.zeroTest d π EStar)
    (hseed : ∀ (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1)),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (seed i).exclusions)
          (circleBandGraph d.quotientDomain (seed j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (seed i).coordinate.quotient) labels) = 0)
    (A : ℕ → Set (GradedRealTest d π EStar)) (hA0 : A 0 = ∅)
    (hmono : Monotone A) (hsingle : ∀ n, (A (n + 1) \ A n).Subsingleton)
    (hnew : ∀ n b, b ∈ A (n + 1) \ A n →
      GradedRealTest.AllowedWith (range seed) (A n) b) :
    ∃ (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere),
      M.Countable ∧ M ⊆ d.dust ∧ c 0 = UngatedRealTest.zeroTest d π EStar ∧
      (∀ i : Fin (m + 1), c i.val = seed i) ∧
      (∀ i, (c i).exclusions ∩ d.dust ⊆ M) ∧
      (∀ b ∈ ⋃ n, A n, ∃ k, c k = b.toUngatedRealTest) ∧
      range c ⊆ range seed ∪ GradedRealTest.toUngatedRealTest '' (⋃ n, A n) ∧
      OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M) := by
  classical
  obtain ⟨q, hq, hpref⟩ := exists_ordered_selection_slots A hA0 hmono hsingle
  let c := finiteSeededRealFamily seed q
  have hpre (i : Fin (m + 1)) : c i.val = seed i := finiteSeededRealFamily_prefix seed q i
  have htail (n : ℕ) : c (n + (m + 1)) =
      (q n).elim (seed 0) GradedRealTest.toUngatedRealTest :=
    finiteSeededRealFamily_tail seed q n
  let M : Set Sphere := (⋃ n, (c n).exclusions) ∩ d.dust
  have hM (i : ℕ) : (c i).exclusions ∩ d.dust ⊆ M :=
    fun _ hx => ⟨mem_iUnion.mpr ⟨i, hx.1⟩, hx.2⟩
  have hprevious {j i : ℕ} (hi : i < j + (m + 1)) :
      c i ∈ range seed ∪ GradedRealTest.toUngatedRealTest '' A j := by
    by_cases hip : i < m + 1
    · exact Or.inl ⟨⟨i, hip⟩, (hpre ⟨i, hip⟩).symm⟩
    · have hie : i = (i - (m + 1)) + (m + 1) := by omega
      rw [hie, htail]
      cases he : q (i - (m + 1)) with
      | none => exact Or.inl ⟨0, rfl⟩
      | some b =>
        exact Or.inr ⟨b, (hpref j b).mpr ⟨i - (m + 1), by omega, he⟩, rfl⟩
  refine ⟨c, M, (countable_iUnion fun i => (c i).exclusions_countable).mono
    inter_subset_left, inter_subset_right, (hpre 0).trans hzero, hpre, hM, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    obtain ⟨k, _, hk⟩ := (hpref n b).mp hn
    exact ⟨k + (m + 1), (htail k).trans (by rw [hk]; rfl)⟩
  · rintro a ⟨i, rfl⟩
    have hp := hprevious (j := i) (i := i) (by omega)
    exact (union_subset_union_right _ (image_mono (subset_iUnion A i))) hp
  · intro j n labels hlt
    simp only [realTestLevelData.level_relation]
    by_cases hj : j < m + 1
    · let labels' (i : Fin n) : Fin (m + 1) := ⟨labels i, lt_trans (hlt i) hj⟩
      have hz := hseed ⟨j, hj⟩ n labels' (fun i => hlt i)
      rw [UngatedRealTest.freeComponentFailure_congr_selected
        (d.dust \ ⋃ i, (seed i).exclusions)
        (circleBandGraph d.quotientDomain (seed ⟨j, hj⟩).coordinate.quotient)
        (fun i : Fin (m + 1) => circleBandGraph d.quotientDomain (seed i).coordinate.quotient)
        (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient)
        labels' labels (fun i => congrArg (fun a : UngatedRealTest d π EStar =>
          circleBandGraph d.quotientDomain a.coordinate.quotient) (hpre (labels' i)).symm)] at hz
      rw [hpre ⟨j, hj⟩]
      apply measure_mono_null _ hz
      rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
      refine ⟨(x, t, θ), ⟨⟨hx.1.1, ?_⟩, hx.2⟩, rfl⟩
      intro hxseed
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxseed
      exact hx.1.2 (hM i.val ⟨(hpre i).symm ▸ hi, hx.1.1⟩)
    · have hjr : j = (j - (m + 1)) + (m + 1) := by omega
      have hcj := htail (j - (m + 1))
      rw [← hjr] at hcj
      cases he : q (j - (m + 1)) with
      | none =>
        rw [he] at hcj
        rw [hcj, hzero]
        exact zero_coordinate_compatibility d.quotientDomain (d.dust \ M)
          (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) n labels
      | some b =>
        rw [he] at hcj
        have hb := hnew (j - (m + 1)) b ((hq _ b).mp he)
        have hz := hb.2 n (fun i => c (labels i)) (fun i => hprevious (by have hi := hlt i; omega))
        rw [UngatedRealTest.freeComponentFailure_congr_selected
          (d.dust \ b.exclusions) (circleBandGraph d.quotientDomain b.coordinate.quotient)
          (fun i : Fin n => circleBandGraph d.quotientDomain (c (labels i)).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient)
          id labels (fun _ => rfl)] at hz
        rw [hcj]
        apply measure_mono_null _ hz
        rintro _ ⟨⟨x, t, θ⟩, hx, rfl⟩
        exact ⟨(x, t, θ), ⟨⟨hx.1.1, fun h => hx.1.2
          (hM j ⟨hcj.symm ▸ h, hx.1.1⟩)⟩, hx.2⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SeededSmallRealTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual graded selection gives one countable family, with only
countably many marked or uncovered ends across all accuracies. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r60a8cf_5 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_countable_small_real_tests_with_seed
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (_hBimage : d.dust = π '' d.physicalDomainᶜ)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : d.dust, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : d.dust, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {m : ℕ} (seed : Fin (m + 1) → UngatedRealTest d π EStar)
    (hzero : seed 0 = UngatedRealTest.zeroTest d π EStar)
    (hseed : ∀ (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1)),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (seed i).exclusions)
          (circleBandGraph d.quotientDomain (seed j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (seed i).coordinate.quotient) labels) = 0)
    : ∃ (A : Set (GradedRealTest d π EStar)) (c : ℕ → UngatedRealTest d π EStar)
        (M : Set Sphere), M.Countable ∧ M ⊆ d.dust ∧ c 0 = UngatedRealTest.zeroTest d π EStar ∧
      (∀ i : Fin (m + 1), c i.val = seed i) ∧
      (∀ i, (c i).exclusions ∩ d.dust ⊆ M) ∧
      (∀ b ∈ A, ∃ i, c i = b.toUngatedRealTest) ∧
      OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M) ∧
      ∀ p ∈ d.dust \ M, ∀ k, ∃ b ∈ A, b.grade = k ∧ p ∈ b.region := by
  classical
  obtain ⟨A, hA0, _, hmono, hsingle, hnew, _, hcover⟩ :=
    GradedRealTest.exists_countable_selection_with (range seed)
  obtain ⟨c, M, hMc, hMB, hc0, hprefix, hM, hselected, _, hcompat⟩ :=
    exists_finite_seeded_real_family d seed hzero hseed A hA0 hmono hsingle hnew
  have hselected' : range seed ∪ GradedRealTest.toUngatedRealTest '' (⋃ n, A n) ⊆
      range c := by
    intro a ha
    rcases ha with ⟨i, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨i.val, hprefix i⟩
    · exact hselected b hb
  have hcover' : ∀ b : GradedRealTest d π EStar,
      b.toUngatedRealTest.CompatibleWith (range c) →
      ∀ x ∈ b.toUngatedRealTest.openEnds,
        ∃ a ∈ ⋃ n, A n, a.grade = b.grade ∧ x ∈ a.toUngatedRealTest.openEnds := by
    intro b hb
    exact hcover b (hb.mono hselected')
  have hcount (k : ℕ) : (uncoveredTestEnds (⋃ n, A n) k).Countable := by
    apply countable_uncovered_test_endpoints_of_range hcross hcoarea hLusin hsard hsch
      d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad hinf
      EStar hE hEU hEStar hEStarE hinfE (uncoveredTestEnds (⋃ n, A n) k)
      (fun _ hp => hp.1) (fun p => D ⟨p.val, p.property.1⟩)
      (fun p => hnest ⟨p.val, p.property.1⟩)
      (fun p => hshrink ⟨p.val, p.property.1⟩)
      (fun p => hED ⟨p.val, p.property.1⟩) hfiber harcs
      (⋃ n, A n) k (fun _ hp => hp) c M hcover' hMc hMB hM hcompat
      C hC hderiv hstandard hpath ω hω hωsum hdual hlift
  let N : Set Sphere := M ∪ ⋃ k, uncoveredTestEnds (⋃ n, A n) k
  have hMN : M ⊆ N := subset_union_left
  have hNB : N ⊆ d.dust := by
    intro p hp
    rcases hp with hp | hp
    · exact hMB hp
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hp
      exact hk.1
  refine ⟨⋃ n, A n, c, N, hMc.union (countable_iUnion hcount), hNB, hc0, hprefix,
    (fun i => (hM i).trans hMN), hselected, hcompat.mono ?_, ?_⟩
  · intro p hp
    exact ⟨hp.1, fun h => hp.2 (hMN h)⟩
  · intro p hp k
    by_contra h
    apply hp.2
    right
    apply mem_iUnion.mpr
    refine ⟨k, hp.1, ?_⟩
    intro b hb hbk hpb
    exact h ⟨b, hb, hbk, hpb⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MapDiskExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-circuit exclusions in the compact-open space of maps and disks.
The circuit restriction is continuous, so these are the open sets used by
countable selection, not just open sets of boundary traces. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem mapDiskData_secondCountable {G : Set Sphere} (hG : IsOpen G) :
    SecondCountableTopology (MapDiskData G) := by
  let : LocallyCompactSpace (FiniteSource G) :=
    (hG.preimage OnePoint.continuous_coe).locallyCompactSpace
  infer_instance

 theorem continuous_circuitRestriction {G : Set Sphere} (γ : C(PathTime, FiniteSource G)) :
    Continuous (circuitRestriction γ) :=
  ((ContinuousMap.continuous_precomp γ).comp continuous_fst).prodMk continuous_snd

 theorem isOpen_mapDiskExclusion {G : Set Sphere} (γ : C(PathTime, FiniteSource G))
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (budget : ℝ) :
    IsOpen (mapDiskExclusion γ v budget) :=
  (isOpen_boundaryExclusionSet v hv budget).preimage (continuous_circuitRestriction γ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SeededMaskedSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable open selection retains every seed and the actual order of
later masked coordinates. Its cover assertion concerns every candidate
compatible with the final list; geometric availability is proved separately. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem seededMaskedAllowed_mono {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π) {T : Type*}
    (data : T → SelectableMaskedCoordinate d π) {A B : Set T} (hAB : A ⊆ B)
    {c : T} (h : seededMaskedAllowed seed data B c) : seededMaskedAllowed seed data A c :=
  h.mono (union_subset_union (Subset.refl _) (image_mono hAB))

 theorem exists_seeded_masked_selection
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (hzero : (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0))
    (hseed : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
          (fun k => (seed k).coordinate.graph) labels) = 0)
    {T X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (data : T → SelectableMaskedCoordinate d π) (V : T → Set X) (hV : ∀ c, IsOpen (V c)) :
    ∃ (A : ℕ → Set T) (q : ℕ → Option T),
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧ (⋃ n, A n).Countable ∧
      (∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n) ∧
      (∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c) ∧
      (∀ c, seededMaskedAllowed seed data (⋃ n, A n) c →
        V c ⊆ ⋃ t ∈ ⋃ n, A n, V t) ∧
      (∀ c ∈ ⋃ n, A n, ∃ j : ℕ ⊕ₗ ℕ, orderedSelectedCoordinates seed data q j = data c) ∧
      let D := orderedSelectedCoordinates seed data q
      ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
            (fun k => (D k).coordinate.graph) labels) = 0 := by
  obtain ⟨A, hA0, hfin, hmono, hsingle, hnew, hcount, hcover⟩ :=
    exists_countable_open_selection V hV (seededMaskedAllowed seed data)
      (fun hAB c hc => ⟨c, seededMaskedAllowed_mono seed data hAB hc, Subset.rfl⟩)
  obtain ⟨q, hq, hpref⟩ := exists_ordered_selection_slots A hA0 hmono hsingle
  refine ⟨A, q, hA0, hfin, hmono, hcount, hq, hpref, hcover, ?_, ?_⟩
  · intro c hc
    obtain ⟨n, hn⟩ := mem_iUnion.mp hc
    obtain ⟨k, _, hk⟩ := (hpref n c).mp hn
    refine ⟨Sum.inrₗ k, ?_⟩
    simp only [orderedSelectedCoordinates, ofLex_toLex, hk, Option.elim_some]
  · exact orderedSelectedCoordinates_compatibility seed hzero hseed data A q hq hpref hnew

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExactRealSelections
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerate the actual real choices without repetition, preserving their chosen lifts and
exact band widths. Infinitely many seed labels provide the required infinite index set. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem infinite_real_presentations_of_seed
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {L : Type*}
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (presentation : ∀ l, SelectedLevelPresentation hsch d π (C l))
    (seed : ℕ → L) (hinj : Injective seed)
    (hseed : ∀ n, ∃ r, presentation (seed n) = Sum.inl r) :
    {l | ∃ r, presentation l = Sum.inl r}.Infinite := by
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact hseed n

 theorem exists_injective_real_presentations
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {L : Type*} [Countable L]
    (C : L → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (presentation : ∀ l, SelectedLevelPresentation hsch d π (C l))
    (hinfinite : {l | ∃ r, presentation l = Sum.inl r}.Infinite) :
    ∃ ι : ℕ → L, Injective ι ∧
      ∃ R : ∀ n, RealCoordinatePresentation d π (C (ι n)),
        (∀ n, presentation (ι n) = Sum.inl (R n)) ∧
        ∀ l (r : RealCoordinatePresentation d π (C l)), presentation l = Sum.inl r →
          ∃ n, ι n = l ∧ (R n).coordinate.physical = r.coordinate.physical ∧
            (R n).coordinate.quotient = r.coordinate.quotient := by
  let S : Set L := {l | ∃ r, presentation l = Sum.inl r}
  let : Infinite S := hinfinite.to_subtype
  let : Denumerable S := Classical.choice (nonempty_denumerable S)
  let e : ℕ ≃ S := (Denumerable.eqv S).symm
  let ι : ℕ → L := fun n => (e n).val
  have hR (n : ℕ) : ∃ r, presentation (ι n) = Sum.inl r := (e n).property
  let R (n : ℕ) := Classical.choose (hR n)
  have hp (n : ℕ) : presentation (ι n) = Sum.inl (R n) := Classical.choose_spec (hR n)
  refine ⟨ι, Subtype.val_injective.comp e.injective, R, hp, ?_⟩
  intro l r hr
  obtain ⟨n, hn⟩ := e.surjective ⟨l, r, hr⟩
  have hl : ι n = l := congrArg Subtype.val hn
  subst l
  have heq : R n = r := Sum.inl.inj ((hp n).symm.trans hr)
  exact ⟨n, rfl, congrArg (fun q => q.coordinate.physical) heq,
    congrArg (fun q => q.coordinate.quotient) heq⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SeededLevelPresentations
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carry the actual real or mean presentation through the ordered selection, including
unused slots filled by the original zero coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem orderedSelectedPresentations_seed
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) (n : ℕ) :
    orderedSelectedPresentations seed seedPresentation data presentation q (Sum.inlₗ n) =
      Sum.inl (seedPresentation n) := rfl

 theorem orderedSelectedPresentations_infinite_real
    {hsch : PlanarSchoenflies} {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (seed : ℕ → SelectableMaskedCoordinate d π)
    (seedPresentation : ∀ n, RealCoordinatePresentation d π (seed n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate d π)
    (presentation : ∀ t, SelectedLevelPresentation hsch d π (data t).coordinate)
    (q : ℕ → Option T) :
    {j | ∃ r, orderedSelectedPresentations seed seedPresentation data presentation q j =
      Sum.inl r}.Infinite := by
  refine infinite_real_presentations_of_seed
    (fun j => (orderedSelectedCoordinates seed data q j).coordinate)
    (orderedSelectedPresentations seed seedPresentation data presentation q)
    (fun n => (Sum.inlₗ n : ℕ ⊕ₗ ℕ))
    (fun _ _ hij => Sum.inl.inj (congrArg ofLex hij)) ?_
  intro n
  exact ⟨seedPresentation n, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PresentedMixedExhaustion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the common mixed exhaustion from its actual real subfamily.
Only physical functions and terminal widths must agree; auxiliary chart choices and
dummy singular labels need not be identical as dependent structures. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}

 theorem exists_mixed_model_exhaustion_of_real_subfamily
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (hG : IsOpen G) (hconn : IsConnected G) (hinfty : OnePoint.infty ∈ G)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) [Countable S]
    (d : CountableRealCoordinates G π σ) (hUB : d.source ⊆ (π '' Gᶜ)ᶜ)
    {C : Type*} [LinearOrder C] [Countable C]
    (data : C → MaskedCoordinateData G d.source π σ)
    (retained : ℕ → C) (hinj : Injective retained)
    (R₀ : RealCoordinateSubfamily data retained)
    (hphysical : ∀ j, R₀.physical j = d.physical j)
    (hwidth₀ : ∀ j s, (data (retained j)).upper s - (data (retained j)).lower s =
      d.upper j s - d.lower j s)
    (hcompat : ∀ (c : C) (k : ℕ) (labels : Fin k → C), (∀ i, labels i < c) →
      (volume.prod (Measure.pi (fun _ : Fin k => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (data c).graph
          (fun c => (data c).graph) labels) = 0)
    (O : ℕ → S → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (σ s))
    (ε ρ : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hρ : ∀ n, 0 < ρ n) :
    Nonempty (MixedModelExhaustion d data retained O ε ρ) := by
  classical
  let R : RealCoordinateSubfamily data retained := {
    R₀ with
    physical := d.physical
    smooth := d.physical_smooth
    energy := d.physical_energy
    pullback := fun j x hx => by simpa only [hphysical] using R₀.pullback j x hx
    projection := fun j x => by simpa only [hphysical] using R₀.projection j x }
  obtain ⟨r, D, K, hrpos, hDo, hDc, hDm, _, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinfty
  obtain ⟨size, label, slot, Flag, hslot, hretained, hcoords, hFlag, hFlagm, hFlagne, Q, hmarks⟩ :=
    exists_countable_mixed_stages hsard hsch hcompact hfinite hG hinfty
      π hπ hclosed hsurj hr hTD hUB d.source_map σ d.labels_injective d.labels_dust
      (fun s hs => hUB hs (d.labels_dust s)) data retained hinj R hcompat
      (fun n => realChartDomain (K n)) (fun n => isClosed_realChartDomain (hK n).1.isClosed)
      (fun n => preimage_mono (hK n).2) O hO ε ρ hε hρ
  let T (n : ℕ) := (Q n).realStage hG
    (fun j => by simpa only [hretained] using R.full_mask j)
    (fun j => d.physical_smooth j) (fun j => d.physical_energy j)
    (fun j x => by simpa only [hretained] using R.projection j x)
  have hwidth (n : ℕ) (j : Fin (n + 1)) (s : S) :
      (data (label n (slot n j))).upper s - (data (label n (slot n j))).lower s =
        d.upper j s - d.lower j s := by
    rw [hretained]
    exact hwidth₀ j s
  let T' (n : ℕ) : d.Stage n (Flag n) (O n) (realChartDomain (K n)) (ε n) :=
    (T n).withBands (fun j => d.lower j) (fun j => d.upper j) (hwidth n)
  have hplane (n : ℕ) : ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ K n :=
    (hDK n).trans interior_subset
  let M : RealModelExhaustion d O ε := {
    radius := 2 * r
    radius_pos := mul_pos (by norm_num) hrpos
    plane := D
    plane_open := hDo
    plane_connected := hDc
    plane_monotone := hDm
    cores := K
    core_compact := fun n => (hK n).1
    core_source := fun n => (hK n).2
    plane_core := hplane
    exhausts := by simpa only [image_iUnion, iUnion_union, iUnion_const] using hcover
    exterior_core := by
      intro n p hp
      apply hplane n
      cases p using OnePoint.rec with
      | infty => exact Or.inr rfl
      | coe z =>
        refine Or.inl ⟨z, hDm (Nat.zero_le n) (hext ?_), rfl⟩
        change 2 * r ≤ ‖z‖
        simpa only [mem_compl_iff, OnePoint.coe_injective.mem_set_image,
          mem_ball, dist_zero_right, not_lt] using hp
    exterior_plane := by
      intro z hz
      apply hext
      change 2 * r ≤ ‖z‖
      change 2 * (2 * r) ≤ ‖z‖ at hz
      linarith
    flags := Flag
    flags_finite := hFlag
    flags_monotone := hFlagm
    stages := T'
    indices_nonempty := fun n _ => (hFlagne n).mono (Q n).flags
    marks := hmarks }
  exact ⟨{
    real := M
    size := size
    label := label
    slot := slot
    slot_injective := hslot
    label_real := hretained
    coordinate_eventually := hcoords
    stages := Q
    same_indices := fun _ => rfl
    same_terminals := fun _ => HEq.rfl
    same_forward := fun _ => rfl
    same_inverse := fun _ => rfl
    same_domain := fun _ => rfl }⟩


end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PresentedRealCoordinates
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic real family for a mixed model needs no artificial natural-number ordering.
Its actual band widths and functions are obtained from the selected presentations; finite
stages retain the inherited order of the whole mixed family. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_mixed_exhaustion_from_presentations
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hinfty : OnePoint.infty ∈ base.physicalDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hTD : IsTotallyDisconnected base.dust) (hUB : Disjoint base.quotientDomain base.dust)
    {L : Type*} [LinearOrder L] [Countable L]
    (C : L → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val)) (ι : ℕ → L) (hinj : Injective ι)
    (R : ∀ n, RealCoordinatePresentation base π (C (ι n)))
    (A : Set base.dust) [Countable A] (hsing : ∀ l, (C l).singular ∈ A)
    (hsupport : ∀ l s, (C l).upper s - (C l).lower s ≠ 0 → s ∈ A)
    (hcompat : ∀ (l : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < l) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' base.physicalDomainᶜ) \ range (fun s : A => s.val.val))
          (C l).graph (fun k => (C k).graph) labels) = 0)
    (O : ℕ → A → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (s.val.val))
    (ε ρ : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hρ : ∀ n, 0 < ρ n) :
    Nonempty (MixedModelExhaustion
      (realCoordinatesFromPresentations base hU hdense π he hB C ι R A hsupport)
      (fun l => (C l).restrictMarks A (hsing l) (hsupport l)) ι O ε ρ) := by
  let d := realCoordinatesFromPresentations base hU hdense π he hB C ι R A hsupport
  let R' := (realSubfamily_of_presentations C ι R hdense).restrictMarks A hsing hsupport
  apply exists_mixed_model_exhaustion_of_real_subfamily hsard hsch hcompact hfinite
    hG hconn hinfty hπ hclosed hsurj hr (hB ▸ hTD) d
    (fun x hx hxb => Set.disjoint_left.mp hUB hx (hB.symm ▸ hxb))
    (fun l => (C l).restrictMarks A (hsing l) (hsupport l)) ι hinj R'
    (fun _ => rfl) ?_ hcompat O hO ε ρ hε hρ
  intro n s
  exact (R n).band_width s.val

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SelectedMixedModels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable selected family produces actual mixed finite models. Every chosen real
presentation, including a real barrier selected after the seed, is retained with its exact
physical and quotient functions. The finite coordinates keep the selected family's order. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_selected_mixed_models
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hinfty : OnePoint.infty ∈ base.physicalDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hTD : IsTotallyDisconnected base.dust) (hUB : Disjoint base.quotientDomain base.dust)
    {L : Type*} [LinearOrder L] [Countable L]
    (D : L → SelectableMaskedCoordinate base π)
    (presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate)
    (hinfinite : {l | ∃ r, presentation l = Sum.inl r}.Infinite)
    (hcompat : ∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0)
    (B₀ : Set base.dust) (hB₀ : B₀.Countable) :
    Nonempty (SelectedMixedModels hsch base hU hdense π he hB D presentation B₀) := by
  let marks : Set base.dust := Subtype.val ⁻¹' (⋃ k, (D k).flags) ∪ B₀
  have hmarks : marks.Countable :=
    ((countable_iUnion fun k => (D k).flags_countable).preimage Subtype.val_injective).union hB₀
  let : Countable marks := hmarks.to_subtype
  have hflags (l : L) (x : Sphere) (hx : x ∈ (D l).flags) : x ∈ Subtype.val '' marks :=
    ⟨⟨x, (D l).flags_dust hx⟩, Or.inl (mem_iUnion.mpr ⟨l, hx⟩), rfl⟩
  have hsing (l : L) : (D l).coordinate.singular ∈ marks :=
    Or.inl (mem_iUnion.mpr ⟨l, (D l).singular_marked⟩)
  have hsupp (l : L) (s : base.dust)
      (hs : (D l).coordinate.upper s - (D l).coordinate.lower s ≠ 0) : s ∈ marks := by
    apply Or.inl
    apply mem_iUnion.mpr
    refine ⟨l, (D l).weight_support ?_⟩
    change (D l).coordinate.dustWeight s.val ≠ 0
    rw [MaskedCoordinateData.dustWeight, dite_eq_left s.property]
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (lt_of_le_of_ne ((D l).coordinate.width_nonneg s) (Ne.symm hs))
  obtain ⟨ι, hι, R, hR, hcover⟩ := exists_injective_real_presentations
    (fun l => (D l).coordinate) presentation hinfinite
  have hcomp (j : L) (n : ℕ) (labels : Fin n → L) (hlt : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' base.physicalDomainᶜ) \ range (fun s : marks => s.val.val))
          (D j).coordinate.graph (fun k => (D k).coordinate.graph) labels) = 0 := by
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ labels) (hcompat j n labels hlt)
    intro x hx
    refine ⟨hB.symm ▸ hx.1, ?_⟩
    intro hxflags
    obtain ⟨l, hl⟩ := mem_iUnion.mp hxflags
    obtain ⟨s, hs, hval⟩ := hflags l x hl
    exact hx.2 ⟨⟨s, hs⟩, hval⟩
  obtain ⟨M⟩ := exists_mixed_exhaustion_from_presentations hsard hsch hcompact hfinite
    base hU hG hconn hinfty hdense π hπ hclosed hsurj hr he hB hTD hUB
    (fun l => (D l).coordinate) ι hι R marks hsing hsupp hcomp
    (markedNeighborhoods (fun s : marks => s.val.val)) (markedNeighborhoods_nhds _)
    modelError modelError modelError_pos modelError_pos
  exact ⟨⟨marks, hmarks, subset_union_right, hflags, hsing, hsupp, ι, hι, R, hR, hcover, M⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedMixedSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open selection with its inherited ordering and common mixed
finite models. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_selected_mixed_selection
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcompact : SmoothCompactMetricSphereUniformization)
    (hfinite : FiniteJordanModelUniformization)
    (base : PathCodeData Sphere Sphere) (hU : IsOpen base.quotientDomain)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hinfty : OnePoint.infty ∈ base.physicalDomain) (hdense : Dense base.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hTD : IsTotallyDisconnected base.dust) (hUB : Disjoint base.quotientDomain base.dust)
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    (hzero : (seed 0).coordinate.graph = circleBandGraph base.quotientDomain (fun _ => 0))
    (hseed : ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
          (fun k => (seed k).coordinate.graph) labels) = 0)
    {T X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (data : T → SelectableMaskedCoordinate base π)
    (presentation : ∀ t, SelectedLevelPresentation hsch base π (data t).coordinate)
    (V : T → Set X) (hV : ∀ t, IsOpen (V t))
    (B₀ : Set base.dust) (hB₀ : B₀.Countable) :
    ∃ (A : ℕ → Set T) (q : ℕ → Option T),
      A 0 = ∅ ∧ (∀ n, (A n).Finite) ∧ Monotone A ∧ (⋃ n, A n).Countable ∧
      (∀ n c, q n = some c ↔ c ∈ A (n + 1) \ A n) ∧
      (∀ n c, c ∈ A n ↔ ∃ k < n, q k = some c) ∧
      (∀ c, seededMaskedAllowed seed data (⋃ n, A n) c →
        V c ⊆ ⋃ t ∈ ⋃ n, A n, V t) ∧
      (let D := orderedSelectedCoordinates seed data q
       ∀ (j : ℕ ⊕ₗ ℕ) (n : ℕ) (labels : Fin n → ℕ ⊕ₗ ℕ), (∀ i, labels i < j) →
         (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
           (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
             (fun k => (D k).coordinate.graph) labels) = 0) ∧
      Nonempty (SelectedMixedModels hsch base hU hdense π he hB
        (orderedSelectedCoordinates seed data q)
        (orderedSelectedPresentations seed seedPresentation data presentation q) B₀) := by
  let : Countable (ℕ ⊕ₗ ℕ) := Function.Injective.countable
    (show Injective (ofLex : (ℕ ⊕ₗ ℕ) → ℕ ⊕ ℕ) from fun _ _ h => by
      simpa only [toLex_ofLex] using congrArg toLex h)
  obtain ⟨A, q, hA0, hfin, hmono, hcount, hq, hpref, hcover, _, hcompat⟩ :=
    exists_seeded_masked_selection seed hzero hseed data V hV
  refine ⟨A, q, hA0, hfin, hmono, hcount, hq, hpref, hcover, hcompat, ?_⟩
  exact exists_selected_mixed_models hsard hsch hcompact hfinite base hU hG hconn
    hinfty hdense π hπ hclosed hsurj hr he hB hTD hUB
    (orderedSelectedCoordinates seed data q)
    (orderedSelectedPresentations seed seedPresentation data presentation q)
    (orderedSelectedPresentations_infinite_real seed seedPresentation data presentation q)
    hcompat B₀ hB₀

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedMixedSmallness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real seed's collapse estimates survive the common mixed construction, even when
its real coordinates are enumerated differently and further marked points are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {L : Type*} [LinearOrder L] {D : L → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem retains_real_presentation
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (l : L) (R : RealCoordinatePresentation base π (D l).coordinate)
    (hR : presentation l = Sum.inl R) :
    ∃ n, F.realLabels n = l ∧ F.realCoordinates.physical n = R.coordinate.physical ∧
      F.realCoordinates.coordinate n = R.coordinate.quotient :=
  F.real_cover l R hR

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealExclusionWitness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real barrier test retains its actual presentation, band weight,
open map neighborhood, and the proved radius-dependent exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RealExclusionWitness
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}
  (W : RealExclusionWitness base π C)

 theorem isOpen_sizedNeighborhood : IsOpen W.sizedNeighborhood :=
    (W.isOpen_neighborhood.prod isOpen_univ).prod isOpen_Iio

end RealExclusionWitness

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanExclusionWitness
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A constructed mean test retains its actual source curve, mask containment,
singular fiber containment, and the open neighborhood it excludes. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem isOpen_neighborhood : IsOpen W.neighborhood :=
  isOpen_mapDiskExclusion _ W.lift W.smooth_lift _

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SizedMeanExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Record the exterior model radius in the same second countable test
space. An open radius interval retains the quantitative Stokes exclusion
under subsequent common-model selection. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem isOpen_sizedNeighborhood (B : ℝ) : IsOpen (W.sizedNeighborhood B) :=
  W.isOpen_neighborhood.prod isOpen_Ioo

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CoordinateExclusionTest
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and mean tests use one common map--disk--radius space. The mark
index is kept discrete, so each selected test retains the component it excludes. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {π : Sphere → Sphere} {B₀ : Set base.dust} {B : ℝ}
  (T : CoordinateExclusionTest hsch base π B₀ B)

 theorem isOpen_neighborhood [TopologicalSpace B₀] [DiscreteTopology B₀] :
    IsOpen T.neighborhood := by
  change IsOpen ({T.mark} ×ˢ _)
  apply IsOpen.prod (isOpen_discrete _)
  cases h : T.witness with
  | inl W => exact W.isOpen_sizedNeighborhood
  | inr W => exact W.witness.isOpen_sizedNeighborhood B

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExteriorZeroAnchor
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed quotient neighborhood of infinity contains the image of a
sufficiently far exterior region in the physical sphere. -/

open Set Function Metric
open scoped Topology

namespace CircleDomainRigidity

theorem exists_exterior_in_quotient_neighborhood
    {π : Sphere → Sphere} (hπ : Continuous π) {E : Set Sphere}
    (hE : π OnePoint.infty ∈ interior E) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → π (z : Sphere) ∈ E := by
  let V := π ⁻¹' interior E
  have hV : IsOpen V := isOpen_interior.preimage hπ
  have hinf : OnePoint.infty ∈ V := hE
  have hK : IsCompact (((↑) : ℂ → Sphere) ⁻¹' V)ᶜ :=
    ((OnePoint.isOpen_iff_of_mem hinf).mp hV).2
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, ?_⟩
  intro z hz
  apply interior_subset
  by_contra h
  exact (not_lt_of_ge hz) (hbound z h)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedCircleModel
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual graded real seed, countable open exclusion selection,
common mixed models and their normal limit into a circle uniformization. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

open FiniteTransfer

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_36
theorem exists_retained_real_circle_model
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hconn : IsConnected d.physicalDomain) (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hdust : d.dust = d.quotientDomainᶜ) (hne : d.dust.Nonempty)
    (hinftyU : OnePoint.infty ∈ d.quotientDomain)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (hinfStar : π OnePoint.infty ∈ interior EStar)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ EStar)
    (hBimage : d.dust = π '' d.physicalDomainᶜ)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : d.dust, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : d.dust, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)] (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {m : ℕ} (T : Fin (m + 1) → UngatedRealTest d π EStar)
    (hT0 : T 0 = UngatedRealTest.zeroTest d π EStar)
    (hT : ∀ (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1)),
      (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (T i).exclusions)
          (circleBandGraph d.quotientDomain (T j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (T i).coordinate.quotient) labels) = 0)
    : Nonempty (RetainedRealCircleModel d π (fun i => (T i).coordinate)) := by
  classical
  obtain ⟨tests, c, N, hNc, hNB, hc0, hprefix, _, hselected, hcompat, htests⟩ :=
    exists_countable_small_real_tests_with_seed hcross hcoarea hLusin hsard hsch d hU hG hdisj
      π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar
      hEStarE hinfE hBimage D hnest hshrink hED hfiber harcs C hC hderiv hstandard hpath
      ω hω hωsum hdual hlift T hT0 hT
  obtain ⟨p, hp⟩ := hne
  obtain ⟨seed, _, hseed0, hseed, P, hP⟩ := exists_presented_real_seed hcoarea d hU hG hdense
    π hπ he hBimage ⟨p, hp⟩ EStar hinfStar c
    (by rw [hc0]; rfl) N hNc hNB hcompat
  let B₀ : Set d.dust := Subtype.val ⁻¹' N
  have hB₀ : B₀.Countable := hNc.preimage Subtype.val_injective
  let : Countable B₀ := hB₀.to_subtype
  let : TopologicalSpace B₀ := ⊥
  let : DiscreteTopology B₀ := ⟨rfl⟩
  let : SecondCountableTopology (MapDiskData d.physicalDomain) := mapDiskData_secondCountable hG
  obtain ⟨S, q, _, _, _, _, _, hpref, hcover, hordered, ⟨F⟩⟩ :=
    exists_selected_mixed_selection hsard hsch hcompact hfinite d hU hG hconn hinf
      hdense π hπ hclosed hsurj hr he hBimage hTD hdisj seed P hseed0 hseed
      (T := CoordinateExclusionTest hsch d π B₀ (B / 4))
      CoordinateExclusionTest.coordinate CoordinateExclusionTest.presentation
      CoordinateExclusionTest.neighborhood (fun t => t.isOpen_neighborhood) B₀ hB₀
  let R := max F.model.real.radius (max (B / 4 + 1) (B / 2))
  let F' := F.withRadius R (le_max_left _ _)
  have hBR : B / 4 < F'.model.real.radius := by
    change B / 4 < R
    exact lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans (le_max_right _ _))
  have hB2 : B ≤ 2 * F'.model.real.radius := by
    change B ≤ 2 * R
    have h : B / 2 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  let : Countable F'.marks := F'.marks_countable.to_subtype
  obtain ⟨A⟩ := F'.model.exists_assigned_limit harea hmontel hhurwitz hzero
    hsard hsch hG hconn
  have hcircle : IsCircleDomain (extendAtInfinity A.function '' d.physicalDomain) := by
    refine selected_limit_isCircleDomain hplane hcoarea hLusin hsard hsch hsep hcollar
      hselect hgreen harea d hG hconn hU hdense hdust hinftyU π hπ hclosed hsurj hr he (hdust ▸ hTD) (fun p hp => hdust ▸ hbad p hp)
      hinf hBimage hfiber harcs EStar hEStar (hEStarE.trans (interior_subset.trans hEU))
      B hfar B₀ seed P S q hpref hcover hordered F' A hBR hB2 tests ?_ ?_
      C hC hderiv hstandard hpath ω hω hωsum hdual hlift
    · intro b hb
      obtain ⟨i, hi⟩ := hselected b hb
      exact ⟨i, (hP i).trans (congrArg UngatedRealTest.coordinate hi)⟩
    · intro p hp k
      apply htests p ⟨hp.1, ?_⟩ k
      intro hpN
      apply hp.2
      exact ⟨⟨p, hp.1⟩, hpN, rfl⟩
  have hretained (i : Fin (m + 1)) : ∃ j,
      F'.realCoordinates.physical j = (T i).coordinate.physical ∧
      F'.realCoordinates.coordinate j = (T i).coordinate.quotient := by
    obtain ⟨j, _, hp, hq⟩ := F'.retains_real_presentation (Sum.inlₗ i.val) (P i.val)
      (orderedSelectedPresentations_seed seed P CoordinateExclusionTest.coordinate
        CoordinateExclusionTest.presentation q i.val)
    have hQ : (P i.val).coordinate = (T i).coordinate :=
      (hP i.val).trans (congrArg UngatedRealTest.coordinate (hprefix i))
    exact ⟨j, hp.trans (congrArg PhysicalRealCoordinate.physical hQ),
      hq.trans (congrArg PhysicalRealCoordinate.quotient hQ)⟩
  choose idx hphysical hquotient using hretained
  exact ⟨{
    marks := F'.marks
    marks_countable := F'.marks_countable
    coordinates := F'.realCoordinates
    source := rfl
    model := F'.model.real
    limit := A.toReal
    circle := hcircle
    index := idx
    physical := hphysical
    quotient := hquotient }⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ExactTraceFamily
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A whole finite list has simultaneous exact-trace replacements. The
original pair-null condition passes unchanged to these actual coordinates,
and a retained model of them is a Sobolev model of every original test. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 local instance instBorelSpaceSphere_67_r60a8cf_1 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_exact_trace_family
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = x.val)
    (hne : (physicalPlaneDomain d.physicalDomain)ᶜ.Nonempty)
    {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hunit : ∀ i x, u i x ∈ Icc 0 1)
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain d.physicalDomain))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ∀ i, ExactTraceTest d (u i), ∀ i j,
      eLpNorm (fun x => (T i).error.weakGrad x j) 2 volume < ε := by
  classical
  choose T hT using fun i => exists_exact_trace_test d hG he hne (hu i) (hs i) (hunit i) (H i) hε
  exact ⟨T, hT⟩

 theorem exactTraceFamily_pair_null
    {d : PathCodeData Sphere Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (T : ∀ i, ExactTraceTest d (u i)) (hB : d.dust ⊆ d.physicalDomainᶜ)
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' d.dust) = 0) :
    ∀ i j, i ≠ j → volume
      ((fun p => ((T i).coordinate.quotient p, (T j).coordinate.quotient p)) '' d.dust) = 0 := by
  intro i j hij
  have he : (fun p => ((T i).coordinate.quotient p, (T j).coordinate.quotient p)) '' d.dust =
      (fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' d.dust := by
    apply image_congr
    intro p hp
    exact Prod.ext ((T i).trace_on_sphere (hB hp)) ((T j).trace_on_sphere (hB hp))
  rw [he]
  exact hpair i j hij

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AffineTracePairs
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine changes of the two scalar coordinates preserve outer-null
trace pairs, including singular changes with one constant coordinate. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem affine_pair_image_null {S : Set (ℝ × ℝ)} (hS : volume S = 0)
    (a b c d : ℝ) :
    volume ((fun x : ℝ × ℝ => (a * x.1 + b, c * x.2 + d)) '' S) = 0 := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (c • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL : volume (L '' S) = 0 := by
    rw [Measure.addHaar_image_continuousLinearMap, hS, mul_zero]
  have he : (fun x : ℝ × ℝ => (a * x.1 + b, c * x.2 + d)) '' S =
      (fun y => y - (b, d)) ⁻¹' (L '' S) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [L]⟩
    · rintro ⟨x, hx, he⟩
      refine ⟨x, hx, ?_⟩
      have hh := congrArg (fun z : ℝ × ℝ => z + (b, d)) he
      simp only [sub_add_cancel] at hh
      change (a * x.1 + b, c * x.2 + d) = y at hh
      exact hh
  rw [he]
  simpa only [sub_eq_add_neg, measure_preimage_add_right] using hL

 theorem affine_trace_pair_null {X : Type*} (B : Set X) (u v : X → ℝ)
    (h : volume ((fun x => (u x, v x)) '' B) = 0) (a b c d : ℝ) :
    volume ((fun x => (a * u x + b, c * v x + d)) '' B) = 0 := by
  simpa only [image_image, comp_def] using affine_pair_image_null h a b c d

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DenseComplementaryDust
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A totally disconnected subset of the sphere has empty interior. This supplies
actual density of the component quotient domain in the countable selection. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem dense_compl_of_totallyDisconnected_sphere {D : Set Sphere}
    (hD : IsTotallyDisconnected D) : Dense Dᶜ := by
  apply dense_iff_inter_open.mpr
  intro W hW hne
  by_contra h
  have hWD : W ⊆ D := by
    intro x hx
    by_contra hxD
    exact h ⟨x, hx, hxD⟩
  have hd : Dense (range ((↑) : ℂ → Sphere)) := OnePoint.denseRange_coe
  obtain ⟨p, ⟨z, rfl⟩, hp⟩ := hd.exists_mem_open hW hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hW.preimage OnePoint.continuous_coe) z hp
  have hsub := hD (((↑) : ℂ → Sphere) '' Metric.ball z r)
    (by rintro _ ⟨w, hw, rfl⟩; exact hWD (hball hw))
    (((convex_ball z r).isPreconnected).image _ OnePoint.continuous_coe.continuousOn)
  have hs : (Metric.ball z r).Subsingleton := by
    intro x hx y hy
    exact OnePoint.coe_injective (hsub ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
  have heq : Metric.ball z r = {z} :=
    Set.Subset.antisymm (fun w hw => hs hw (Metric.mem_ball_self hr))
      (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  exact not_isOpen_singleton z (heq ▸ Metric.isOpen_ball)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ScalarSeedCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar pair-null hypothesis of the rigidity companion gives the exact
ordered level compatibility required by the retained finite models. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem circleBandGraph_value_of_continuousAt
    {X : Type*} [TopologicalSpace X] {U : Set X} {f : X → ℝ} {x : X}
    (hf : ContinuousAt f x) {t : UnitAddCircle} (ht : (x, t) ∈ circleBandGraph U f) :
    (f x : UnitAddCircle) = t := by
  obtain ⟨⟨y, a⟩, ha, he⟩ := ht
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨b, c, s, hb, hc, _, ha⟩ := mem_intervalFiberHull_iff.mp ha
  rw [clusterGraph_fiber_eq_of_continuousAt hf hb,
    clusterGraph_fiber_eq_of_continuousAt hf hc] at ha
  have he : a = f y := by linarith
  exact congrArg (fun r : ℝ => (r : UnitAddCircle)) he.symm

 local instance localInst_r60a8cf_6 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩
theorem scalar_pair_null_free_compatibility
    {X : Type*} [TopologicalSpace X] (U B : Set X)
    (f : X → ℝ) (hf : Continuous f) {n : ℕ} (g : Fin n → X → ℝ)
    (hg : ∀ i, Continuous (g i))
    (hpair : ∀ i, volume ((fun x => (f x, g i x)) '' B) = 0) :
    ((volume : Measure UnitAddCircle).prod
      (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure B (circleBandGraph U f)
        (fun i => circleBandGraph U (g i)) id) = 0 := by
  let E (i : Fin n) : Set (UnitAddCircle × (Fin n → UnitAddCircle)) :=
    (fun p => (p.1, p.2 i)) ⁻¹'
      ((fun x => ((f x : UnitAddCircle), (g i x : UnitAddCircle))) '' B)
  have hnull (i : Fin n) : (volume.prod (Measure.pi (fun _ : Fin n =>
      (volume : Measure UnitAddCircle)))) (E i) = 0 := by
    exact ((MeasurePreserving.id volume).prod
      (measurePreserving_eval (fun _ : Fin n => (volume : Measure UnitAddCircle)) i)).preimage_null
        (scalar_trace_pair_null_mod_one B f (g i) (hpair i))
  apply measure_mono_null (t := ⋃ i, E i) ?_ (measure_iUnion_null hnull)
  rintro p ⟨⟨x, t, θ⟩, ⟨hxB, hxf, hcomp⟩, rfl⟩
  have hxold : (x, θ) ∈ finiteLevelUnionGraph (fun i => circleBandGraph U (g i)) id := by
    by_contra hxold
    have he : connectedComponentIn
        {z | (z, θ) ∈ finiteLevelUnionGraph (fun i => circleBandGraph U (g i)) id} x = ∅ :=
      connectedComponentIn_eq_empty hxold
    change (connectedComponentIn
      {z | (z, θ) ∈ finiteLevelUnionGraph (fun i => circleBandGraph U (g i)) id} x).Nontrivial at hcomp
    exact Set.not_nontrivial_empty (he ▸ hcomp)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxold
  refine mem_iUnion.mpr ⟨i, x, hxB, ?_⟩
  exact Prod.ext (circleBandGraph_value_of_continuousAt hf.continuousAt hxf)
    (circleBandGraph_value_of_continuousAt (hg i).continuousAt hi)

 theorem scalar_seed_ordered_compatibility
    {X : Type*} [TopologicalSpace X] (U B : Set X) {m : ℕ}
    (u : Fin m → X → ℝ) (hu : ∀ i, Continuous (u i))
    (hpair : ∀ i j, i ≠ j → volume ((fun x => (u i x, u j x)) '' B) = 0)
    (j : Fin m) (n : ℕ) (labels : Fin n → Fin m) (hlt : ∀ i, labels i < j) :
    ((volume : Measure UnitAddCircle).prod
      (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure B (circleBandGraph U (u j))
        (fun i => circleBandGraph U (u i)) labels) = 0 := by
  have h := scalar_pair_null_free_compatibility U B (u j) (hu j)
    (u ∘ labels) (fun i => hu (labels i))
    (fun i => hpair j (labels i) (ne_of_gt (hlt i)))
  simpa only [freeComponentFailure, finiteLevelUnionGraph, comp_apply, id_eq] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrescribedScalarSeed
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed finite scalar list with null trace pairs gives actual
selectable real seed coordinates, with unchanged functions and zero bands. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 omit [MeasurableSpace C(PathTime, Sphere)] in
 private theorem pair_image_zero_left {X : Type*} (B : Set X) (v : X → ℝ) :
    volume ((fun x => ((0 : ℝ), v x)) '' B) = 0 := by
  rw [Measure.volume_eq_prod]
  apply measure_mono_null (t := ({0} : Set ℝ) ×ˢ univ)
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨rfl, mem_univ _⟩
  · simp only [Measure.prod_prod, measure_singleton, zero_mul]

 omit [MeasurableSpace C(PathTime, Sphere)] in
 private theorem pair_image_zero_right {X : Type*} (B : Set X) (v : X → ℝ) :
    volume ((fun x => (v x, (0 : ℝ))) '' B) = 0 := by
  rw [Measure.volume_eq_prod]
  apply measure_mono_null (t := univ ×ˢ ({0} : Set ℝ))
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨mem_univ _, rfl⟩
  · simp only [Measure.prod_prod, measure_singleton, mul_zero]

 theorem finiteScalarSeedTests_pair_null
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    {m : ℕ} (Q : Fin m → UngatedRealTest d π EStar)
    (hpair : ∀ i j, i ≠ j → volume
      ((fun x => ((Q i).coordinate.quotient x, (Q j).coordinate.quotient x)) '' d.dust) = 0) :
    ∀ i j, i ≠ j → volume ((fun x =>
      ((finiteScalarSeedTests Q i).coordinate.quotient x,
        (finiteScalarSeedTests Q j).coordinate.quotient x)) '' d.dust) = 0 := by
  intro i j hij
  cases i with
  | zero => exact pair_image_zero_left _ _
  | succ i =>
    cases j with
    | zero => exact pair_image_zero_right _ _
    | succ j =>
      by_cases hi : i < m
      · by_cases hj : j < m
        · simp only [finiteScalarSeedTests, dite_eq_left hi, dite_eq_left hj]
          exact hpair ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Nat.succ (congrArg Fin.val h)))
        · simp only [finiteScalarSeedTests, dite_eq_left hi, dite_eq_right hj,
            UngatedRealTest.zeroTest, PhysicalRealCoordinate.zero]
          exact pair_image_zero_right _ _
      · simp only [finiteScalarSeedTests, dite_eq_right hi,
          UngatedRealTest.zeroTest, PhysicalRealCoordinate.zero]
        exact pair_image_zero_left _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SignedScalarTests
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact real tests can be encoded by unit-interval tests and a common
cutoff. On the dust this is an affine coordinate change, so pair-nullity
is preserved exactly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem signedScalarEncoding_unit
    {η u : EuclideanPlane → ℝ} {C : ℝ} (hC : 0 < C)
    (hη : ∀ x, η x ∈ Icc 0 1) (hu : ∀ x, ‖u x‖ ≤ C)
    (hone : ∀ x, u x ≠ 0 → η x = 1) (x : EuclideanPlane) :
    signedScalarEncoding η u C x ∈ Icc 0 1 := by
  have hb : -C ≤ u x ∧ u x ≤ C := abs_le.mp (by simpa only [Real.norm_eq_abs] using hu x)
  by_cases hz : u x = 0
  · unfold signedScalarEncoding
    rw [hz, zero_div, add_zero]
    constructor <;> linarith [(hη x).1, (hη x).2]
  · have hl : -1 ≤ u x / C := (le_div_iff₀ hC).mpr (by nlinarith [hb.1])
    have hh : u x / C ≤ 1 := (div_le_iff₀ hC).mpr (by nlinarith [hb.2])
    unfold signedScalarEncoding
    rw [hone x hz]
    constructor <;> linarith

 theorem signedScalarEncoding_continuous
    {η u : EuclideanPlane → ℝ} (hη : Continuous η) (hu : Continuous u) (C : ℝ) :
    Continuous (signedScalarEncoding η u C) :=
  (hη.add (hu.div_const C)).div_const 2

 theorem signedScalarEncoding_compact
    {η u : EuclideanPlane → ℝ} (hη : HasCompactSupport η) (hu : HasCompactSupport u) (C : ℝ) :
    HasCompactSupport (signedScalarEncoding η u C) := by
  change HasCompactSupport (fun x => (η x + u x / C) / 2)
  simp only [div_eq_mul_inv]
  exact (hη.add hu.mul_right).mul_right

 theorem signedScalarEncoding_recovery (η u : EuclideanPlane → ℝ)
    {C : ℝ} (hC : C ≠ 0) (x : EuclideanPlane) :
    (2 * C) * signedScalarEncoding η u C x - C * η x = u x := by
  unfold signedScalarEncoding
  field_simp
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AnchoredCollarFamily
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose all prescribed shrinking collars outside the fixed anchor.
The zero-weight specialization needs only the published geometric inputs. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_anchored_collar_family
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (B : Set Sphere) (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B) (hinfty : π OnePoint.infty ∉ B)
    (E : Set Sphere) (hE : IsClosed E) (hEB : Disjoint E B) :
    ∃ D : ∀ p : B, ℕ → WeightedCollar G π B p.val (fun _ => 0),
      (∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region) ∧
      (∀ p : B, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ, ∀ n ≥ k, closure (D p n).region ⊆ V) ∧
      ∀ p, Disjoint E (closure (D p 0).region) := by
  have hex (p : B) := exists_shrinking_weighted_collars hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad p.property
    (fun h => hinfty (h ▸ p.property)) hE.isOpen_compl
    (fun h => disjoint_left.mp hEB h p.property) (fun _ => 0) measurable_const
    (by simp)
  choose D hD0 hnest _ hshrink using hex
  refine ⟨D, hnest, ?_, ?_⟩
  · intro p V hV
    obtain ⟨k, hk⟩ := hshrink p V hV
    exact ⟨k, fun n hn => (hk n hn).1⟩
  · intro p
    apply disjoint_left.mpr
    intro x hxE hxD
    exact hD0 p hxD hxE

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PointDustModels
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source data and a common exterior zero anchor for a finite family of
compact tests on a point-complement sphere domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance instBorelSpaceSphere_68_r60a8cf_1 : BorelSpace Sphere := ⟨rfl⟩
omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem plane_complement_nonempty {G : Set Sphere}
    (hinf : OnePoint.infty ∈ G) (hne : Gᶜ.Nonempty) :
    (physicalPlaneDomain G)ᶜ.Nonempty := by
  obtain ⟨p, hp⟩ := hne
  have hpn : p ≠ OnePoint.infty := fun h => hp (h ▸ hinf)
  obtain ⟨x, rfl⟩ := exists_planeSphere_eq hpn
  exact ⟨x, hp⟩

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem exists_common_test_anchor
    {G : Set Sphere} (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {m : ℕ} (v : Fin m → EuclideanPlane → ℝ) (hs : ∀ i, HasCompactSupport (v i)) :
    ∃ E A : Set Sphere, IsCompact E ∧ IsClosed A ∧ E ⊆ interior A ∧ A ⊆ G ∧
      OnePoint.infty ∈ interior E ∧ ∀ i p, p ∈ E → sphereFromPlaneFunction (v i) p = 0 := by
  let K : Set Sphere := ⋃ i, planeSphere '' tsupport (v i)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hs i).isCompact.image continuous_planeSphere)
  have hinK : OnePoint.infty ∉ K := by
    intro hp
    obtain ⟨i, x, _, hx⟩ := mem_iUnion.mp hp
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) hx
  have hZ : IsOpen (G \ K) := hG.sdiff hK.isClosed
  obtain ⟨E, hE, _, hinE, hEZ⟩ := exists_compact_closed_between
    (isCompact_singleton (x := (OnePoint.infty : Sphere))) hZ
    (singleton_subset_iff.mpr ⟨hinf, hinK⟩)
  obtain ⟨A, _, hA, hEA, hAG⟩ := exists_compact_closed_between hE hG (hEZ.trans sdiff_subset)
  refine ⟨E, A, hE, hA, hEA, hAG, hinE (mem_singleton _), ?_⟩
  intro i p hp
  have hpK := (hEZ hp).2
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hpK (mem_iUnion.mpr ⟨i, complexPlaneCoordinates.symm z, hz, by
      simp only [planeSphere, ContinuousLinearEquiv.apply_symm_apply]⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SignedTestFamily
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common cutoff encodes a finite signed list by unit-interval tests.
The cutoff is constant on the source dust, so all new trace pairs are null. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem constant_left_trace_pair_null {X : Type*} (B : Set X) (v : X → ℝ) (c : ℝ) :
    volume ((fun x => (c, v x)) '' B) = 0 := by
  apply measure_mono_null (t := ({c} : Set ℝ) ×ˢ univ)
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨rfl, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

 theorem constant_right_trace_pair_null {X : Type*} (B : Set X) (v : X → ℝ) (c : ℝ) :
    volume ((fun x => (v x, c)) '' B) = 0 := by
  apply measure_mono_null (t := univ ×ˢ ({c} : Set ℝ))
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨trivial, rfl⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_70
theorem exists_common_signed_cutoff {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hs : ∀ i, HasCompactSupport (u i)) :
    ∃ η : EuclideanPlane → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc 0 1) ∧ (∀ x ∉ physicalPlaneDomain G, η x = 1) ∧
      (∀ i x, u i x ≠ 0 → η x = 1) := by
  let K : Set EuclideanPlane := (physicalPlaneDomain G)ᶜ ∪ ⋃ i, tsupport (u i)
  have hB : IsCompact (physicalPlaneDomain G)ᶜ := by
    have hh := (isCompact_finite_preimage hG.isClosed_compl (not_not.mpr hinf)).image
      complexPlaneCoordinates.symm.continuous
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_compl_iff, physicalPlaneDomain, mem_preimage, mem_image]
    constructor
    · intro hx
      exact ⟨complexPlaneCoordinates x, hx, complexPlaneCoordinates.symm_apply_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      simpa only [planeSphere, ContinuousLinearEquiv.apply_symm_apply] using hz
  have hK : IsCompact K := hB.union (isCompact_iUnion fun i => hs i)
  obtain ⟨f, hf, hfs, _, hfr, hfo⟩ := exists_smooth_planar_cutoff
    (hK.image complexPlaneCoordinates.continuous) isOpen_univ (subset_univ _)
  refine ⟨f ∘ complexPlaneCoordinates, hf.comp complexPlaneCoordinates.contDiff,
    hfs.comp_homeomorph complexPlaneCoordinates.toHomeomorph, fun x => hfr _, ?_, ?_⟩
  · intro x hx
    exact hfo.self_of_nhdsSet _ (mem_image_of_mem _ (Or.inl hx))
  · intro i x hx
    exact hfo.self_of_nhdsSet _ (mem_image_of_mem _
      (Or.inr (mem_iUnion.mpr ⟨i, subset_tsupport _ hx⟩)))

 theorem exists_signed_test_family {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0) :
    Nonempty (SignedTestFamily G u) := by
  classical
  obtain ⟨η, hη, hηs, hηr, hηB, hηu⟩ := exists_common_signed_cutoff hG hinf u hs
  choose C hC using fun i => (hu i).bounded_above_of_compact_support (hs i)
  let D : Fin m → ℝ := fun i => |C i| + 1
  have hD : ∀ i, 0 < D i := fun i => by dsimp [D] <;> positivity
  have huD : ∀ i x, ‖u i x‖ ≤ D i := fun i x => (hC i x).trans
    (by dsimp [D] <;> linarith [le_abs_self (C i)])
  let v : Fin (m + 1) → EuclideanPlane → ℝ :=
    Fin.cases η (fun i => signedScalarEncoding η (u i) (D i))
  let Hη := (smoothCompactPlaneWitness hη hηs).restrict
    (hG.preimage continuous_planeSphere) (subset_univ _)
  have hvpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (v i) p, sphereFromPlaneFunction (v j) p)) '' Gᶜ) = 0 := by
    have he (i : Fin m) (p : Sphere) (hp : p ∈ Gᶜ) :
        sphereFromPlaneFunction (v i.succ) p =
          (D i)⁻¹ / 2 * sphereFromPlaneFunction (u i) p + 1 / 2 := by
      have hpn : p ≠ OnePoint.infty := fun h => hp (h ▸ hinf)
      obtain ⟨x, rfl⟩ := exists_planeSphere_eq hpn
      change sphereFromPlaneFunction (signedScalarEncoding η (u i) (D i)) (planeSphere x) = _
      simp only [planeSphere, sphereFromPlaneFunction_coe, ContinuousLinearEquiv.symm_apply_apply]
      rw [signedScalarEncoding, hηB x hp]
      ring
    have he0 (p : Sphere) (hp : p ∈ Gᶜ) : sphereFromPlaneFunction (v 0) p = 1 := by
      have hpn : p ≠ OnePoint.infty := fun h => hp (h ▸ hinf)
      obtain ⟨x, rfl⟩ := exists_planeSphere_eq hpn
      change sphereFromPlaneFunction η (planeSphere x) = 1
      simpa only [planeSphere, sphereFromPlaneFunction_coe,
        ContinuousLinearEquiv.symm_apply_apply] using hηB x hp
    intro i j hij
    refine Fin.cases ?_ (fun a => ?_) i hij
    · refine Fin.cases ?_ (fun b _ => ?_) j
      · exact fun h => (h rfl).elim
      · convert constant_left_trace_pair_null Gᶜ (fun p => sphereFromPlaneFunction (v b.succ) p) 1
          using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        apply image_congr
        intro p hp
        rw [he0 p hp]
    · refine Fin.cases (fun _ => ?_) (fun b hab => ?_) j
      · convert constant_right_trace_pair_null Gᶜ (fun p => sphereFromPlaneFunction (v a.succ) p) 1
          using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        apply image_congr
        intro p hp
        rw [he0 p hp]
      · have hab' : a ≠ b := fun h => hab (congrArg Fin.succ h)
        have hh := affine_trace_pair_null Gᶜ
          (sphereFromPlaneFunction (u a)) (sphereFromPlaneFunction (u b)) (hpair a b hab')
          ((D a)⁻¹ / 2) (1 / 2) ((D b)⁻¹ / 2) (1 / 2)
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        apply image_congr
        intro p hp
        rw [he a p hp, he b p hp]
  refine ⟨{
    test := v
    continuous := Fin.cases hη.continuous (fun i => signedScalarEncoding_continuous hη.continuous (hu i) _)
    compact := Fin.cases hηs (fun i => signedScalarEncoding_compact hηs (hs i) _)
    unit := Fin.cases hηr (fun i => signedScalarEncoding_unit (hD i) hηr (huD i) (hηu i))
    witness := Fin.cases Hη (fun i => signedScalarEncoding_witness Hη (H i) (D i))
    pair_null := hvpair
    scale := D
    recovery := fun i x => signedScalarEncoding_recovery η (u i) (hD i).ne' x }⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ScalarCircleModel
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The null trace-pair hypothesis gives a circle-domain model retaining
exactly the prescribed continuous smooth scalar tests. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r60a8cf_7 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_retained_scalar_circle_model
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hconn : IsConnected d.physicalDomain) (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hdust : d.dust = d.quotientDomainᶜ) (hne : d.dust.Nonempty)
    (hinftyU : OnePoint.infty ∈ d.quotientDomain)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (hinfStar : π OnePoint.infty ∈ interior EStar)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ EStar)
    (hBimage : d.dust = π '' d.physicalDomainᶜ)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : d.dust, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : d.dust, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)] (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {m : ℕ} (Q : Fin m → PhysicalRealCoordinate d π)
    (hQ : ∀ i, Continuous (Q i).quotient)
    (hz : ∀ i x, x ∈ EStar → (Q i).quotient x = 0)
    (hpair : ∀ i j, i ≠ j → volume
      ((fun x => ((Q i).quotient x, (Q j).quotient x)) '' d.dust) = 0) :
    Nonempty (RetainedRealCircleModel d π Q) := by
  let W (i : Fin m) := (Q i).continuousTest (hQ i) (hz i) hdense
  let c := finiteScalarSeedTests W
  let T (i : Fin (m + 1)) := c i.val
  have hc (n : ℕ) : Continuous (c n).coordinate.quotient := by
    cases n with
    | zero => exact continuous_const
    | succ n =>
      by_cases hn : n < m
      · simpa only [c, finiteScalarSeedTests, dite_eq_left hn, W,
          PhysicalRealCoordinate.continuousTest] using hQ ⟨n, hn⟩
      · simp only [c, finiteScalarSeedTests, dite_eq_right hn,
          UngatedRealTest.zeroTest, PhysicalRealCoordinate.zero]
        exact continuous_const
  have hpairs := finiteScalarSeedTests_pair_null W hpair
  have hT (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1))
      (hlt : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (T i).exclusions)
          (circleBandGraph d.quotientDomain (T j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (T i).coordinate.quotient) labels) = 0 := by
    have hn := scalar_seed_ordered_compatibility d.quotientDomain d.dust
      (fun i => (T i).coordinate.quotient) (fun i => hc i.val)
      (fun i k hik => hpairs i.val k.val (fun h => hik (Fin.ext h))) j n labels hlt
    exact measure_mono_null (freeComponentFailure_mono_free sdiff_subset _ _ labels) hn
  obtain ⟨M⟩ := exists_retained_real_circle_model hcross hplane hcoarea hLusin hsard hsch
    hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    d hU hconn hG hdisj π hπ hclosed hsurj hr he hdust hne hinftyU hB hTD hBU hdense
    hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE hinfStar B hfar hBimage D
    hnest hshrink hED hfiber harcs C hC hderiv hstandard hpath ω hω hωsum hdual hlift
    T rfl hT
  have hQT : (fun i : Fin m => (T i.succ).coordinate) = Q := by
    funext i
    simp only [T, c, Fin.val_succ, finiteScalarSeedTests, dite_eq_left i.isLt]
    rfl
  exact ⟨hQT ▸ M.select Fin.succ⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ContinuousScalarCircleModel
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-list model construction for continuous compact planar
tests on a point-complement domain from retained tests. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r60a8cf_8 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_compact_scalar_circle_model
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ) (hBne : Gᶜ.Nonempty)
    {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hunit : ∀ i x, u i x ∈ Icc 0 1)
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0) :
    Nonempty (CompactScalarCircleModel G u) := by
  classical
  let d₀ := pointDustPathData G ∅
  obtain ⟨T₀, _⟩ := exists_exact_trace_family d₀ hG (fun x => rfl)
    (plane_complement_nonempty hinf hBne) u hu hs hunit H (ε := 1) (by norm_num)
  obtain ⟨E, A, hE, hA, hEA, hAG, hinE, hzeroAnchor⟩ :=
    exists_common_test_anchor hG hinf (fun i => (T₀ i).smooth) (fun i => (T₀ i).compact)
  let d := pointDustPathData G A
  choose Q hQ hQc hnorm using fun i =>
    exists_prescribed_plane_coordinate d hG (fun x => rfl) (T₀ i).smooth
      (T₀ i).continuous (T₀ i).compact (T₀ i).contDiff (T₀ i).unit (T₀ i).partial_memLp
  let T : ∀ i, ExactTraceTest d (u i) := fun i => {
    smooth := (T₀ i).smooth
    continuous := (T₀ i).continuous
    compact := (T₀ i).compact
    contDiff := (T₀ i).contDiff
    unit := (T₀ i).unit
    partial_memLp := (T₀ i).partial_memLp
    trace := (T₀ i).trace
    coordinate := Q i
    coordinate_eq := hQ i
    coordinate_continuous := hQc i
    error := (T₀ i).error }
  have hcc : ∀ q p, p ∈ connectedComponentIn Gᶜ q → p = q :=
    point_component_eq_of_totallyDisconnected hTD
  have hr : ∀ x y : Sphere, id x = id y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x) := by
    intro x y
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact (hcc x y h.2).symm
  have hdense : Dense G := by
    simpa only [compl_compl] using dense_compl_of_totallyDisconnected_sphere hTD
  have hbad : ∀ x ∈ Gᶜ, id x ∈ Gᶜ := fun _ hx => hx
  obtain ⟨D, hnest, hshrink, hED⟩ := exists_anchored_collar_family hcoarea hsard hsch
    G id continuous_id (Homeomorph.refl Sphere).isClosedMap surjective_id hr Gᶜ hG.isClosed_compl hTD hbad
    (show id OnePoint.infty ∉ Gᶜ from not_not.mpr hinf) A hA
    (disjoint_compl_right.mono_left hAG)
  obtain ⟨B, _, hfar⟩ := exists_exterior_in_quotient_neighborhood continuous_id hinE
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  obtain ⟨ω, hω, hωsum⟩ := exists_positive_summable_weights TupleType
  have hωsum' : (∑' i, ω i) < ∞ := lt_of_le_of_lt hωsum (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum'
  obtain ⟨R⟩ := exists_retained_scalar_circle_model hcross hplane hcoarea hLusin hsard hsch
    hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    d hG hconn hG disjoint_compl_right id continuous_id (Homeomorph.refl Sphere).isClosedMap surjective_id hr
    (fun x => rfl) rfl hBne hinf hG.isClosed_compl hTD (by simp [d, pointDustPathData]) hdense
    (show id OnePoint.infty ∉ d.dust from not_not.mpr hinf) hbad hinf
    E hA hAG hE hEA (hEA (interior_subset hinE)) hinE B hfar (by simp [d, pointDustPathData]) D
    hnest hshrink hED (fun x => by simpa only [preimage_id] using isConnected_singleton (x := x))
    harcs C hC hderiv hstandard hpath ω (fun i => (hω i).ne') hωsum' hdual hlift
    (fun i => (T i).coordinate) (fun i => (T i).coordinate_continuous)
    (fun i p hp => by rw [(T i).coordinate_eq]; exact hzeroAnchor i p hp)
    (exactTraceFamily_pair_null T (Subset.refl _) hpair)
  exact ⟨R.compactScalarCircleModel harea hsch hG hcc T hu hs⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SignedScalarCircleModel
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite signed compact tests have a common circle model. The proof
uses the proved unit-test construction, and recovers all original tests
by an exact linear combination on the same model. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r60a8cf_9 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_signed_compact_scalar_circle_model_oai
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0) :
    Nonempty (CompactScalarCircleModel G u) := by
  classical
  by_cases hBne : Gᶜ.Nonempty
  · obtain ⟨T⟩ := exists_signed_test_family hG hinf u hu hs H hpair
    obtain ⟨M⟩ := exists_compact_scalar_circle_model hcross hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
      harcs hstandard hpath hdual hlift hG hconn hinf hTD hBne
      T.test T.continuous T.compact T.unit T.witness T.pair_null
    have he : (fun i x => (2 * T.scale i) * T.test i.succ x - T.scale i * T.test 0 x) = u := by
      funext i x
      exact T.recovery i x
    rw [← he]
    exact ⟨M.linearDifference Fin.succ (fun _ => 0) (fun i => 2 * T.scale i) T.scale⟩
  · have hGu : G = univ := by
      apply eq_univ_of_forall
      intro p
      by_contra hp
      exact hBne ⟨p, hp⟩
    subst G
    have hphys : physicalPlaneDomain (univ : Set Sphere) = univ := rfl
    exact ⟨compactScalarCircleModel_identity u (fun i => hphys ▸ H i)⟩

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.exists_signed_compact_scalar_circle_model_oai := @OAI.CircleDomainRigidity.exists_signed_compact_scalar_circle_model_oai
