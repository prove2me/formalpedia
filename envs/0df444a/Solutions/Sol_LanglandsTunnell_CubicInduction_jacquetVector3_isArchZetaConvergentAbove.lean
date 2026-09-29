-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_isArchZetaConvergentAbove
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c8147007-bbe7-5e8b-af33-3a2d327d75d5

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicLambda
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iotaGL_diagUnitGL2_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_norm_iteratedFDerivWithin_diagOne_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Ring.Units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

open MeasureTheory Set Topology

namespace AbsInvDensity

private noncomputable def nnDensity (y : ℝ) : NNReal := Real.toNNReal |y|⁻¹

private theorem measurable_nnDensity : Measurable nnDensity :=
  (measurable_abs.inv).real_toNNReal

private theorem ofReal_abs_inv_eq (y : ℝ) : ENNReal.ofReal |y|⁻¹ = (nnDensity y : ENNReal) := rfl

private theorem coe_nnDensity (y : ℝ) : (nnDensity y : ℝ) = |y|⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg y))

private theorem pos_of_map_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) : 0 < κ := by
  by_contra hle
  have h0 : ENNReal.ofReal κ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
  have hmap : Measure.map T μ = 0 := by rw [hκ, h0, zero_smul]
  apply hμ
  rw [← Measure.measure_univ_eq_zero, ← Set.preimage_univ (f := T), ← Measure.map_apply hT MeasurableSet.univ, hmap]
  rfl

private theorem map_eq_smul_withDensity {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => (nnDensity y : ENNReal) := hκ

private theorem map_absolutelyContinuous {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ ≪ (volume : Measure ℝ) := by
  rw [hκ]
  exact (withDensity_absolutelyContinuous _ _).smul_left (ENNReal.ofReal κ)

private theorem nnDensity_smul_eq (f : ℝ → ℂ) (y : ℝ) : nnDensity y • f y = f y * ((|y| : ℝ) : ℂ)⁻¹ := by
  change ((nnDensity y : ℝ)) • f y = f y * ((|y| : ℝ) : ℂ)⁻¹
  rw [Complex.real_smul, coe_nnDensity, Complex.ofReal_inv, mul_comm]

private theorem integral_comp_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    0 < κ ∧ ∫ x, f (T x) ∂μ = (κ : ℂ) * ∫ y : ℝ, f y * ((|y| : ℝ) : ℂ)⁻¹ := by
  have hpos : 0 < κ := pos_of_map_eq μ T hT κ hκ hμ
  refine ⟨hpos, ?_⟩
  have hf' : AEStronglyMeasurable f (Measure.map T μ) := hf.mono_ac (map_absolutelyContinuous μ T κ hκ)
  rw [← integral_map hT.aemeasurable hf', map_eq_smul_withDensity μ T κ hκ, integral_smul_measure,
    integral_withDensity_eq_integral_smul measurable_nnDensity, ENNReal.toReal_ofReal hpos.le]
  refine Complex.real_smul.trans ?_
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => nnDensity_smul_eq f y)

private theorem integrable_comp_iff {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    Integrable (fun x => f (T x)) μ ↔ Integrable (fun y => f y * ((|y| : ℝ) : ℂ)⁻¹) volume := by
  have hpos : 0 < κ := pos_of_map_eq μ T hT κ hκ hμ
  have hf' : AEStronglyMeasurable f (Measure.map T μ) := hf.mono_ac (map_absolutelyContinuous μ T κ hκ)
  have h1 : Integrable (fun x => f (T x)) μ ↔ Integrable f (Measure.map T μ) :=
    (integrable_map_measure hf' hT.aemeasurable).symm
  rw [h1, map_eq_smul_withDensity μ T κ hκ,
    integrable_smul_measure (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top,
    integrable_withDensity_iff_integrable_smul measurable_nnDensity]
  exact integrable_congr (Filter.Eventually.of_forall fun y => nnDensity_smul_eq f y)

end AbsInvDensity

private theorem norm_component_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x Rat.infinitePlace‖ = |StandardKernel.realCoord x| := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (Rat.isReal_infinitePlace)).norm_map_of_map_zero (map_zero _) (x Rat.infinitePlace)
  rw [← h, Real.norm_eq_abs]
  rfl

private theorem ideleChar_section_eq_quasiChar_realCoord
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) :
    ((σ (E z) : ℂˣ) : ℂ) = ArchR.quasiChar t (e : ZMod 2) (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) := by
  have hvr : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace
  let zv : ((Rat.infinitePlace).Completion)ˣ :=
    Units.map (Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace).toMonoidHom z
  have hzv : ((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion) =
      (z : InfiniteAdeleRing ℚ) Rat.infinitePlace := rfl
  obtain ⟨h1, h2⟩ := hE z
  have h1' : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = (z : InfiniteAdeleRing ℚ) := by
    have h := congrArg Units.val h1
    simp [M4aHerbrand.infPart, RingHom.coe_fst, RingHom.coe_snd] at h
    exact h
  have h2' : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    have h := congrArg Units.val h2
    simp [RatIdele.finPart, RingHom.coe_fst, RingHom.coe_snd] at h
    exact h
  have hEz : E z = NumberField.TateGlobal.archUnitHom Rat.infinitePlace zv := by
    apply Units.ext
    refine Prod.ext ?_ ?_
    · rw [h1']
      funext w
      obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      simp [NumberField.TateGlobal.archUnitHom, NumberField.AdelicVolume.archCentralUnit, hzv]
    · exact h2'
  have hloc := hσ Rat.infinitePlace hvr zv
  have hσE : ((σ (E z) : ℂˣ) : ℂ) =
      ((NumberField.TateGlobal.archLocalChar σ Rat.infinitePlace zv : ℂˣ) : ℂ) := by
    rw [hEz]; rfl
  rw [hσE, hloc]
  set r : ℝ := StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) with hr
  have hnorm : ‖((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion)‖ = |r| := by
    rw [hzv, hr]; exact norm_component_eq_abs_realCoord _
  have hemb : InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
      ((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion) = (r : ℂ) := by
    rw [hzv, hr, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hvr]
    rfl
  have hmult : ((Rat.infinitePlace).mult : ℂ) = 1 := by
    have h : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨Rat.infinitePlace, hvr⟩
    rw [h]; norm_num
  have hr0 : r ≠ 0 := (z.isUnit.map StandardKernel.realCoord).ne_zero
  rw [hnorm, hemb, hmult, one_mul]
  unfold ArchR.quasiChar
  congr 1
  have hcast : ((e : ZMod 2) = 0) ↔ Even e := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
    norm_cast
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have habs : |r| = -r := abs_of_neg hneg
    have hsign : SignType.sign r = -1 := sign_neg hneg
    rw [habs, hsign]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
    by_cases he : Even e
    · rw [he.neg_one_zpow, if_pos (hcast.mpr he)]
    · rw [(Int.not_even_iff_odd.mp he).neg_one_zpow, if_neg (fun h => he (hcast.mp h))]
      simp
  · have habs : |r| = r := abs_of_pos hpos
    have hsign : SignType.sign r = 1 := sign_pos hpos
    rw [habs, hsign, div_self (by exact_mod_cast hr0), one_zpow]
    split_ifs <;> simp

private theorem norm_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x‖ = |StandardKernel.realCoord x| := by
  rw [InfiniteAdeleRing.norm_def, Fintype.prod_unique]
  have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  have hm : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  rw [hd, hm, pow_one]
  exact norm_component_eq_abs_realCoord x

private theorem measurable_realCoord_units [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] :
    Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  have hc : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      (continuous_apply Rat.infinitePlace)
  exact (hc.comp Units.continuous_val).measurable

section HaarScalar

p2m_open "MeasureTheory Measure MeasureTheory.Measure Topology Set"
open scoped ENNReal

namespace ArchUnitsHaar

private noncomputable def lineHaar : Measure ℝ := (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹

private theorem measurable_density : Measurable fun y : ℝ => ENNReal.ofReal |y|⁻¹ :=
  ENNReal.measurable_ofReal.comp continuous_abs.measurable.inv

private theorem lineHaar_singleton_zero : lineHaar ({0} : Set ℝ) = 0 := by
  rw [lineHaar]
  exact withDensity_absolutelyContinuous _ _ Real.volume_singleton

private theorem map_mul_left_lineHaar {c : ℝ} (hc : c ≠ 0) : Measure.map (c * ·) lineHaar = lineHaar := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul c) hs, lineHaar, withDensity_apply _ (measurable_const_mul c hs),
    withDensity_apply _ hs]

  rw [← lintegral_indicator (measurable_const_mul c hs), ← lintegral_indicator hs]
  have key : ∀ y : ℝ, ((c * ·) ⁻¹' s).indicator (fun y : ℝ => ENNReal.ofReal |y|⁻¹) y =
      ENNReal.ofReal |c| * s.indicator (fun z : ℝ => ENNReal.ofReal |z|⁻¹) (c * y) := by
    intro y
    by_cases hy : c * y ∈ s
    · rw [indicator_of_mem (show y ∈ (c * ·) ⁻¹' s from hy), indicator_of_mem hy, ← ENNReal.ofReal_mul (abs_nonneg c),
        abs_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]
    · rw [indicator_of_notMem (show y ∉ (c * ·) ⁻¹' s from hy), indicator_of_notMem hy, mul_zero]
  simp_rw [key]
  have hmeas : Measurable (s.indicator fun z : ℝ => ENNReal.ofReal |z|⁻¹) := measurable_density.indicator hs
  have hmeas' : Measurable fun y : ℝ => s.indicator (fun z : ℝ => ENNReal.ofReal |z|⁻¹) (c * y) :=
    hmeas.comp (measurable_const_mul c)
  rw [lintegral_const_mul _ hmeas']

  have hsub := lintegral_map (μ := (volume : Measure ℝ)) hmeas (measurable_const_mul c)
  simp only [Real.map_volume_mul_left hc, lintegral_smul_measure, smul_eq_mul] at hsub
  rw [← hsub, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg c), abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hc),
    ENNReal.ofReal_one, one_mul]

section Group

variable {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {e : G → ℝ}

private noncomputable def pullback (e : G → ℝ) : Measure G := Measure.comap e lineHaar

private theorem pullback_apply (he : IsOpenEmbedding e) (s : Set G) : pullback e s = lineHaar (e '' s) :=
  he.measurableEmbedding.comap_apply _ _

private theorem pullback_isFiniteMeasureOnCompacts (he : IsOpenEmbedding e) (hne : ∀ g : G, e g ≠ 0) :
    IsFiniteMeasureOnCompacts (pullback e) := by
  refine ⟨fun K hK => ?_⟩
  rw [pullback_apply he]
  have hK' : IsCompact (e '' K) := hK.image he.continuous

  rcases (e '' K).eq_empty_or_nonempty with h | h
  · rw [h, measure_empty]; exact ENNReal.zero_lt_top
  obtain ⟨y₀, hy₀K, hy₀⟩ := hK'.exists_isMinOn h continuous_abs.continuousOn
  obtain ⟨g₀, -, rfl⟩ := hy₀K
  have hpos : 0 < |e g₀| := abs_pos.mpr (hne g₀)
  calc lineHaar (e '' K) = ∫⁻ y in e '' K, ENNReal.ofReal |y|⁻¹ := withDensity_apply _ hK'.measurableSet
    _ ≤ ∫⁻ _ in e '' K, ENNReal.ofReal |e g₀|⁻¹ := by
        refine setLIntegral_mono measurable_const fun y hy => ?_
        exact ENNReal.ofReal_le_ofReal (inv_anti₀ hpos (hy₀ hy))
    _ = ENNReal.ofReal |e g₀|⁻¹ * volume (e '' K) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK'.measure_lt_top

private theorem pullback_isOpenPosMeasure (he : IsOpenEmbedding e) (hne : ∀ g : G, e g ≠ 0) :
    IsOpenPosMeasure (pullback e) := by
  refine ⟨fun U hU hUne => ?_⟩
  rw [pullback_apply he, lineHaar, Ne, withDensity_apply_eq_zero measurable_density]
  have hopen : IsOpen (e '' U) := he.isOpenMap U hU
  have hsub : e '' U ⊆ {y : ℝ | ENNReal.ofReal |y|⁻¹ ≠ 0} := by
    rintro _ ⟨g, -, rfl⟩
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (abs_pos.mpr (hne g)))).ne'
  rw [inter_eq_self_of_subset_right hsub]
  exact hopen.measure_ne_zero volume (hUne.image e)

private theorem pullback_isMulLeftInvariant [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) : IsMulLeftInvariant (pullback e) := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hg : Measurable (g * ·) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hg hs, pullback_apply he, pullback_apply he]
  have himage : e '' ((g * ·) ⁻¹' s) = (e g * ·) ⁻¹' (e '' s) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g * x, hx, hmul g x⟩
    · rintro ⟨z, hz, hzy⟩

      refine ⟨g⁻¹ * z, ?_, ?_⟩
      · show g * (g⁻¹ * z) ∈ s
        rwa [mul_inv_cancel_left]
      · have h1 : e g * e (g⁻¹ * z) = e z := by rw [← hmul, mul_inv_cancel_left]
        have h2 : e g * e (g⁻¹ * z) = e g * y := by rw [h1, hzy]
        exact mul_left_cancel₀ (hne g) h2
  rw [himage, ← Measure.map_apply (measurable_const_mul (e g)) (he.measurableEmbedding.measurableSet_image' hs),
    map_mul_left_lineHaar (hne g)]

private theorem pullback_isHaarMeasure [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) : IsHaarMeasure (pullback e) := by
  haveI := pullback_isFiniteMeasureOnCompacts he hne
  haveI := pullback_isMulLeftInvariant he hmul hne
  haveI := pullback_isOpenPosMeasure he hne
  exact IsHaarMeasure.mk

private theorem map_pullback (he : IsOpenEmbedding e) (hrange : ∀ y : ℝ, y ≠ 0 → y ∈ range e) :
    Measure.map e (pullback e) = lineHaar := by
  rw [pullback, he.measurableEmbedding.map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine measure_mono_null ?_ lineHaar_singleton_zero
  intro y hy
  rw [mem_singleton_iff]
  by_contra h0
  exact hy (hrange y h0)

private theorem exists_map_eq_smul [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) (hrange : ∀ y : ℝ, y ≠ 0 → y ∈ range e)
    (ν : Measure G) [ν.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧ Measure.map e ν = ENNReal.ofReal κ • lineHaar := by
  haveI : LocallyCompactSpace G := he.locallyCompactSpace
  haveI : SecondCountableTopology G := he.isEmbedding.secondCountableTopology
  haveI : IsHaarMeasure (pullback e) := pullback_isHaarMeasure he hmul hne
  obtain ⟨r, hr, hν⟩ : ∃ r : NNReal, 0 < r ∧ ν = r • pullback e :=
    ⟨_, haarScalarFactor_pos_of_isHaarMeasure ν (pullback e), isMulLeftInvariant_eq_smul ν (pullback e)⟩
  refine ⟨(r : ℝ), NNReal.coe_pos.mpr hr, ?_⟩
  rw [ENNReal.ofReal_coe_nnreal, hν, Measure.map_smul, map_pullback he hrange]
  exact (Measure.coe_nnreal_smul r lineHaar).symm

end Group

end ArchUnitsHaar

end HaarScalar

namespace DirectArchZetaBound

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem continuous_realCoord : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private noncomputable def realCoordEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := StandardKernel.realCoord
  invFun := StandardKernel.ofReal
  left_inv := StandardKernel.ofReal_realCoord
  right_inv := realCoord_ofReal
  map_mul' := map_mul StandardKernel.realCoord
  map_add' := map_add StandardKernel.realCoord

private noncomputable def unitsHomeomorph : (InfiniteAdeleRing ℚ)ˣ ≃ₜ ℝˣ where
  toEquiv := (Units.mapEquiv realCoordEquiv.toMulEquiv).toEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨continuous_realCoord.comp Units.continuous_val, continuous_realCoord.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨StandardKernel.continuous_ofReal.comp Units.continuous_val,
      StandardKernel.continuous_ofReal.comp Units.continuous_coe_inv⟩

private theorem unitsHomeomorph_apply_val (z : (InfiniteAdeleRing ℚ)ˣ) :
    ((unitsHomeomorph z : ℝˣ) : ℝ) = StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
  rfl

private theorem isOpenEmbedding_realCoord_units :
    IsOpenEmbedding fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
  Units.isOpenEmbedding_val.comp unitsHomeomorph.isOpenEmbedding

private theorem realCoord_units_mul (z w : (InfiniteAdeleRing ℚ)ˣ) :
    StandardKernel.realCoord ((z * w : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) =
      StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) * StandardKernel.realCoord (w : InfiniteAdeleRing ℚ) := by
  rw [Units.val_mul, map_mul]

private theorem realCoord_units_ne_zero (z : (InfiniteAdeleRing ℚ)ˣ) :
    StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) ≠ 0 :=
  (z.isUnit.map StandardKernel.realCoord).ne_zero

private theorem realCoord_units_range (y : ℝ) (hy : y ≠ 0) :
    y ∈ Set.range fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  refine ⟨unitsHomeomorph.symm (Units.mk0 y hy), ?_⟩
  show ((unitsHomeomorph (unitsHomeomorph.symm (Units.mk0 y hy)) : ℝˣ) : ℝ) = y
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem exists_haarScalar [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
        ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹ :=
  ArchUnitsHaar.exists_map_eq_smul isOpenEmbedding_realCoord_units realCoord_units_mul realCoord_units_ne_zero
    realCoord_units_range ν_mul

private theorem integrable_mul_abs_mul_inv_of_integrable {G : ℝ → ℂ} (hG : Integrable G volume) (c : ℂ) :
    Integrable (fun y : ℝ => c * (G y * ((|y| : ℝ) : ℂ)) * ((|y| : ℝ) : ℂ)⁻¹) volume := by
  refine (hG.const_mul c).congr ?_
  have hnull : (volume : Measure ℝ) {y : ℝ | ¬ (c * G y = c * (G y * ((|y| : ℝ) : ℂ)) * ((|y| : ℝ) : ℂ)⁻¹)} = 0 := by
    refine measure_mono_null ?_ (Real.volume_singleton (a := 0))
    intro y hy
    rw [Set.mem_singleton_iff]
    by_contra hy0
    apply hy
    have habs : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hy0
    rw [mul_assoc c, mul_inv_cancel_right₀ habs]
  exact (MeasureTheory.ae_iff).2 hnull

end DirectArchZetaBound

open _root_.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction in
open scoped Classical in

private theorem DirectArchZetaBound.direct_half
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁)) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
      ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ),
        IsArchZeta30ConvergentAbove ν_mul
            (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
            (σ.comp E) 1 (max c₀ (-(uR w₀ h₀).re) - t.re) := by
  have _ := hc₁
  intro σ _hσ t e ht gInf
  unfold IsArchZeta30ConvergentAbove
  intro s hs

  have hC := LanglandsTunnell.CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar K hdeg μ hμ uR aR uC
    kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS c₀ hc₀ t e gInf s hs

  have hG : Integrable (fun y : ℝ =>
      (∫ e' : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) ((a : ℝ) * y) psiInf S gInf e') *
        ArchR.quasiChar t (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹) volume := by
    have h := hC.integral_prod_left
    simpa only [integral_mul_const] using h

  obtain ⟨κ, -, hκ⟩ := DirectArchZetaBound.exists_haarScalar ν_mul
  have hT := measurable_realCoord_units
  have hν0 : ν_mul ≠ 0 := Measure.measure_univ_ne_zero.1 (isOpen_univ.measure_ne_zero ν_mul Set.univ_nonempty)
  set c : ℂ := ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (StandardKernel.realMat gInf).det with hc
  set G : ℝ → ℂ := fun y =>
      (∫ e' : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) ((a : ℝ) * y) psiInf S gInf e') *
        ArchR.quasiChar t (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ with hGdef
  have hf : AEStronglyMeasurable (fun y : ℝ => c * (G y * ((|y| : ℝ) : ℂ))) volume :=
    (hG.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp continuous_abs).aestronglyMeasurable).const_mul c
  have htransport :=
    (AbsInvDensity.integrable_comp_iff ν_mul _ hT κ hκ hν0 (fun y => c * (G y * ((|y| : ℝ) : ℂ))) hf).2
      (DirectArchZetaBound.integrable_mul_abs_mul_inv_of_integrable hG c)
  refine htransport.congr (Filter.Eventually.of_forall fun z => ?_)

  have hy0 : ((|StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (DirectArchZetaBound.realCoord_units_ne_zero z)
  simp only [hGdef]
  rw [mul_one, jacquetVector3_iotaGL_diagUnitGL2_mul, jacquetVector3_eq, MonoidHom.comp_apply,
    ideleChar_section_eq_quasiChar_realCoord σ t e ht E hE z, norm_eq_abs_realCoord, hc, inv_mul_cancel_right₀ hy0]
  ring

section E0_slice_bound

open scoped BigOperators
open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam signShift signShift_zero RealArchParam.gammaR RealArchParam.gammaC RealArchParam.twist RealArchParam.dual RealArchParam.centralExponent RealArchParam.discrete RealArchParam.principal CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq embedMat2 iotaGL IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 transposeInv3 diagUnitGL2 jacquetVector3_iotaGL_diagUnitGL2_mul integrable_jacquetIntegrand3_dilate_mul_quasiChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (ι : Type) [Fintype ι] (N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢((ι → ℝ), ℂ)) (ξ : ι → ℝ),
      ‖∫ u : ι → ℝ, φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (s.sup (schwartzSeminormFamily ℝ (ι → ℝ) ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  classical

  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let T : 𝓢((ι → ℝ), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
    (SchwartzMap.fourierTransformCLM ℂ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)

  have hcont : ∀ k : ℕ, Continuous
      ((schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ (k, 0)).comp (T : 𝓢((ι → ℝ), ℂ) →ₗ[ℂ] _)) := by
    intro k
    exact ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ ι) ℂ).continuous_seminorm (k, 0)).comp T.continuous
  obtain ⟨s₀, C₀, -, h₀⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (ι → ℝ) ℂ) _ (hcont 0)
  obtain ⟨s₁, C₁, -, h₁⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (ι → ℝ) ℂ) _ (hcont N)
  refine ⟨s₀ ∪ s₁, 2 ^ N * ((C₀ : ℝ) + C₁), by positivity, ?_⟩
  intro φ ξ
  set S : ℝ := ((s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ (ι → ℝ) ℂ)) φ with hS
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hbridge : ((s₀ ∪ s₁).sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ)) φ = S := by
    rw [hS]
    simp only [Seminorm.finset_sup_apply]
    rfl

  have hb : ∀ (k : ℕ) (sk : Finset (ℕ × ℕ)) (Ck : NNReal),
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ (k, 0)).comp (T : 𝓢((ι → ℝ), ℂ) →ₗ[ℂ] _) ≤
        Ck • sk.sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ) → sk ⊆ s₀ ∪ s₁ →
        SchwartzMap.seminorm ℂ k 0 (T φ) ≤ (Ck : ℝ) * S := by
    intro k sk Ck hk hsub
    have h1 := Seminorm.le_def.1 hk φ
    have h2 : (sk.sup (schwartzSeminormFamily ℂ (ι → ℝ) ℂ)) φ ≤ S := by
      rw [← hbridge]
      exact Seminorm.le_def.1 (Finset.sup_mono hsub) φ
    simp only [Seminorm.comp_apply, SchwartzMap.schwartzSeminormFamily_apply, Seminorm.smul_apply, NNReal.smul_def,
      smul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 Ck.coe_nonneg)
  have hq₀ := hb 0 s₀ C₀ h₀ Finset.subset_union_left
  have hqN := hb N s₁ C₁ h₁ Finset.subset_union_right

  set x : EuclideanSpace ℝ ι := WithLp.toLp 2 ξ with hx
  have hξx : ‖ξ‖ ≤ ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
    exact PiLp.norm_apply_le x i
  have hTx : T φ x = (𝓕 (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ)) : EuclideanSpace ℝ ι → ℂ) x := by
    simp only [T, ContinuousLinearMap.comp_apply]
    rfl
  have hmp : MeasureTheory.MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)) := by
    simpa using (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm _
  have hId : (∫ u : ι → ℝ, φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I)) =
      T φ x := by
    rw [hTx, Real.fourier_eq', ← hmp.integral_comp']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hinner : @inner ℝ _ _ (WithLp.toLp 2 u : EuclideanSpace ℝ ι) x = ∑ i, ξ i * u i := by
      simp only [hx, PiLp.inner_apply]
      rfl
    simp only [smul_eq_mul, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, e,
      PiLp.coe_continuousLinearEquiv, MeasurableEquiv.coe_toLp, hinner]
    rw [mul_comm]
    congr 2
    push_cast
    ring

  have hpow : ∀ a : ℝ, 0 ≤ a → (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
    intro a ha
    calc (1 + a) ^ N ≤ (2 * max 1 a) ^ N :=
          pow_le_pow_left₀ (by positivity) (by linarith [le_max_left 1 a, le_max_right 1 a]) N
      _ = 2 ^ N * (max 1 a) ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) := by
          gcongr
          rcases max_cases 1 a with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
          · rw [one_pow]; linarith [pow_nonneg ha N]
          · linarith
  have hdecay : (1 + ‖x‖) ^ N * ‖T φ x‖ ≤
      2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := by
    have hA := SchwartzMap.norm_le_seminorm ℂ (T φ) x
    have hB := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T φ) N x
    calc (1 + ‖x‖) ^ N * ‖T φ x‖ ≤ 2 ^ N * (1 + ‖x‖ ^ N) * ‖T φ x‖ :=
          mul_le_mul_of_nonneg_right (hpow _ (norm_nonneg x)) (norm_nonneg _)
      _ = 2 ^ N * (‖T φ x‖ + ‖x‖ ^ N * ‖T φ x‖) := by ring
      _ ≤ 2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := by gcongr

  have hbase : 0 < 1 + ‖ξ‖ := by positivity
  rw [hId, Real.rpow_neg hbase.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hmono : (1 + ‖ξ‖) ^ N ≤ (1 + ‖x‖) ^ N := pow_le_pow_left₀ hbase.le (by linarith) N
  calc ‖T φ x‖ * (1 + ‖ξ‖) ^ N ≤ ‖T φ x‖ * (1 + ‖x‖) ^ N :=
        mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
    _ = (1 + ‖x‖) ^ N * ‖T φ x‖ := mul_comm _ _
    _ ≤ 2 ^ N * (SchwartzMap.seminorm ℂ 0 0 (T φ) + SchwartzMap.seminorm ℂ N 0 (T φ)) := hdecay
    _ ≤ 2 ^ N * ((C₀ : ℝ) * S + (C₁ : ℝ) * S) := by gcongr
    _ = 2 ^ N * ((C₀ : ℝ) + C₁) * S := by ring

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam signShift signShift_zero RealArchParam.gammaR RealArchParam.gammaC RealArchParam.twist RealArchParam.dual RealArchParam.centralExponent RealArchParam.discrete RealArchParam.principal CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq embedMat2 iotaGL IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 transposeInv3 diagUnitGL2 jacquetVector3_iotaGL_diagUnitGL2_mul integrable_jacquetIntegrand3_dilate_mul_quasiChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod"
namespace G0
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem iteratedDeriv_real_exp (n : ℕ) : iteratedDeriv n Real.exp = Real.exp := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]

private theorem norm_iteratedFDeriv_real_exp_le (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp y‖ ≤ Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos y)]

private theorem exists_forall_pow_mul_exp_neg_pi_sq_le (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → t ^ m * Real.exp (-(Real.pi * t ^ 2)) ≤ C := by
  refine ⟨1 + m.factorial / Real.pi ^ m, fun t ht => ?_⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  have hexp : (Real.pi * t ^ 2) ^ m / m.factorial ≤ Real.exp (Real.pi * t ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) m
  have hpos : 0 < Real.exp (Real.pi * t ^ 2) := Real.exp_pos _
  rw [Real.exp_neg]
  rcases le_or_gt t 1 with h1 | h1
  · calc t ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ 1 * 1 := by
          gcongr
          · exact pow_le_one₀ ht h1
          · exact inv_le_one_of_one_le₀ (Real.one_le_exp (by positivity))
      _ ≤ 1 + m.factorial / Real.pi ^ m := by
          have : (0 : ℝ) ≤ m.factorial / Real.pi ^ m := by positivity
          linarith
  ·
    have htm : t ^ m ≤ (t ^ 2) ^ m := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ h1.le (by omega)
    have key : (t ^ 2) ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ m.factorial / Real.pi ^ m := by
      rw [mul_inv_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have := hexp
      rw [div_le_iff₀ (by positivity), mul_pow] at this
      nlinarith [this, pow_pos hπ m, pow_nonneg (sq_nonneg t) m]
    calc t ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ ≤ (t ^ 2) ^ m * (Real.exp (Real.pi * t ^ 2))⁻¹ := by
          gcongr
      _ ≤ m.factorial / Real.pi ^ m := key
      _ ≤ 1 + m.factorial / Real.pi ^ m := by linarith

private theorem norm_sq_le_sum_sq {ι : Type} [Fintype ι] (x : ι → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim x 0]
  · obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖x i‖
    have hnorm : ‖x‖ = ‖x i‖ := by
      apply le_antisymm
      · exact pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 hi
      · exact norm_le_pi_norm x i
    rw [hnorm, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

variable {ι : Type} [Fintype ι]

private def quad (x : ι → ℝ) : ℝ := -(Real.pi * ∑ i, x i ^ 2)

private theorem contDiff_quad : ContDiff ℝ (⊤ : ℕ∞) (quad (ι := ι)) := by
  unfold quad
  apply ContDiff.neg
  apply ContDiff.mul contDiff_const
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).pow 2

private theorem norm_proj_le_one (i : ι) : ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using norm_le_pi_norm x i

private theorem norm_iteratedFDeriv_proj_le (i : ι) (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖ ≤ max ‖x‖ 1 := by
  rcases j with _ | j
  · rw [norm_iteratedFDeriv_zero]
    exact (norm_le_pi_norm x i).trans (le_max_left _ _)
  · rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) =
        fun _ => (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) := funext fun _ => ContinuousLinearMap.fderiv _
    rw [hfd]
    rcases j with _ | j
    · rw [norm_iteratedFDeriv_zero]
      exact (norm_proj_le_one i).trans (le_max_right _ _)
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
      simp

private theorem contDiff_proj (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
  exact ContinuousLinearMap.contDiff _

private theorem norm_iteratedFDeriv_coord_sq_le (i : ι) (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ι → ℝ => y i ^ 2) x‖ ≤ 2 ^ j * max ‖x‖ 1 ^ 2 := by
  have hfun : (fun y : ι → ℝ => y i ^ 2) = fun y => (ContinuousLinearMap.mul ℝ ℝ)
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) y) ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) y) := by
    funext y; simp [sq]
  rw [hfun]
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear (contDiff_proj i) (contDiff_proj i) x
    (n := j) (by exact_mod_cast le_top)).trans ?_
  have hm : (0 : ℝ) ≤ max ‖x‖ 1 := le_max_of_le_right zero_le_one
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖ *
            ‖iteratedFDeriv ℝ (j - k) (⇑(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x‖
        ≤ 1 * ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * max ‖x‖ 1 * max ‖x‖ 1 := by
          gcongr with k _
          all_goals first
            | exact Finset.sum_nonneg fun k _ => by positivity
            | exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
            | exact norm_iteratedFDeriv_proj_le i _ x
            | positivity
      _ = 2 ^ j * max ‖x‖ 1 ^ 2 := by
          rw [one_mul, ← Finset.sum_mul, ← Finset.sum_mul]
          have h2 : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) = 2 ^ j := by
            exact_mod_cast Nat.sum_range_choose j
          rw [h2]; ring

private theorem norm_iteratedFDeriv_quad_le (j : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (quad (ι := ι)) x‖ ≤ Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) := by
  have hq : quad (ι := ι) = fun y => (-Real.pi) • ∑ i, (fun z : ι → ℝ => z i ^ 2) y := by
    funext y; simp [quad]
  rw [hq]
  have hcd : ∀ i : ι, ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => z i ^ 2) := fun i => (contDiff_apply ℝ ℝ i).pow 2
  have hcdj : ∀ i : ι, ContDiff ℝ (j : ℕ) (fun z : ι → ℝ => z i ^ 2) := fun i => (hcd i).of_le (by exact_mod_cast le_top)
  have hS : ContDiff ℝ (j : ℕ) (fun y : ι → ℝ => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) :=
    ContDiff.sum fun i _ => hcdj i
  have hsplit := congrFun (iteratedFDeriv_sum (𝕜 := ℝ) (f := fun i : ι => fun z : ι → ℝ => z i ^ 2) (u := Finset.univ)
    (i := j) (fun i _ => hcdj i)) x
  simp only [Finset.sum_apply] at hsplit
  calc ‖iteratedFDeriv ℝ j (fun y => (-Real.pi) • ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖
      = ‖(-Real.pi) • iteratedFDeriv ℝ j (fun y => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖ := by
        rw [iteratedFDeriv_const_smul_apply' hS.contDiffAt]
    _ = Real.pi * ‖iteratedFDeriv ℝ j (fun y => ∑ i, (fun z : ι → ℝ => z i ^ 2) y) x‖ := by
        rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi * ∑ i : ι, ‖iteratedFDeriv ℝ j (fun z : ι → ℝ => z i ^ 2) x‖ := by
        gcongr
        rw [hsplit]
        exact norm_sum_le _ _
    _ ≤ Real.pi * ∑ _i : ι, 2 ^ j * max ‖x‖ 1 ^ 2 := by
        gcongr with i _
        exact norm_iteratedFDeriv_coord_sq_le i j x
    _ = Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private def gauss (x : ι → ℝ) : ℝ := Real.exp (quad x)

private theorem contDiff_gauss : ContDiff ℝ (⊤ : ℕ∞) (gauss (ι := ι)) :=
  Real.contDiff_exp.comp contDiff_quad

private theorem norm_iteratedFDeriv_quad_le_pow (j : ℕ) (hj : 1 ≤ j) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ j (quad (ι := ι)) x‖ ≤ (2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2) ^ j := by
  set A : ℝ := Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hD2 : (2 : ℝ) ≤ 2 * A + 2 := by linarith
  refine (norm_iteratedFDeriv_quad_le j x).trans ?_
  have hre : Real.pi * Fintype.card ι * (2 ^ j * max ‖x‖ 1 ^ 2) = 2 ^ j * A := by rw [hA]; ring
  have hD : 2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2 = 2 * A + 2 := by rw [hA]; ring
  rw [hre, hD]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  calc (2 : ℝ) ^ (k + 1) * A = 2 ^ k * (2 * A) := by ring
    _ ≤ (2 * A + 2) ^ k * (2 * A + 2) := by
        gcongr
        linarith
    _ = (2 * A + 2) ^ (k + 1) := by ring

private theorem norm_iteratedFDeriv_gauss_le (n : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤
      n.factorial * Real.exp (quad x) * (2 * Real.pi * Fintype.card ι * max ‖x‖ 1 ^ 2 + 2) ^ n := by
  have h : gauss (ι := ι) = Real.exp ∘ quad := rfl
  rw [h]
  exact norm_iteratedFDeriv_comp_le Real.contDiff_exp contDiff_quad (by exact_mod_cast le_top) x
    (fun i _ => norm_iteratedFDeriv_real_exp_le i (quad x))
    (fun i hi _ => norm_iteratedFDeriv_quad_le_pow i hi x)

private theorem exp_quad_le (x : ι → ℝ) : Real.exp (quad x) ≤ Real.exp (-(Real.pi * ‖x‖ ^ 2)) := by
  apply Real.exp_le_exp.2
  unfold quad
  have := norm_sq_le_sum_sq x
  nlinarith [Real.pi_pos]

private theorem gauss_decay (k n : ℕ) : ∃ C : ℝ, ∀ x : ι → ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖ ≤ C := by

  set c₁ : ℝ := 2 * Real.pi * Fintype.card ι + 2 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  obtain ⟨C₀, hC₀⟩ := exists_forall_pow_mul_exp_neg_pi_sq_le (k + 2 * n)
  refine ⟨n.factorial * c₁ ^ n * (2 ^ (k + 2 * n) * (1 + C₀)), fun x => ?_⟩
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  set t : ℝ := ‖x‖ with ht
  have hmax : max t 1 ≤ 1 + t := max_le (by linarith) (by linarith)
  have hD : 2 * Real.pi * Fintype.card ι * max t 1 ^ 2 + 2 ≤ c₁ * (1 + t) ^ 2 := by
    have h1 : max t 1 ^ 2 ≤ (1 + t) ^ 2 := pow_le_pow_left₀ (le_max_of_le_right zero_le_one) hmax 2
    have h2 : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Fintype.card ι)
    rw [hc₁]; nlinarith [h3, h2]
  have hgauss : Real.exp (quad x) ≤ Real.exp (-(Real.pi * t ^ 2)) := exp_quad_le x
  have hexp0 : 0 < Real.exp (-(Real.pi * t ^ 2)) := Real.exp_pos _
  have hpow : t ^ k * (1 + t) ^ (2 * n) ≤ (1 + t) ^ (k + 2 * n) := by
    rw [pow_add]; gcongr; linarith
  have hkey : (1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2)) ≤ 2 ^ (k + 2 * n) * (1 + C₀) := by
    have hC₀' := hC₀ t hx0
    have hexp1 : Real.exp (-(Real.pi * t ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have hbin : (1 + t) ^ (k + 2 * n) ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) := by
      have hm : (1 + t) ≤ 2 * max 1 t := by linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
      calc (1 + t) ^ (k + 2 * n) ≤ (2 * max 1 t) ^ (k + 2 * n) := by gcongr
        _ = 2 ^ (k + 2 * n) * max 1 t ^ (k + 2 * n) := mul_pow _ _ _
        _ ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) := by
            gcongr
            rcases le_total t 1 with h | h
            · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx0 (k + 2 * n)]
            · rw [max_eq_right h]; linarith
    calc (1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))
        ≤ 2 ^ (k + 2 * n) * (1 + t ^ (k + 2 * n)) * Real.exp (-(Real.pi * t ^ 2)) := by gcongr
      _ = 2 ^ (k + 2 * n) * (Real.exp (-(Real.pi * t ^ 2)) + t ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))) := by
          ring
      _ ≤ 2 ^ (k + 2 * n) * (1 + C₀) := by gcongr
  calc t ^ k * ‖iteratedFDeriv ℝ n (gauss (ι := ι)) x‖
      ≤ t ^ k * (n.factorial * Real.exp (quad x) * (2 * Real.pi * Fintype.card ι * max t 1 ^ 2 + 2) ^ n) := by
        gcongr; exact norm_iteratedFDeriv_gauss_le n x
    _ ≤ t ^ k * (n.factorial * Real.exp (-(Real.pi * t ^ 2)) * (c₁ * (1 + t) ^ 2) ^ n) := by
        gcongr
    _ = n.factorial * c₁ ^ n * ((t ^ k * (1 + t) ^ (2 * n)) * Real.exp (-(Real.pi * t ^ 2))) := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ n.factorial * c₁ ^ n * ((1 + t) ^ (k + 2 * n) * Real.exp (-(Real.pi * t ^ 2))) := by gcongr
    _ ≤ n.factorial * c₁ ^ n * (2 ^ (k + 2 * n) * (1 + C₀)) := by gcongr

private theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq' :
    ∃ Φ : SchwartzMap (ι → ℝ) ℝ, ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) :=
  ⟨⟨gauss, contDiff_gauss, gauss_decay⟩, fun _ => rfl⟩

private abbrev Arr : Type := Fin 2 → Fin 3 → ℝ

private abbrev Pl : Type := Fin 2 → ℝ

private def blk (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : Arr := fun i => ![h i 0, h i 1, w i]

private def rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : Arr := fun i b => (Matrix.of X * T) i b

private theorem rmul_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) (i : Fin 2) (b : Fin 3) :
    rmul T X i b = ∑ k : Fin 3, X i k * T k b := by
  simp [rmul, Matrix.mul_apply]

private theorem rmul_add (T : Matrix (Fin 3) (Fin 3) ℝ) (X Y : Arr) : rmul T (X + Y) = rmul T X + rmul T Y := by
  funext i b; simp [rmul_apply, add_mul, Finset.sum_add_distrib]

private theorem rmul_smul (T : Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (X : Arr) : rmul T (c • X) = c • rmul T X := by
  funext i b; simp [rmul_apply, Finset.mul_sum, mul_assoc]

private theorem rmul_rmul (T S : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : rmul S (rmul T X) = rmul (T * S) X := by
  funext i b
  simp only [rmul_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem rmul_inv_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (X : Arr) : rmul T⁻¹ (rmul T X) = X := by
  rw [rmul_rmul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hT)]
  funext i b; simp [rmul_apply, Matrix.one_apply]

private theorem blk_add (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : blk h w = blk h 0 + blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

private theorem blk_zero_add_smul (w w' : Pl) : blk 0 (w + w') = blk 0 w + blk 0 w' := by
  funext i b; fin_cases b <;> simp [blk]

private theorem blk_zero_smul (c : ℝ) (w : Pl) : blk 0 (c • w) = c • blk 0 w := by
  funext i b; fin_cases b <;> simp [blk]

private def mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ‖(fun i j => T i j : Fin 3 → Fin 3 → ℝ)‖

private theorem mnorm_nonneg (T : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ mnorm T := norm_nonneg _

private theorem abs_entry_le_mnorm (T : Matrix (Fin 3) (Fin 3) ℝ) (k b : Fin 3) : |T k b| ≤ mnorm T := by
  have h1 := norm_le_pi_norm (fun i j => T i j : Fin 3 → Fin 3 → ℝ) k
  have h2 := norm_le_pi_norm (fun j => T k j : Fin 3 → ℝ) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

private theorem abs_entry_le_norm (X : Arr) (i : Fin 2) (b : Fin 3) : |X i b| ≤ ‖X‖ := by
  have h1 := norm_le_pi_norm X i
  have h2 := norm_le_pi_norm (X i) b
  simp only [Real.norm_eq_abs] at h2
  exact h2.trans h1

private theorem norm_rmul_le (T : Matrix (Fin 3) (Fin 3) ℝ) (X : Arr) : ‖rmul T X‖ ≤ 3 * ‖X‖ * mnorm T := by
  have hnn : (0 : ℝ) ≤ 3 * ‖X‖ * mnorm T := mul_nonneg (by positivity) (mnorm_nonneg T)
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => (pi_norm_le_iff_of_nonneg hnn).2 fun b => ?_
  rw [Real.norm_eq_abs, rmul_apply]
  calc |∑ k : Fin 3, X i k * T k b| ≤ ∑ k : Fin 3, |X i k * T k b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 3, ‖X‖ * mnorm T := by
        gcongr with k _
        rw [abs_mul]
        exact mul_le_mul (abs_entry_le_norm X i k) (abs_entry_le_mnorm T k b) (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖X‖ * mnorm T := by simp [Finset.sum_const]; ring

private theorem norm_le_norm_blk_left (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖h‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  fin_cases j
  · have h2 := norm_le_pi_norm (blk h w i) 0
    simp only [blk, Matrix.cons_val_zero] at h2
    exact h2.trans h1
  · have h2 := norm_le_pi_norm (blk h w i) 1
    simp only [blk, Matrix.cons_val_one] at h2
    exact h2.trans h1

private theorem norm_le_norm_blk_right (h : Fin 2 → Fin 2 → ℝ) (w : Pl) : ‖w‖ ≤ ‖blk h w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 := norm_le_pi_norm (blk h w) i
  have h2 := norm_le_pi_norm (blk h w i) 2
  simp only [blk] at h2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
  exact h2.trans h1

private def sliceLin (T : Matrix (Fin 3) (Fin 3) ℝ) : Pl →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => rmul T (blk 0 w)
      map_add' := fun w w' => by rw [blk_zero_add_smul, rmul_add]
      map_smul' := fun c w => by rw [blk_zero_smul, rmul_smul]; rfl }

private theorem sliceLin_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (w : Pl) : sliceLin T w = rmul T (blk 0 w) := rfl

private theorem rmul_blk_eq (T : Matrix (Fin 3) (Fin 3) ℝ) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    rmul T (blk h w) = sliceLin T w + rmul T (blk h 0) := by
  rw [blk_add, rmul_add, sliceLin_apply, add_comm]

private theorem norm_blk_zero_le (w : Pl) : ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  fin_cases b <;> simp [blk]
  exact norm_le_pi_norm w i

private theorem norm_sliceLin_le (T : Matrix (Fin 3) (Fin 3) ℝ) : ‖sliceLin T‖ ≤ 3 * mnorm T := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (mnorm_nonneg T)) fun w => ?_
  rw [sliceLin_apply]
  calc ‖rmul T (blk 0 w)‖ ≤ 3 * ‖blk (0 : Fin 2 → Fin 2 → ℝ) w‖ * mnorm T := norm_rmul_le T _
    _ ≤ 3 * ‖w‖ * mnorm T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_blk_zero_le w) (by norm_num)) (mnorm_nonneg T)
    _ = 3 * mnorm T * ‖w‖ := by ring

private theorem norm_iteratedFDeriv_slice_le {F : Arr → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (T : Matrix (Fin 3) (Fin 3) ℝ)
    (h : Fin 2 → Fin 2 → ℝ) (n : ℕ) (w : Pl) :
    ‖iteratedFDeriv ℝ n (fun w' : Pl => F (rmul T (blk h w'))) w‖ ≤
      ‖sliceLin T‖ ^ n * ‖iteratedFDeriv ℝ n F (rmul T (blk h w))‖ := by
  have hfun : (fun w' : Pl => F (rmul T (blk h w'))) = (fun X => F (X + rmul T (blk h 0))) ∘ (sliceLin T) := by
    funext w'; simp only [Function.comp]; rw [rmul_blk_eq T h w']
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun X : Arr => F (X + rmul T (blk h 0))) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [hfun, (sliceLin T).iteratedFDeriv_comp_right hG w (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]
  gcongr
  rw [iteratedFDeriv_comp_add_right, rmul_blk_eq T h w]

open scoped SchwartzMap

private theorem norm_blk_le_norm_rmul (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) (w : Pl) :
    ‖blk h w‖ ≤ 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by
  calc ‖blk h w‖ = ‖rmul T⁻¹ (rmul T (blk h w))‖ := by rw [rmul_inv_rmul T hT]
    _ ≤ 3 * ‖rmul T (blk h w)‖ * mnorm T⁻¹ := norm_rmul_le _ _
    _ = 3 * mnorm T⁻¹ * ‖rmul T (blk h w)‖ := by ring

private theorem exists_bound_mnorm_of_isCompact (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hKdet : ∀ T ∈ K, T.det ≠ 0) : ∃ R : ℝ, 1 ≤ R ∧ ∀ T ∈ K, mnorm T ≤ R ∧ mnorm T⁻¹ ≤ R := by
  have hc1 : Continuous (fun T : Matrix (Fin 3) (Fin 3) ℝ => (fun i j => T i j : Fin 3 → Fin 3 → ℝ)) :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  have hinv : ContinuousOn (fun T : Matrix (Fin 3) (Fin 3) ℝ => T⁻¹) K := fun T hT =>
    (continuousAt_matrix_inv T (by
      have hdet : T.det ≠ 0 := hKdet T hT
      simpa [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet))).continuousWithinAt
  have hc2 : ContinuousOn (fun T : Matrix (Fin 3) (Fin 3) ℝ => (fun i j => T⁻¹ i j : Fin 3 → Fin 3 → ℝ)) K :=
    hc1.comp_continuousOn hinv
  obtain ⟨R₁, hR₁⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨R₂, hR₂⟩ := hK.exists_bound_of_continuousOn hc2
  refine ⟨max 1 (max R₁ R₂), le_max_left _ _, fun T hT => ⟨?_, ?_⟩⟩
  · exact (hR₁ T hT).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hR₂ T hT).trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ K, ∀ (h : Fin 2 → Fin 2 → ℝ) (w : Pl),
      ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (fun w' : Pl => Ψ (rmul T (blk h w'))) w‖ ≤ C * ((1 + ‖h‖) ^ N)⁻¹ := by
  obtain ⟨R, hR1, hR⟩ := exists_bound_mnorm_of_isCompact K hK hKdet
  set m : ℕ := k + N with hm

  set B : ℝ := 2 ^ m * (Finset.Iic (m, n)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) Ψ with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  have hΨ : ∀ P : Arr, (1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ ≤ B := fun P =>
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (m, n)) le_rfl le_rfl Ψ P
  have h3R : (1 : ℝ) ≤ 3 * R := by linarith
  refine ⟨(3 * R) ^ n * (3 * R) ^ m * B, by positivity, fun T hT h w => ?_⟩
  obtain ⟨hTn, hTi⟩ := hR T hT
  set P : Arr := rmul T (blk h w) with hP
  have hpos : (0 : ℝ) < (1 + ‖h‖) ^ N := by positivity
  rw [le_mul_inv_iff₀ hpos]

  have hblk : 1 + ‖blk h w‖ ≤ 3 * R * (1 + ‖P‖) := by
    have h1 := norm_blk_le_norm_rmul T (hKdet T hT) h w
    have h2 : 3 * mnorm T⁻¹ * ‖P‖ ≤ 3 * R * ‖P‖ := by
      gcongr
    nlinarith [norm_nonneg P]
  have hsl : ‖sliceLin T‖ ≤ 3 * R := (norm_sliceLin_le T).trans (by gcongr)
  have hD := norm_iteratedFDeriv_slice_le (F := ⇑Ψ) (Ψ.smooth (⊤ : ℕ∞)) T h n w
  have hw : ‖w‖ ≤ ‖blk h w‖ := norm_le_norm_blk_right h w
  have hh : ‖h‖ ≤ ‖blk h w‖ := norm_le_norm_blk_left h w
  have hD0 : 0 ≤ ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ := norm_nonneg _
  calc ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (fun w' : Pl => Ψ (rmul T (blk h w'))) w‖ * (1 + ‖h‖) ^ N
      ≤ (1 + ‖blk h w‖) ^ k * (‖sliceLin T‖ ^ n * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) * (1 + ‖blk h w‖) ^ N := by
        gcongr
        linarith
    _ ≤ (1 + ‖blk h w‖) ^ k * ((3 * R) ^ n * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) * (1 + ‖blk h w‖) ^ N := by
        gcongr
    _ = (3 * R) ^ n * ((1 + ‖blk h w‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        rw [hm, pow_add]; ring
    _ ≤ (3 * R) ^ n * ((3 * R * (1 + ‖P‖)) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        gcongr
    _ = (3 * R) ^ n * (3 * R) ^ m * ((1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        rw [mul_pow (3 * R) (1 + ‖P‖) m]; ring
    _ ≤ (3 * R) ^ n * (3 * R) ^ m * B := by
        gcongr
        exact hΨ P

private def sliceSchwartz (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ) :
    𝓢(Pl, ℂ) where
  toFun := fun w => Ψ (rmul T (blk h w))
  smooth' := by
    have hfun : (fun w : Pl => rmul T (blk h w)) = fun w => sliceLin T w + rmul T (blk h 0) :=
      funext fun w => rmul_blk_eq T h w
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun w : Pl => rmul T (blk h w)) := by
      rw [hfun]; exact (sliceLin T).contDiff.add contDiff_const
    exact (Ψ.smooth (⊤ : ℕ∞)).comp hc
  decay' := by
    intro k n
    obtain ⟨C, -, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Ψ {T} isCompact_singleton
      (by simpa using hT) k n 0
    refine ⟨C, fun w => ?_⟩
    simpa using hC T (Set.mem_singleton T) h w

private theorem sliceSchwartz_apply (Ψ : 𝓢(Arr, ℂ)) (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T.det ≠ 0) (h : Fin 2 → Fin 2 → ℝ)
    (w : Pl) : sliceSchwartz Ψ T hT h w = Ψ (rmul T (blk h w)) := rfl

private theorem exists_forall_seminorm_sliceSchwartz_le (Ψ : 𝓢(Arr, ℂ)) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K)
    (hKdet : ∀ T ∈ K, T.det ≠ 0) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : T ∈ K) (h : Fin 2 → Fin 2 → ℝ),
      SchwartzMap.seminorm ℝ k n (sliceSchwartz Ψ T (hKdet T hT) h) ≤ C * ((1 + ‖h‖) ^ N)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_slice_le Ψ K hK hKdet k n N
  refine ⟨C, hC0, fun T hT h => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun w => ?_
  exact hC T hT h w

private theorem character_eq (c : ℝ) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) (v : Pl) :
    c * v 1 = ∑ i, (c • ((Matrix.of h)⁻¹ 1)) i * ((Matrix.of h).mulVec v) i := by
  have hv : (Matrix.of h)⁻¹.mulVec ((Matrix.of h).mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  have h1 : v 1 = ∑ i, (Matrix.of h)⁻¹ 1 i * ((Matrix.of h).mulVec v) i := by
    conv_lhs => rw [← hv]
    simp [Matrix.mulVec, dotProduct]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem _root_.LanglandsTunnell.CubicInduction.G0.integral_comp_mulVec_eq {G : Pl → ℂ} (hG : Continuous G) (h : Fin 2 → Fin 2 → ℝ) (hdet : (Matrix.of h).det ≠ 0) :
    ∫ v : Pl, G ((Matrix.of h).mulVec v) = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) * ∫ u : Pl, G u := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 2) hdet
  have hmeas : Measurable (Matrix.toLin' (Matrix.of h)) := (Matrix.toLin' (Matrix.of h)).continuous_of_finiteDimensional.measurable
  have hfun : (fun v : Pl => G ((Matrix.of h).mulVec v)) = fun v => G (Matrix.toLin' (Matrix.of h) v) := by
    funext v; simp [Matrix.toLin'_apply]
  rw [hfun, ← MeasureTheory.integral_map hmeas.aemeasurable (hG.aestronglyMeasurable), hmap,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (by positivity), abs_inv]
  exact Complex.real_smul

p2m_export "LanglandsTunnell.CubicInduction.G0" "integral_comp_mulVec_eq"

private theorem inv_pow_mul_inv_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    ((1 + a) ^ N)⁻¹ * ((1 + b) ^ N)⁻¹ ≤ ((1 + a + b) ^ N)⁻¹ := by
  rw [← mul_inv, ← mul_pow]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg ha hb]

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (c : ℝ) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨s, C₂, hC₂0, hB2⟩ :=
    LanglandsTunnell.CubicInduction.exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (Fin 2) N

  choose C₁ hC₁0 hC₁ using fun p : ℕ × ℕ => exists_forall_seminorm_sliceSchwartz_le Ψ K hK hKdet p.1 p.2 N
  set C₁s : ℝ := ∑ p ∈ s, C₁ p with hC₁s
  have hC₁s0 : 0 ≤ C₁s := Finset.sum_nonneg fun p _ => hC₁0 p
  refine ⟨C₂ * C₁s, fun T hT h hdet => ?_⟩
  set φ : 𝓢(Pl, ℂ) := sliceSchwartz Ψ T (hKdet T hT) h with hφ
  set ξ : Pl := c • ((Matrix.of h)⁻¹ 1) with hξ

  set G : Pl → ℂ := fun u => φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := by
    rw [hG]
    refine φ.continuous.mul (Complex.continuous_exp.comp ?_)
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).neg
  have hint : (fun v : Pl =>
      Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
        Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) = fun v => G ((Matrix.of h).mulVec v) := by
    funext v
    rw [hG]
    simp only []
    rw [hφ, sliceSchwartz_apply]
    congr 2
    rw [mul_assoc (2 * Real.pi) c (v 1), character_eq c h hdet v]
  rw [hint, integral_comp_mulVec_eq hGc h hdet, norm_mul, Complex.norm_of_nonneg (by positivity)]

  have hsup : (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ ≤ C₁s * ((1 + ‖h‖) ^ N)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
    obtain ⟨a, b⟩ := p
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hC₁ (a, b) T hT h).trans (by gcongr; exact Finset.single_le_sum (fun q _ => hC₁0 q) hp)
  have hξn : ‖ξ‖ = |c| * ‖(Matrix.of h)⁻¹ 1‖ := by rw [hξ, norm_smul, Real.norm_eq_abs]
  have hrpow : ∀ x : ℝ, 0 ≤ x → x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx, Real.rpow_natCast]
  have hdetpos : 0 < |(Matrix.of h).det|⁻¹ := by positivity
  calc |(Matrix.of h).det|⁻¹ * ‖∫ u : Pl, G u‖
      ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
        gcongr
        exact hB2 φ ξ
    _ ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (C₁s * ((1 + ‖h‖) ^ N)⁻¹) * ((1 + ‖ξ‖) ^ N)⁻¹) := by
        rw [hrpow _ (by positivity)]
        gcongr
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖ξ‖) ^ N)⁻¹) := by ring
    _ ≤ C₂ * C₁s * |(Matrix.of h).det|⁻¹ * ((1 + ‖h‖ + ‖ξ‖) ^ N)⁻¹ := by
        gcongr
        exact inv_pow_mul_inv_pow_le _ _ (norm_nonneg _) (norm_nonneg _) N
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
        rw [hrpow _ (by positivity), hξn]

end LanglandsTunnell.CubicInduction.G0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam signShift signShift_zero RealArchParam.gammaR RealArchParam.gammaC RealArchParam.twist RealArchParam.dual RealArchParam.centralExponent RealArchParam.discrete RealArchParam.principal CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq embedMat2 iotaGL IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 transposeInv3 diagUnitGL2 jacquetVector3_iotaGL_diagUnitGL2_mul integrable_jacquetIntegrand3_dilate_mul_quasiChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_schwartzMap_eq_exp_neg_pi_sum_sq (ι : Type) [Fintype ι] :
    ∃ Φ : 𝓢((ι → ℝ), ℝ), ∀ x : ι → ℝ, Φ x = Real.exp (-(Real.pi * ∑ i, x i ^ 2)) := by
  exact G0.exists_schwartzMap_eq_exp_neg_pi_sum_sq' (ι := ι)

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (c : ℝ) (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (_hK : IsCompact K) (_hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  exact G0.norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le' Ψ N c K _hK _hKdet

open G0 in

private theorem norm_integral_schwartzMap_cols_mulVec_mul_right_mul_exp_le_uniform (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ)
    (K : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hK : IsCompact K) (hKdet : ∀ T ∈ K, T.det ≠ 0) :
    ∃ C : ℝ, ∀ (c : ℝ), ∀ T ∈ K, ∀ h : Fin 2 → Fin 2 → ℝ, (Matrix.of h).det ≠ 0 →
      ‖∫ v : Fin 2 → ℝ,
          Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
            Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
  obtain ⟨s, C₂, hC₂0, hB2⟩ :=
    LanglandsTunnell.CubicInduction.exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (Fin 2) N
  choose C₁ hC₁0 hC₁ using fun p : ℕ × ℕ => exists_forall_seminorm_sliceSchwartz_le Ψ K hK hKdet p.1 p.2 N
  set C₁s : ℝ := ∑ p ∈ s, C₁ p with hC₁s
  have hC₁s0 : 0 ≤ C₁s := Finset.sum_nonneg fun p _ => hC₁0 p
  refine ⟨C₂ * C₁s, fun c T hT h hdet => ?_⟩
  set φ : 𝓢(Pl, ℂ) := sliceSchwartz Ψ T (hKdet T hT) h with hφ
  set ξ : Pl := c • ((Matrix.of h)⁻¹ 1) with hξ
  set G : Pl → ℂ := fun u => φ u * Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * u i) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := by
    rw [hG]
    refine φ.continuous.mul (Complex.continuous_exp.comp ?_)
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).neg
  have hint : (fun v : Pl =>
      Ψ (fun i b => (Matrix.of (fun i' => ![h i' 0, h i' 1, (Matrix.of h).mulVec v i']) * T) i b) *
        Complex.exp (((-(2 * Real.pi * c * v 1) : ℝ) : ℂ) * Complex.I)) = fun v => G ((Matrix.of h).mulVec v) := by
    funext v
    rw [hG]
    simp only []
    rw [hφ, sliceSchwartz_apply]
    congr 2
    rw [mul_assoc (2 * Real.pi) c (v 1), character_eq c h hdet v]
  rw [hint, integral_comp_mulVec_eq hGc h hdet, norm_mul, Complex.norm_of_nonneg (by positivity)]
  have hsup : (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ ≤ C₁s * ((1 + ‖h‖) ^ N)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
    obtain ⟨a, b⟩ := p
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hC₁ (a, b) T hT h).trans (by gcongr; exact Finset.single_le_sum (fun q _ => hC₁0 q) hp)
  have hξn : ‖ξ‖ = |c| * ‖(Matrix.of h)⁻¹ 1‖ := by rw [hξ, norm_smul, Real.norm_eq_abs]
  have hrpow : ∀ x : ℝ, 0 ≤ x → x ^ (-(N : ℝ)) = (x ^ N)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx, Real.rpow_natCast]
  have hdetpos : 0 < |(Matrix.of h).det|⁻¹ := by positivity
  calc |(Matrix.of h).det|⁻¹ * ‖∫ u : Pl, G u‖
      ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (s.sup (schwartzSeminormFamily ℝ Pl ℂ)) φ * (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
        gcongr
        exact hB2 φ ξ
    _ ≤ |(Matrix.of h).det|⁻¹ * (C₂ * (C₁s * ((1 + ‖h‖) ^ N)⁻¹) * ((1 + ‖ξ‖) ^ N)⁻¹) := by
        rw [hrpow _ (by positivity)]
        gcongr
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (((1 + ‖h‖) ^ N)⁻¹ * ((1 + ‖ξ‖) ^ N)⁻¹) := by ring
    _ ≤ C₂ * C₁s * |(Matrix.of h).det|⁻¹ * ((1 + ‖h‖ + ‖ξ‖) ^ N)⁻¹ := by
        gcongr
        exact inv_pow_mul_inv_pow_le _ _ (norm_nonneg _) (norm_nonneg _) N
    _ = C₂ * C₁s * |(Matrix.of h).det|⁻¹ * (1 + ‖h‖ + |c| * ‖(Matrix.of h)⁻¹ 1‖) ^ (-(N : ℝ)) := by
        rw [hrpow _ (by positivity), hξn]

end LanglandsTunnell.CubicInduction

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam signShift signShift_zero RealArchParam.gammaR RealArchParam.gammaC RealArchParam.twist RealArchParam.dual RealArchParam.centralExponent RealArchParam.discrete RealArchParam.principal CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq embedMat2 iotaGL IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 transposeInv3 diagUnitGL2 jacquetVector3_iotaGL_diagUnitGL2_mul integrable_jacquetIntegrand3_dilate_mul_quasiChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Matrix MeasureTheory
open scoped SchwartzMap Matrix

noncomputable section

private def ip (X Y : Fin 2 → Fin 3 → ℝ) : ℝ := ∑ i, ∑ b, X i b * Y i b

private def gram (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => ip (l i) (l j)

namespace SliceBound

private theorem exists_transpose_mul_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n ℝ}
    (hG : G.PosSemidef) (hdet : G.det ≠ 0) :
    ∃ A : Matrix n n ℝ, Aᵀ * G * A = 1 ∧ A * Aᵀ = G⁻¹ ∧ |A.det| = (Real.sqrt G.det)⁻¹ := by
  have hH : G.IsHermitian := hG.1
  set U : Matrix n n ℝ := (hH.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  set lam : n → ℝ := hH.eigenvalues with hlam
  have hdetG : G.det = ∏ i, lam i := by
    have h := hH.det_eq_prod_eigenvalues
    simpa [hlam] using h
  have hpos : ∀ i, 0 < lam i := fun i => by
    have hnn : 0 ≤ lam i := hG.eigenvalues_nonneg i
    have hne : lam i ≠ 0 := by
      rw [hdetG] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
    exact lt_of_le_of_ne hnn (Ne.symm hne)

  have hUtU : Uᵀ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
    simpa [hUdef, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
  have hUUt : U * Uᵀ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
    simpa [hUdef, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

  have hspec : G = U * diagonal lam * Uᵀ := by
    have h := hH.spectral_theorem
    simpa [hUdef, hlam, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, Function.comp_def] using h
  set d : n → ℝ := fun i => (Real.sqrt (lam i))⁻¹ with hd
  have hd_pos : ∀ i, 0 < d i := fun i => inv_pos.2 (Real.sqrt_pos.2 (hpos i))
  have hdd : ∀ i, d i * lam i * d i = 1 := fun i => by
    simp only [hd]
    have hs : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i := Real.mul_self_sqrt (hpos i).le
    have hs0 : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.2 (hpos i)).ne'
    field_simp
    linarith [hs]
  have hdiag1 : diagonal (fun i => d i * lam i * d i) = (1 : Matrix n n ℝ) := by
    rw [← diagonal_one]
    congr 1
    funext i
    exact hdd i
  have hdiag2 : diagonal (fun i => lam i * d i * d i) = (1 : Matrix n n ℝ) := by
    rw [← diagonal_one]
    congr 1
    funext i
    rw [← hdd i]; ring
  refine ⟨U * diagonal d, ?_, ?_, ?_⟩
  ·
    rw [transpose_mul, diagonal_transpose, hspec]
    calc diagonal d * Uᵀ * (U * diagonal lam * Uᵀ) * (U * diagonal d)
        = diagonal d * (Uᵀ * U) * diagonal lam * (Uᵀ * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = diagonal d * diagonal lam * diagonal d := by rw [hUtU, Matrix.mul_one, Matrix.mul_one]
      _ = diagonal (fun i => d i * lam i * d i) := by
          rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      _ = 1 := hdiag1
  ·
    have hinv : G * (U * diagonal d * (U * diagonal d)ᵀ) = 1 := by
      rw [transpose_mul, diagonal_transpose, hspec]
      calc U * diagonal lam * Uᵀ * (U * diagonal d * (diagonal d * Uᵀ))
          = U * (diagonal lam * (Uᵀ * U) * diagonal d * diagonal d) * Uᵀ := by
            simp only [Matrix.mul_assoc]
        _ = U * diagonal (fun i => lam i * d i * d i) * Uᵀ := by
            rw [hUtU, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
        _ = U * Uᵀ := by rw [hdiag2, Matrix.mul_one]
        _ = 1 := hUUt
    exact (Matrix.inv_eq_right_inv hinv).symm
  ·
    have hdetU : |U.det| = 1 := by
      have h1 : U.det * U.det = 1 := by
        have := congrArg Matrix.det hUtU
        rwa [det_mul, det_transpose, det_one] at this
      have h2 : |U.det| * |U.det| = 1 := by rw [← abs_mul, h1, abs_one]
      nlinarith [abs_nonneg U.det]
    rw [det_mul, det_diagonal, abs_mul, hdetU, one_mul, hdetG,
      abs_of_nonneg (Finset.prod_nonneg fun i _ => (hd_pos i).le)]
    simp only [hd]
    rw [Real.sqrt_prod _ (fun i _ => (hpos i).le), Finset.prod_inv_distrib]

private theorem integral_comp_mulVec_eq {G : (Fin 3 → ℝ) → ℂ} (hG : Continuous G) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.det ≠ 0) :
    ∫ t : Fin 3 → ℝ, G (A *ᵥ t) = ((|A.det|⁻¹ : ℝ) : ℂ) * ∫ u : Fin 3 → ℝ, G u := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 3) hA
  have hmeas : Measurable (Matrix.toLin' A) := (Matrix.toLin' A).continuous_of_finiteDimensional.measurable
  have hfun : (fun t : Fin 3 → ℝ => G (A *ᵥ t)) = fun t => G (Matrix.toLin' A t) := by
    funext t; simp [Matrix.toLin'_apply]
  rw [hfun, ← integral_map hmeas.aemeasurable hG.aestronglyMeasurable, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), abs_inv]
  exact Complex.real_smul

private theorem ip_comm (X Y : Fin 2 → Fin 3 → ℝ) : ip X Y = ip Y X := by
  unfold ip
  simp_rw [mul_comm]

private theorem ip_add_left (X Y Z : Fin 2 → Fin 3 → ℝ) : ip (X + Y) Z = ip X Z + ip Y Z := by
  unfold ip
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem ip_smul_left (c : ℝ) (X Z : Fin 2 → Fin 3 → ℝ) : ip (c • X) Z = c * ip X Z := by
  unfold ip
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem ip_sum_left {ι : Type} (s : Finset ι) (X : ι → (Fin 2 → Fin 3 → ℝ)) (Z : Fin 2 → Fin 3 → ℝ) :
    ip (∑ i ∈ s, X i) Z = ∑ i ∈ s, ip (X i) Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_left, ih]

private theorem ip_add_right (X Y Z : Fin 2 → Fin 3 → ℝ) : ip X (Y + Z) = ip X Y + ip X Z := by
  rw [ip_comm, ip_add_left, ip_comm Y, ip_comm Z]

private theorem ip_smul_right (c : ℝ) (X Z : Fin 2 → Fin 3 → ℝ) : ip X (c • Z) = c * ip X Z := by
  rw [ip_comm, ip_smul_left, ip_comm]

private theorem ip_sum_right {ι : Type} (s : Finset ι) (X : Fin 2 → Fin 3 → ℝ) (Z : ι → (Fin 2 → Fin 3 → ℝ)) :
    ip X (∑ i ∈ s, Z i) = ∑ i ∈ s, ip X (Z i) := by
  rw [ip_comm, ip_sum_left]
  simp_rw [ip_comm X]

private theorem ip_self_nonneg (X : Fin 2 → Fin 3 → ℝ) : 0 ≤ ip X X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

private theorem gram_apply (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (i j : Fin 3) : gram l i j = ip (l i) (l j) := rfl

private theorem gram_posSemidef_entry_symm (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) : (gram l)ᵀ = gram l := by
  ext i j
  simp only [transpose_apply, gram_apply, ip_comm]

private theorem ip_reparam (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (A : Matrix (Fin 3) (Fin 3) ℝ) (i k : Fin 3) :
    ip (∑ j, A j i • l j) (∑ m, A m k • l m) = (Aᵀ * gram l * A) i k := by
  rw [ip_sum_left]
  simp only [ip_smul_left, ip_sum_right, ip_smul_right, Matrix.mul_apply, transpose_apply, gram_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  ring

private theorem sum_mulVec_smul (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (A : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    ∑ j, (A *ᵥ t) j • l j = ∑ i, t i • ∑ j, A j i • l j := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

private theorem sum_mul_mulVec (φ : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ) :
    ∑ i, φ i * (A *ᵥ t) i = ∑ i, (Aᵀ *ᵥ φ) i * t i := by
  have h1 : ∑ i, φ i * (A *ᵥ t) i = φ ⬝ᵥ (A *ᵥ t) := rfl
  have h2 : ∑ i, (Aᵀ *ᵥ φ) i * t i = (Aᵀ *ᵥ φ) ⬝ᵥ t := rfl
  rw [h1, h2, dotProduct_mulVec, mulVec_transpose]

private theorem dotProduct_transpose_mulVec_self (φ : Fin 3 → ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (Aᵀ *ᵥ φ) ⬝ᵥ (Aᵀ *ᵥ φ) = φ ⬝ᵥ ((A * Aᵀ) *ᵥ φ) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact dotProduct_comm _ _

private theorem sq_entry_le_ip_self (X : Fin 2 → Fin 3 → ℝ) (i : Fin 2) (b : Fin 3) : X i b ^ 2 ≤ ip X X := by
  unfold ip
  have h1 : X i b * X i b ≤ ∑ b', X i b' * X i b' :=
    Finset.single_le_sum (f := fun b' => X i b' * X i b') (fun b' _ => mul_self_nonneg _) (Finset.mem_univ b)
  have h2 : ∑ b', X i b' * X i b' ≤ ∑ i', ∑ b', X i' b' * X i' b' :=
    Finset.single_le_sum (f := fun i' => ∑ b', X i' b' * X i' b')
      (fun i' _ => Finset.sum_nonneg fun b' _ => mul_self_nonneg _) (Finset.mem_univ i)
  nlinarith [h1, h2]

private theorem norm_le_sqrt_ip_self (X : Fin 2 → Fin 3 → ℝ) : ‖X‖ ≤ Real.sqrt (ip X X) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro b
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_entry_le_ip_self X i b)

private theorem norm_le_sqrt_sum_sq (t : Fin 3 → ℝ) : ‖t‖ ≤ Real.sqrt (∑ i, t i ^ 2) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => t j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))

private theorem ip_self_add_sum_smul (l' : Fin 3 → (Fin 2 → Fin 3 → ℝ))
    (horth : ∀ i k, ip (l' i) (l' k) = if i = k then 1 else 0)
    (q : Fin 2 → Fin 3 → ℝ) (hq : ∀ i, ip q (l' i) = 0) (t : Fin 3 → ℝ) :
    ip (q + ∑ i, t i • l' i) (q + ∑ i, t i • l' i) = ip q q + ∑ i, t i ^ 2 := by
  have hql : ip q (∑ i, t i • l' i) = 0 := by
    rw [ip_sum_right]
    simp [ip_smul_right, hq]
  have hlq : ip (∑ i, t i • l' i) q = 0 := by rw [ip_comm, hql]
  have hll : ip (∑ i, t i • l' i) (∑ i, t i • l' i) = ∑ i, t i ^ 2 := by
    rw [ip_sum_left]
    simp only [ip_smul_left, ip_sum_right, ip_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [ip_add_left, ip_add_right, ip_add_right, hql, hlq, hll]
  ring

private theorem abs_ip_le_of_ip_self_eq_one (v : Fin 2 → Fin 3 → ℝ) (hv : ip v v = 1) (X : Fin 2 → Fin 3 → ℝ) :
    |ip v X| ≤ 6 * ‖X‖ := by
  have hv1 : ∀ i b, |v i b| ≤ 1 := fun i b => by
    have h := sq_entry_le_ip_self v i b
    rw [hv] at h
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [h])
  have hX : ∀ i b, |X i b| ≤ ‖X‖ := fun i b =>
    (norm_le_pi_norm (X i) b).trans' (le_of_eq (Real.norm_eq_abs _).symm) |>.trans (norm_le_pi_norm X i)
  unfold ip
  calc |∑ i, ∑ b, v i b * X i b| ≤ ∑ i, ∑ b, |v i b * X i b| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 2, ∑ b : Fin 3, ‖X‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul]
        calc |v i b| * |X i b| ≤ 1 * ‖X‖ := by gcongr; exact hv1 i b; exact hX i b
          _ = ‖X‖ := one_mul _
    _ = 6 * ‖X‖ := by simp [Finset.sum_const, Finset.card_univ]; ring

private theorem ip_add_sum_smul_of_orth (v : Fin 2 → Fin 3 → ℝ) (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (hv : ∀ i, ip v (l i) = 0)
    (p : Fin 2 → Fin 3 → ℝ) (t : Fin 3 → ℝ) : ip v (p + ∑ i, t i • l i) = ip v p := by
  rw [ip_add_right, ip_sum_right]
  simp [ip_smul_right, hv]

private theorem ip_add_sum_smul_left (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (p : Fin 2 → Fin 3 → ℝ) (t : Fin 3 → ℝ) (j : Fin 3) :
    ip (p + ∑ i, t i • l i) (l j) = ip p (l j) + (gram l *ᵥ t) j := by
  rw [ip_add_left, ip_sum_left]
  simp only [ip_smul_left, Matrix.mulVec, dotProduct, gram_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ip_comm (l i) (l j), mul_comm]

private theorem ip_shift_orth (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (hl : (gram l).det ≠ 0) (p : Fin 2 → Fin 3 → ℝ) (j : Fin 3) :
    ip (p + ∑ i, (-((gram l)⁻¹ *ᵥ fun i => ip p (l i))) i • l i) (l j) = 0 := by
  rw [ip_add_sum_smul_left, Matrix.mulVec_neg, mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hl),
    one_mulVec]
  simp

end SliceBound

private theorem ip_self_le_six_mul_sq_norm (X : Fin 2 → Fin 3 → ℝ) : ip X X ≤ 6 * ‖X‖ ^ 2 := by
  have hX : ∀ i b, X i b * X i b ≤ ‖X‖ ^ 2 := fun i b => by
    have h1 : |X i b| ≤ ‖X‖ :=
      (Real.norm_eq_abs _).symm.le.trans ((norm_le_pi_norm (X i) b).trans (norm_le_pi_norm X i))
    have h2 : 0 ≤ |X i b| := abs_nonneg _
    nlinarith [abs_mul_abs_self (X i b)]
  unfold ip
  calc ∑ i, ∑ b, X i b * X i b ≤ ∑ i : Fin 2, ∑ b : Fin 3, ‖X‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hX i b
    _ = 6 * ‖X‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ]; ring

private theorem sum_sq_le_three_mul_sq_norm (ξ : Fin 3 → ℝ) : ∑ i, ξ i ^ 2 ≤ 3 * ‖ξ‖ ^ 2 := by
  have h : ∀ i, ξ i ^ 2 ≤ ‖ξ‖ ^ 2 := fun i => by
    have h1 : |ξ i| ≤ ‖ξ‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm ξ i)
    nlinarith [abs_nonneg (ξ i), sq_abs (ξ i)]
  calc ∑ i, ξ i ^ 2 ≤ ∑ i : Fin 3, ‖ξ‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖ξ‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ]

private noncomputable def sliceCLM (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t => ∑ i, t i • l i
      map_add' := fun t t' => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c t => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply] }

private theorem sliceCLM_apply (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (t : Fin 3 → ℝ) : sliceCLM l t = ∑ i, t i • l i := rfl

private theorem norm_sliceCLM_le (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (hl : ∀ i, ip (l i) (l i) ≤ 1) : ‖sliceCLM l‖ ≤ 3 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun t => ?_
  rw [sliceCLM_apply]
  have hli : ∀ i, ‖l i‖ ≤ 1 := fun i =>
    (SliceBound.norm_le_sqrt_ip_self (l i)).trans (Real.sqrt_le_one.2 (hl i))
  calc ‖∑ i, t i • l i‖ ≤ ∑ i, ‖t i • l i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖t‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        calc ‖t i‖ * ‖l i‖ ≤ ‖t‖ * 1 := by gcongr; exact norm_le_pi_norm t i; exact hli i
          _ = ‖t‖ := mul_one _
    _ = 3 * ‖t‖ := by simp [Finset.sum_const, Finset.card_univ]

private theorem norm_iteratedFDeriv_slice_le' {F : (Fin 2 → Fin 3 → ℝ) → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (q : Fin 2 → Fin 3 → ℝ) (n : ℕ) (t : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun t' : Fin 3 → ℝ => F (q + ∑ i, t' i • l i)) t‖ ≤
      ‖sliceCLM l‖ ^ n * ‖iteratedFDeriv ℝ n F (q + ∑ i, t i • l i)‖ := by
  have hfun : (fun t' : Fin 3 → ℝ => F (q + ∑ i, t' i • l i)) = (fun X => F (X + q)) ∘ (sliceCLM l) := by
    funext t'; simp only [Function.comp, sliceCLM_apply, add_comm]
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun X : Fin 2 → Fin 3 → ℝ => F (X + q)) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [hfun, (sliceCLM l).iteratedFDeriv_comp_right hG t (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]
  gcongr
  rw [iteratedFDeriv_comp_add_right, sliceCLM_apply, add_comm]

private structure SliceData where
  l : Fin 3 → (Fin 2 → Fin 3 → ℝ)
  q : Fin 2 → Fin 3 → ℝ
  orth : ∀ i k, ip (l i) (l k) = if i = k then 1 else 0
  hq : ∀ i, ip q (l i) = 0

private theorem exists_forall_norm_pow_mul_norm_iteratedFDeriv_affine_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : SliceData) (w : ℝ), (∀ t : Fin 3 → ℝ, |w| ≤ 6 * ‖σ.q + ∑ i, t i • σ.l i‖) →
      ∀ t : Fin 3 → ℝ,
      ‖t‖ ^ k * ‖iteratedFDeriv ℝ n (fun t' : Fin 3 → ℝ => Ψ (σ.q + ∑ i, t' i • σ.l i)) t‖ ≤
        C * ((1 + |w|) ^ N)⁻¹ := by
  set m : ℕ := k + N with hm
  set B : ℝ := 2 ^ m * (Finset.Iic (m, n)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) Ψ with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  have hΨ : ∀ P : Fin 2 → Fin 3 → ℝ, (1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ ≤ B := fun P =>
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (m, n)) le_rfl le_rfl Ψ P
  refine ⟨3 ^ n * 3 ^ k * 6 ^ N * B, by positivity, fun σ w hw t => ?_⟩
  set P : Fin 2 → Fin 3 → ℝ := σ.q + ∑ i, t i • σ.l i with hP
  have hpos : (0 : ℝ) < (1 + |w|) ^ N := by positivity
  rw [le_mul_inv_iff₀ hpos]

  have ht : ‖t‖ ≤ 3 * ‖P‖ := by
    have h1 : ‖t‖ ^ 2 ≤ ∑ i, t i ^ 2 := by
      have := SliceBound.norm_le_sqrt_sum_sq t
      have h0 : 0 ≤ ∑ i, t i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (∑ i, t i ^ 2), norm_nonneg t]
    have h2 : ∑ i, t i ^ 2 ≤ ip P P := by
      rw [hP, SliceBound.ip_self_add_sum_smul σ.l σ.orth σ.q σ.hq t]
      linarith [SliceBound.ip_self_nonneg σ.q]
    have h3 := ip_self_le_six_mul_sq_norm P
    nlinarith [norm_nonneg t, norm_nonneg P]
  have hvq : |w| ≤ 6 * ‖P‖ := hw t
  have hsl : ‖sliceCLM σ.l‖ ≤ 3 :=
    norm_sliceCLM_le σ.l fun i => by rw [σ.orth i i]; simp
  have hD := norm_iteratedFDeriv_slice_le' (Ψ.smooth (⊤ : ℕ∞)) σ.l σ.q n t
  have hD0 : 0 ≤ ‖iteratedFDeriv ℝ n (⇑Ψ) P‖ := norm_nonneg _
  have hP0 : 0 ≤ ‖P‖ := norm_nonneg _
  have hk : ‖t‖ ^ k ≤ 3 ^ k * (1 + ‖P‖) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
  have hN : (1 + |w|) ^ N ≤ 6 ^ N * (1 + ‖P‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N
  have hn : ‖sliceCLM σ.l‖ ^ n ≤ 3 ^ n := pow_le_pow_left₀ (norm_nonneg _) hsl n
  calc ‖t‖ ^ k * ‖iteratedFDeriv ℝ n (fun t' : Fin 3 → ℝ => Ψ (σ.q + ∑ i, t' i • σ.l i)) t‖ *
        (1 + |w|) ^ N
      ≤ (3 ^ k * (1 + ‖P‖) ^ k) * (3 ^ n * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) * (6 ^ N * (1 + ‖P‖) ^ N) := by
        gcongr
        exact hD.trans (by gcongr)
    _ = 3 ^ n * 3 ^ k * 6 ^ N * ((1 + ‖P‖) ^ m * ‖iteratedFDeriv ℝ n (⇑Ψ) P‖) := by
        rw [hm, pow_add]; ring
    _ ≤ 3 ^ n * 3 ^ k * 6 ^ N * B := by
        gcongr
        exact hΨ P

private noncomputable def affineSliceSchwartz (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (σ : SliceData) : 𝓢((Fin 3 → ℝ), ℂ) where
  toFun := fun t => Ψ (σ.q + ∑ i, t i • σ.l i)
  smooth' := by
    have hfun : (fun t : Fin 3 → ℝ => σ.q + ∑ i, t i • σ.l i) = fun t => σ.q + sliceCLM σ.l t := by
      funext t; rw [sliceCLM_apply]
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : Fin 3 → ℝ => σ.q + ∑ i, t i • σ.l i) := by
      rw [hfun]; exact contDiff_const.add (sliceCLM σ.l).contDiff
    exact (Ψ.smooth (⊤ : ℕ∞)).comp hc
  decay' := by
    intro k n
    obtain ⟨C, -, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_affine_le Ψ k n 0
    exact ⟨C, fun t => by simpa using hC σ 0 (fun t' => by rw [abs_zero]; positivity) t⟩

private theorem affineSliceSchwartz_apply (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (σ : SliceData) (t : Fin 3 → ℝ) :
    affineSliceSchwartz Ψ σ t = Ψ (σ.q + ∑ i, t i • σ.l i) := rfl

private theorem exists_forall_seminorm_affineSliceSchwartz_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : SliceData) (v : Fin 2 → Fin 3 → ℝ), (∀ i, ip v (σ.l i) = 0) → ip v v = 1 →
      SchwartzMap.seminorm ℝ k n (affineSliceSchwartz Ψ σ) ≤ C * ((1 + |ip v σ.q|) ^ N)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_norm_pow_mul_norm_iteratedFDeriv_affine_le Ψ k n N
  refine ⟨C, hC0, fun σ v hv hv1 => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun t => ?_
  refine hC σ (ip v σ.q) (fun t' => ?_) t
  rw [← SliceBound.ip_add_sum_smul_of_orth v σ.l hv σ.q t']
  exact SliceBound.abs_ip_le_of_ip_self_eq_one v hv1 _

private theorem slicePhase_add (φ t₀ u : Fin 3 → ℝ) :
    Complex.exp (((-(2 * Real.pi * ∑ i, φ i * (u + t₀) i) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * ∑ i, φ i * t₀ i : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  push_cast
  ring

private theorem exists_forall_norm_integral_affineSlice_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : SliceData) (v : Fin 2 → Fin 3 → ℝ), (∀ i, ip v (σ.l i) = 0) → ip v v = 1 →
      ∀ ξ : Fin 3 → ℝ,
      ‖∫ t : Fin 3 → ℝ, Ψ (σ.q + ∑ i, t i • σ.l i) *
          Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * t i) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * ((1 + ‖ξ‖) ^ N)⁻¹ * ((1 + |ip v σ.q|) ^ N)⁻¹ := by
  classical
  obtain ⟨s, C₂, hC₂0, hB2⟩ := exists_finset_forall_norm_integral_schwartzMap_mul_exp_neg_inner_le (Fin 3) N
  choose C₁ hC₁0 hC₁ using fun p : ℕ × ℕ => exists_forall_seminorm_affineSliceSchwartz_le Ψ p.1 p.2 N
  set C₁s : ℝ := ∑ p ∈ s, C₁ p with hC₁s
  have hC₁s0 : 0 ≤ C₁s := Finset.sum_nonneg fun p _ => hC₁0 p
  refine ⟨C₂ * C₁s, by positivity, fun σ v hv hv1 ξ => ?_⟩
  have hsup : (s.sup (schwartzSeminormFamily ℝ (Fin 3 → ℝ) ℂ)) (affineSliceSchwartz Ψ σ) ≤
      C₁s * ((1 + |ip v σ.q|) ^ N)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun p hp => ?_
    obtain ⟨a, b⟩ := p
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hC₁ (a, b) σ v hv hv1).trans (by gcongr; exact Finset.single_le_sum (fun q _ => hC₁0 q) hp)
  have hrpow : (1 + ‖ξ‖) ^ (-(N : ℝ)) = ((1 + ‖ξ‖) ^ N)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have h := hB2 (affineSliceSchwartz Ψ σ) ξ
  simp only [affineSliceSchwartz_apply] at h
  refine h.trans ?_
  rw [hrpow]
  calc C₂ * (s.sup (schwartzSeminormFamily ℝ (Fin 3 → ℝ) ℂ)) (affineSliceSchwartz Ψ σ) * ((1 + ‖ξ‖) ^ N)⁻¹
      ≤ C₂ * (C₁s * ((1 + |ip v σ.q|) ^ N)⁻¹) * ((1 + ‖ξ‖) ^ N)⁻¹ := by gcongr
    _ = C₂ * C₁s * ((1 + ‖ξ‖) ^ N)⁻¹ * ((1 + |ip v σ.q|) ^ N)⁻¹ := by ring

private theorem norm_integral_slice_shift (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (l : Fin 3 → (Fin 2 → Fin 3 → ℝ))
    (p : Fin 2 → Fin 3 → ℝ) (φ t₀ : Fin 3 → ℝ) :
    ‖∫ u : Fin 3 → ℝ, Ψ ((p + ∑ i, t₀ i • l i) + ∑ i, u i • l i) *
        Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I)‖ =
      ‖∫ u : Fin 3 → ℝ, Ψ (p + ∑ i, u i • l i) *
        Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I)‖ := by
  set c : ℂ := Complex.exp (((2 * Real.pi * ∑ i, φ i * t₀ i : ℝ) : ℂ) * Complex.I) with hc
  have hc1 : ‖c‖ = 1 := by rw [hc]; exact Complex.norm_exp_ofReal_mul_I _
  have hpt : ∀ u : Fin 3 → ℝ, (p + ∑ i, t₀ i • l i) + ∑ i, u i • l i = p + ∑ i, (u + t₀) i • l i := by
    intro u
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  set F : (Fin 3 → ℝ) → ℂ := fun w => Ψ (p + ∑ i, w i • l i) *
    Complex.exp (((-(2 * Real.pi * ∑ i, φ i * w i) : ℝ) : ℂ) * Complex.I) with hF
  set F' : (Fin 3 → ℝ) → ℂ := fun u => F (u + t₀) with hF'
  have hfun : (fun u : Fin 3 → ℝ => Ψ ((p + ∑ i, t₀ i • l i) + ∑ i, u i • l i) *
      Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I)) = fun u => c * F' u := by
    funext u
    rw [hF', hF]
    simp only []
    rw [hpt u, ← slicePhase_add φ t₀ u, hc]
    ring
  have hshift : ∫ u : Fin 3 → ℝ, F' u = ∫ u : Fin 3 → ℝ, F u := integral_add_right_eq_self (μ := volume) F t₀
  have h2 : ∫ u : Fin 3 → ℝ, c * F' u = c * ∫ u : Fin 3 → ℝ, F' u := integral_const_mul c F'
  rw [hfun, h2, norm_mul, hc1, one_mul]
  exact congrArg norm hshift

private theorem gram_posSemidef (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) : (gram l).PosSemidef := by
  classical
  set B : Matrix (Fin 2 × Fin 3) (Fin 3) ℝ := Matrix.of fun ab i => l i ab.1 ab.2 with hB
  have hgram : gram l = Bᴴ * B := by
    ext i j
    simp only [gram, ip, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hB, star_trivial,
      Fintype.sum_prod_type]
  rw [hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self B

private theorem exists_sliceData (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (hl : 0 < (gram l).det) (p : Fin 2 → Fin 3 → ℝ) :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (t₀ : Fin 3 → ℝ) (σ : SliceData),
      A * Aᵀ = (gram l)⁻¹ ∧ |A.det| = (Real.sqrt (gram l).det)⁻¹ ∧
      σ.l = (fun i => ∑ j, A j i • l j) ∧ σ.q = p + ∑ i, t₀ i • l i := by
  obtain ⟨A, hA1, hA2, hA3⟩ := SliceBound.exists_transpose_mul_mul_eq_one (gram_posSemidef l) hl.ne'
  set t₀ : Fin 3 → ℝ := -((gram l)⁻¹ *ᵥ fun i => ip p (l i)) with ht₀
  have hq : ∀ j, ip (p + ∑ i, t₀ i • l i) (l j) = 0 := fun j => SliceBound.ip_shift_orth l hl.ne' p j
  refine ⟨A, t₀, ⟨fun i => ∑ j, A j i • l j, p + ∑ i, t₀ i • l i, fun i k => ?_, fun i => ?_⟩, hA2, hA3, rfl, rfl⟩
  · rw [SliceBound.ip_reparam, hA1, Matrix.one_apply]
  · rw [SliceBound.ip_sum_right]
    simp [SliceBound.ip_smul_right, hq]

private theorem exists_forall_norm_integral_schwartzMap_slice_mul_exp_le (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : Fin 3 → (Fin 2 → Fin 3 → ℝ)) (p : Fin 2 → Fin 3 → ℝ) (φ : Fin 3 → ℝ)
      (v : Fin 2 → Fin 3 → ℝ), 0 < (gram l).det → (∀ i, ip v (l i) = 0) → ip v v = 1 →
      ‖∫ u : Fin 3 → ℝ, Ψ (p + ∑ i, u i • l i) *
          Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I)‖ ≤
        C / Real.sqrt (gram l).det *
          (1 + Real.sqrt (φ ⬝ᵥ ((gram l)⁻¹ *ᵥ φ)) + |ip v p|) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_forall_norm_integral_affineSlice_le Ψ N
  refine ⟨C * 2 ^ N, by positivity, fun l p φ v hl hv hv1 => ?_⟩
  obtain ⟨A, t₀, σ, hAAt, hAdet, hσl, hσq⟩ := exists_sliceData l hl p
  have hdetA : A.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hAdet
    exact (inv_pos.2 (Real.sqrt_pos.2 hl)).ne' hAdet.symm

  have hv' : ∀ i, ip v (σ.l i) = 0 := fun i => by
    rw [hσl, SliceBound.ip_sum_right]
    simp [SliceBound.ip_smul_right, hv]
  have hvq : ip v σ.q = ip v p := by rw [hσq]; exact SliceBound.ip_add_sum_smul_of_orth v l hv p t₀

  set G : (Fin 3 → ℝ) → ℂ := fun u => Ψ (σ.q + ∑ i, u i • l i) *
    Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := by
    rw [hG]
    refine (Ψ.continuous.comp (continuous_const.add (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const))).mul (Complex.continuous_exp.comp ?_)
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))).neg
  set ξ : Fin 3 → ℝ := Aᵀ *ᵥ φ with hξ
  have hGA : (fun t : Fin 3 → ℝ => G (A *ᵥ t)) = fun t => Ψ (σ.q + ∑ i, t i • σ.l i) *
      Complex.exp (((-(2 * Real.pi * ∑ i, ξ i * t i) : ℝ) : ℂ) * Complex.I) := by
    funext t
    rw [hG]
    simp only []
    rw [SliceBound.sum_mulVec_smul, SliceBound.sum_mul_mulVec, hσl, hξ]

  have hcov : ∫ u : Fin 3 → ℝ, G u = ((|A.det| : ℝ) : ℂ) * ∫ t : Fin 3 → ℝ, G (A *ᵥ t) := by
    rw [SliceBound.integral_comp_mulVec_eq hGc A hdetA, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (abs_ne_zero.2 hdetA), Complex.ofReal_one, one_mul]

  have hξ2 : Real.sqrt (φ ⬝ᵥ ((gram l)⁻¹ *ᵥ φ)) ≤ 2 * ‖ξ‖ := by
    rw [← hAAt, ← SliceBound.dotProduct_transpose_mulVec_self, ← hξ]
    have h1 : ξ ⬝ᵥ ξ = ∑ i, ξ i ^ 2 := by simp only [dotProduct, sq]
    rw [h1]
    calc Real.sqrt (∑ i, ξ i ^ 2) ≤ Real.sqrt ((2 * ‖ξ‖) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have := sum_sq_le_three_mul_sq_norm ξ
          nlinarith [norm_nonneg ξ]
      _ = 2 * ‖ξ‖ := Real.sqrt_sq (by positivity)
  set S : ℝ := Real.sqrt (φ ⬝ᵥ ((gram l)⁻¹ *ᵥ φ)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hbr : ((1 + ‖ξ‖) ^ N)⁻¹ ≤ 2 ^ N * ((1 + S) ^ N)⁻¹ := by
    have h2 : (1 + S) ≤ 2 * (1 + ‖ξ‖) := by linarith
    have hSN : (1 + S) ^ N ≤ 2 ^ N * (1 + ‖ξ‖) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h2 N
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ((1 + ‖ξ‖) ^ N)⁻¹ * (1 + S) ^ N ≤ ((1 + ‖ξ‖) ^ N)⁻¹ * (2 ^ N * (1 + ‖ξ‖) ^ N) := by gcongr
      _ = 2 ^ N := by field_simp
  have hrpow : (1 + S + |ip v p|) ^ (-(N : ℝ)) = ((1 + S + |ip v p|) ^ N)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

  have hmain := hC σ v hv' hv1 ξ
  rw [← hGA] at hmain
  have hshift := norm_integral_slice_shift Ψ l p φ t₀
  rw [← hσq] at hshift
  rw [← hshift]
  change ‖∫ u : Fin 3 → ℝ, G u‖ ≤ _
  rw [hcov, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs, hAdet, hrpow, hvq] at *
  rw [hvq] at hmain
  calc (Real.sqrt (gram l).det)⁻¹ * ‖∫ t : Fin 3 → ℝ, G (A *ᵥ t)‖
      ≤ (Real.sqrt (gram l).det)⁻¹ * (C * ((1 + ‖ξ‖) ^ N)⁻¹ * ((1 + |ip v p|) ^ N)⁻¹) := by gcongr
    _ ≤ (Real.sqrt (gram l).det)⁻¹ * (C * (2 ^ N * ((1 + S) ^ N)⁻¹) * ((1 + |ip v p|) ^ N)⁻¹) := by gcongr
    _ = C * 2 ^ N / Real.sqrt (gram l).det * (((1 + S) ^ N)⁻¹ * ((1 + |ip v p|) ^ N)⁻¹) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ C * 2 ^ N / Real.sqrt (gram l).det * ((1 + S + |ip v p|) ^ N)⁻¹ := by
        gcongr
        exact G0.inv_pow_mul_inv_pow_le S |ip v p| hS0 (abs_nonneg _) N

private theorem integrable_schwartzMap_slice (Ψ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ)) (l : Fin 3 → (Fin 2 → Fin 3 → ℝ))
    (p : Fin 2 → Fin 3 → ℝ) (hl : 0 < (gram l).det) :
    Integrable (fun u : Fin 3 → ℝ => Ψ (p + ∑ i, u i • l i)) := by
  obtain ⟨A, t₀, σ, -, hAdet, hσl, hσq⟩ := exists_sliceData l hl p
  have hdetA : A.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hAdet
    exact (inv_pos.2 (Real.sqrt_pos.2 hl)).ne' hAdet.symm
  set g : (Fin 3 → ℝ) → ℂ := fun u => Ψ (p + ∑ i, u i • l i) with hg
  have hgc : Continuous g := by
    rw [hg]
    exact Ψ.continuous.comp (continuous_const.add (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const))

  have hA' : ∀ t : Fin 3 → ℝ, p + ∑ i, t i • σ.l i = σ.q + ∑ i, (t - A⁻¹ *ᵥ t₀) i • σ.l i := by
    intro t
    rw [hσq, hσl]
    have hAt : ∑ i, t₀ i • l i = ∑ i, (A⁻¹ *ᵥ t₀) i • ∑ j, A j i • l j := by
      rw [← SliceBound.sum_mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdetA),
        Matrix.one_mulVec]
    rw [hAt]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    abel
  have hcomp : (fun t : Fin 3 → ℝ => g (A *ᵥ t)) = fun t => affineSliceSchwartz Ψ σ (t - A⁻¹ *ᵥ t₀) := by
    funext t
    rw [hg]
    simp only []
    rw [SliceBound.sum_mulVec_smul, affineSliceSchwartz_apply, ← hA' t]
    simp only [hσl]
  have hint : Integrable fun t : Fin 3 → ℝ => g (A *ᵥ t) := by
    rw [hcomp]
    exact (affineSliceSchwartz Ψ σ).integrable.comp_sub_right _

  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 3) hdetA
  have hmeas : Measurable (Matrix.toLin' A) := (Matrix.toLin' A).continuous_of_finiteDimensional.measurable
  have hfun : (fun t : Fin 3 → ℝ => g (A *ᵥ t)) = g ∘ (Matrix.toLin' A) := by
    funext t; simp [Function.comp, Matrix.toLin'_apply]
  rw [hfun] at hint
  have h1 : Integrable g (Measure.map (Matrix.toLin' A) volume) :=
    (integrable_map_measure hgc.aestronglyMeasurable hmeas.aemeasurable).2 hint
  rw [hmap] at h1
  exact (integrable_smul_measure (by simp [hdetA]) ENNReal.ofReal_ne_top).1 h1

end

end LanglandsTunnell.CubicInduction

end E0_slice_bound

noncomputable section E1_DOM_regions

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

open MeasureTheory

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam signShift signShift_zero RealArchParam.gammaR RealArchParam.gammaC RealArchParam.twist RealArchParam.dual RealArchParam.centralExponent RealArchParam.discrete RealArchParam.principal CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq embedMat2 iotaGL IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply weylPrime3 transposeInv3 diagUnitGL2 jacquetVector3_iotaGL_diagUnitGL2_mul integrable_jacquetIntegrand3_dilate_mul_quasiChar exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_eq_unip_mul_smul_diagOne_mul_of_det_ne_zero (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    ∃ (s z y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k ∧ 0 < z ∧
      z = Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ∧ |y| = |x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2) ∧
      x = ArchR.unip s * (z • (ArchR.diagOne y * k)) := by
  have hdet : x.det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := Matrix.det_fin_two x
  have hq : 0 < x 1 0 ^ 2 + x 1 1 ^ 2 := by
    by_contra hcon
    have h10 : x 1 0 = 0 := by nlinarith [sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    have h11 : x 1 1 = 0 := by nlinarith [sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    exact hx (by rw [hdet, h10, h11]; ring)
  have hq' : x 1 0 ^ 2 + x 1 1 ^ 2 ≠ 0 := hq.ne'
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) := ⟨_, rfl⟩
  have hz0 : 0 < z := by rw [hz]; exact Real.sqrt_pos.mpr hq
  have hz0' : z ≠ 0 := hz0.ne'
  have hz2 : z ^ 2 = x 1 0 ^ 2 + x 1 1 ^ 2 := by rw [hz]; exact Real.sq_sqrt hq.le
  refine ⟨(x 0 0 * x 1 0 + x 0 1 * x 1 1) / (x 1 0 ^ 2 + x 1 1 ^ 2), z, x.det / (x 1 0 ^ 2 + x 1 1 ^ 2),
    !![x 1 1 / z, -(x 1 0) / z; x 1 0 / z, x 1 1 / z], ?_, hz0, hz, ?_, ?_⟩
  · unfold ArchR.IsK
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> nlinarith [hz2]
  · rw [abs_div, abs_of_pos hq]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ArchR.unip, ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two, hdet] <;> field_simp <;> ring

private theorem norm_psi_le_one (s : ℝ) : ‖ArchR.psi s‖ ≤ 1 := by
  unfold ArchR.psi
  simp [Complex.norm_exp]

private theorem norm_quasiChar_le (u : ℂ) (b : ZMod 2) {z : ℝ} (hz : z ≠ 0) :
    ‖ArchR.quasiChar u b z‖ ≤ |z| ^ u.re := by
  unfold ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hz)]
  refine mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg z) _) ?_
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_or_gt_of_ne hz with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]

private theorem norm_W_smul_le {P : RealArchParam} (D : ArchDatumR P) {z : ℝ} (hz : 0 < z)
    (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖D.W (z • g)‖ ≤ z ^ (P.centralExponent.re + 1) * ‖D.W g‖ := by
  rw [D.central_law z g hz.ne', norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_of_pos hz,
    Real.rpow_add_one hz.ne']
  have h := norm_quasiChar_le P.centralExponent P.centralSign hz.ne'
  rw [abs_of_pos hz] at h
  unfold ArchR.centralChar
  gcongr

private theorem norm_W_unip_mul_le {P : RealArchParam} (D : ArchDatumR P) (s : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖D.W (ArchR.unip s * g)‖ ≤ ‖D.W g‖ := by
  rw [D.unip_law s g, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_psi_le_one s)

private theorem exists_forall_norm_W_diagOne_mul_le_of_le {P : RealArchParam} (D : ArchDatumR P) (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (q : ℝ) (hq : c₀ - 1 ≤ q) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖D.W (ArchR.diagOne y * k)‖ ≤ C * |y| ^ (-q) := by
  obtain ⟨C₁, h₁⟩ := ArchDatumR.norm_iteratedFDerivWithin_diagOne_le P D c₀ hc₀ 0
  obtain ⟨C₂, h₂⟩ := D.decay_top 0 ⌈max q 0⌉₊
  refine ⟨max (max C₁ C₂) 0, ?_⟩
  intro y k hk hy
  have hW : ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ =
      ‖D.W (ArchR.diagOne y * k)‖ := by
    rw [norm_iteratedFDerivWithin_zero]
    simp [ArchR.asPi, ArchR.diagOneMulCoords]
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hC0 : (0 : ℝ) ≤ max (max C₁ C₂) 0 := le_max_right _ _
  have hC₁ : C₁ ≤ max (max C₁ C₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC₂ : C₂ ≤ max (max C₁ C₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  rcases le_or_gt |y| 1 with hle | hlt
  · have h := h₁ y k hk hy hle
    rw [hW] at h
    calc ‖D.W (ArchR.diagOne y * k)‖ ≤ C₁ * |y| ^ (1 - c₀ - ((0 : ℕ) : ℝ)) := h
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (1 - c₀ - ((0 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hC₁ (Real.rpow_nonneg hy0.le _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-q) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy0 hle (by push_cast; linarith)) hC0
  · have h := h₂ y k hk hlt.le
    rw [hW] at h
    calc ‖D.W (ArchR.diagOne y * k)‖ ≤ C₂ * |y| ^ (-((⌈max q 0⌉₊ : ℕ) : ℝ)) := h
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-((⌈max q 0⌉₊ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hC₂ (Real.rpow_nonneg hy0.le _)
      _ ≤ max (max C₁ C₂) 0 * |y| ^ (-q) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hlt.le (neg_le_neg ((le_max_left _ _).trans (Nat.le_ceil _)))) hC0

private theorem archDatumR_exists_forall_norm_W_le_rpow_mul_rpow_of_le {P : RealArchParam} (D : ArchDatumR P)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (q : ℝ) (hq : c₀ - 1 ≤ q) :
    ∃ C : ℝ, ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 →
      ‖D.W x‖ ≤ C * Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
        (|x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2)) ^ (-q) := by
  obtain ⟨C, hC⟩ := exists_forall_norm_W_diagOne_mul_le_of_le D c₀ hc₀ q hq
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨s, z, y, k, hk, hz, hzeq, hyabs, hxeq⟩ := exists_eq_unip_mul_smul_diagOne_mul_of_det_ne_zero x hx
  have hq : 0 < x 1 0 ^ 2 + x 1 1 ^ 2 := by
    have h := hz
    rw [hzeq] at h
    exact Real.sqrt_pos.mp h
  have hy : y ≠ 0 := by
    intro h
    rw [h, abs_zero, eq_comm, div_eq_zero_iff] at hyabs
    rcases hyabs with h0 | h0
    · exact hx (abs_eq_zero.mp h0)
    · exact hq.ne' h0
  calc ‖D.W x‖ = ‖D.W (ArchR.unip s * (z • (ArchR.diagOne y * k)))‖ := by rw [← hxeq]
    _ ≤ ‖D.W (z • (ArchR.diagOne y * k))‖ := norm_W_unip_mul_le D s _
    _ ≤ z ^ (P.centralExponent.re + 1) * ‖D.W (ArchR.diagOne y * k)‖ := norm_W_smul_le D hz _
    _ ≤ z ^ (P.centralExponent.re + 1) * (C * |y| ^ (-q)) :=
        mul_le_mul_of_nonneg_left (hC y k hk hy) (Real.rpow_nonneg hz.le _)
    _ = C * Real.sqrt (x 1 0 ^ 2 + x 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
          (|x.det| / (x 1 0 ^ 2 + x 1 1 ^ 2)) ^ (-q) := by
        rw [← hzeq, ← hyabs]
        ring

section SchwartzSlices

open scoped BigOperators SchwartzMap FourierTransform

namespace G0

private def entryL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj v.2 : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj v.1 : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))

private theorem entryL_apply (v : Fin 2 × Fin 3) (M : Fin 2 → Fin 3 → ℝ) : entryL v M = M v.1 v.2 := rfl

private def uncurryL : (Fin 2 → Fin 3 → ℝ) →L[ℝ] (Fin 2 × Fin 3 → ℝ) :=
  ContinuousLinearMap.pi entryL

private theorem uncurryL_apply (M : Fin 2 → Fin 3 → ℝ) (v : Fin 2 × Fin 3) : uncurryL M v = M v.1 v.2 := rfl

private def coordL (v : Fin 2 × Fin 3) : (Fin 2 → Fin 3 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (entryL v)

private theorem norm_le_norm_uncurryL (M : Fin 2 → Fin 3 → ℝ) : ‖M‖ ≤ ‖uncurryL M‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => ?_
  have := norm_le_pi_norm (uncurryL M) (i, b)
  simpa [uncurryL_apply] using this

private theorem hasTemperateGrowth_eval (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq => simpa [MvPolynomial.eval_add, Pi.add_def] using hp.add hq
  | mul_X p v hp =>
    have hX : Function.HasTemperateGrowth fun M : Fin 2 → Fin 3 → ℝ => ((M v.1 v.2 : ℝ) : ℂ) := by
      have h := (coordL v).hasTemperateGrowth
      convert h using 1
      all_goals try rfl
    simpa [MvPolynomial.eval_mul, Pi.mul_def] using hp.mul hX

private theorem exists_schwartzMap_eq_gaussian3 :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℝ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ,
      Φ (fun i b => M i b) = Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2)) := by
  obtain ⟨Φ₀, hΦ₀⟩ := LanglandsTunnell.CubicInduction.exists_schwartzMap_eq_exp_neg_pi_sum_sq (Fin 2 × Fin 3)
  refine ⟨SchwartzMap.compCLM ℝ uncurryL.hasTemperateGrowth ⟨1, 1, fun M => ?_⟩ Φ₀, fun M => ?_⟩
  · have := norm_le_norm_uncurryL M
    nlinarith [norm_nonneg (uncurryL M)]
  · rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦ₀]
    simp only [uncurryL_apply, Fintype.sum_prod_type]

private theorem exists_schwartzMap_eq_of_mem_polyGauss3' {S : Matrix (Fin 2) (Fin 3) ℝ → ℂ} (hS : S ∈ polyGauss3) :
    ∃ Φ : 𝓢((Fin 2 → Fin 3 → ℝ), ℂ), ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Φ (fun i b => M i b) = S M := by
  obtain ⟨p, rfl⟩ := hS
  obtain ⟨Φg, hΦg⟩ := exists_schwartzMap_eq_gaussian3
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun M : Fin 2 → Fin 3 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p) (Φg.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM), fun M => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_eval p), SchwartzMap.postcompCLM_apply, hΦg M, smul_eq_mul]
  rfl

end G0

end SchwartzSlices

end LanglandsTunnell.CubicInduction

end E1_DOM_regions

section R1_B4_and_M1

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction LanglandsTunnell.Converse MeasureTheory NumberField"
open scoped Matrix SchwartzMap

noncomputable section

namespace DualArchZetaBound

p2m_open "AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.Converse.ArchR"

private abbrev Arr : Type := Fin 2 → Fin 3 → ℝ

private theorem psiArch_eq_psi_realCoord (w : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch w = ArchR.psi (StandardKernel.realCoord w) := by
  have h1 : NumberField.StandardAddChar.psiArch w =
      NumberField.StandardAddChar.psiArchPlace Rat.infinitePlace (w Rat.infinitePlace) := by
    rw [NumberField.StandardAddChar.psiArch_apply]
    exact finprod_eq_single _ Rat.infinitePlace fun v hv => absurd (Subsingleton.elim v Rat.infinitePlace) hv
  rw [h1, NumberField.StandardAddChar.psiArchPlace_apply, ArchR.psi, StandardKernel.realCoord_apply]

private theorem realCoord_ratCast (a : ℚ) :
    StandardKernel.realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) a) = (a : ℝ) := by
  rw [← RingHom.comp_apply]
  exact eq_ratCast (StandardKernel.realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

private theorem _root_.DualArchZetaBound.realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

p2m_export "DualArchZetaBound" "realCoord_ofReal"
private theorem psiInf_ofReal_neg (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) (t : ℝ) :
    psiInf (StandardKernel.ofReal (-t)) =
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  rw [hpsiInf, psiArch_eq_psi_realCoord, map_mul, realCoord_ratCast, realCoord_ofReal, ArchR.psi]
  congr 1
  push_cast
  ring

private theorem _root_.DualArchZetaBound.integral_comp_mulVec_eq {G : (Fin 2 → ℝ) → ℂ} (hG : Continuous G) (h : Fin 2 → Fin 2 → ℝ)
    (hdet : (Matrix.of h).det ≠ 0) :
    ∫ v : Fin 2 → ℝ, G ((Matrix.of h).mulVec v) = ((|(Matrix.of h).det|⁻¹ : ℝ) : ℂ) * ∫ u : Fin 2 → ℝ, G u := by
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 2) hdet
  have hmeas : Measurable (Matrix.toLin' (Matrix.of h)) :=
    (Matrix.toLin' (Matrix.of h)).continuous_of_finiteDimensional.measurable
  have hfun : (fun v : Fin 2 → ℝ => G ((Matrix.of h).mulVec v)) = fun v => G (Matrix.toLin' (Matrix.of h) v) := by
    funext v; simp [Matrix.toLin'_apply]
  rw [hfun, ← MeasureTheory.integral_map hmeas.aemeasurable (hG.aestronglyMeasurable), hmap,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (by positivity), abs_inv]
  exact Complex.real_smul

p2m_export "DualArchZetaBound" "integral_comp_mulVec_eq"

private def shearedInner (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (m : Matrix (Fin 3) (Fin 3) ℝ) (c x : ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∫ w : Fin 2 → ℝ,
    S (h * Matrix.of ![fun b => m 1 b + w 0 * (m 0 b - x * m 2 b),
        fun b => m 2 b + w 1 * (m 0 b - x * m 2 b)]) *
      ψ (ofReal (-(c⁻¹ * w 1)))

private def colNorm (h : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.sqrt (h 0 0 ^ 2 + h 1 0 ^ 2)

private def IsTransversal (h : Matrix (Fin 2) (Fin 2) ℝ) : Prop := h 0 0 * h 0 1 + h 1 0 * h 1 1 = 0

private theorem W_diagOne_mul_inv_mul_unip {P : RealArchParam} (D : ArchDatumR P) (a ξ : ℝ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) :
    D.W (diagOne a * (h * unip ξ)⁻¹) = psi (-(a * ξ)) * D.W (diagOne a * h⁻¹) := by
  have hinv : (unip ξ)⁻¹ = unip (-ξ) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unip, Matrix.mul_apply, Fin.sum_univ_two]
  have hkey : diagOne a * (h * unip ξ)⁻¹ = unip (-(a * ξ)) * (diagOne a * h⁻¹) := by
    rw [Matrix.mul_inv_rev, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unip, diagOne, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hkey, D.unip_law]

private theorem det_mul_unip (h : Matrix (Fin 2) (Fin 2) ℝ) (ξ : ℝ) : (h * unip ξ).det = h.det := by
  rw [Matrix.det_mul]
  simp [unip, Matrix.det_fin_two_of]

private theorem wedge_sq_shear (m : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) :
    (∑ b, m 2 b ^ 2) * (∑ b, (m 0 b - x * m 2 b) ^ 2) - (∑ b, m 2 b * (m 0 b - x * m 2 b)) ^ 2 =
      (∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2 := by
  simp only [Fin.sum_univ_three]
  ring

private theorem wedge_sq_pos (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) :
    0 < (∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2 := by

  set c₀ : ℝ := m 2 1 * m 0 2 - m 2 2 * m 0 1 with hc₀
  set c₁ : ℝ := m 2 2 * m 0 0 - m 2 0 * m 0 2 with hc₁
  set c₂ : ℝ := m 2 0 * m 0 1 - m 2 1 * m 0 0 with hc₂
  have hL : (∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2 = c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 := by
    simp only [Fin.sum_univ_three, hc₀, hc₁, hc₂]
    ring
  have hdet : m.det = m 1 0 * c₀ + m 1 1 * c₁ + m 1 2 * c₂ := by
    rw [Matrix.det_fin_three]
    simp only [hc₀, hc₁, hc₂]
    ring
  rw [hL]
  refine lt_of_not_ge fun hle => ?_
  have h0 : c₀ = 0 := by nlinarith [sq_nonneg c₀, sq_nonneg c₁, sq_nonneg c₂]
  have h1 : c₁ = 0 := by nlinarith [sq_nonneg c₀, sq_nonneg c₁, sq_nonneg c₂]
  have h2 : c₂ = 0 := by nlinarith [sq_nonneg c₀, sq_nonneg c₁, sq_nonneg c₂]
  exact hm (by rw [hdet, h0, h1, h2]; ring)

private theorem shear_norm_sq_bounds (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) :
    ∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ 0 < κ₂ ∧ ∀ x : ℝ,
      κ₁ * (1 + x ^ 2) ≤ ∑ b, (m 0 b - x * m 2 b) ^ 2 ∧ ∑ b, (m 0 b - x * m 2 b) ^ 2 ≤ κ₂ * (1 + x ^ 2) := by
  set A : ℝ := ∑ b, m 0 b ^ 2 with hA
  set B : ℝ := ∑ b, m 0 b * m 2 b with hB
  set Cq : ℝ := ∑ b, m 2 b ^ 2 with hCq
  have hW : 0 < Cq * A - B ^ 2 := by
    have := wedge_sq_pos m hm
    have hB' : (∑ b, m 2 b * m 0 b) = B := by simp only [hB, Fin.sum_univ_three]; ring
    rw [hB'] at this
    exact this
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hC0 : 0 ≤ Cq := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hAC : 0 < A + Cq := by nlinarith [sq_nonneg B]
  have hexp : ∀ x : ℝ, ∑ b, (m 0 b - x * m 2 b) ^ 2 = A - 2 * x * B + x ^ 2 * Cq := by
    intro x
    simp only [hA, hB, hCq, Fin.sum_univ_three]
    ring
  refine ⟨(Cq * A - B ^ 2) / (A + Cq), A + |B| + Cq + 1, div_pos hW hAC, by positivity, fun x => ?_⟩
  rw [hexp]
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hAC]
    nlinarith [sq_nonneg (A - x * B), sq_nonneg (B - x * Cq)]
  · have h1 : -(2 * x * B) ≤ (1 + x ^ 2) * |B| := by
      have hb : -(2 * x * B) ≤ 2 * |x| * |B| := by
        have := neg_abs_le (2 * x * B)
        rw [abs_mul, abs_mul, abs_two] at this
        linarith
      have hx : 2 * |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
      nlinarith [abs_nonneg B]
    nlinarith [abs_nonneg B]

private theorem exists_unit_normal (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) :
    ∃ n : Fin 3 → ℝ, (∑ b, n b * m 0 b = 0) ∧ (∑ b, n b * m 2 b = 0) ∧ (∑ b, n b ^ 2 = 1) ∧
      |∑ b, n b * m 1 b| =
        |m.det| / Real.sqrt ((∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2) := by
  set c₀ : ℝ := m 2 1 * m 0 2 - m 2 2 * m 0 1 with hc₀
  set c₁ : ℝ := m 2 2 * m 0 0 - m 2 0 * m 0 2 with hc₁
  set c₂ : ℝ := m 2 0 * m 0 1 - m 2 1 * m 0 0 with hc₂
  have hL : (∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2 = c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 := by
    simp only [Fin.sum_univ_three, hc₀, hc₁, hc₂]
    ring
  have hpos : 0 < c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 := hL ▸ wedge_sq_pos m hm
  set L : ℝ := Real.sqrt (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) with hLdef
  have hL0 : 0 < L := Real.sqrt_pos.2 hpos
  have hLsq : L ^ 2 = c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 := Real.sq_sqrt hpos.le
  have hdet : m.det = m 1 0 * c₀ + m 1 1 * c₁ + m 1 2 * c₂ := by
    rw [Matrix.det_fin_three]
    simp only [hc₀, hc₁, hc₂]
    ring
  refine ⟨![c₀ / L, c₁ / L, c₂ / L], ?_, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp, hc₀,
      hc₁, hc₂]
    field_simp
    ring
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp, hc₀,
      hc₁, hc₂]
    field_simp
    ring
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    field_simp
    linarith [hLsq]
  · rw [hL, ← hLdef]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp]
    rw [hdet, show c₀ / L * m 1 0 + c₁ / L * m 1 1 + c₂ / L * m 1 2 = (m 1 0 * c₀ + m 1 1 * c₁ + m 1 2 * c₂) / L by
      field_simp]
    rw [abs_div, abs_of_pos hL0]

private def sliceDir (m : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ) : Fin 3 → Arr :=
  ![fun i b => h i 0 * m 2 b, fun i b => h i 0 * (m 0 b - x * m 2 b), fun i b => h i 1 * (m 0 b - x * m 2 b)]

private def sliceOffset (m : Matrix (Fin 3) (Fin 3) ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ) : Arr :=
  fun i b => h i 0 * m 1 b + h i 1 * m 2 b

private theorem gram_sliceDir_eq (m : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ)
    (ht : IsTransversal h) :
    gram (sliceDir m x h) =
      !![(h 0 0 ^ 2 + h 1 0 ^ 2) * ∑ b, m 2 b ^ 2, (h 0 0 ^ 2 + h 1 0 ^ 2) * ∑ b, m 2 b * (m 0 b - x * m 2 b), 0;
         (h 0 0 ^ 2 + h 1 0 ^ 2) * ∑ b, m 2 b * (m 0 b - x * m 2 b),
           (h 0 0 ^ 2 + h 1 0 ^ 2) * ∑ b, (m 0 b - x * m 2 b) ^ 2, 0;
         0, 0, (h 0 1 ^ 2 + h 1 1 ^ 2) * ∑ b, (m 0 b - x * m 2 b) ^ 2] := by
  have ht' : h 0 0 * h 0 1 + h 1 0 * h 1 1 = 0 := ht
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [gram, ip, sliceDir, Matrix.of_apply, Fin.sum_univ_two, Fin.sum_univ_three, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp] <;>
    first
      | ring1
      | linear_combination
          (m 2 0 * (m 0 0 - x * m 2 0) + m 2 1 * (m 0 1 - x * m 2 1) + m 2 2 * (m 0 2 - x * m 2 2)) * ht'
      | linear_combination ((m 0 0 - x * m 2 0) ^ 2 + (m 0 1 - x * m 2 1) ^ 2 + (m 0 2 - x * m 2 2) ^ 2) * ht'

private theorem det_sq_of_isTransversal (h : Matrix (Fin 2) (Fin 2) ℝ) (ht : IsTransversal h) :
    h.det ^ 2 = (h 0 0 ^ 2 + h 1 0 ^ 2) * (h 0 1 ^ 2 + h 1 1 ^ 2) := by
  have ht' : h 0 0 * h 0 1 + h 1 0 * h 1 1 = 0 := ht
  rw [Matrix.det_fin_two]
  linear_combination (-(h 0 0 * h 0 1 + h 1 0 * h 1 1)) * ht'

private theorem gram_det_sliceDir (m : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ)
    (ht : IsTransversal h) :
    (gram (sliceDir m x h)).det =
      (h 0 0 ^ 2 + h 1 0 ^ 2) * h.det ^ 2 *
        ((∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2) * (∑ b, (m 0 b - x * m 2 b) ^ 2) := by
  rw [gram_sliceDir_eq m x h ht, Matrix.det_fin_three, det_sq_of_isTransversal h ht, ← wedge_sq_shear m x]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

private theorem quadForm_sliceDir (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) (x : ℝ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (ht : IsTransversal h) (hh : h.det ≠ 0) (a f : ℝ) :
    (![a, 0, f] : Fin 3 → ℝ) ⬝ᵥ ((gram (sliceDir m x h))⁻¹ *ᵥ ![a, 0, f]) =
      a ^ 2 * (∑ b, (m 0 b - x * m 2 b) ^ 2) /
          ((h 0 0 ^ 2 + h 1 0 ^ 2) * ((∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2)) +
        f ^ 2 * (h 0 0 ^ 2 + h 1 0 ^ 2) / (h.det ^ 2 * ∑ b, (m 0 b - x * m 2 b) ^ 2) := by

  rw [← wedge_sq_shear m x]
  set ρ2 : ℝ := h 0 0 ^ 2 + h 1 0 ^ 2 with hρ2
  set s2 : ℝ := h 0 1 ^ 2 + h 1 1 ^ 2 with hs2
  set M22 : ℝ := ∑ b, m 2 b ^ 2 with hM22
  set M2r : ℝ := ∑ b, m 2 b * (m 0 b - x * m 2 b) with hM2r
  set Mrr : ℝ := ∑ b, (m 0 b - x * m 2 b) ^ 2 with hMrr
  have hdet2 : h.det ^ 2 = ρ2 * s2 := det_sq_of_isTransversal h ht
  have hdet2pos : 0 < h.det ^ 2 := by positivity
  have hρ2pos : 0 < ρ2 := by
    rcases (mul_pos_iff.1 (hdet2 ▸ hdet2pos)) with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 (not_lt.2 (by positivity))
  have hs2pos : 0 < s2 := by
    rcases (mul_pos_iff.1 (hdet2 ▸ hdet2pos)) with ⟨_, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (not_lt.2 (by positivity))
  have hW : 0 < M22 * Mrr - M2r ^ 2 := by
    have h1 := wedge_sq_pos m hm
    rw [← wedge_sq_shear m x] at h1
    exact h1
  have hMrrpos : 0 < Mrr := by
    have hM22nn : 0 ≤ M22 := Finset.sum_nonneg fun b _ => sq_nonneg _
    nlinarith [sq_nonneg M2r]
  set ψ : Fin 3 → ℝ := ![a * Mrr / (ρ2 * (M22 * Mrr - M2r ^ 2)), -(a * M2r) / (ρ2 * (M22 * Mrr - M2r ^ 2)),
    f / (s2 * Mrr)] with hψ
  have hG : gram (sliceDir m x h) = !![ρ2 * M22, ρ2 * M2r, 0; ρ2 * M2r, ρ2 * Mrr, 0; 0, 0, s2 * Mrr] :=
    gram_sliceDir_eq m x h ht
  have hGψ : gram (sliceDir m x h) *ᵥ ψ = ![a, 0, f] := by
    rw [hG]
    ext i
    fin_cases i <;>
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', hψ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_succ,
        Matrix.vecHead,
        Matrix.vecTail, Function.comp] <;>
      field_simp <;> ring
  have hdetG : (gram (sliceDir m x h)).det ≠ 0 := by
    rw [hG, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
    have : ρ2 * M22 * (ρ2 * Mrr) * (s2 * Mrr) - ρ2 * M2r * (ρ2 * M2r) * (s2 * Mrr) =
        ρ2 ^ 2 * s2 * Mrr * (M22 * Mrr - M2r ^ 2) := by ring
    nlinarith [this, mul_pos (mul_pos (mul_pos (pow_pos hρ2pos 2) hs2pos) hMrrpos) hW]
  have hinvψ : (gram (sliceDir m x h))⁻¹ *ᵥ ![a, 0, f] = ψ := by
    rw [← hGψ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdetG), Matrix.one_mulVec]
  have hρ2ne : ρ2 ≠ 0 := hρ2pos.ne'
  have hs2ne : s2 ≠ 0 := hs2pos.ne'
  have hWne : M22 * Mrr - M2r ^ 2 ≠ 0 := hW.ne'
  have hMrrne : Mrr ≠ 0 := hMrrpos.ne'
  rw [hinvψ, hψ, hdet2]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp]
  field_simp
  ring

private theorem exists_slice_normal (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) (x : ℝ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (ht : IsTransversal h) (hρ : colNorm h ≠ 0) :
    ∃ v : Arr, (∀ i, ip v (sliceDir m x h i) = 0) ∧ ip v v = 1 ∧
      |ip v (sliceOffset m h)| =
        colNorm h * |m.det| / Real.sqrt ((∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2) := by
  obtain ⟨n, hn0, hn2, hn1, hnm⟩ := exists_unit_normal m hm
  have ht' : h 0 0 * h 0 1 + h 1 0 * h 1 1 = 0 := ht
  have hρpos : 0 < colNorm h := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hρ)
  have hρsq : colNorm h ^ 2 = h 0 0 ^ 2 + h 1 0 ^ 2 := Real.sq_sqrt (by positivity)
  have hnr : ∑ b, n b * (m 0 b - x * m 2 b) = 0 := by
    have : ∑ b, n b * (m 0 b - x * m 2 b) = (∑ b, n b * m 0 b) - x * ∑ b, n b * m 2 b := by
      simp only [Fin.sum_univ_three]; ring
    rw [this, hn0, hn2]; ring
  refine ⟨fun i b => h i 0 / colNorm h * n b, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp only [ip, sliceDir, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ,
        Matrix.vecHead, Matrix.vecTail,
        Function.comp]
    · have e : ∀ i : Fin 2, ∑ b, h i 0 / colNorm h * n b * (h i 0 * m 2 b) =
          h i 0 / colNorm h * h i 0 * ∑ b, n b * m 2 b := by
        intro i; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
      rw [e 0, e 1, hn2]; ring
    · have e : ∀ i : Fin 2, ∑ b, h i 0 / colNorm h * n b * (h i 0 * (m 0 b - x * m 2 b)) =
          h i 0 / colNorm h * h i 0 * ∑ b, n b * (m 0 b - x * m 2 b) := by
        intro i; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
      rw [e 0, e 1, hnr]; ring
    · have e : ∀ i : Fin 2, ∑ b, h i 0 / colNorm h * n b * (h i 1 * (m 0 b - x * m 2 b)) =
          h i 0 / colNorm h * h i 1 * ∑ b, n b * (m 0 b - x * m 2 b) := by
        intro i; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
      rw [e 0, e 1, hnr]; ring
  · simp only [ip, Fin.sum_univ_two]
    have e : ∀ i : Fin 2, ∑ b, h i 0 / colNorm h * n b * (h i 0 / colNorm h * n b) =
        (h i 0 / colNorm h) ^ 2 * ∑ b, n b ^ 2 := by
      intro i; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
    rw [e 0, e 1, hn1]
    field_simp
    linarith [hρsq]
  · simp only [ip, sliceOffset, Fin.sum_univ_two]
    have e : ∀ i : Fin 2, ∑ b, h i 0 / colNorm h * n b * (h i 0 * m 1 b + h i 1 * m 2 b) =
        h i 0 / colNorm h * h i 0 * (∑ b, n b * m 1 b) + h i 0 / colNorm h * h i 1 * ∑ b, n b * m 2 b := by
      intro i; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => by ring
    rw [e 0, e 1, hn2]
    have hcollapse : h 0 0 / colNorm h * h 0 0 * (∑ b, n b * m 1 b) + h 0 0 / colNorm h * h 0 1 * 0 +
        (h 1 0 / colNorm h * h 1 0 * (∑ b, n b * m 1 b) + h 1 0 / colNorm h * h 1 1 * 0) =
          colNorm h * ∑ b, n b * m 1 b := by
      have : h 0 0 / colNorm h * h 0 0 + h 1 0 / colNorm h * h 1 0 = colNorm h := by
        field_simp
        linarith [hρsq]
      linear_combination (∑ b, n b * m 1 b) * this
    rw [hcollapse, abs_mul, abs_of_pos hρpos, hnm, mul_div_assoc]

private theorem shearedInner_mul_unip (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (Ψ : 𝓢(Arr, ℂ))
    (hΨ : ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Ψ (fun i b => M i b) = S M) (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ t : InfiniteAdeleRing ℚ,
      psiInf t = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * t))
    (m : Matrix (Fin 3) (Fin 3) ℝ) (c x ξ : ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ) :
    shearedInner psiInf S m c x (h * unip ξ) =
      ∫ w : Fin 2 → ℝ,
        Ψ (sliceOffset m h + ξ • sliceDir m x h 0 + w 0 • sliceDir m x h 1 + w 1 • sliceDir m x h 2) *
          Complex.exp (((-(2 * Real.pi * (a : ℝ) * (c⁻¹ * w 1)) : ℝ) : ℂ) * Complex.I) := by

  set G : (Fin 2 → ℝ) → ℂ := fun w =>
    Ψ (sliceOffset m h + ξ • sliceDir m x h 0 + w 0 • sliceDir m x h 1 + w 1 • sliceDir m x h 2) *
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * (c⁻¹ * w 1)) : ℝ) : ℂ) * Complex.I) with hG
  have hGc : Continuous G := by
    refine Continuous.mul (Ψ.continuous.comp ?_) ?_
    · exact ((continuous_const.add continuous_const).add ((continuous_apply 0).smul continuous_const)).add
        ((continuous_apply 1).smul continuous_const)
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_apply 1).const_mul _)).neg).mul
          continuous_const)
  set T : Fin 2 → Fin 2 → ℝ := ![![1, ξ], ![0, 1]] with hT
  have hTdet : (Matrix.of T).det ≠ 0 := by simp [hT, Matrix.det_fin_two_of]
  have hpt : ∀ w : Fin 2 → ℝ,
      S ((h * unip ξ) * Matrix.of ![fun b => m 1 b + w 0 * (m 0 b - x * m 2 b),
          fun b => m 2 b + w 1 * (m 0 b - x * m 2 b)]) * psiInf (ofReal (-(c⁻¹ * w 1))) =
        G ((Matrix.of T).mulVec w) := by
    intro w
    have hw0 : (Matrix.of T).mulVec w 0 = w 0 + ξ * w 1 := by
      simp [hT, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hw1 : (Matrix.of T).mulVec w 1 = w 1 := by
      simp [hT, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hG]
    simp only [hw0, hw1]
    rw [← hΨ, psiInf_ofReal_neg a psiInf hpsiInf]
    refine congrArg₂ (· * ·) (congrArg (fun z : Arr => Ψ z) ?_) rfl
    funext i b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sliceOffset, sliceDir, Matrix.mul_apply, unip,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp]
    ring
  unfold shearedInner
  simp_rw [hpt]
  rw [integral_comp_mulVec_eq hGc T hTdet]
  have : |(Matrix.of T).det| = 1 := by simp [hT, Matrix.det_fin_two_of]
  rw [this, inv_one, Complex.ofReal_one, one_mul]

private theorem psi_mul_exp (a ξ g : ℝ) :
    psi (-(a * ξ)) * Complex.exp (((-(2 * Real.pi * a * g) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(2 * Real.pi * (a * ξ + a * g)) : ℝ) : ℂ) * Complex.I) := by
  rw [psi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_integral_psi_mul_shearedInner_le (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (Ψ : 𝓢(Arr, ℂ))
    (hΨ : ∀ M : Matrix (Fin 2) (Fin 3) ℝ, Ψ (fun i b => M i b) = S M)
    (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ t : InfiniteAdeleRing ℚ,
      psiInf t = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * t))
    (m : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.det ≠ 0) (N : ℕ) :
    ∃ C : ℝ, ∀ (c x : ℝ), c ≠ 0 → ∀ h : Matrix (Fin 2) (Fin 2) ℝ, IsTransversal h → h.det ≠ 0 →
      ‖∫ ξ : ℝ, psi (-((a : ℝ) * ξ)) * shearedInner psiInf S m c x (h * unip ξ)‖ ≤
        C / (colNorm h ^ 2 * (|h.det| / colNorm h) * Real.sqrt (1 + x ^ 2)) *
          (1 + |(a : ℝ)| * Real.sqrt (1 + x ^ 2) / colNorm h +
              |(a : ℝ) / c| / ((|h.det| / colNorm h) * Real.sqrt (1 + x ^ 2)) + colNorm h) ^ (-(N : ℝ)) := by
  obtain ⟨κ₁, κ₂, hκ₁, hκ₂, hr⟩ := shear_norm_sq_bounds m hm
  obtain ⟨C, hC0, hC⟩ := exists_forall_norm_integral_schwartzMap_slice_mul_exp_le Ψ N
  set Wd : ℝ := (∑ b, m 2 b ^ 2) * (∑ b, m 0 b ^ 2) - (∑ b, m 2 b * m 0 b) ^ 2 with hWd
  have hWpos : 0 < Wd := wedge_sq_pos m hm
  have hsWd : 0 < Real.sqrt Wd := Real.sqrt_pos.2 hWpos
  have hsκ₁ : 0 < Real.sqrt κ₁ := Real.sqrt_pos.2 hκ₁
  have hsκ₂ : 0 < Real.sqrt κ₂ := Real.sqrt_pos.2 hκ₂
  have hdm : 0 < |m.det| := abs_pos.2 hm

  set κ : ℝ := min 1 (min (Real.sqrt κ₁ / (2 * Real.sqrt Wd)) (min (1 / (2 * Real.sqrt κ₂)) (|m.det| / Real.sqrt Wd)))
    with hκ
  have hκpos : 0 < κ := by
    refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hκle1 : κ ≤ 1 := min_le_left _ _
  have hκA : κ ≤ Real.sqrt κ₁ / (2 * Real.sqrt Wd) := (min_le_right _ _).trans (min_le_left _ _)
  have hκB : κ ≤ 1 / (2 * Real.sqrt κ₂) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκC : κ ≤ |m.det| / Real.sqrt Wd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨C / (Real.sqrt Wd * Real.sqrt κ₁) * κ ^ (-(N : ℝ)), ?_⟩
  intro c x hc h ht hh

  have hρ2 : 0 < h 0 0 ^ 2 + h 1 0 ^ 2 := by
    have hd2 := det_sq_of_isTransversal h ht
    have : 0 < h.det ^ 2 := by positivity
    rw [hd2] at this
    rcases mul_pos_iff.1 this with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (not_lt.2 (by positivity))
  set ρ : ℝ := colNorm h with hρdef
  have hρpos : 0 < ρ := Real.sqrt_pos.2 hρ2
  have hρsq : ρ ^ 2 = h 0 0 ^ 2 + h 1 0 ^ 2 := Real.sq_sqrt hρ2.le
  set δ : ℝ := |h.det| / ρ with hδdef
  have hδpos : 0 < δ := div_pos (abs_pos.2 hh) hρpos
  have hdetρδ : |h.det| = ρ * δ := by rw [hδdef]; field_simp
  set X : ℝ := Real.sqrt (1 + x ^ 2) with hXdef
  have hXpos : 0 < X := Real.sqrt_pos.2 (by positivity)
  set R2 : ℝ := ∑ b, (m 0 b - x * m 2 b) ^ 2 with hR2
  obtain ⟨hR2lo, hR2hi⟩ := hr x
  have hR2pos : 0 < R2 := lt_of_lt_of_le (by positivity) hR2lo
  set R : ℝ := Real.sqrt R2 with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.2 hR2pos
  have hRsq : R ^ 2 = R2 := Real.sq_sqrt hR2pos.le
  have hRlo : Real.sqrt κ₁ * X ≤ R := by
    rw [hXdef, hRdef, ← Real.sqrt_mul hκ₁.le]
    exact Real.sqrt_le_sqrt hR2lo
  have hRhi : R ≤ Real.sqrt κ₂ * X := by
    rw [hXdef, hRdef, ← Real.sqrt_mul hκ₂.le]
    exact Real.sqrt_le_sqrt hR2hi

  clear_value Wd κ ρ δ X R2 R
  obtain ⟨f, hf⟩ : ∃ f : ℝ, f = (a : ℝ) * c⁻¹ := ⟨_, rfl⟩
  have hfabs : |(a : ℝ) / c| = |f| := by rw [hf, div_eq_mul_inv]

  have hdetG : 0 < (gram (sliceDir m x h)).det := by
    rw [gram_det_sliceDir m x h ht, ← hWd, ← hR2, ← hρsq]
    positivity

  set φ : Fin 3 → ℝ := ![(a : ℝ), 0, f] with hφ
  set F : (Fin 3 → ℝ) → ℂ := fun u =>
    Ψ (sliceOffset m h + ∑ i, u i • sliceDir m x h i) *
      Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I) with hF
  have hFint : Integrable F := by
    have h1 := integrable_schwartzMap_slice Ψ (sliceDir m x h) (sliceOffset m h) hdetG
    have h2 : Integrable (fun u : Fin 3 → ℝ =>
        Complex.exp (((-(2 * Real.pi * ∑ i, φ i * u i) : ℝ) : ℂ) * Complex.I) *
          Ψ (sliceOffset m h + ∑ i, u i • sliceDir m x h i)) := by
      refine h1.bdd_mul ?_ (Filter.Eventually.of_forall fun u => (Complex.norm_exp_ofReal_mul_I _).le)
      refine (Complex.continuous_exp.comp ?_).aestronglyMeasurable
      refine (Complex.continuous_ofReal.comp ?_).mul continuous_const
      exact (continuous_const.mul (continuous_finsetSum _ fun i _ => (continuous_apply i).const_mul _)).neg
    refine h2.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF]
    ring
  have hident : ∫ ξ : ℝ, psi (-((a : ℝ) * ξ)) * shearedInner psiInf S m c x (h * unip ξ) = ∫ u, F u := by

    have hsplit : ∫ u, F u = ∫ ξ : ℝ, ∫ w : Fin 2 → ℝ, F (Fin.cons ξ w) := by
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0 with he
      have hmp : MeasurePreserving e.symm :=
        (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm e
      have h1 : ∫ u, F u = ∫ p : ℝ × (Fin 2 → ℝ), F (e.symm p) :=
        (hmp.integral_comp (MeasurableEquiv.measurableEmbedding _) F).symm
      have h2 : Integrable (fun p : ℝ × (Fin 2 → ℝ) => F (e.symm p)) :=
        (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hFint
      rw [h1, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod _ h2]
      simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
        Fin.insertNth_zero']
    rw [hsplit]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [shearedInner_mul_unip S Ψ hΨ a psiInf hpsiInf m c x ξ h, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    dsimp only
    have hX : sliceOffset m h + ∑ i, (Fin.cons ξ w : Fin 3 → ℝ) i • sliceDir m x h i =
        sliceOffset m h + ξ • sliceDir m x h 0 + w 0 • sliceDir m x h 1 + w 1 • sliceDir m x h 2 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.cons_zero, Fin.cons_succ]
      simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      abel
    have hsum : ∑ i, φ i * (Fin.cons ξ w : Fin 3 → ℝ) i = (a : ℝ) * ξ + (a : ℝ) * (c⁻¹ * w 1) := by
      simp only [hφ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.cons_zero, Fin.cons_succ,
        Matrix.cons_val_succ, Matrix.cons_val_zero]
      simp only [Fin.succ_zero_eq_one]
      rw [hf]
      ring
    simp only [hF]
    rw [hX, hsum, ← psi_mul_exp (a : ℝ) ξ (c⁻¹ * w 1)]
    ring

  obtain ⟨v, hv0, hv1, hvp⟩ := exists_slice_normal m hm x h ht (by rw [← hρdef]; exact hρpos.ne')
  have hbrick := hC (sliceDir m x h) (sliceOffset m h) φ v hdetG hv0 hv1
  rw [hident]
  refine hbrick.trans ?_
  rw [gram_det_sliceDir m x h ht, quadForm_sliceDir m hm x h ht hh (a : ℝ) f, hvp, ← hWd, ← hR2, ← hρsq, ← hρdef,
    hfabs]

  have hjac : Real.sqrt (ρ ^ 2 * h.det ^ 2 * Wd * R2) = ρ * (ρ * δ) * Real.sqrt Wd * R := by
    rw [← hRsq, ← hdetρδ]
    have : ρ ^ 2 * h.det ^ 2 * Wd * R ^ 2 = (ρ * |h.det| * Real.sqrt Wd * R) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hWpos.le]
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hjac]
  set A : ℝ := |(a : ℝ)| * R / (ρ * Real.sqrt Wd) with hA
  set B : ℝ := |f| / (δ * R) with hB
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  clear_value A B
  have hquad : Real.sqrt ((a : ℝ) ^ 2 * R2 / (ρ ^ 2 * Wd) + f ^ 2 * ρ ^ 2 / (h.det ^ 2 * R2)) =
      Real.sqrt (A ^ 2 + B ^ 2) := by
    congr 1
    rw [hA, hB, ← hRsq, div_pow, div_pow, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hWpos.le]
    have hd2 : h.det ^ 2 = (ρ * δ) ^ 2 := by rw [← sq_abs, hdetρδ]
    rw [hd2]
    field_simp
  rw [hquad]
  have hsqrtAB : (A + B) / 2 ≤ Real.sqrt (A ^ 2 + B ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), ← sub_nonneg,
      show A ^ 2 + B ^ 2 - ((A + B) / 2) ^ 2 = ((A - B) ^ 2 + 2 * A ^ 2 + 2 * B ^ 2) / 4 by ring]
    positivity

  set Q₁ : ℝ := |(a : ℝ)| * X / ρ with hQ₁
  set Q₂ : ℝ := |f| / (δ * X) with hQ₂
  have hQ₁nn : 0 ≤ Q₁ := by rw [hQ₁]; positivity
  have hQ₂nn : 0 ≤ Q₂ := by rw [hQ₂]; positivity
  clear_value Q₁ Q₂
  have hAeq : A * (ρ * Real.sqrt Wd) = |(a : ℝ)| * R := by rw [hA]; field_simp
  have hBeq : B * (δ * R) = |f| := by rw [hB]; field_simp
  have hQ₁eq : Q₁ * ρ = |(a : ℝ)| * X := by rw [hQ₁]; field_simp
  have hQ₂eq : Q₂ * (δ * X) = |f| := by rw [hQ₂]; field_simp
  have hκA' : κ * (2 * Real.sqrt Wd) ≤ Real.sqrt κ₁ := by rwa [le_div_iff₀ (by positivity)] at hκA
  have hκB' : κ * (2 * Real.sqrt κ₂) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hκB
  have hQ₁A : κ * Q₁ ≤ A / 2 := by
    rw [le_div_iff₀ two_pos]
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < ρ * Real.sqrt Wd)
    rw [hAeq]
    calc κ * Q₁ * 2 * (ρ * Real.sqrt Wd) = κ * (2 * Real.sqrt Wd) * (Q₁ * ρ) := by ring
      _ = κ * (2 * Real.sqrt Wd) * (|(a : ℝ)| * X) := by rw [hQ₁eq]
      _ ≤ Real.sqrt κ₁ * (|(a : ℝ)| * X) := mul_le_mul_of_nonneg_right hκA' (by positivity)
      _ = |(a : ℝ)| * (Real.sqrt κ₁ * X) := by ring
      _ ≤ |(a : ℝ)| * R := mul_le_mul_of_nonneg_left hRlo (abs_nonneg _)
  have hQ₂B : κ * Q₂ ≤ B / 2 := by
    rw [le_div_iff₀ two_pos]
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < δ * R * X)
    calc κ * Q₂ * 2 * (δ * R * X) = κ * 2 * R * (Q₂ * (δ * X)) := by ring
      _ = κ * 2 * R * |f| := by rw [hQ₂eq]
      _ ≤ κ * 2 * (Real.sqrt κ₂ * X) * |f| := by gcongr
      _ = κ * (2 * Real.sqrt κ₂) * (X * |f|) := by ring
      _ ≤ 1 * (X * |f|) := mul_le_mul_of_nonneg_right hκB' (by positivity)
      _ = |f| * X := by ring
      _ = B * (δ * R) * X := by rw [hBeq]
      _ = B * (δ * R * X) := by ring
  have hQ₃ : κ * ρ ≤ ρ * |m.det| / Real.sqrt Wd := by
    rw [mul_div_assoc, mul_comm]
    exact mul_le_mul_of_nonneg_left hκC hρpos.le
  have hbr : κ * (1 + Q₁ + Q₂ + ρ) ≤ 1 + Real.sqrt (A ^ 2 + B ^ 2) + ρ * |m.det| / Real.sqrt Wd := by
    have : κ * (1 + Q₁ + Q₂ + ρ) = κ * 1 + κ * Q₁ + κ * Q₂ + κ * ρ := by ring
    rw [this]
    have hk1 : κ * 1 ≤ 1 := by rw [mul_one]; exact hκle1
    linarith [hsqrtAB]
  have hbrpos : 0 < κ * (1 + Q₁ + Q₂ + ρ) := by positivity
  have hpow : (1 + Real.sqrt (A ^ 2 + B ^ 2) + ρ * |m.det| / Real.sqrt Wd) ^ (-(N : ℝ)) ≤
      κ ^ (-(N : ℝ)) * (1 + Q₁ + Q₂ + ρ) ^ (-(N : ℝ)) := by
    rw [← Real.mul_rpow hκpos.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos hbrpos hbr (by simp)

  have hjacle : C / (ρ * (ρ * δ) * Real.sqrt Wd * R) ≤ C / (Real.sqrt Wd * Real.sqrt κ₁) / (ρ ^ 2 * δ * X) := by
    rw [div_div]
    refine div_le_div_of_nonneg_left hC0 (by positivity) ?_
    calc Real.sqrt Wd * Real.sqrt κ₁ * (ρ ^ 2 * δ * X) = ρ * (ρ * δ) * Real.sqrt Wd * (Real.sqrt κ₁ * X) := by ring
      _ ≤ ρ * (ρ * δ) * Real.sqrt Wd * R := mul_le_mul_of_nonneg_left hRlo (by positivity)
  refine (mul_le_mul hjacle hpow (by positivity) (by positivity)).trans (le_of_eq ?_)
  ring

private theorem continuous_of_mem_polyGauss3 (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) :
    Continuous S := by
  obtain ⟨Φ, hΦ⟩ := G0.exists_schwartzMap_eq_of_mem_polyGauss3' hS
  have hSΦ : S = fun M : Matrix (Fin 2) (Fin 3) ℝ => Φ (fun i b => M i b) := funext fun M => (hΦ M).symm
  rw [hSΦ]
  exact Φ.continuous.comp
    (continuous_pi fun i => continuous_pi fun b => (continuous_apply b).comp (continuous_apply i))

private noncomputable def dualIntegrandR {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (m : Matrix (Fin 3) (Fin 3) ℝ)
    (z : (ℝ × ℝ) × (Fin 2 → Fin 2 → ℝ)) : ℂ :=
  ((z.1.1 ^ 2)⁻¹ • shearedInner ψ S m z.1.1 z.1.2 (Matrix.of z.2)) *
    ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of z.2).det * (((|(Matrix.of z.2).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (ArchR.diagOne a * (Matrix.of z.2)⁻¹)

private theorem measurable_dualIntegrandR {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ha : a ≠ 0) (a₀ : ℚ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hψ : ∀ x : InfiniteAdeleRing ℚ,
      ψ x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a₀ * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    Measurable (dualIntegrandR D u₃ a₃ a ψ S m) := by
  classical
  have hScont : Continuous S := continuous_of_mem_polyGauss3 S hS

  have hψc : Continuous fun r : ℝ => ψ (StandardKernel.ofReal (-r)) := by
    have hrw : (fun r : ℝ => ψ (StandardKernel.ofReal (-r))) =
        fun r : ℝ => Complex.exp (((-(2 * Real.pi * (a₀ : ℝ) * r) : ℝ) : ℂ) * Complex.I) :=
      funext fun r => psiInf_ofReal_neg a₀ ψ hψ r
    rw [hrw]
    fun_prop

  have hf : Measurable fun p : ((ℝ × ℝ) × (Fin 2 → Fin 2 → ℝ)) × (Fin 2 → ℝ) =>
      S (Matrix.of p.1.2 * Matrix.of ![fun b => m 1 b + p.2 0 * (m 0 b - p.1.1.2 * m 2 b),
          fun b => m 2 b + p.2 1 * (m 0 b - p.1.1.2 * m 2 b)]) *
        ψ (StandardKernel.ofReal (-(p.1.1.1⁻¹ * p.2 1))) := by
    refine Measurable.mul ?_ ?_
    · refine (hScont.comp ?_).measurable
      refine Continuous.matrix_mul ?_ ?_
      · exact continuous_matrix fun i j =>
          (continuous_apply j).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
      · refine continuous_matrix fun i j => ?_
        fin_cases i <;> simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
          Fin.mk_one, Fin.isValue] <;> fun_prop
    · exact hψc.measurable.comp
        (measurable_fst.fst.fst.inv.mul ((measurable_pi_apply (1 : Fin 2)).comp measurable_snd))
  have hSI : Measurable fun z : (ℝ × ℝ) × (Fin 2 → Fin 2 → ℝ) =>
      shearedInner ψ S m z.1.1 z.1.2 (Matrix.of z.2) :=
    (hf.stronglyMeasurable.integral_prod_right').measurable

  have hdet : Continuous fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det :=
    (continuous_id : Continuous (id : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ)).matrix_det
  have hopen : IsOpen ArchR.glSet := isOpen_ne_fun hdet continuous_const
  have hE : Measurable fun e : Fin 2 → Fin 2 → ℝ =>
      ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹) := by
    have hpw : (fun e : Fin 2 → Fin 2 → ℝ =>
        ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
          D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) =
        ArchR.glSet.piecewise (fun e : Fin 2 → Fin 2 → ℝ =>
          ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) (fun _ => (0 : ℂ)) := by
      funext e
      by_cases he : e ∈ ArchR.glSet
      · rw [Set.piecewise_eq_of_mem _ _ _ he]
      · rw [Set.piecewise_eq_of_notMem _ _ _ he]
        have hd : (Matrix.of e).det = 0 := by simpa [ArchR.glSet] using he
        simp [hd]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hopen.measurableSet
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    ·
      intro e he
      have hde : (Matrix.of e).det ≠ 0 := he
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.comp (g := ArchR.quasiChar (u₃ + 2) a₃) ?_ hdet.continuousAt
      show ContinuousAt (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ (u₃ + 2) *
        (if a₃ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ))) _
      refine ContinuousAt.mul ?_ ?_
      · refine ContinuousAt.comp (g := fun w : ℂ => w ^ (u₃ + 2)) ?_
          (Complex.continuous_ofReal.comp continuous_abs).continuousAt
        exact continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 (abs_pos.2 hde))
      · by_cases h3 : a₃ = 0
        · simp only [h3, ↓reduceIte]
          exact continuousAt_const
        · simp only [h3, ↓reduceIte]
          exact ((Complex.continuous_ofReal.comp
            (continuous_of_discreteTopology (f := fun s : SignType => (s : ℝ)))).continuousAt.comp
              (continuousAt_sign_of_ne_zero hde))
    ·
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.inv₀ ((continuous_abs.comp hdet).pow 2).continuousOn fun e he => ?_
      exact pow_ne_zero 2 (abs_ne_zero.2 he)
    ·
      have hW : ContinuousOn (ArchR.asPi D.W) ArchR.glSet := D.smooth.continuousOn
      have hinner : ContinuousOn
          (fun e : Fin 2 → Fin 2 → ℝ => Matrix.of.symm (ArchR.diagOne a * (Matrix.of e)⁻¹)) ArchR.glSet := by
        intro e he
        refine ContinuousAt.continuousWithinAt ?_
        have hinv : ContinuousAt (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) (Matrix.of e) :=
          continuousAt_matrix_inv (Matrix.of e) (NormedRing.inverse_continuousAt (Units.mk0 _ he))
        exact ((continuous_const (y := ArchR.diagOne a)).matrix_mul continuous_id).continuousAt.comp hinv
      have hmaps : Set.MapsTo
          (fun e : Fin 2 → Fin 2 → ℝ => Matrix.of.symm (ArchR.diagOne a * (Matrix.of e)⁻¹)) ArchR.glSet
            ArchR.glSet := by
        intro e he
        have hde : (Matrix.of e).det ≠ 0 := he
        show (Matrix.of (Matrix.of.symm (ArchR.diagOne a * (Matrix.of e)⁻¹))).det ≠ 0
        rw [Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
        have h1 : (ArchR.diagOne a).det = a := by simp [ArchR.diagOne, Matrix.det_fin_two_of]
        rw [h1]
        exact mul_ne_zero ha (inv_ne_zero hde)
      exact hW.comp hinner hmaps

  have hfun : dualIntegrandR D u₃ a₃ a ψ S m = fun z =>
      ((z.1.1 ^ 2)⁻¹ • shearedInner ψ S m z.1.1 z.1.2 (Matrix.of z.2)) *
        (ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of z.2).det * (((|(Matrix.of z.2).det| ^ 2)⁻¹ : ℝ) : ℂ) *
          D.W (ArchR.diagOne a * (Matrix.of z.2)⁻¹)) := by
    funext z
    unfold dualIntegrandR
    simp only [mul_assoc]
  rw [hfun]
  exact (((measurable_fst.fst.pow_const 2).inv.smul hSI)).mul (hE.comp measurable_snd)

end DualArchZetaBound

end

end R1_B4_and_M1

section R3_B12

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction LanglandsTunnell.Converse MeasureTheory NumberField"
open scoped Matrix

namespace DualArchZetaBound

open AutomorphicForm.StandardKernel

private theorem coe_longWeyl3_mul_transposeInv3_point (α : (InfiniteAdeleRing ℚ)ˣ) (x : InfiniteAdeleRing ℚ) :
    ((longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) :
        GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      !![0, 1, 0; 0, 0, 1; ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ), 0,
          -(x * ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ))] := by
  have h1 : (transposeInv3 (1 : GL (Fin 3) (InfiniteAdeleRing ℚ))) = 1 := by
    apply Units.ext
    change (((1 : GL (Fin 3) (InfiniteAdeleRing ℚ))⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ = 1
    simp
  rw [h1, mul_one, Units.val_mul]
  change ((longWeyl3 : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) *
      (((iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * weylPrime3)⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ = _
  rw [mul_inv_rev, mul_inv_rev, Units.val_mul, Units.val_mul]

  have hw : (((weylPrime3 : GL (Fin 3) (InfiniteAdeleRing ℚ))⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl
  have hu : (((lowerUnipotent21 x : GL (Fin 3) (InfiniteAdeleRing ℚ))⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = !![1, 0, 0; -x, 1, 0; 0, 0, 1] := rfl
  have hd : (((iotaGL (diagUnitGL2 α) : GL (Fin 3) (InfiniteAdeleRing ℚ))⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
        !![((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ), 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [← map_inv]
    change embedMat2 ((diagUnitGL2 α)⁻¹ : GL (Fin 2) (InfiniteAdeleRing ℚ)).val = _
    change embedMat2 (!![((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ), 0; 0, 1]) = _
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hw, hu, hd, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]

private theorem realMat_dual_point_mul (α : (InfiniteAdeleRing ℚ)ˣ) (x : InfiniteAdeleRing ℚ)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    AutomorphicForm.StandardKernel.realMat
        (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          gInf) =
      !![0, 1, 0; 0, 0, 1;
          AutomorphicForm.StandardKernel.realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ), 0,
          -(AutomorphicForm.StandardKernel.realCoord x *
            AutomorphicForm.StandardKernel.realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ))] *
        AutomorphicForm.StandardKernel.realMat gInf := by
  rw [AutomorphicForm.StandardKernel.realMat_mul]
  congr 1
  rw [AutomorphicForm.StandardKernel.realMat_eq, coe_longWeyl3_mul_transposeInv3_point]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem det_dual_point_matrix (c d : ℝ) :
    (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, d] : Matrix (Fin 3) (Fin 3) ℝ).det = c := by
  rw [Matrix.det_fin_three]
  simp

private theorem godementInner3_point (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) (c x : ℝ) (hc : c ≠ 0) :
    godementInner3 ψ S h (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) =
      (c ^ 2)⁻¹ • ∫ w : Fin 2 → ℝ,
        S (h * Matrix.of ![fun b => m 1 b + w 0 * (m 0 b - x * m 2 b),
            fun b => m 2 b + w 1 * (m 0 b - x * m 2 b)]) *
          ψ (ofReal (-(c⁻¹ * w 1))) := by
  have h0 : ∀ b, (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) 0 b = m 1 b := fun b => by
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h1 : ∀ b, (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) 1 b = m 2 b := fun b => by
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h2 : ∀ b, (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) 2 b = c * (m 0 b - x * m 2 b) := fun b => by
    simp [Matrix.mul_apply, Fin.sum_univ_three]; ring1
  unfold godementInner3
  set f : (Fin 2 → ℝ) → ℂ := fun v =>
    S (h * Matrix.of ![fun b => (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) 0 b +
          v 0 * (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) 2 b,
        fun b => (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) 1 b +
          v 1 * (!![(0 : ℝ), 1, 0; 0, 0, 1; c, 0, -(x * c)] * m) 2 b]) *
      ψ (ofReal (-(v 1))) with hf
  have hsmul : ∫ w : Fin 2 → ℝ, f (c⁻¹ • w) = |((c⁻¹) ^ (Module.finrank ℝ (Fin 2 → ℝ)))⁻¹| • ∫ v, f v :=
    Measure.integral_comp_smul volume f c⁻¹
  have hrank : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  rw [hrank] at hsmul
  have hpos : |((c⁻¹) ^ 2)⁻¹| = c ^ 2 := by
    rw [inv_pow, inv_inv, abs_of_nonneg (by positivity)]
  rw [hpos] at hsmul
  have hc2 : (c ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hc
  have hmain : ∫ v, f v = (c ^ 2)⁻¹ • ∫ w : Fin 2 → ℝ, f (c⁻¹ • w) := by
    rw [hsmul, smul_smul, inv_mul_cancel₀ hc2, one_smul]
  change ∫ v, f v = _
  rw [hmain]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hf, Pi.smul_apply, smul_eq_mul, h0, h1, h2]
  congr 2
  · congr 1
    ext i b
    fin_cases i <;> simp <;> field_simp

private theorem jacquetVector3_dual_point {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (α : (InfiniteAdeleRing ℚ)ˣ) (x : InfiniteAdeleRing ℚ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D u₃ a₃ a ψ S
        (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          gInf) =
      ArchR.quasiChar (u₃ + 1) a₃
          (realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) * (realMat gInf).det) *
        ∫ e : Fin 2 → Fin 2 → ℝ,
          ((realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) ^ 2)⁻¹ •
              ∫ w : Fin 2 → ℝ,
                S (Matrix.of e * Matrix.of ![fun b => realMat gInf 1 b +
                      w 0 * (realMat gInf 0 b - realCoord x * realMat gInf 2 b),
                    fun b => realMat gInf 2 b +
                      w 1 * (realMat gInf 0 b - realCoord x * realMat gInf 2 b)]) *
                  ψ (ofReal (-((realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ))⁻¹ * w 1)))) *
            ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
              D.W (ArchR.diagOne a * (Matrix.of e)⁻¹) := by
  set c : ℝ := realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) with hcdef
  have hc : c ≠ 0 := by
    intro h0
    have hone : realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) *
        realCoord (α : InfiniteAdeleRing ℚ) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [← hcdef, h0, zero_mul] at hone
    exact zero_ne_one hone
  rw [jacquetVector3_eq, realMat_dual_point_mul, Matrix.det_mul, det_dual_point_matrix]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  unfold jacquetIntegrand3
  rw [realMat_dual_point_mul, godementInner3_point ψ S (Matrix.of e) _ c _ hc]

end DualArchZetaBound

end R3_B12

section R4_B5_B6i_core

open MeasureTheory Set
open scoped Matrix ENNReal

noncomputable section

namespace DualArchZetaBound

private def rad (c₀ : Fin 2 → ℝ) : ℝ := Real.sqrt (c₀ 0 ^ 2 + c₀ 1 ^ 2)

private def transv (c₀ : Fin 2 → ℝ) (d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c₀ 0, -(d * c₀ 1) / rad c₀; c₀ 1, d * c₀ 0 / rad c₀]

private def shear (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, ξ; 0, 1]

private theorem transv_colNorm (c₀ : Fin 2 → ℝ) (d : ℝ) :
    Real.sqrt (transv c₀ d 0 0 ^ 2 + transv c₀ d 1 0 ^ 2) = rad c₀ := by
  simp [transv, rad]

private theorem transv_isTransversal (c₀ : Fin 2 → ℝ) (d : ℝ) :
    transv c₀ d 0 0 * transv c₀ d 0 1 + transv c₀ d 1 0 * transv c₀ d 1 1 = 0 := by
  simp only [transv, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

private theorem rad_sq (c₀ : Fin 2 → ℝ) : rad c₀ ^ 2 = c₀ 0 ^ 2 + c₀ 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem rad_nonneg (c₀ : Fin 2 → ℝ) : 0 ≤ rad c₀ := Real.sqrt_nonneg _

private theorem rad_eq_zero_iff (c₀ : Fin 2 → ℝ) : rad c₀ = 0 ↔ c₀ = 0 := by
  rw [rad, Real.sqrt_eq_zero (by positivity)]
  constructor
  · intro h
    have h0 : c₀ 0 = 0 := by nlinarith [sq_nonneg (c₀ 0), sq_nonneg (c₀ 1)]
    have h1 : c₀ 1 = 0 := by nlinarith [sq_nonneg (c₀ 0), sq_nonneg (c₀ 1)]
    ext i; fin_cases i <;> simp [h0, h1]
  · intro h; simp [h]

private theorem transv_det (c₀ : Fin 2 → ℝ) (d : ℝ) : (transv c₀ d).det = d * rad c₀ := by
  rw [transv, Matrix.det_fin_two_of]
  by_cases h : rad c₀ = 0
  · have hc : c₀ = 0 := (rad_eq_zero_iff c₀).mp h
    simp [hc, rad]
  · have hsq := rad_sq c₀
    field_simp
    linear_combination (-d) * hsq

private theorem transv_mul_shear_apply (c₀ : Fin 2 → ℝ) (d ξ : ℝ) (i : Fin 2) :
    (transv c₀ d * shear ξ) i 0 = c₀ i ∧
      (transv c₀ d * shear ξ) i 1 = ξ * c₀ i + d / rad c₀ * ![-(c₀ 1), c₀ 0] i := by
  fin_cases i <;> simp [transv, shear, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private def colMap (c₀ : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' !![-(c₀ 1) / rad c₀, c₀ 0; c₀ 0 / rad c₀, c₀ 1]

private theorem det_colMap (c₀ : Fin 2 → ℝ) (hc : c₀ ≠ 0) : LinearMap.det (colMap c₀) = -rad c₀ := by
  rw [colMap, LinearMap.det_toLin', Matrix.det_fin_two_of]
  have hρ : rad c₀ ≠ 0 := fun h => hc ((rad_eq_zero_iff c₀).mp h)
  have hsq := rad_sq c₀
  field_simp
  nlinarith [hsq]

private theorem colMap_apply (c₀ : Fin 2 → ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    colMap c₀ v i = v 1 * c₀ i + v 0 / rad c₀ * ![-(c₀ 1), c₀ 0] i := by
  fin_cases i <;> simp [colMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] <;> ring

private def transposeLin : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) where
  toFun e := fun i j => e j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem transposeLin_comp_self : transposeLin ∘ₗ transposeLin = LinearMap.id := rfl

private theorem abs_det_transposeLin : |LinearMap.det transposeLin| = 1 := by
  have h : LinearMap.det transposeLin * LinearMap.det transposeLin = 1 := by
    rw [← LinearMap.det_comp, transposeLin_comp_self, LinearMap.det_id]
  have h' : |LinearMap.det transposeLin| * |LinearMap.det transposeLin| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg (LinearMap.det transposeLin)]

private theorem map_transposeLin_volume :
    Measure.map transposeLin (volume : Measure (Fin 2 → Fin 2 → ℝ)) = volume := by
  have hdet : LinearMap.det transposeLin ≠ 0 := by
    intro h; have := abs_det_transposeLin; rw [h, abs_zero] at this; exact zero_ne_one this
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet]
  have : |(LinearMap.det transposeLin)⁻¹| = 1 := by rw [abs_inv, abs_det_transposeLin, inv_one]
  simp [this]

private def transposeEquiv : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (Fin 2 → Fin 2 → ℝ) where
  toFun e := fun i j => e j i
  invFun e := fun i j => e j i
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun :=
    measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)
  measurable_invFun :=
    measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun j => (measurable_pi_apply i).comp (measurable_pi_apply j)

private theorem transposeEquiv_measurePreserving : MeasurePreserving transposeEquiv volume volume :=
  ⟨transposeEquiv.measurable, map_transposeLin_volume⟩

private def colSplit : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  transposeEquiv.trans MeasurableEquiv.finTwoArrow

private theorem colSplit_measurePreserving : MeasurePreserving colSplit volume volume :=
  (volume_preserving_finTwoArrow (Fin 2 → ℝ)).comp transposeEquiv_measurePreserving

private theorem colSplit_symm_apply (c₀ v : Fin 2 → ℝ) (i j : Fin 2) : colSplit.symm (c₀, v) i j = ![c₀, v] j i := rfl

private theorem colSplit_symm_colMap (c₀ w : Fin 2 → ℝ) :
    colSplit.symm (c₀, colMap c₀ w) = fun i j => (transv c₀ (w 0) * shear (w 1)) i j := by
  ext i j
  rw [colSplit_symm_apply]
  obtain ⟨h0, h1⟩ := transv_mul_shear_apply c₀ (w 0) (w 1) i
  fin_cases j
  · simpa using h0.symm
  · simpa [colMap_apply] using h1.symm

private theorem measurable_colMap (c₀ : Fin 2 → ℝ) : Measurable (colMap c₀) :=
  (colMap c₀).continuous_of_finiteDimensional.measurable

private theorem rad_pos_of_ne_zero {c₀ : Fin 2 → ℝ} (hc : c₀ ≠ 0) : 0 < rad c₀ :=
  lt_of_le_of_ne (rad_nonneg c₀) fun h => hc ((rad_eq_zero_iff c₀).mp h.symm)

private theorem map_colMap_volume {c₀ : Fin 2 → ℝ} (hc : c₀ ≠ 0) :
    Measure.map (colMap c₀) (volume : Measure (Fin 2 → ℝ)) = ENNReal.ofReal (rad c₀)⁻¹ • volume := by
  have hdet : LinearMap.det (colMap c₀) ≠ 0 := by
    rw [det_colMap c₀ hc]; exact neg_ne_zero.mpr (rad_pos_of_ne_zero hc).ne'
  rw [Measure.map_linearMap_addHaar_pi_eq_smul_addHaar hdet, det_colMap c₀ hc, abs_inv, abs_neg,
    abs_of_pos (rad_pos_of_ne_zero hc)]

private theorem ae_ne_zero_col : ∀ᵐ c₀ : Fin 2 → ℝ, c₀ ≠ 0 := by
  rw [ae_iff]
  simp

private theorem lintegral_colMap {c₀ : Fin 2 → ℝ} (hc : c₀ ≠ 0) (g : (Fin 2 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v, g v = ∫⁻ w, g (colMap c₀ w) * ENNReal.ofReal (rad c₀) := by
  have hρ := rad_pos_of_ne_zero hc
  have h1 : ∫⁻ w, g (colMap c₀ w) = ENNReal.ofReal (rad c₀)⁻¹ * ∫⁻ v, g v := by
    rw [← lintegral_map hg (measurable_colMap c₀), map_colMap_volume hc, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_mul_const' _ (fun w => g (colMap c₀ w)) ENNReal.ofReal_ne_top, h1, mul_comm, ← mul_assoc,
    ← ENNReal.ofReal_mul hρ.le, mul_inv_cancel₀ hρ.ne', ENNReal.ofReal_one, one_mul]

private theorem integral_colMap {c₀ : Fin 2 → ℝ} (hc : c₀ ≠ 0) (g : (Fin 2 → ℝ) → ℂ) (hg : AEStronglyMeasurable g volume) :
    ∫ v, g v = (rad c₀ : ℂ) * ∫ w, g (colMap c₀ w) := by
  have hρ := rad_pos_of_ne_zero hc
  have hg' : AEStronglyMeasurable g (Measure.map (colMap c₀) volume) := by
    rw [map_colMap_volume hc]; exact hg.mono_ac (Measure.smul_absolutelyContinuous)
  have h1 : ∫ w, g (colMap c₀ w) = (rad c₀)⁻¹ • ∫ v, g v := by
    rw [← integral_map (measurable_colMap c₀).aemeasurable hg', map_colMap_volume hc, integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hρ.le)]
  rw [h1, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hρ.ne', Complex.ofReal_one, one_mul]

private theorem integrable_comp_colMap {c₀ : Fin 2 → ℝ} (hc : c₀ ≠ 0) {g : (Fin 2 → ℝ) → ℂ} (hg : Integrable g) :
    Integrable fun w => g (colMap c₀ w) := by
  have hρ := rad_pos_of_ne_zero hc
  have hg' : Integrable g (Measure.map (colMap c₀) volume) := by
    rw [map_colMap_volume hc]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_measure hg'.aestronglyMeasurable (measurable_colMap c₀).aemeasurable).mp hg'

private theorem finTwoArrow_symm_pair (d ξ : ℝ) : (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (d, ξ) = ![d, ξ] := by
  ext k; fin_cases k <;> rfl

private theorem lintegral_finTwo (G : (Fin 2 → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ w, G w = ∫⁻ d : ℝ, ∫⁻ ξ : ℝ, G ![d, ξ] := by
  rw [MeasurePreserving.lintegral_map_equiv G MeasurableEquiv.finTwoArrow.symm
    ((volume_preserving_finTwoArrow ℝ).symm _), Measure.volume_eq_prod,
    lintegral_prod (fun p : ℝ × ℝ => G (MeasurableEquiv.finTwoArrow.symm p))
      (hG.comp MeasurableEquiv.finTwoArrow.symm.measurable).aemeasurable]
  simp only [finTwoArrow_symm_pair]

private theorem integral_finTwo (G : (Fin 2 → ℝ) → ℂ) (hG : Integrable G) :
    ∫ w, G w = ∫ d : ℝ, ∫ ξ : ℝ, G ![d, ξ] := by
  rw [← MeasurePreserving.integral_comp' ((volume_preserving_finTwoArrow ℝ).symm _) G, Measure.volume_eq_prod,
    integral_prod _ (by
      rw [← Measure.volume_eq_prod]
      exact ((volume_preserving_finTwoArrow ℝ).symm _ |>.integrable_comp_emb
        MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).mpr hG)]
  simp only [finTwoArrow_symm_pair]

private theorem lintegral_eq_lintegral_transv_mul_shear (f : (Fin 2 → Fin 2 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ e : Fin 2 → Fin 2 → ℝ, f e =
      ∫⁻ c₀ : Fin 2 → ℝ, ∫⁻ d : ℝ, ∫⁻ ξ : ℝ,
        f (fun i j => (transv c₀ d * shear ξ) i j) * ENNReal.ofReal (rad c₀) := by
  have hfs : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => f (colSplit.symm p) := hf.comp colSplit.symm.measurable
  rw [MeasurePreserving.lintegral_map_equiv f colSplit.symm (colSplit_measurePreserving.symm _),
    Measure.volume_eq_prod, lintegral_prod _ hfs.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ne_zero_col] with c₀ hc
  rw [lintegral_colMap hc (fun v => f (colSplit.symm (c₀, v))) (hfs.comp measurable_prodMk_left),
    lintegral_finTwo (fun w => f (colSplit.symm (c₀, colMap c₀ w)) * ENNReal.ofReal (rad c₀))
      (((hfs.comp measurable_prodMk_left).comp (measurable_colMap c₀)).mul_const _)]
  refine lintegral_congr fun d => lintegral_congr fun ξ => ?_
  rw [colSplit_symm_colMap]
  simp

private theorem continuous_rad : Continuous rad := Real.continuous_sqrt.comp (by fun_prop)

private def arr (z : ((Fin 2 → ℝ) × ℝ) × ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => (transv z.1.1 z.1.2 * shear z.2) i j

private theorem arr_eq_colSplit (z : ((Fin 2 → ℝ) × ℝ) × ℝ) : arr z = colSplit.symm (z.1.1, colMap z.1.1 ![z.1.2, z.2]) := by
  rw [colSplit_symm_colMap]; rfl

private theorem measurable_arr : Measurable arr := by
  have hrad : Measurable rad := continuous_rad.measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [arr, transv, shear, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem ae_fst_fst_ne_zero : ∀ᵐ z : ((Fin 2 → ℝ) × ℝ) × ℝ, z.1.1 ≠ 0 := by
  rw [ae_iff]
  have : {z : ((Fin 2 → ℝ) × ℝ) × ℝ | ¬ z.1.1 ≠ 0} =
      (({0} : Set (Fin 2 → ℝ)) ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) := by
    ext z; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    measure_singleton, zero_mul, zero_mul]

private theorem lintegral_triple (φ : ((Fin 2 → ℝ) × ℝ) × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z, φ z = ∫⁻ c₀ : Fin 2 → ℝ, ∫⁻ d : ℝ, ∫⁻ ξ : ℝ, φ ((c₀, d), ξ) := by
  rw [Measure.volume_eq_prod, lintegral_prod φ hφ.aemeasurable, Measure.volume_eq_prod,
    lintegral_prod (fun q : (Fin 2 → ℝ) × ℝ => ∫⁻ ξ : ℝ, φ (q, ξ)) hφ.lintegral_prod_right'.aemeasurable]

private theorem quasiMeasurePreserving_arr : Measure.QuasiMeasurePreserving arr volume volume := by
  refine ⟨measurable_arr, Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_⟩
  rw [Measure.map_apply measurable_arr hN]
  have hφ : Measurable fun z : ((Fin 2 → ℝ) × ℝ) × ℝ =>
      N.indicator (1 : (Fin 2 → Fin 2 → ℝ) → ℝ≥0∞) (arr z) * ENNReal.ofReal (rad z.1.1) :=
    ((measurable_one.indicator hN).comp measurable_arr).mul
      (ENNReal.measurable_ofReal.comp (continuous_rad.measurable.comp measurable_fst.fst))
  have hzero : ∫⁻ z : ((Fin 2 → ℝ) × ℝ) × ℝ,
      N.indicator (1 : (Fin 2 → Fin 2 → ℝ) → ℝ≥0∞) (arr z) * ENNReal.ofReal (rad z.1.1) = 0 := by
    rw [lintegral_triple _ hφ]
    have key := lintegral_eq_lintegral_transv_mul_shear (N.indicator 1) (measurable_one.indicator hN)
    rw [lintegral_indicator_one hN, hN0] at key
    exact key.symm
  have hae := (lintegral_eq_zero_iff hφ).mp hzero
  have hnot : ∀ᵐ z : ((Fin 2 → ℝ) × ℝ) × ℝ, arr z ∉ N := by
    filter_upwards [hae, ae_fst_fst_ne_zero] with z hz hz0 hmem
    have hρ := rad_pos_of_ne_zero hz0
    simp only [Pi.zero_apply, Set.indicator_of_mem hmem, Pi.one_apply, one_mul] at hz
    exact (ENNReal.ofReal_pos.mpr hρ).ne' hz
  have := ae_iff.mp hnot
  simpa [Set.preimage] using this

private theorem integrable_rad_mul_comp_arr (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (hF : Integrable F) :
    Integrable fun z : ((Fin 2 → ℝ) × ℝ) × ℝ => (rad z.1.1 : ℂ) * F (arr z) := by
  obtain ⟨F', hF'm, hFF'⟩ := hF.aestronglyMeasurable
  have hcomp : (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ => F (arr z)) =ᵐ[volume] fun z => F' (arr z) :=
    quasiMeasurePreserving_arr.ae_eq_comp hFF'
  have hradm : AEStronglyMeasurable (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ => (rad z.1.1 : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (continuous_rad.comp continuous_fst.fst)).aestronglyMeasurable
  refine ⟨hradm.mul (hF.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_arr), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hF'e : Measurable fun e => ‖F' e‖ₑ := hF'm.measurable.enorm
  calc ∫⁻ z, ‖(rad z.1.1 : ℂ) * F (arr z)‖ₑ
      = ∫⁻ z : ((Fin 2 → ℝ) × ℝ) × ℝ, ‖F' (arr z)‖ₑ * ENNReal.ofReal (rad z.1.1) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hcomp] with z hz
        rw [enorm_mul, hz, mul_comm, ← ofReal_norm ((rad z.1.1 : ℝ) : ℂ), Complex.norm_of_nonneg (rad_nonneg _)]
    _ = ∫⁻ c₀ : Fin 2 → ℝ, ∫⁻ d : ℝ, ∫⁻ ξ : ℝ,
          ‖F' (fun i j => (transv c₀ d * shear ξ) i j)‖ₑ * ENNReal.ofReal (rad c₀) :=
        lintegral_triple _ ((hF'e.comp measurable_arr).mul
          (ENNReal.measurable_ofReal.comp (continuous_rad.measurable.comp measurable_fst.fst)))
    _ = ∫⁻ e, ‖F' e‖ₑ := (lintegral_eq_lintegral_transv_mul_shear _ hF'e).symm
    _ = ∫⁻ e, ‖F e‖ₑ := lintegral_congr_ae (hFF'.symm.fun_comp _)
    _ < ∞ := hF.hasFiniteIntegral

private theorem integral_eq_integral_transv_mul_shear (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (hF : Integrable F) :
    ∫ e : Fin 2 → Fin 2 → ℝ, F e =
      ∫ c₀ : Fin 2 → ℝ, ∫ d : ℝ, (rad c₀ : ℂ) * ∫ ξ : ℝ, F (fun i j => (transv c₀ d * shear ξ) i j) := by
  have hFs : Integrable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => F (colSplit.symm p) :=
    ((colSplit_measurePreserving.symm _).integrable_comp_emb colSplit.symm.measurableEmbedding).mpr hF
  rw [← MeasurePreserving.integral_comp' (colSplit_measurePreserving.symm _) F, Measure.volume_eq_prod,
    integral_prod _ (by rwa [← Measure.volume_eq_prod])]
  refine integral_congr_ae ?_
  have hslice := hFs.prod_right_ae
  filter_upwards [ae_ne_zero_col, hslice] with c₀ hc hint
  rw [integral_colMap hc _ hint.aestronglyMeasurable, integral_finTwo _ (integrable_comp_colMap hc hint)]
  refine Eq.trans ?_
    (integral_const_mul (rad c₀ : ℂ) fun d : ℝ => ∫ ξ : ℝ, F (fun i j => (transv c₀ d * shear ξ) i j)).symm
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show F (colSplit.symm (c₀, colMap c₀ ![d, ξ])) = F (fun i j => (transv c₀ d * shear ξ) i j)
  exact congrArg F (by rw [colSplit_symm_colMap]; rfl)

private theorem integrable_transv_slices (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (hF : Integrable F) :
    (∀ᵐ q : (Fin 2 → ℝ) × ℝ, Integrable fun ξ : ℝ => F (fun i j => (transv q.1 q.2 * shear ξ) i j)) ∧
      Integrable (fun q : (Fin 2 → ℝ) × ℝ =>
        (rad q.1 : ℂ) * ∫ ξ : ℝ, F (fun i j => (transv q.1 q.2 * shear ξ) i j)) := by
  have hK := integrable_rad_mul_comp_arr F hF
  rw [Measure.volume_eq_prod] at hK
  have hq0 : ∀ᵐ q : (Fin 2 → ℝ) × ℝ, q.1 ≠ 0 := by
    rw [ae_iff]
    have : {q : (Fin 2 → ℝ) × ℝ | ¬ q.1 ≠ 0} = ({0} : Set (Fin 2 → ℝ)) ×ˢ (univ : Set ℝ) := by ext q; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  refine ⟨?_, ?_⟩
  · filter_upwards [hK.prod_right_ae, hq0] with q hq hq0
    have hρ : (rad q.1 : ℂ) ≠ 0 := by exact_mod_cast (rad_pos_of_ne_zero hq0).ne'
    have := hq.const_mul (rad q.1 : ℂ)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    show (rad q.1 : ℂ)⁻¹ * ((rad q.1 : ℂ) * F (arr (q, ξ))) = F (arr (q, ξ))
    rw [← mul_assoc, inv_mul_cancel₀ hρ, one_mul]
  · refine hK.integral_prod_left.congr (Filter.Eventually.of_forall fun q => ?_)
    show ∫ y : ℝ, (rad q.1 : ℂ) * F (arr (q, y)) = (rad q.1 : ℂ) * ∫ ξ : ℝ, F (arr (q, ξ))
    exact integral_const_mul _ _

private def bracket (a α x ρ δ : ℝ) : ℝ :=
  1 + |a| * Real.sqrt (1 + x ^ 2) / ρ + |a| * |α| / (δ * Real.sqrt (1 + x ^ 2)) + ρ

private def majorant (a p u g q₁ q₂ : ℝ) (N : ℕ) (z : (ℝ × ℝ) × ((Fin 2 → ℝ) × ℝ)) : ℝ :=
  let α := z.1.1
  let x := z.1.2
  let ρ := rad z.2.1
  let δ := |z.2.2|
  |α| ^ (p - 1) * ρ * (ρ ^ 2 * δ * Real.sqrt (1 + x ^ 2))⁻¹ * bracket a α x ρ δ ^ (-(N : ℝ)) *
    (ρ * δ) ^ u * δ ^ (-(g + 1)) * min ((|a| * δ / ρ) ^ (-q₁)) ((|a| * δ / ρ) ^ (-q₂))

private theorem integrableOn_rpow_mul_bracket {p : ℝ} (hp : 0 < p) {N : ℕ} (hpN : p < N) :
    IntegrableOn (fun u : ℝ => u ^ (p - 1) * (1 + u) ^ (-(N : ℝ))) (Ioi 0) := by
  have hcont : ContinuousOn (fun u : ℝ => u ^ (p - 1) * (1 + u) ^ (-(N : ℝ))) (Ioi 0) := by
    refine ContinuousOn.mul ?_ ?_
    · exact fun u hu => (Real.continuousAt_rpow_const u (p - 1) (Or.inl (mem_Ioi.1 hu).ne')).continuousWithinAt
    · refine fun u hu => ContinuousAt.continuousWithinAt ?_
      have h1 : (1 + u) ≠ 0 := by have := (mem_Ioi.1 hu); positivity
      exact (continuous_const.add continuous_id).continuousAt.rpow_const (Or.inl h1)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext u; simp only [mem_Ioi, mem_union, mem_Ioc]; constructor
    · intro h; by_cases h1 : u ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact lt_trans zero_lt_one h
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    have hint : IntegrableOn (fun u : ℝ => u ^ (p - 1)) (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine hint.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    obtain ⟨hu0, -⟩ := hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have hb : (1 + u) ^ (-(N : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)
    calc u ^ (p - 1) * (1 + u) ^ (-(N : ℝ)) ≤ u ^ (p - 1) * 1 := by gcongr
      _ = u ^ (p - 1) := mul_one _
  ·
    have hint : IntegrableOn (fun u : ℝ => u ^ (p - 1 - N)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hint.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have hb : (1 + u) ^ (-(N : ℝ)) ≤ u ^ (-(N : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by simp)
    calc u ^ (p - 1) * (1 + u) ^ (-(N : ℝ)) ≤ u ^ (p - 1) * u ^ (-(N : ℝ)) := by
          gcongr
      _ = u ^ (p - 1 - N) := by rw [← Real.rpow_add hu0]; ring_nf

private theorem integral_rpow_mul_bracket_scale (p : ℝ) (N : ℕ) {l : ℝ} (hl : 0 < l) :
    ∫ u in Ioi (0 : ℝ), u ^ (p - 1) * (1 + l * u) ^ (-(N : ℝ)) =
      l ^ (-p) * ∫ u in Ioi (0 : ℝ), u ^ (p - 1) * (1 + u) ^ (-(N : ℝ)) := by
  have hcomp := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ (p - 1) * (1 + u) ^ (-(N : ℝ))) (0 : ℝ) hl
  rw [mul_zero] at hcomp

  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      u ^ (p - 1) * (1 + l * u) ^ (-(N : ℝ)) =
        l ^ (-(p - 1)) * ((l * u) ^ (p - 1) * (1 + l * u) ^ (-(N : ℝ))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.mul_rpow hl.le hu0.le, Real.rpow_neg hl.le]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hcomp, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one l, ← Real.rpow_add hl]
  ring_nf

private theorem bracket_rpow_neg_le (a α x ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (N' η M : ℕ) :
    bracket a α x ρ δ ^ (-((N' + η + M : ℕ) : ℝ)) ≤
      (1 + |a| * |α| / (δ * Real.sqrt (1 + x ^ 2))) ^ (-(N' : ℝ)) *
        (1 + |a| * Real.sqrt (1 + x ^ 2) / ρ) ^ (-(η : ℝ)) * (1 + ρ) ^ (-(M : ℝ)) := by
  set X : ℝ := Real.sqrt (1 + x ^ 2) with hX
  have hX0 : 0 < X := Real.sqrt_pos.2 (by positivity)
  set A : ℝ := |a| * X / ρ with hA
  set B : ℝ := |a| * |α| / (δ * X) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hbr : bracket a α x ρ δ = 1 + A + B + ρ := by simp only [bracket, hA, hB, hX]
  have hrpow : ∀ (y : ℝ) (n : ℕ), 0 ≤ y → y ^ (-(n : ℝ)) = (y ^ n)⁻¹ := fun y n hy => by
    rw [Real.rpow_neg hy, Real.rpow_natCast]
  rw [hbr, hrpow _ _ (by positivity), hrpow _ _ (by positivity), hrpow _ _ (by positivity),
    hrpow _ _ (by positivity), ← mul_inv, ← mul_inv]
  apply inv_anti₀ (by positivity)
  rw [pow_add, pow_add]
  have h1 : (1 + B) ^ N' ≤ (1 + A + B + ρ) ^ N' := pow_le_pow_left₀ (by positivity) (by linarith) N'
  have h2 : (1 + A) ^ η ≤ (1 + A + B + ρ) ^ η := pow_le_pow_left₀ (by positivity) (by linarith) η
  have h3 : (1 + ρ) ^ M ≤ (1 + A + B + ρ) ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
  calc (1 + B) ^ N' * (1 + A) ^ η * (1 + ρ) ^ M
      ≤ (1 + A + B + ρ) ^ N' * (1 + A + B + ρ) ^ η * (1 + A + B + ρ) ^ M := by gcongr

private theorem exists_integral_sqrt_rpow_mul_bracket_le (p : ℝ) (η : ℕ) (hpη : p < η) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ l : ℝ, 0 < l →
      Integrable (fun x : ℝ => Real.sqrt (1 + x ^ 2) ^ (p - 1) * (1 + l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ))) ∧
        ∫ x : ℝ, Real.sqrt (1 + x ^ 2) ^ (p - 1) * (1 + l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ)) ≤
          J * l ^ (-(η : ℝ)) := by

  set r : ℝ := η - p + 1 with hr
  have hr1 : (1 : ℝ) < r := by rw [hr]; linarith
  have hint : Integrable fun x : ℝ => (1 + ‖x‖) ^ (-r) :=
    integrable_one_add_norm (E := ℝ) (by simpa using hr1)
  set J : ℝ := Real.sqrt 2 ^ r * ∫ x : ℝ, (1 + ‖x‖) ^ (-r) with hJ
  have hsqrt : ∀ x : ℝ, (1 + |x|) / Real.sqrt 2 ≤ Real.sqrt (1 + x ^ 2) := by
    intro x
    rw [div_le_iff₀ (by positivity)]
    rw [← Real.sqrt_mul (by positivity), Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]

  have hpt : ∀ x : ℝ, Real.sqrt (1 + x ^ 2) ^ (p - 1 - η) ≤ Real.sqrt 2 ^ r * (1 + ‖x‖) ^ (-r) := by
    intro x
    have hXpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hexp : p - 1 - η = -r := by rw [hr]; ring
    rw [hexp, Real.norm_eq_abs]
    calc Real.sqrt (1 + x ^ 2) ^ (-r) ≤ ((1 + |x|) / Real.sqrt 2) ^ (-r) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (hsqrt x) (by linarith)
      _ = Real.sqrt 2 ^ r * (1 + |x|) ^ (-r) := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.sqrt 2),
            div_inv_eq_mul, mul_comm]
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    exact mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)
  refine ⟨J, hJ0, fun l hl => ?_⟩

  set f : ℝ → ℝ := fun x => Real.sqrt (1 + x ^ 2) ^ (p - 1) * (1 + l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ)) with hf
  have hdom : ∀ x : ℝ, f x ≤ l ^ (-(η : ℝ)) * (Real.sqrt 2 ^ r * (1 + ‖x‖) ^ (-r)) := by
    intro x
    have hXpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
    have h1 : (1 + l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ)) ≤ (l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
    calc f x ≤ Real.sqrt (1 + x ^ 2) ^ (p - 1) * (l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ)) := by
          simp only [hf]
          gcongr
      _ = l ^ (-(η : ℝ)) * Real.sqrt (1 + x ^ 2) ^ (p - 1 - η) := by
          rw [Real.mul_rpow hl.le hXpos.le, sub_eq_add_neg (p - 1) (η : ℝ), Real.rpow_add hXpos]
          ring
      _ ≤ l ^ (-(η : ℝ)) * (Real.sqrt 2 ^ r * (1 + ‖x‖) ^ (-r)) := by
          gcongr
          exact hpt x
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  have hfc : Continuous f := by
    simp only [hf]
    have hX : Continuous fun x : ℝ => Real.sqrt (1 + x ^ 2) := by fun_prop
    have hY : Continuous fun x : ℝ => (1 : ℝ) + l * Real.sqrt (1 + x ^ 2) := by fun_prop
    have hY0 : ∀ x : ℝ, (1 : ℝ) + l * Real.sqrt (1 + x ^ 2) ≠ 0 := fun x =>
      (add_pos_of_pos_of_nonneg one_pos (mul_nonneg hl.le (Real.sqrt_nonneg _))).ne'
    exact (hX.rpow_const fun x => Or.inl (Real.sqrt_pos.2 (by positivity)).ne').mul
      (hY.rpow_const fun x => Or.inl (hY0 x))
  have hg : Integrable fun x : ℝ => l ^ (-(η : ℝ)) * (Real.sqrt 2 ^ r * (1 + ‖x‖) ^ (-r)) :=
    (hint.const_mul _).const_mul _
  have hfi : Integrable f :=
    hg.mono' hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hf0 x)]; exact hdom x)
  refine ⟨hfi, ?_⟩
  calc ∫ x : ℝ, f x ≤ ∫ x : ℝ, l ^ (-(η : ℝ)) * (Real.sqrt 2 ^ r * (1 + ‖x‖) ^ (-r)) :=
        integral_mono hfi hg hdom
    _ = J * l ^ (-(η : ℝ)) := by
        rw [integral_const_mul, integral_const_mul, hJ]
        ring

private theorem integrableOn_rpow_mul_min_rpow (e q₁ q₂ : ℝ) (h₁ : -1 < e - q₁) (h₂ : e - q₂ < -1) :
    IntegrableOn (fun δ : ℝ => δ ^ e * min (δ ^ (-q₁)) (δ ^ (-q₂))) (Ioi 0) := by
  set f : ℝ → ℝ := fun δ => δ ^ e * min (δ ^ (-q₁)) (δ ^ (-q₂)) with hf
  have hfm : Measurable f := by
    simp only [hf]
    exact (measurable_id.pow_const e).mul ((measurable_id.pow_const (-q₁)).min (measurable_id.pow_const (-q₂)))
  have hf0 : ∀ δ : ℝ, 0 < δ → 0 ≤ f δ := fun δ hδ => by
    simp only [hf]
    exact mul_nonneg (Real.rpow_nonneg hδ.le _) (le_min (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hδ.le _))
  have hle₁ : ∀ δ : ℝ, 0 < δ → f δ ≤ δ ^ (e - q₁) := fun δ hδ => by
    simp only [hf]
    rw [sub_eq_add_neg, Real.rpow_add hδ]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg hδ.le _)
  have hle₂ : ∀ δ : ℝ, 0 < δ → f δ ≤ δ ^ (e - q₂) := fun δ hδ => by
    simp only [hf]
    rw [sub_eq_add_neg, Real.rpow_add hδ]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hδ.le _)

  have h₁ : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    have hg : IntegrableOn (fun δ : ℝ => δ ^ (e - q₁)) (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 (intervalIntegral.intervalIntegrable_rpow' h₁)
    refine hg.mono' hfm.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with δ hδ
    rw [Real.norm_of_nonneg (hf0 δ hδ.1)]
    exact hle₁ δ hδ.1

  have h₂ : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hg : IntegrableOn (fun δ : ℝ => δ ^ (e - q₂)) (Ioi (1 : ℝ)) := integrableOn_Ioi_rpow_of_lt h₂ one_pos
    refine hg.mono' hfm.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with δ hδ
    have hδ0 : (0 : ℝ) < δ := lt_trans one_pos hδ
    rw [Real.norm_of_nonneg (hf0 δ hδ0)]
    exact hle₂ δ hδ0
  have := h₁.union h₂
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

private theorem integrable_comp_abs_of_integrableOn_Ioi {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable fun t : ℝ => f |t| := by
  have h1 : Integrable fun t : ℝ => (Ioi (0 : ℝ)).indicator f t := hf.integrable_indicator measurableSet_Ioi
  have h2 : Integrable fun t : ℝ => (Ioi (0 : ℝ)).indicator f (-t) := h1.comp_neg
  refine (h1.add h2).congr ?_
  have h0 : (volume : Measure ℝ) {(0 : ℝ)} = 0 := measure_singleton 0
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun t ht => ?_) h0
  simp only [mem_setOf_eq] at ht
  by_contra hne
  apply ht
  simp only [Pi.add_apply]
  rcases lt_or_gt_of_ne hne with h | h
  · have hn : t ∉ Ioi (0 : ℝ) := fun h' => (not_lt.2 h.le) (mem_Ioi.1 h')
    have hm : -t ∈ Ioi (0 : ℝ) := mem_Ioi.2 (neg_pos.2 h)
    rw [abs_of_neg h, indicator_of_notMem hn f, indicator_of_mem hm f, zero_add]
  · have hm : t ∈ Ioi (0 : ℝ) := mem_Ioi.2 h
    have hn : -t ∉ Ioi (0 : ℝ) := fun h' => (not_lt.2 (neg_nonpos.2 h.le)) (mem_Ioi.1 h')
    rw [abs_of_pos h, indicator_of_mem hm f, indicator_of_notMem hn f, add_zero]

private theorem integrable_abs_rpow_mul_min (e q₁ q₂ : ℝ) (h₁ : -1 < e - q₁) (h₂ : e - q₂ < -1) :
    Integrable fun d : ℝ => |d| ^ e * min (|d| ^ (-q₁)) (|d| ^ (-q₂)) :=
  integrable_comp_abs_of_integrableOn_Ioi (integrableOn_rpow_mul_min_rpow e q₁ q₂ h₁ h₂)

private theorem integrable_rad_rpow_mul_one_add_rpow (s : ℝ) (M : ℕ) (hs : 0 ≤ s) (hsM : s + 2 < M) :
    Integrable fun c₀ : Fin 2 → ℝ => rad c₀ ^ s * (1 + rad c₀) ^ (-(M : ℝ)) := by
  have hr : (2 : ℝ) < M - s := by linarith
  have hint : Integrable fun c₀ : Fin 2 → ℝ => (1 + ‖c₀‖) ^ (-(M - s)) :=
    integrable_one_add_norm (E := Fin 2 → ℝ) (by simpa using hr)
  have hmeas : Measurable fun c₀ : Fin 2 → ℝ => rad c₀ ^ s * (1 + rad c₀) ^ (-(M : ℝ)) :=
    (continuous_rad.measurable.pow_const s).mul ((continuous_const.add continuous_rad).measurable.pow_const _)
  refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun c₀ => ?_)
  have hρ0 := rad_nonneg c₀
  have hnorm : ‖c₀‖ ≤ rad c₀ := by
    rw [pi_norm_le_iff_of_nonneg hρ0]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (c₀ 0), sq_nonneg (c₀ 1)]
  rw [Real.norm_of_nonneg (by positivity)]
  calc rad c₀ ^ s * (1 + rad c₀) ^ (-(M : ℝ)) ≤ (1 + rad c₀) ^ s * (1 + rad c₀) ^ (-(M : ℝ)) := by
        gcongr
        linarith
    _ = (1 + rad c₀) ^ (-(M - s)) := by
        rw [← Real.rpow_add (by positivity)]
        ring_nf
    _ ≤ (1 + ‖c₀‖) ^ (-(M - s)) := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

private theorem inner_integrable_and_le (a p : ℝ) (ha : a ≠ 0) (hp : 0 < p) (N' η : ℕ) (hpN' : p < N')
    (J : ℝ) (hJ : ∀ l : ℝ, 0 < l →
      Integrable (fun x : ℝ => Real.sqrt (1 + x ^ 2) ^ (p - 1) * (1 + l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ))) ∧
        ∫ x : ℝ, Real.sqrt (1 + x ^ 2) ^ (p - 1) * (1 + l * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ)) ≤
          J * l ^ (-(η : ℝ)))
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) :
    Integrable (fun w : ℝ × ℝ => |w.1| ^ (p - 1) * (Real.sqrt (1 + w.2 ^ 2))⁻¹ *
        (1 + |a| * |w.1| / (δ * Real.sqrt (1 + w.2 ^ 2))) ^ (-(N' : ℝ)) *
        (1 + |a| * Real.sqrt (1 + w.2 ^ 2) / ρ) ^ (-(η : ℝ))) ∧
      ∫ w : ℝ × ℝ, |w.1| ^ (p - 1) * (Real.sqrt (1 + w.2 ^ 2))⁻¹ *
          (1 + |a| * |w.1| / (δ * Real.sqrt (1 + w.2 ^ 2))) ^ (-(N' : ℝ)) *
          (1 + |a| * Real.sqrt (1 + w.2 ^ 2) / ρ) ^ (-(η : ℝ)) ≤
        2 * (∫ t in Ioi (0 : ℝ), t ^ (p - 1) * (1 + t) ^ (-(N' : ℝ))) * |a| ^ (-p) * δ ^ p * J *
          (|a| / ρ) ^ (-(η : ℝ)) := by
  have ha0 : 0 < |a| := abs_pos.2 ha
  set I₀ : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * (1 + t) ^ (-(N' : ℝ)) with hI₀
  set F : ℝ × ℝ → ℝ := fun w => |w.1| ^ (p - 1) * (Real.sqrt (1 + w.2 ^ 2))⁻¹ *
    (1 + |a| * |w.1| / (δ * Real.sqrt (1 + w.2 ^ 2))) ^ (-(N' : ℝ)) *
    (1 + |a| * Real.sqrt (1 + w.2 ^ 2) / ρ) ^ (-(η : ℝ)) with hF
  have hF0 : ∀ w, 0 ≤ F w := fun w => by
    simp only [hF]
    positivity
  have hFm : Measurable F := by
    simp only [hF]
    fun_prop
  have hX : ∀ x : ℝ, 0 < Real.sqrt (1 + x ^ 2) := fun x => Real.sqrt_pos.2 (by positivity)

  set lam : ℝ → ℝ := fun x => |a| / (δ * Real.sqrt (1 + x ^ 2)) with hlam
  have hlam0 : ∀ x, 0 < lam x := fun x => by
    simp only [hlam]
    have := hX x
    positivity
  set cx : ℝ → ℝ := fun x =>
    (Real.sqrt (1 + x ^ 2))⁻¹ * (1 + |a| * Real.sqrt (1 + x ^ 2) / ρ) ^ (-(η : ℝ)) with hcx
  have hslice : ∀ x : ℝ, (fun α : ℝ => F (α, x)) =
      fun α => cx x * ((fun t : ℝ => t ^ (p - 1) * (1 + lam x * t) ^ (-(N' : ℝ))) |α|) := by
    intro x
    funext α
    simp only [hF, hcx, hlam]
    ring_nf
  have hB3b_int : ∀ x : ℝ,
      IntegrableOn (fun t : ℝ => t ^ (p - 1) * (1 + lam x * t) ^ (-(N' : ℝ))) (Ioi 0) := by
    intro x
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => t ^ (p - 1) * (1 + t) ^ (-(N' : ℝ))) (0 : ℝ)
      (hlam0 x)).2 (by rw [mul_zero]; exact integrableOn_rpow_mul_bracket hp hpN')
    refine IntegrableOn.congr_fun (Integrable.const_mul h ((lam x) ^ (-(p - 1)))) (fun t ht => ?_) measurableSet_Ioi
    have ht : (0 : ℝ) < t := ht
    rw [Real.mul_rpow (hlam0 x).le ht.le, Real.rpow_neg (hlam0 x).le]
    have hl0 : lam x ^ (p - 1) ≠ 0 := (Real.rpow_pos_of_pos (hlam0 x) _).ne'
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
  have hB3b_val : ∀ x : ℝ,
      ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * (1 + lam x * t) ^ (-(N' : ℝ)) = (lam x) ^ (-p) * I₀ :=
    fun x => integral_rpow_mul_bracket_scale p N' (hlam0 x)
  have hslice_int : ∀ x : ℝ, Integrable fun α : ℝ => F (α, x) := fun x => by
    rw [hslice x]
    exact (integrable_comp_abs_of_integrableOn_Ioi (hB3b_int x)).const_mul _
  have hslice_val : ∀ x : ℝ, ∫ α : ℝ, F (α, x) = cx x * (2 * ((lam x) ^ (-p) * I₀)) := fun x => by
    rw [hslice x, integral_const_mul,
      integral_comp_abs (f := fun t : ℝ => t ^ (p - 1) * (1 + lam x * t) ^ (-(N' : ℝ))), hB3b_val x]

  have hl : 0 < |a| / ρ := by positivity
  obtain ⟨hJint, hJle⟩ := hJ (|a| / ρ) hl
  have houter : ∀ x : ℝ, cx x * (2 * ((lam x) ^ (-p) * I₀)) = 2 * I₀ * |a| ^ (-p) * δ ^ p *
      (Real.sqrt (1 + x ^ 2) ^ (p - 1) * (1 + |a| / ρ * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ))) := by
    intro x
    have hXx := hX x
    have h1 : (lam x) ^ (-p) = |a| ^ (-p) * (δ ^ p * Real.sqrt (1 + x ^ 2) ^ p) := by
      simp only [hlam]
      rw [Real.div_rpow ha0.le (by positivity), Real.rpow_neg ha0.le, Real.rpow_neg (by positivity),
        Real.mul_rpow hδ.le hXx.le, div_inv_eq_mul]
    have h2 : (Real.sqrt (1 + x ^ 2))⁻¹ * Real.sqrt (1 + x ^ 2) ^ p = Real.sqrt (1 + x ^ 2) ^ (p - 1) := by
      rw [sub_eq_add_neg, Real.rpow_add hXx, Real.rpow_neg_one]
      ring
    have h3 : |a| * Real.sqrt (1 + x ^ 2) / ρ = |a| / ρ * Real.sqrt (1 + x ^ 2) := by ring
    simp only [hcx]
    rw [h1, h3]
    calc (Real.sqrt (1 + x ^ 2))⁻¹ * (1 + |a| / ρ * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ)) *
          (2 * (|a| ^ (-p) * (δ ^ p * Real.sqrt (1 + x ^ 2) ^ p) * I₀))
        = 2 * I₀ * |a| ^ (-p) * δ ^ p * (((Real.sqrt (1 + x ^ 2))⁻¹ * Real.sqrt (1 + x ^ 2) ^ p) *
            (1 + |a| / ρ * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ))) := by ring
      _ = _ := by rw [h2]
  have houter_int : Integrable fun x : ℝ => ∫ α : ℝ, F (α, x) := by
    simp_rw [hslice_val, houter]
    exact hJint.const_mul _

  have hFint : Integrable F := by
    rw [Measure.volume_eq_prod]
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hslice_int, ?_⟩
    refine houter_int.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    congr 1
    funext α
    rw [Real.norm_of_nonneg (hF0 _)]
  refine ⟨hFint, ?_⟩
  have hswap : ∫ w : ℝ × ℝ, F w = ∫ x : ℝ, ∫ α : ℝ, F (α, x) := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_symm F (by rwa [← Measure.volume_eq_prod])
  rw [hswap]
  simp_rw [hslice_val, houter]
  rw [integral_const_mul]
  have hI₀0 : 0 ≤ I₀ := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : (0 : ℝ) < t := ht
    positivity
  calc 2 * I₀ * |a| ^ (-p) * δ ^ p *
        ∫ x : ℝ, Real.sqrt (1 + x ^ 2) ^ (p - 1) * (1 + |a| / ρ * Real.sqrt (1 + x ^ 2)) ^ (-(η : ℝ))
      ≤ 2 * I₀ * |a| ^ (-p) * δ ^ p * (J * (|a| / ρ) ^ (-(η : ℝ))) := by gcongr
    _ = 2 * I₀ * |a| ^ (-p) * δ ^ p * J * (|a| / ρ) ^ (-(η : ℝ)) := by ring

private theorem majorant_eq (a p u g q₁ q₂ : ℝ) (N : ℕ) (z : (ℝ × ℝ) × ((Fin 2 → ℝ) × ℝ)) :
    majorant a p u g q₁ q₂ N z =
      |z.1.1| ^ (p - 1) * rad z.2.1 * (rad z.2.1 ^ 2 * |z.2.2| * Real.sqrt (1 + z.1.2 ^ 2))⁻¹ *
        bracket a z.1.1 z.1.2 (rad z.2.1) |z.2.2| ^ (-(N : ℝ)) * (rad z.2.1 * |z.2.2|) ^ u *
        |z.2.2| ^ (-(g + 1)) *
        min ((|a| * |z.2.2| / rad z.2.1) ^ (-q₁)) ((|a| * |z.2.2| / rad z.2.1) ^ (-q₂)) := rfl

private theorem min_coupled_le (K₁ K₂ X₁ X₂ Y₁ Y₂ : ℝ) (hK₁ : 0 ≤ K₁) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) :
    min (K₁ * Y₁ * X₁) (K₂ * Y₂ * X₂) ≤ max K₁ K₂ * (X₁ + X₂) * min Y₁ Y₂ := by
  rcases le_total Y₁ Y₂ with h | h
  · rw [min_eq_left h]
    calc min (K₁ * Y₁ * X₁) (K₂ * Y₂ * X₂) ≤ K₁ * Y₁ * X₁ := min_le_left _ _
      _ ≤ max K₁ K₂ * Y₁ * (X₁ + X₂) := by gcongr <;> first | exact le_max_left _ _ | linarith
      _ = max K₁ K₂ * (X₁ + X₂) * Y₁ := by ring
  · rw [min_eq_right h]
    calc min (K₁ * Y₁ * X₁) (K₂ * Y₂ * X₂) ≤ K₂ * Y₂ * X₂ := min_le_right _ _
      _ ≤ max K₁ K₂ * Y₂ * (X₁ + X₂) := by gcongr <;> first | exact le_max_right _ _ | linarith
      _ = max K₁ K₂ * (X₁ + X₂) * Y₂ := by ring

private theorem gauge_term_eq (a ρ δ q : ℝ) (ha : 0 < |a|) (hρ : 0 < ρ) (hδ : 0 < δ) :
    (|a| * δ / ρ) ^ (-q) = |a| ^ (-q) * δ ^ (-q) * ρ ^ q := by
  rw [Real.div_rpow (by positivity) hρ.le, Real.mul_rpow ha.le hδ.le, Real.rpow_neg hρ.le, div_eq_mul_inv, inv_inv]

private theorem majorant_nonneg (a p u g q₁ q₂ : ℝ) (N : ℕ) (z : (ℝ × ℝ) × ((Fin 2 → ℝ) × ℝ)) :
    0 ≤ majorant a p u g q₁ q₂ N z := by
  rw [majorant_eq]
  have h1 := rad_nonneg z.2.1
  have hbr : 0 ≤ bracket a z.1.1 z.1.2 (rad z.2.1) |z.2.2| := by
    unfold bracket
    positivity
  positivity

private theorem measurable_majorant (a p u g q₁ q₂ : ℝ) (N : ℕ) : Measurable (majorant a p u g q₁ q₂ N) := by
  have hb : Measurable fun z : (ℝ × ℝ) × ((Fin 2 → ℝ) × ℝ) => bracket a z.1.1 z.1.2 (rad z.2.1) |z.2.2| := by
    unfold bracket
    have := continuous_rad
    fun_prop
  have hr := continuous_rad
  have h : Measurable fun z : (ℝ × ℝ) × ((Fin 2 → ℝ) × ℝ) =>
      |z.1.1| ^ (p - 1) * rad z.2.1 * (rad z.2.1 ^ 2 * |z.2.2| * Real.sqrt (1 + z.1.2 ^ 2))⁻¹ *
        bracket a z.1.1 z.1.2 (rad z.2.1) |z.2.2| ^ (-(N : ℝ)) * (rad z.2.1 * |z.2.2|) ^ u *
        |z.2.2| ^ (-(g + 1)) *
        min ((|a| * |z.2.2| / rad z.2.1) ^ (-q₁)) ((|a| * |z.2.2| / rad z.2.1) ^ (-q₂)) := by
    fun_prop
  exact h

private theorem exists_integrable_majorant (a p u g q₁ q₂ : ℝ) (ha : a ≠ 0) (hp : 0 < p)
    (hq₁ : -1 < p + u - g - q₁ - 2) (hq₂ : p + u - g - q₂ - 2 < -1) :
    ∃ N : ℕ, Integrable (majorant a p u g q₁ q₂ N) := by
  have ha0 : 0 < |a| := abs_pos.2 ha

  set N' : ℕ := ⌈p⌉₊ + 1 with hN'
  have hpN' : p < N' := by
    rw [hN']
    push_cast
    linarith [Nat.le_ceil p]
  set η : ℕ := ⌈p⌉₊ + ⌈|u| + |q₁| + |q₂|⌉₊ + 2 with hη
  have hceil : |u| + |q₁| + |q₂| ≤ (⌈|u| + |q₁| + |q₂|⌉₊ : ℝ) := Nat.le_ceil _
  have hceilp : (0 : ℝ) ≤ (⌈p⌉₊ : ℝ) := Nat.cast_nonneg _
  have hpη : p < η := by
    rw [hη]
    push_cast
    linarith [Nat.le_ceil p, abs_nonneg u, abs_nonneg q₁, abs_nonneg q₂]
  set s₁ : ℝ := -1 + u + q₁ + η with hs₁def
  set s₂ : ℝ := -1 + u + q₂ + η with hs₂def
  have hs₁ : 0 ≤ s₁ := by
    rw [hs₁def, hη]
    push_cast
    linarith [neg_abs_le u, neg_abs_le q₁, abs_nonneg q₂]
  have hs₂ : 0 ≤ s₂ := by
    rw [hs₂def, hη]
    push_cast
    linarith [neg_abs_le u, neg_abs_le q₂, abs_nonneg q₁]
  obtain ⟨J, hJ0, hJ⟩ := exists_integral_sqrt_rpow_mul_bracket_le p η hpη
  set M : ℕ := ⌈s₁⌉₊ + ⌈s₂⌉₊ + 3 with hM
  have hM₁ : s₁ + 2 < M := by
    rw [hM]
    push_cast
    linarith [Nat.le_ceil s₁, (Nat.cast_nonneg ⌈s₂⌉₊ : (0 : ℝ) ≤ ⌈s₂⌉₊)]
  have hM₂ : s₂ + 2 < M := by
    rw [hM]
    push_cast
    linarith [Nat.le_ceil s₂, (Nat.cast_nonneg ⌈s₁⌉₊ : (0 : ℝ) ≤ ⌈s₁⌉₊)]
  refine ⟨N' + η + M, ?_⟩
  set I₀ : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * (1 + t) ^ (-(N' : ℝ)) with hI₀
  have hI₀0 : 0 ≤ I₀ := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : (0 : ℝ) < t := ht
    positivity
  set e : ℝ := p + u - g - 2 with he
  have he₁ : -1 < e - q₁ := by rw [he]; linarith
  have he₂ : e - q₂ < -1 := by rw [he]; linarith

  set K : ℝ := 2 * I₀ * |a| ^ (-p) * J * |a| ^ (-(η : ℝ)) * max (|a| ^ (-q₁)) (|a| ^ (-q₂)) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := le_max_left (|a| ^ (-q₁)) (|a| ^ (-q₂))
    have h0 : 0 ≤ |a| ^ (-q₁) := by positivity
    positivity
  set R : (Fin 2 → ℝ) → ℝ := fun c₀ =>
    rad c₀ ^ s₁ * (1 + rad c₀) ^ (-(M : ℝ)) + rad c₀ ^ s₂ * (1 + rad c₀) ^ (-(M : ℝ)) with hR
  set Dg : ℝ → ℝ := fun d => |d| ^ e * min (|d| ^ (-q₁)) (|d| ^ (-q₂)) with hDg
  have hRint : Integrable R :=
    (integrable_rad_rpow_mul_one_add_rpow s₁ M hs₁ hM₁).add (integrable_rad_rpow_mul_one_add_rpow s₂ M hs₂ hM₂)
  have hDint : Integrable Dg := integrable_abs_rpow_mul_min e q₁ q₂ he₁ he₂
  have hHint : Integrable fun v : (Fin 2 → ℝ) × ℝ => K * (R v.1 * Dg v.2) := by
    have := hRint.mul_prod hDint
    rw [← Measure.volume_eq_prod] at this
    exact this.const_mul K

  have hmeas := measurable_majorant a p u g q₁ q₂ (N' + η + M)
  rw [Measure.volume_eq_prod]
  have hmeas' : AEStronglyMeasurable (majorant a p u g q₁ q₂ (N' + η + M))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ((Fin 2 → ℝ) × ℝ))) := by
    rw [← Measure.volume_eq_prod]
    exact hmeas.aestronglyMeasurable

  have hslice : ∀ v : (Fin 2 → ℝ) × ℝ,
      Integrable (fun w : ℝ × ℝ => majorant a p u g q₁ q₂ (N' + η + M) (w, v)) ∧
        ∫ w : ℝ × ℝ, majorant a p u g q₁ q₂ (N' + η + M) (w, v) ≤ K * (R v.1 * Dg v.2) := by
    intro v
    obtain ⟨c₀, d⟩ := v
    set ρ : ℝ := rad c₀ with hρdef
    set δ : ℝ := |d| with hδdef
    have hρ0 : 0 ≤ ρ := rad_nonneg c₀
    have hδ0 : 0 ≤ δ := abs_nonneg d
    have hR0 : 0 ≤ R c₀ := by simp only [hR]; positivity
    have hD0 : 0 ≤ Dg d := by
      simp only [hDg]
      have h1 : 0 ≤ |d| ^ (-q₁) := by positivity
      have h2 : 0 ≤ |d| ^ (-q₂) := by positivity
      exact mul_nonneg (by positivity) (le_min h1 h2)
    by_cases hsing : ρ = 0 ∨ δ = 0
    ·
      have hzero : (fun w : ℝ × ℝ => majorant a p u g q₁ q₂ (N' + η + M) (w, (c₀, d))) = fun _ => 0 := by
        funext w
        rw [majorant_eq]
        simp only []
        rcases hsing with h | h
        · rw [← hρdef] at *
          simp [h]
        · rw [← hδdef] at *
          simp [h]
      rw [hzero]
      refine ⟨integrable_zero _ _ _, ?_⟩
      simp only [integral_zero]
      positivity
    · obtain ⟨hρne, hδne⟩ := not_or.1 hsing
      have hρ : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρne)
      have hδ : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδne)
      obtain ⟨hFint, hFle⟩ := inner_integrable_and_le a p ha hp N' η hpN' J hJ ρ δ hρ hδ
      set F : ℝ × ℝ → ℝ := fun w => |w.1| ^ (p - 1) * (Real.sqrt (1 + w.2 ^ 2))⁻¹ *
        (1 + |a| * |w.1| / (δ * Real.sqrt (1 + w.2 ^ 2))) ^ (-(N' : ℝ)) *
        (1 + |a| * Real.sqrt (1 + w.2 ^ 2) / ρ) ^ (-(η : ℝ)) with hF
      set Cv : ℝ := ρ * (ρ ^ 2 * δ)⁻¹ * (1 + ρ) ^ (-(M : ℝ)) * (ρ * δ) ^ u * δ ^ (-(g + 1)) *
        min ((|a| * δ / ρ) ^ (-q₁)) ((|a| * δ / ρ) ^ (-q₂)) with hCv
      have hCv0 : 0 ≤ Cv := by
        rw [hCv]
        have h1 : 0 ≤ (|a| * δ / ρ) ^ (-q₁) := by positivity
        have h2 : 0 ≤ (|a| * δ / ρ) ^ (-q₂) := by positivity
        exact mul_nonneg (by positivity) (le_min h1 h2)

      have hdom : ∀ w : ℝ × ℝ, majorant a p u g q₁ q₂ (N' + η + M) (w, (c₀, d)) ≤ Cv * F w := by
        intro w
        rw [majorant_eq]
        simp only []
        rw [← hρdef, ← hδdef]
        have hX : 0 < Real.sqrt (1 + w.2 ^ 2) := Real.sqrt_pos.2 (by positivity)
        have hsplit := bracket_rpow_neg_le a w.1 w.2 ρ δ hρ hδ N' η M
        have hmin0 : 0 ≤ min ((|a| * δ / ρ) ^ (-q₁)) ((|a| * δ / ρ) ^ (-q₂)) := by
          have h1 : 0 ≤ (|a| * δ / ρ) ^ (-q₁) := by positivity
          exact le_min h1 (by positivity)
        calc |w.1| ^ (p - 1) * ρ * (ρ ^ 2 * δ * Real.sqrt (1 + w.2 ^ 2))⁻¹ *
              bracket a w.1 w.2 ρ δ ^ (-((N' + η + M : ℕ) : ℝ)) * (ρ * δ) ^ u * δ ^ (-(g + 1)) *
              min ((|a| * δ / ρ) ^ (-q₁)) ((|a| * δ / ρ) ^ (-q₂))
            ≤ |w.1| ^ (p - 1) * ρ * (ρ ^ 2 * δ * Real.sqrt (1 + w.2 ^ 2))⁻¹ *
              ((1 + |a| * |w.1| / (δ * Real.sqrt (1 + w.2 ^ 2))) ^ (-(N' : ℝ)) *
                (1 + |a| * Real.sqrt (1 + w.2 ^ 2) / ρ) ^ (-(η : ℝ)) * (1 + ρ) ^ (-(M : ℝ))) *
              (ρ * δ) ^ u * δ ^ (-(g + 1)) * min ((|a| * δ / ρ) ^ (-q₁)) ((|a| * δ / ρ) ^ (-q₂)) := by
              gcongr
          _ = Cv * F w := by
              rw [hCv, hF]
              simp only []
              rw [mul_inv (ρ ^ 2 * δ) (Real.sqrt (1 + w.2 ^ 2))]
              ring
      have hint : Integrable fun w : ℝ × ℝ => majorant a p u g q₁ q₂ (N' + η + M) (w, (c₀, d)) := by
        refine (hFint.const_mul Cv).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
        · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        · rw [Real.norm_of_nonneg (majorant_nonneg _ _ _ _ _ _ _ _)]
          exact hdom w
      refine ⟨hint, ?_⟩

      have hgauge : Cv * (2 * I₀ * |a| ^ (-p) * δ ^ p * J * (|a| / ρ) ^ (-(η : ℝ))) ≤ K * (R c₀ * Dg d) := by

        have hmin : min ((|a| * δ / ρ) ^ (-q₁)) ((|a| * δ / ρ) ^ (-q₂)) ≤
            max (|a| ^ (-q₁)) (|a| ^ (-q₂)) * (ρ ^ q₁ + ρ ^ q₂) * min (δ ^ (-q₁)) (δ ^ (-q₂)) := by
          rw [gauge_term_eq a ρ δ q₁ ha0 hρ hδ, gauge_term_eq a ρ δ q₂ ha0 hρ hδ]
          exact min_coupled_le _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
            (by positivity)

        have hρpow : ∀ q : ℝ, ρ * (ρ ^ 2 * δ)⁻¹ * (ρ * δ) ^ u * δ ^ (-(g + 1)) * δ ^ p * (|a| / ρ) ^ (-(η : ℝ)) *
            ρ ^ q = |a| ^ (-(η : ℝ)) * (ρ ^ (-1 + u + q + η) * (δ ^ e)) := by
          intro q
          have hη : (|a| / ρ) ^ (-(η : ℝ)) = |a| ^ (-(η : ℝ)) * ρ ^ (η : ℝ) := by
            rw [Real.div_rpow ha0.le hρ.le, Real.rpow_neg hρ.le, div_inv_eq_mul]
          have hρ3 : ρ ^ (-1 + u + q + η) = ρ⁻¹ * ρ ^ u * ρ ^ q * ρ ^ (η : ℝ) := by
            rw [Real.rpow_add hρ, Real.rpow_add hρ, Real.rpow_add hρ, Real.rpow_neg_one]
          have hδ4 : δ ^ e = δ⁻¹ * δ ^ u * δ ^ (-(g + 1)) * δ ^ p := by
            rw [he, show (p + u - g - 2 : ℝ) = -1 + u + (-(g + 1)) + p by ring, Real.rpow_add hδ, Real.rpow_add hδ,
              Real.rpow_add hδ, Real.rpow_neg_one]
          have hc : ρ * (ρ ^ 2 * δ)⁻¹ = ρ⁻¹ * δ⁻¹ := by
            rw [mul_inv, pow_two, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
          rw [hη, hρ3, hδ4, Real.mul_rpow hρ.le hδ.le, hc]
          ring
        have hR₁ : R c₀ = ρ ^ s₁ * (1 + ρ) ^ (-(M : ℝ)) + ρ ^ s₂ * (1 + ρ) ^ (-(M : ℝ)) := rfl
        have hDg' : Dg d = δ ^ e * min (δ ^ (-q₁)) (δ ^ (-q₂)) := rfl
        have hmin0 : 0 ≤ min (δ ^ (-q₁)) (δ ^ (-q₂)) := by
          have h1 : 0 ≤ δ ^ (-q₁) := by positivity
          exact le_min h1 (by positivity)
        have hpre : 0 ≤ ρ * (ρ ^ 2 * δ)⁻¹ * (1 + ρ) ^ (-(M : ℝ)) * (ρ * δ) ^ u * δ ^ (-(g + 1)) := by positivity
        calc Cv * (2 * I₀ * |a| ^ (-p) * δ ^ p * J * (|a| / ρ) ^ (-(η : ℝ)))
            ≤ (ρ * (ρ ^ 2 * δ)⁻¹ * (1 + ρ) ^ (-(M : ℝ)) * (ρ * δ) ^ u * δ ^ (-(g + 1)) *
                (max (|a| ^ (-q₁)) (|a| ^ (-q₂)) * (ρ ^ q₁ + ρ ^ q₂) * min (δ ^ (-q₁)) (δ ^ (-q₂)))) *
                (2 * I₀ * |a| ^ (-p) * δ ^ p * J * (|a| / ρ) ^ (-(η : ℝ))) := by
                rw [hCv]
                gcongr
          _ = K * (R c₀ * Dg d) := by
                rw [hK, hR₁, hDg', hs₁def, hs₂def]
                have h₁ := hρpow q₁
                have h₂ := hρpow q₂

                have expand : ρ * (ρ ^ 2 * δ)⁻¹ * (1 + ρ) ^ (-(M : ℝ)) * (ρ * δ) ^ u * δ ^ (-(g + 1)) *
                    (max (|a| ^ (-q₁)) (|a| ^ (-q₂)) * (ρ ^ q₁ + ρ ^ q₂) * min (δ ^ (-q₁)) (δ ^ (-q₂))) *
                    (2 * I₀ * |a| ^ (-p) * δ ^ p * J * (|a| / ρ) ^ (-(η : ℝ))) =
                    2 * I₀ * |a| ^ (-p) * J * max (|a| ^ (-q₁)) (|a| ^ (-q₂)) * min (δ ^ (-q₁)) (δ ^ (-q₂)) *
                      (1 + ρ) ^ (-(M : ℝ)) *
                      ((ρ * (ρ ^ 2 * δ)⁻¹ * (ρ * δ) ^ u * δ ^ (-(g + 1)) * δ ^ p * (|a| / ρ) ^ (-(η : ℝ)) * ρ ^ q₁) +
                        (ρ * (ρ ^ 2 * δ)⁻¹ * (ρ * δ) ^ u * δ ^ (-(g + 1)) * δ ^ p * (|a| / ρ) ^ (-(η : ℝ)) *
                          ρ ^ q₂)) := by ring
                rw [expand, h₁, h₂]
                ring
      calc ∫ w : ℝ × ℝ, majorant a p u g q₁ q₂ (N' + η + M) (w, (c₀, d)) ≤ ∫ w : ℝ × ℝ, Cv * F w :=
            integral_mono hint (hFint.const_mul Cv) hdom
        _ = Cv * ∫ w : ℝ × ℝ, F w := integral_const_mul _ _
        _ ≤ Cv * (2 * I₀ * |a| ^ (-p) * δ ^ p * J * (|a| / ρ) ^ (-(η : ℝ))) := by gcongr
        _ ≤ K * (R c₀ * Dg d) := hgauge
  refine (integrable_prod_iff' hmeas').2 ⟨Filter.Eventually.of_forall fun v => (hslice v).1, ?_⟩
  refine hHint.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact hmeas'.norm.prod_swap.integral_prod_right'
  · have h0 : 0 ≤ ∫ w : ℝ × ℝ, ‖majorant a p u g q₁ q₂ (N' + η + M) (w, v)‖ := integral_nonneg fun w => norm_nonneg _
    rw [Real.norm_of_nonneg h0]
    calc ∫ w : ℝ × ℝ, ‖majorant a p u g q₁ q₂ (N' + η + M) (w, v)‖
        = ∫ w : ℝ × ℝ, majorant a p u g q₁ q₂ (N' + η + M) (w, v) := by
          congr 1
          funext w
          exact Real.norm_of_nonneg (majorant_nonneg _ _ _ _ _ _ _ _)
      _ ≤ K * (R v.1 * Dg v.2) := (hslice v).2

private theorem integrable_majorant_inner (a p u g q₁ q₂ : ℝ) (N : ℕ) (hM : Integrable (majorant a p u g q₁ q₂ N)) :
    (∀ᵐ w : ℝ × ℝ, Integrable fun v : (Fin 2 → ℝ) × ℝ => majorant a p u g q₁ q₂ N (w, v)) ∧
      Integrable fun w : ℝ × ℝ => ∫ v : (Fin 2 → ℝ) × ℝ, majorant a p u g q₁ q₂ N (w, v) := by
  rw [Measure.volume_eq_prod] at hM
  exact ⟨hM.prod_right_ae, hM.integral_prod_left⟩

private def M0 (a u g q₁ q₂ : ℝ) (N : ℕ) (α x : ℝ) (v : (Fin 2 → ℝ) × ℝ) : ℝ :=
  rad v.1 * (rad v.1 ^ 2 * |v.2| * Real.sqrt (1 + x ^ 2))⁻¹ * bracket a α x (rad v.1) |v.2| ^ (-(N : ℝ)) *
    (rad v.1 * |v.2|) ^ u * |v.2| ^ (-(g + 1)) *
      min ((|a| * |v.2| / rad v.1) ^ (-q₁)) ((|a| * |v.2| / rad v.1) ^ (-q₂))

private theorem majorant_eq_M0 (a p u g q₁ q₂ : ℝ) (N : ℕ) (α x : ℝ) (v : (Fin 2 → ℝ) × ℝ) :
    majorant a p u g q₁ q₂ N ((α, x), v) = |α| ^ (p - 1) * M0 a u g q₁ q₂ N α x v := by
  simp only [majorant, M0]
  ring

private theorem M0_nonneg (a u g q₁ q₂ : ℝ) (N : ℕ) (α x : ℝ) (v : (Fin 2 → ℝ) × ℝ) : 0 ≤ M0 a u g q₁ q₂ N α x v := by
  unfold M0
  have h₁ : 0 ≤ rad v.1 := rad_nonneg _
  have h₂ : 0 ≤ (|a| * |v.2| / rad v.1) ^ (-q₁) := Real.rpow_nonneg (by positivity) _
  have h₃ : 0 ≤ (|a| * |v.2| / rad v.1) ^ (-q₂) := Real.rpow_nonneg (by positivity) _
  have h₄ : 0 ≤ bracket a α x (rad v.1) |v.2| ^ (-(N : ℝ)) := by
    apply Real.rpow_nonneg
    unfold bracket
    positivity
  have h₅ : 0 ≤ (rad v.1 * |v.2|) ^ u := Real.rpow_nonneg (by positivity) _
  have h₆ : 0 ≤ |v.2| ^ (-(g + 1)) := Real.rpow_nonneg (abs_nonneg _) _
  have h₇ : 0 ≤ (rad v.1 ^ 2 * |v.2| * Real.sqrt (1 + x ^ 2))⁻¹ := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h₁ h₇) h₄) h₅) h₆) (le_min h₂ h₃)

private theorem transv_inv_data (a : ℝ) (c₀ : Fin 2 → ℝ) (d : ℝ) (hd : d ≠ 0) (hρ : 0 < rad c₀) :
    (!![a, 0; 0, 1] * (transv c₀ d)⁻¹).det = a / (d * rad c₀) ∧
      (!![a, 0; 0, 1] * (transv c₀ d)⁻¹) 1 0 ^ 2 + (!![a, 0; 0, 1] * (transv c₀ d)⁻¹) 1 1 ^ 2 = (d ^ 2)⁻¹ := by
  have hdet : (transv c₀ d).det = d * rad c₀ := transv_det c₀ d
  have hdet0 : (transv c₀ d).det ≠ 0 := by rw [hdet]; exact mul_ne_zero hd hρ.ne'
  have hinv : (transv c₀ d)⁻¹ = (d * rad c₀)⁻¹ • (transv c₀ d).adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet]
  have hadj : (transv c₀ d).adjugate = !![d * c₀ 0 / rad c₀, -(-(d * c₀ 1) / rad c₀); -c₀ 1, c₀ 0] := by
    rw [transv, Matrix.adjugate_fin_two_of]
  constructor
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdet, Matrix.det_fin_two_of]
    ring
  · have hρ2 := rad_sq c₀
    simp only [hinv, hadj, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul]
    field_simp
    nlinarith [hρ2]

private theorem norm_apply_transv_inv_le (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g q₁ q₂ C₁ C₂ : ℝ)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖W X‖ ≤ C₁ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (g + 1) * (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₁))
    (hC₂ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖W X‖ ≤ C₂ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (g + 1) * (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₂))
    (a : ℝ) (ha : a ≠ 0) (c₀ : Fin 2 → ℝ) (d : ℝ) (hd : d ≠ 0) (hρ : 0 < rad c₀) :
    ‖W (!![a, 0; 0, 1] * (transv c₀ d)⁻¹)‖ ≤
      max C₁ C₂ * (|d| ^ (-(g + 1)) * min ((|a| * |d| / rad c₀) ^ (-q₁)) ((|a| * |d| / rad c₀) ^ (-q₂))) := by
  obtain ⟨hdet, hrow⟩ := transv_inv_data a c₀ d hd hρ
  set X := !![a, 0; 0, 1] * (transv c₀ d)⁻¹ with hX
  have hX0 : X.det ≠ 0 := by rw [hdet]; exact div_ne_zero ha (mul_ne_zero hd hρ.ne')
  have hsqrt : Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (g + 1) = |d| ^ (-(g + 1)) := by
    rw [hrow, Real.sqrt_inv, Real.sqrt_sq_eq_abs, Real.inv_rpow (abs_nonneg d), Real.rpow_neg (abs_nonneg d)]
  have hτ : |X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2) = |a| * |d| / rad c₀ := by
    rw [hdet, hrow, abs_div, abs_mul, abs_of_pos hρ, div_inv_eq_mul, ← sq_abs d]
    have hd' : |d| ≠ 0 := abs_ne_zero.2 hd
    field_simp
  have h₁ := hC₁ X hX0
  have h₂ := hC₂ X hX0
  rw [hsqrt, hτ] at h₁ h₂
  have hA : 0 ≤ |d| ^ (-(g + 1)) := Real.rpow_nonneg (abs_nonneg d) _
  have hM : 0 ≤ max C₁ C₂ := le_max_of_le_left hC₁0
  rw [mul_min_of_nonneg _ _ hA, mul_min_of_nonneg _ _ hM]
  refine le_min ?_ ?_
  · calc ‖W X‖ ≤ C₁ * |d| ^ (-(g + 1)) * (|a| * |d| / rad c₀) ^ (-q₁) := h₁
      _ ≤ max C₁ C₂ * |d| ^ (-(g + 1)) * (|a| * |d| / rad c₀) ^ (-q₁) := by
        gcongr
        exact le_max_left _ _
      _ = max C₁ C₂ * (|d| ^ (-(g + 1)) * (|a| * |d| / rad c₀) ^ (-q₁)) := by ring
  · calc ‖W X‖ ≤ C₂ * |d| ^ (-(g + 1)) * (|a| * |d| / rad c₀) ^ (-q₂) := h₂
      _ ≤ max C₁ C₂ * |d| ^ (-(g + 1)) * (|a| * |d| / rad c₀) ^ (-q₂) := by
        gcongr
        exact le_max_right _ _
      _ = max C₁ C₂ * (|d| ^ (-(g + 1)) * (|a| * |d| / rad c₀) ^ (-q₂)) := by ring

private theorem abs_rpow_add_two_mul_inv_sq (t u : ℝ) (ht : t ≠ 0) : |t| ^ (u + 2) * (|t| ^ 2)⁻¹ = |t| ^ u := by
  have h0 : 0 < |t| := abs_pos.2 ht
  rw [Real.rpow_add h0, Real.rpow_two, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 h0.ne'), mul_one]

private theorem abs_rpow_prefactor (y : ℝ) (hy : y ≠ 0) (u tr sr : ℝ) :
    |y| ^ (-(u + 1)) * |y| ^ (-tr) * |y| ^ (sr - 1) = |y| ^ (sr - tr - u - 2) := by
  have h0 : 0 < |y| := abs_pos.2 hy
  rw [← Real.rpow_add h0, ← Real.rpow_add h0]
  congr 1
  ring

private theorem abs_rpow_sub_two_mul_sq (y : ℝ) (hy : y ≠ 0) (p : ℝ) : |y| ^ (p - 2) * y ^ 2 = |y| * |y| ^ (p - 1) := by
  have h0 : 0 < |y| := abs_pos.2 hy
  have h1 : |y| ^ (p - 2) * y ^ 2 = |y| ^ p := by
    rw [← sq_abs y, ← Real.rpow_two, ← Real.rpow_add h0]
    congr 1
    ring
  have h2 : |y| * |y| ^ (p - 1) = |y| ^ p := by
    calc |y| * |y| ^ (p - 1) = |y| ^ (1 : ℝ) * |y| ^ (p - 1) := by rw [Real.rpow_one]
      _ = |y| ^ p := by
        rw [← Real.rpow_add h0]
        congr 1
        ring
  rw [h1, h2]

private theorem abs_inv_mul_rpow (y m r : ℝ) : |y⁻¹ * m| ^ r = |y| ^ (-r) * |m| ^ r := by
  rw [abs_mul, abs_inv, Real.mul_rpow (inv_nonneg.2 (abs_nonneg y)) (abs_nonneg m), Real.inv_rpow (abs_nonneg y),
    Real.rpow_neg (abs_nonneg y)]

end DualArchZetaBound

end

end R4_B5_B6i_core

section R6_B5a

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam signShift signShift_zero RealArchParam.gammaR RealArchParam.gammaC RealArchParam.twist RealArchParam.dual RealArchParam.centralExponent RealArchParam.discrete RealArchParam.principal CubicInduction.integrable_jacquetIntegrand3_dilate_mul_quasiChar"
p2m_open "LanglandsTunnell"

namespace RealArchParam p2m_export "LanglandsTunnell.RealArchParam" "gammaR gammaC twist dual centralExponent centralSign discrete principal" end RealArchParam
p2m_open_scoped "LanglandsTunnell.RealArchParam" in

private theorem RealArchParam.exists_floor_add_centralExponent_re_lt_of_dual_floor (P : RealArchParam) (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P.dual.twist 0 a).gammaC, -ν.re < c₁)) :
    ∃ c₀' : ℝ, (∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀') ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀')) ∧
      c₀' + P.centralExponent.re < c₁ := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    have hsh : ∀ x : ZMod 2, 0 ≤ (signShift x).re := by
      intro x; unfold signShift; split_ifs <;> simp
    have hself : ∀ x : ZMod 2, x + x = 0 := by decide
    have h₁ : u₁.re < c₁ := by
      have h := (hc₁ a₁).1 (-u₁ + 0 + signShift (a₁ + a₁))
        (by simp [RealArchParam.dual, RealArchParam.twist, RealArchParam.gammaR])
      rw [hself] at h
      simp only [signShift_zero, Complex.neg_re, add_zero, neg_neg] at h
      exact h
    have h₂ : u₂.re < c₁ := by
      have h := (hc₁ a₂).1 (-u₂ + 0 + signShift (a₂ + a₂))
        (by simp [RealArchParam.dual, RealArchParam.twist, RealArchParam.gammaR])
      rw [hself] at h
      simp only [signShift_zero, Complex.neg_re, add_zero, neg_neg] at h
      exact h
    refine ⟨max (-u₁.re) (-u₂.re) + (c₁ - max u₁.re u₂.re) / 2, ?_, ?_⟩
    · intro a
      refine ⟨?_, by simp [RealArchParam.twist, RealArchParam.gammaC]⟩
      intro μ hμ
      have hmax : max u₁.re u₂.re < c₁ := max_lt h₁ h₂
      have e₁ := le_max_left (-u₁.re) (-u₂.re)
      have e₂ := le_max_right (-u₁.re) (-u₂.re)
      simp only [RealArchParam.twist, RealArchParam.gammaR, Multiset.insert_eq_cons, Multiset.mem_cons,
        Multiset.mem_singleton] at hμ
      rcases hμ with rfl | rfl
      · have := hsh (a₁ + a)
        simp only [Complex.add_re, add_zero]
        linarith
      · have := hsh (a₂ + a)
        simp only [Complex.add_re, add_zero]
        linarith
    · simp only [RealArchParam.centralExponent, Complex.add_re, max_def]
      split_ifs <;> linarith
  | discrete u₀ k hk =>
    have h : u₀.re - ((k : ℂ) / 2).re < c₁ := by
      have h := (hc₁ 0).2 (-u₀ + 0 + (k : ℂ) / 2)
        (by simp [RealArchParam.dual, RealArchParam.twist, RealArchParam.gammaC])
      simp only [Complex.add_re, Complex.neg_re, add_zero] at h
      linarith
    have h2 : (2 * u₀).re = 2 * u₀.re := by simp
    refine ⟨-(u₀.re + ((k : ℂ) / 2).re) + (c₁ - (u₀.re - ((k : ℂ) / 2).re)) / 2, ?_, ?_⟩
    · intro a
      refine ⟨by simp [RealArchParam.twist, RealArchParam.gammaR], ?_⟩
      intro ν hν
      simp only [RealArchParam.twist, RealArchParam.gammaC, Multiset.mem_singleton] at hν
      subst hν
      simp only [Complex.add_re, add_zero]
      linarith
    · simp only [RealArchParam.centralExponent, h2]
      linarith

end LanglandsTunnell

end R6_B5a

section R8_G1

open NumberField AutomorphicForm
open MeasureTheory

namespace DualArchZetaBound

open scoped Classical in

private theorem map_realCoord_nu_add (a : ℚ)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume) :
    MeasureTheory.Measure.map (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) ν_add =
      ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) • (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by

  have hsymm : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm =
      StandardKernel.ofReal ∘ StandardKernel.mixedCoord := by
    funext y
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).injective
    rw [RingEquiv.apply_symm_apply]
    symm
    refine Prod.ext ?_ ?_
    · funext w
      obtain ⟨v, hv⟩ := w
      obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
      simp only [Function.comp_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply _
    · funext w
      obtain ⟨v, hv⟩ := w
      obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
      exact (InfinitePlace.not_isComplex_iff_isReal.mpr Rat.isReal_infinitePlace hv).elim

  have hcont : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      (continuous_apply Rat.infinitePlace)
  have hmeas₁ : Measurable (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) := hcont.measurable
  have hmeas₂ : Measurable (StandardKernel.ofReal ∘ StandardKernel.mixedCoord) :=
    (StandardKernel.continuous_ofReal.comp StandardKernel.contDiff_mixedCoord.continuous).measurable

  have hcomp : (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) ∘
      (StandardKernel.ofReal ∘ StandardKernel.mixedCoord) = StandardKernel.mixedCoord := by
    funext y
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply _

  haveI hU : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    ⟨⟨⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩⟩, fun w => Subtype.ext (Subsingleton.elim _ _)⟩
  haveI hC : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} := ⟨fun w => by
    obtain ⟨v, hv⟩ := w
    obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
    exact InfinitePlace.not_isComplex_iff_isReal.mpr Rat.isReal_infinitePlace hv⟩
  have hproj : Measure.map StandardKernel.mixedCoord (volume : Measure (mixedEmbedding.mixedSpace ℚ)) =
      (volume : Measure ℝ) := by
    have h₁ : StandardKernel.mixedCoord =
        (fun f : {w : InfinitePlace ℚ // w.IsReal} → ℝ => f ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩) ∘
          (Prod.fst : mixedEmbedding.mixedSpace ℚ → _) := by
      funext y
      rfl
    have h₂ : (volume : Measure ({w : InfinitePlace ℚ // w.IsComplex} → ℂ)) Set.univ = 1 := by
      rw [volume_pi, Measure.pi_of_empty]
      simp
    rw [h₁, ← Measure.map_map (measurable_pi_apply _) measurable_fst, Measure.volume_eq_prod, Measure.map_fst_prod, h₂,
      one_smul]
    convert (volume_preserving_funUnique {w : InfinitePlace ℚ // w.IsReal} ℝ).map_eq <;>
      first | rfl | exact Subsingleton.elim _ _ | (rename_i f; exact congrArg f (Subsingleton.elim _ _))

  rw [hν_add, Measure.map_smul, hsymm, Measure.map_map hmeas₁ hmeas₂, hcomp, hproj]

end DualArchZetaBound

end R8_G1

section R9_seam_and_H1

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

open MeasureTheory Set Topology

namespace DualArchZetaBound

open AutomorphicForm.StandardKernel

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction in

private noncomputable def dualPointIntegrand {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (σ' : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (z : ((InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ) × (Fin 2 → Fin 2 → ℝ)) : ℂ :=
  ArchR.quasiChar (u₃ + 1) a₃
      (realCoord ((z.1.1⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) * (realMat gInf).det) *
      ((realCoord ((z.1.1⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) ^ 2)⁻¹ •
          ∫ w : Fin 2 → ℝ,
            S (Matrix.of z.2 * Matrix.of ![fun b => realMat gInf 1 b +
                  w 0 * (realMat gInf 0 b - realCoord z.1.2 * realMat gInf 2 b),
                fun b => realMat gInf 2 b +
                  w 1 * (realMat gInf 0 b - realCoord z.1.2 * realMat gInf 2 b)]) *
              ψ (ofReal (-((realCoord ((z.1.1⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ))⁻¹ * w 1)))) *
        ArchR.quasiChar (u₃ + 2) a₃ (Matrix.of z.2).det * (((|(Matrix.of z.2).det| ^ 2)⁻¹ : ℝ) : ℂ) *
          D.W (ArchR.diagOne a * (Matrix.of z.2)⁻¹) *
    ((σ' z.1.1 : ℂˣ) : ℂ) * ((‖(z.1.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction in

private theorem dualWhittaker_integrand_eq {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (σ' : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ) (p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ) :
    dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ a ψ S (h * gInf))
          (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 1)) *
        ((σ' p.1 : ℂˣ) : ℂ) * ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1) =
      ∫ e : Fin 2 → Fin 2 → ℝ, dualPointIntegrand D u₃ a₃ a ψ S gInf σ' s (p, e) := by
  simp only [dualWhittakerFn3_apply]
  rw [jacquetVector3_dual_point]
  simp only [dualPointIntegrand]
  rw [integral_mul_const, integral_mul_const]
  simp only [mul_assoc]
  rw [integral_const_mul]
  simp only [mul_assoc]

section H1Body

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction AutomorphicForm.StandardKernel"

private theorem diagOne_eq_of (a : ℝ) : ArchR.diagOne a = !![a, 0; 0, 1] := rfl

private theorem h1_norm_quasiChar (u : ℂ) (b : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    ‖ArchR.quasiChar u b y‖ = |y| ^ u.re := by
  have hpos : 0 < |y| := abs_pos.2 hy
  unfold ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hsgn : ‖(if b = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ))‖ = 1 := by
    split_ifs
    · simp
    · rw [Complex.norm_real, Real.norm_eq_abs]
      rcases lt_or_gt_of_ne hy with h | h
      · simp [sign_neg h]
      · simp [sign_pos h]
  rw [hsgn, mul_one]

private theorem h1_measurable_quasiChar (u : ℂ) (b : ZMod 2) : Measurable (ArchR.quasiChar u b) := by
  unfold ArchR.quasiChar
  refine Measurable.mul ((Complex.measurable_ofReal.comp continuous_abs.measurable).pow_const u) ?_
  split_ifs
  · exact measurable_const
  · have hrw : (fun y : ℝ => ((SignType.sign y : ℝ) : ℂ)) =
        fun y => if 0 < y then (1 : ℂ) else if y < 0 then -1 else 0 := by
      funext y
      rcases lt_trichotomy y 0 with h | h | h
      · simp [sign_neg h, h, not_lt.2 h.le]
      · simp [h]
      · simp [sign_pos h, h]
    rw [hrw]
    exact Measurable.ite measurableSet_Ioi measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)

private theorem det_realMat_ne_zero (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (realMat gInf).det ≠ 0 := by
  have h : realMat gInf * realMat gInf⁻¹ = 1 := by rw [← realMat_mul, mul_inv_cancel, realMat_one]
  intro h0
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

private theorem realCoord_units_inv (α : (InfiniteAdeleRing ℚ)ˣ) :
    realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) =
      (realCoord (α : InfiniteAdeleRing ℚ))⁻¹ := by
  have h : realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) *
      realCoord (α : InfiniteAdeleRing ℚ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h

private noncomputable def dualKernel {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a c : ℝ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (((c ^ 2)⁻¹ : ℝ) : ℂ) * ArchR.quasiChar (u₃ + 2) a₃ h.det * (((|h.det| ^ 2)⁻¹ : ℝ) : ℂ) *
    D.W (ArchR.diagOne a * h⁻¹)

private theorem dualIntegrandR_transv_shear {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (m : Matrix (Fin 3) (Fin 3) ℝ) (c x : ℝ) (c₀ : Fin 2 → ℝ) (d ξ : ℝ) :
    dualIntegrandR D u₃ a₃ (a : ℝ) ψ S m ((c, x), fun i j => (transv c₀ d * shear ξ) i j) =
      dualKernel D u₃ a₃ (a : ℝ) c (transv c₀ d) *
        (ArchR.psi (-((a : ℝ) * ξ)) * shearedInner ψ S m c x (transv c₀ d * ArchR.unip ξ)) := by
  have hof : (Matrix.of fun i j => (transv c₀ d * shear ξ) i j) = transv c₀ d * ArchR.unip ξ := rfl
  simp only [dualIntegrandR, dualKernel, hof, det_mul_unip, W_diagOne_mul_inv_mul_unip, Complex.real_smul]
  push_cast
  ring

private theorem norm_dualKernel_transv_le {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℝ) (ha : a ≠ 0) (g q₁ q₂ C₁ C₂ : ℝ) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ C₁ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (g + 1) * (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₁))
    (hC₂ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ C₂ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (g + 1) * (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₂))
    (y : ℝ) (c₀ : Fin 2 → ℝ) (d : ℝ) (hd : d ≠ 0) (hρ : 0 < rad c₀) :
    ‖dualKernel D u₃ a₃ a y⁻¹ (transv c₀ d)‖ ≤
      y ^ 2 * (rad c₀ * |d|) ^ u₃.re *
        (max C₁ C₂ * (|d| ^ (-(g + 1)) * min ((|a| * |d| / rad c₀) ^ (-q₁)) ((|a| * |d| / rad c₀) ^ (-q₂)))) := by
  have hdet : (transv c₀ d).det = d * rad c₀ := transv_det c₀ d
  have hdet0 : (transv c₀ d).det ≠ 0 := by rw [hdet]; exact mul_ne_zero hd hρ.ne'
  have hW := norm_apply_transv_inv_le D.W g q₁ q₂ C₁ C₂ hC₁0 hC₁ hC₂ a ha c₀ d hd hρ
  have h1 : |((y⁻¹) ^ 2)⁻¹| = y ^ 2 := by rw [inv_pow, inv_inv, abs_of_nonneg (sq_nonneg y)]
  have h2 : |(|(transv c₀ d).det| ^ 2)⁻¹| = (|(transv c₀ d).det| ^ 2)⁻¹ := abs_of_nonneg (by positivity)
  have hre : (u₃ + 2).re = u₃.re + 2 := by simp
  have h3 : |(transv c₀ d).det| ^ (u₃ + 2).re * (|(transv c₀ d).det| ^ 2)⁻¹ = (rad c₀ * |d|) ^ u₃.re := by
    rw [hre, abs_rpow_add_two_mul_inv_sq _ _ hdet0, hdet, abs_mul, abs_of_pos hρ, mul_comm]
  unfold dualKernel
  rw [diagOne_eq_of]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, h1_norm_quasiChar _ _ hdet0]
  calc y ^ 2 * |(transv c₀ d).det| ^ (u₃ + 2).re * (|(transv c₀ d).det| ^ 2)⁻¹ *
          ‖D.W (!![a, 0; 0, 1] * (transv c₀ d)⁻¹)‖
        = y ^ 2 * (|(transv c₀ d).det| ^ (u₃ + 2).re * (|(transv c₀ d).det| ^ 2)⁻¹) *
          ‖D.W (!![a, 0; 0, 1] * (transv c₀ d)⁻¹)‖ := by ring
    _ = y ^ 2 * (rad c₀ * |d|) ^ u₃.re * ‖D.W (!![a, 0; 0, 1] * (transv c₀ d)⁻¹)‖ := by rw [h3]
    _ ≤ y ^ 2 * (rad c₀ * |d|) ^ u₃.re *
          (max C₁ C₂ * (|d| ^ (-(g + 1)) * min ((|a| * |d| / rad c₀) ^ (-q₁)) ((|a| * |d| / rad c₀) ^ (-q₂)))) := by
        gcongr

private theorem rad_mul_norm_integral_slice_le {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ) (ha : a ≠ 0) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (m : Matrix (Fin 3) (Fin 3) ℝ) (N : ℕ) (C₄ : ℝ)
    (hC₄ : ∀ (c x : ℝ), c ≠ 0 → ∀ h : Matrix (Fin 2) (Fin 2) ℝ, IsTransversal h → h.det ≠ 0 →
      ‖∫ ξ : ℝ, ArchR.psi (-((a : ℝ) * ξ)) * shearedInner ψ S m c x (h * ArchR.unip ξ)‖ ≤
        C₄ / (colNorm h ^ 2 * (|h.det| / colNorm h) * Real.sqrt (1 + x ^ 2)) *
          (1 + |(a : ℝ)| * Real.sqrt (1 + x ^ 2) / colNorm h +
              |(a : ℝ) / c| / ((|h.det| / colNorm h) * Real.sqrt (1 + x ^ 2)) + colNorm h) ^ (-(N : ℝ)))
    (g q₁ q₂ C₁ C₂ : ℝ) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ C₁ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (g + 1) * (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₁))
    (hC₂ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ C₂ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (g + 1) * (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₂))
    (y x : ℝ) (hy : y ≠ 0) (v : (Fin 2 → ℝ) × ℝ) :
    rad v.1 *
        ‖∫ ξ : ℝ, dualIntegrandR D u₃ a₃ (a : ℝ) ψ S m ((y⁻¹, x), fun i j => (transv v.1 v.2 * shear ξ) i j)‖ ≤
      max C₁ C₂ * max C₄ 0 * y ^ 2 * M0 (a : ℝ) u₃.re g q₁ q₂ N y x v := by
  obtain ⟨c₀, d⟩ := v
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  simp only [dualIntegrandR_transv_shear, integral_const_mul, norm_mul]
  by_cases hdet : (transv c₀ d).det = 0
  · have hK : dualKernel D u₃ a₃ (a : ℝ) y⁻¹ (transv c₀ d) = 0 := by simp [dualKernel, hdet]
    rw [hK, norm_zero, zero_mul, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_max_of_le_left hC₁0) (le_max_right _ _)) (sq_nonneg y))
      (M0_nonneg _ _ _ _ _ _ _ _ _)
  · have hdρ : d ≠ 0 ∧ rad c₀ ≠ 0 := by rw [transv_det] at hdet; exact mul_ne_zero_iff.1 hdet
    have hd : d ≠ 0 := hdρ.1
    have hρ : 0 < rad c₀ := lt_of_le_of_ne (rad_nonneg c₀) (Ne.symm hdρ.2)
    have hcol : colNorm (transv c₀ d) = rad c₀ := transv_colNorm c₀ d
    have hδ : |(transv c₀ d).det| / rad c₀ = |d| := by
      rw [transv_det, abs_mul, abs_of_pos hρ, mul_div_assoc, div_self hρ.ne', mul_one]
    have hB := hC₄ y⁻¹ x (inv_ne_zero hy) (transv c₀ d) (transv_isTransversal c₀ d) hdet
    rw [hcol, hδ] at hB
    have hbr : 1 + |(a : ℝ)| * Real.sqrt (1 + x ^ 2) / rad c₀ +
        |(a : ℝ) / y⁻¹| / (|d| * Real.sqrt (1 + x ^ 2)) + rad c₀ = bracket (a : ℝ) y x (rad c₀) |d| := by
      simp only [bracket, div_inv_eq_mul, abs_mul]
    rw [hbr] at hB
    have hX : 0 < rad c₀ ^ 2 * |d| * Real.sqrt (1 + x ^ 2) := by positivity
    have hbr0 : 0 ≤ bracket (a : ℝ) y x (rad c₀) |d| ^ (-(N : ℝ)) := by
      apply Real.rpow_nonneg
      unfold bracket
      positivity
    have hB' : ‖∫ ξ : ℝ, ArchR.psi (-((a : ℝ) * ξ)) * shearedInner ψ S m y⁻¹ x (transv c₀ d * ArchR.unip ξ)‖ ≤
        max C₄ 0 / (rad c₀ ^ 2 * |d| * Real.sqrt (1 + x ^ 2)) * bracket (a : ℝ) y x (rad c₀) |d| ^ (-(N : ℝ)) :=
      hB.trans (by gcongr; exact le_max_left _ _)
    have hK := norm_dualKernel_transv_le D u₃ a₃ (a : ℝ) ha' g q₁ q₂ C₁ C₂ hC₁0 hC₁ hC₂ y c₀ d hd hρ
    have hK0 : 0 ≤ y ^ 2 * (rad c₀ * |d|) ^ u₃.re *
        (max C₁ C₂ * (|d| ^ (-(g + 1)) * min ((|(a : ℝ)| * |d| / rad c₀) ^ (-q₁))
          ((|(a : ℝ)| * |d| / rad c₀) ^ (-q₂)))) := by
      have hmin : 0 ≤ min ((|(a : ℝ)| * |d| / rad c₀) ^ (-q₁)) ((|(a : ℝ)| * |d| / rad c₀) ^ (-q₂)) :=
        le_min (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
      have hmax : 0 ≤ max C₁ C₂ := le_max_of_le_left hC₁0
      have hu : 0 ≤ (rad c₀ * |d|) ^ u₃.re := Real.rpow_nonneg (by positivity) _
      have hg : 0 ≤ |d| ^ (-(g + 1)) := Real.rpow_nonneg (abs_nonneg d) _
      positivity
    calc rad c₀ * (‖dualKernel D u₃ a₃ (a : ℝ) y⁻¹ (transv c₀ d)‖ *
            ‖∫ ξ : ℝ, ArchR.psi (-((a : ℝ) * ξ)) * shearedInner ψ S m y⁻¹ x (transv c₀ d * ArchR.unip ξ)‖)
        ≤ rad c₀ * ((y ^ 2 * (rad c₀ * |d|) ^ u₃.re *
            (max C₁ C₂ * (|d| ^ (-(g + 1)) * min ((|(a : ℝ)| * |d| / rad c₀) ^ (-q₁))
              ((|(a : ℝ)| * |d| / rad c₀) ^ (-q₂))))) *
            (max C₄ 0 / (rad c₀ ^ 2 * |d| * Real.sqrt (1 + x ^ 2)) *
              bracket (a : ℝ) y x (rad c₀) |d| ^ (-(N : ℝ)))) := by
          gcongr
      _ = max C₁ C₂ * max C₄ 0 * y ^ 2 * M0 (a : ℝ) u₃.re g q₁ q₂ N y x (c₀, d) := by
          simp only [M0, div_eq_mul_inv]
          ring

private theorem norm_integral_dualIntegrandR_le {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (m : Matrix (Fin 3) (Fin 3) ℝ)
    (c x : ℝ) (hint : Integrable fun e : Fin 2 → Fin 2 → ℝ => dualIntegrandR D u₃ a₃ a ψ S m ((c, x), e)) :
    ‖∫ e : Fin 2 → Fin 2 → ℝ, dualIntegrandR D u₃ a₃ a ψ S m ((c, x), e)‖ ≤
      ∫ v : (Fin 2 → ℝ) × ℝ,
        rad v.1 * ‖∫ ξ : ℝ, dualIntegrandR D u₃ a₃ a ψ S m ((c, x), fun i j => (transv v.1 v.2 * shear ξ) i j)‖ := by
  set F : (Fin 2 → Fin 2 → ℝ) → ℂ := fun e => dualIntegrandR D u₃ a₃ a ψ S m ((c, x), e) with hF
  have h1 := integral_eq_integral_transv_mul_shear F hint
  have h2 := (integrable_transv_slices F hint).2
  have h3 : ∫ v : (Fin 2 → ℝ) × ℝ, (rad v.1 : ℂ) * ∫ ξ : ℝ, F (fun i j => (transv v.1 v.2 * shear ξ) i j) =
      ∫ c₀ : Fin 2 → ℝ, ∫ d : ℝ, (rad c₀ : ℂ) * ∫ ξ : ℝ, F (fun i j => (transv c₀ d * shear ξ) i j) :=
    integral_prod _ h2
  calc ‖∫ e, F e‖
      = ‖∫ v : (Fin 2 → ℝ) × ℝ, (rad v.1 : ℂ) * ∫ ξ : ℝ, F (fun i j => (transv v.1 v.2 * shear ξ) i j)‖ := by
        rw [h1, h3]
    _ ≤ ∫ v : (Fin 2 → ℝ) × ℝ, ‖(rad v.1 : ℂ) * ∫ ξ : ℝ, F (fun i j => (transv v.1 v.2 * shear ξ) i j)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v : (Fin 2 → ℝ) × ℝ, rad v.1 * ‖∫ ξ : ℝ, F (fun i j => (transv v.1 v.2 * shear ξ) i j)‖ := by
        congr 1
        funext v
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rad_nonneg _)]

private theorem jacquetIntegrand3_dual_point_eq {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (α : (InfiniteAdeleRing ℚ)ˣ) (x : InfiniteAdeleRing ℚ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (e : Fin 2 → Fin 2 → ℝ) :
    jacquetIntegrand3 D u₃ a₃ a ψ S
        (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
          gInf) e =
      dualIntegrandR D u₃ a₃ a ψ S (realMat gInf)
        ((realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ), realCoord x), e) := by
  have hc : realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) ≠ 0 :=
    DirectArchZetaBound.realCoord_units_ne_zero _
  unfold jacquetIntegrand3
  rw [realMat_dual_point_mul, godementInner3_point ψ S (Matrix.of e) (realMat gInf) _ _ hc]
  rfl

private theorem integrable_dualIntegrandR_of_ne_zero {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
    (a : ℚ) (ha : a ≠ 0) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (c₀' : ℝ)
    (hdom : ∀ (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)) (q : ℝ), max c₀' (-u₃.re) < q →
      ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
        ∀ g ∈ U, ∀ A : ℝ, A ≠ 0 → ∀ e : Fin 2 → Fin 2 → ℝ,
          ‖jacquetIntegrand3 D u₃ a₃ A ψ S g e‖ ≤ |A| ^ (1 - q) * F e)
    (hmeas : Measurable (dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf))) (y x : ℝ) (hy : y ≠ 0) :
    Integrable fun e : Fin 2 → Fin 2 → ℝ => dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf) ((y⁻¹, x), e) := by
  obtain ⟨α, hα⟩ := DirectArchZetaBound.realCoord_units_range y hy
  have hαy : realCoord (α : InfiniteAdeleRing ℚ) = y := hα
  have hc : realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = y⁻¹ := by
    rw [realCoord_units_inv, hαy]
  set g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
    longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 α) * lowerUnipotent21 (ofReal x) * (weylPrime3 * transposeInv3 1)) *
      gInf with hg₀
  have hpt : ∀ e : Fin 2 → Fin 2 → ℝ,
      dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf) ((y⁻¹, x), e) =
        jacquetIntegrand3 D u₃ a₃ (a : ℝ) ψ S g₀ e := by
    intro e
    have h := jacquetIntegrand3_dual_point_eq D u₃ a₃ (a : ℝ) ψ S α (ofReal x) gInf e
    rw [hc, DirectArchZetaBound.realCoord_ofReal] at h
    exact h.symm
  have hmeas' : AEStronglyMeasurable
      (fun e : Fin 2 → Fin 2 → ℝ => dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf) ((y⁻¹, x), e)) volume :=
    (hmeas.comp (measurable_prodMk_left (m := inferInstance))).aestronglyMeasurable
  obtain ⟨U, hU, F, hF, hb⟩ := hdom g₀ (max c₀' (-u₃.re) + 1) (lt_add_one _)
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  refine (hF.const_mul (|(a : ℝ)| ^ (1 - (max c₀' (-u₃.re) + 1)))).mono' hmeas'
    (Filter.Eventually.of_forall fun e => ?_)
  rw [hpt e]
  exact hb g₀ (mem_of_mem_nhds hU) (a : ℝ) ha' e

end H1Body

section H1Body2

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction AutomorphicForm.StandardKernel"

private noncomputable def dualFr {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (t : ℂ) (e : ℤ) (s : ℂ) (y x : ℝ) : ℂ :=
  (ArchR.quasiChar (u₃ + 1) a₃ (y⁻¹ * (realMat gInf).det) * (ArchR.quasiChar t (e : ZMod 2) y)⁻¹ *
      ((|y| : ℝ) : ℂ) ^ (s - 1)) *
    ∫ e' : Fin 2 → Fin 2 → ℝ, dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf) ((y⁻¹, x), e')

private theorem h1_integrand_eq_dualFr {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ) (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (s : ℂ) :
    (fun p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
      dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ (a : ℝ) ψ S (h * gInf))
          (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 1)) *
        ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
        ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) =
      fun p => dualFr D u₃ a₃ a ψ S gInf t e s (realCoord (p.1 : InfiniteAdeleRing ℚ)) (realCoord p.2) := by
  funext p
  rw [dualWhittaker_integrand_eq]
  have htw : ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) =
      (ArchR.quasiChar t (e : ZMod 2) (realCoord (p.1 : InfiniteAdeleRing ℚ)))⁻¹ := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, MonoidHom.comp_apply,
      ideleChar_section_eq_quasiChar_realCoord σ t e hte E hE p.1]
  have hn : ‖(p.1 : InfiniteAdeleRing ℚ)‖ = |realCoord (p.1 : InfiniteAdeleRing ℚ)| := norm_eq_abs_realCoord _
  unfold dualFr
  rw [← integral_const_mul]
  congr 1
  funext e'
  simp only [dualPointIntegrand, dualIntegrandR, shearedInner, realCoord_units_inv, hn]
  rw [htw]
  ring

private theorem measurable_dualFr {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (t : ℂ) (e : ℤ) (s : ℂ) (hmeas : Measurable (dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf))) :
    Measurable fun w : ℝ × ℝ => dualFr D u₃ a₃ a ψ S gInf t e s w.1 w.2 := by
  unfold dualFr
  have hI : Measurable fun w : ℝ × ℝ =>
      ∫ e' : Fin 2 → Fin 2 → ℝ, dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf) (w, e') :=
    hmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hI' : Measurable fun w : ℝ × ℝ =>
      ∫ e' : Fin 2 → Fin 2 → ℝ, dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf) ((w.1⁻¹, w.2), e') :=
    hI.comp (measurable_fst.inv.prodMk measurable_snd)
  refine Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) hI'
  · exact (h1_measurable_quasiChar _ _).comp (measurable_fst.inv.mul_const _)
  · exact ((h1_measurable_quasiChar _ _).comp measurable_fst).inv
  · exact (Complex.measurable_ofReal.comp (continuous_abs.measurable.comp measurable_fst)).pow_const _

private theorem norm_dualFr_le {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℚ) (ha : a ≠ 0)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (t : ℂ) (e : ℤ) (s : ℂ) (c₀' : ℝ)
    (hdom : ∀ (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)) (q : ℝ), max c₀' (-u₃.re) < q →
      ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
        ∀ g ∈ U, ∀ A : ℝ, A ≠ 0 → ∀ e : Fin 2 → Fin 2 → ℝ,
          ‖jacquetIntegrand3 D u₃ a₃ A ψ S g e‖ ≤ |A| ^ (1 - q) * F e)
    (hmeas : Measurable (dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf)))
    (N : ℕ) (C₄ : ℝ)
    (hC₄ : ∀ (c x : ℝ), c ≠ 0 → ∀ h : Matrix (Fin 2) (Fin 2) ℝ, IsTransversal h → h.det ≠ 0 →
      ‖∫ ξ : ℝ, ArchR.psi (-((a : ℝ) * ξ)) * shearedInner ψ S (realMat gInf) c x (h * ArchR.unip ξ)‖ ≤
        C₄ / (colNorm h ^ 2 * (|h.det| / colNorm h) * Real.sqrt (1 + x ^ 2)) *
          (1 + |(a : ℝ)| * Real.sqrt (1 + x ^ 2) / colNorm h +
              |(a : ℝ) / c| / ((|h.det| / colNorm h) * Real.sqrt (1 + x ^ 2)) + colNorm h) ^ (-(N : ℝ)))
    (q₁ q₂ C₁ C₂ : ℝ) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ C₁ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
        (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₁))
    (hC₂ : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ C₂ * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (P.centralExponent.re + 1) *
        (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₂))
    (p : ℝ) (hp : p = s.re - t.re - u₃.re) (y x : ℝ) (hy : y ≠ 0)
    (hMv : Integrable fun v : (Fin 2 → ℝ) × ℝ =>
      majorant (a : ℝ) p u₃.re P.centralExponent.re q₁ q₂ N ((y, x), v)) :
    ‖dualFr D u₃ a₃ a ψ S gInf t e s y x‖ ≤
      |(realMat gInf).det| ^ (u₃.re + 1) * (max C₁ C₂ * max C₄ 0) * |y| *
        ∫ v : (Fin 2 → ℝ) × ℝ, majorant (a : ℝ) p u₃.re P.centralExponent.re q₁ q₂ N ((y, x), v) := by
  have hdet := det_realMat_ne_zero gInf
  have hA := integrable_dualIntegrandR_of_ne_zero D u₃ a₃ a ha ψ S gInf c₀' hdom hmeas y x hy
  have h1 := norm_integral_dualIntegrandR_le D u₃ a₃ (a : ℝ) ψ S (realMat gInf) y⁻¹ x hA
  have hM0int : Integrable fun v : (Fin 2 → ℝ) × ℝ => M0 (a : ℝ) u₃.re P.centralExponent.re q₁ q₂ N y x v := by
    have hpow : |y| ^ (p - 1) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.2 hy) _).ne'
    refine (hMv.const_mul (|y| ^ (p - 1))⁻¹).congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [majorant_eq_M0]
    field_simp
  have h2 : ∫ v : (Fin 2 → ℝ) × ℝ, rad v.1 * ‖∫ ξ : ℝ, dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf)
        ((y⁻¹, x), fun i j => (transv v.1 v.2 * shear ξ) i j)‖ ≤
      ∫ v : (Fin 2 → ℝ) × ℝ, max C₁ C₂ * max C₄ 0 * y ^ 2 * M0 (a : ℝ) u₃.re P.centralExponent.re q₁ q₂ N y x v :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => mul_nonneg (rad_nonneg _) (norm_nonneg _))
      (hM0int.const_mul _)
      (Filter.Eventually.of_forall fun v => rad_mul_norm_integral_slice_le D u₃ a₃ a ha ψ S (realMat gInf) N C₄ hC₄
        P.centralExponent.re q₁ q₂ C₁ C₂ hC₁0 hC₁ hC₂ y x hy v)
  rw [integral_const_mul] at h2
  have hpre : ‖ArchR.quasiChar (u₃ + 1) a₃ (y⁻¹ * (realMat gInf).det) * (ArchR.quasiChar t (e : ZMod 2) y)⁻¹ *
      ((|y| : ℝ) : ℂ) ^ (s - 1)‖ = |(realMat gInf).det| ^ (u₃.re + 1) * |y| ^ (p - 2) := by
    have hre1 : (u₃ + 1).re = u₃.re + 1 := by simp
    have hre2 : (s - 1).re = s.re - 1 := by simp
    rw [norm_mul, norm_mul, norm_inv, h1_norm_quasiChar _ _ (mul_ne_zero (inv_ne_zero hy) hdet),
      h1_norm_quasiChar _ _ hy, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy), hre1, hre2,
      abs_inv_mul_rpow y _ _, ← Real.rpow_neg (abs_nonneg y)]
    have h3 := abs_rpow_prefactor y hy u₃.re t.re s.re
    rw [hp]
    calc |y| ^ (-(u₃.re + 1)) * |(realMat gInf).det| ^ (u₃.re + 1) * |y| ^ (-t.re) * |y| ^ (s.re - 1)
        = (|y| ^ (-(u₃.re + 1)) * |y| ^ (-t.re) * |y| ^ (s.re - 1)) * |(realMat gInf).det| ^ (u₃.re + 1) := by ring
      _ = |(realMat gInf).det| ^ (u₃.re + 1) * |y| ^ (s.re - t.re - u₃.re - 2) := by rw [h3, mul_comm]
  have hI0 : 0 ≤ ∫ v : (Fin 2 → ℝ) × ℝ, M0 (a : ℝ) u₃.re P.centralExponent.re q₁ q₂ N y x v :=
    integral_nonneg fun v => M0_nonneg _ _ _ _ _ _ _ _ _
  have hK0 : 0 ≤ max C₁ C₂ * max C₄ 0 := mul_nonneg (le_max_of_le_left hC₁0) (le_max_right _ _)
  have hpre0 : 0 ≤ |(realMat gInf).det| ^ (u₃.re + 1) * |y| ^ (p - 2) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hmaj : ∫ v : (Fin 2 → ℝ) × ℝ, majorant (a : ℝ) p u₃.re P.centralExponent.re q₁ q₂ N ((y, x), v) =
      |y| ^ (p - 1) * ∫ v : (Fin 2 → ℝ) × ℝ, M0 (a : ℝ) u₃.re P.centralExponent.re q₁ q₂ N y x v := by
    simp_rw [majorant_eq_M0]
    exact integral_const_mul _ _
  have hsq := abs_rpow_sub_two_mul_sq y hy p
  unfold dualFr
  rw [norm_mul, hpre, hmaj]
  calc |(realMat gInf).det| ^ (u₃.re + 1) * |y| ^ (p - 2) *
          ‖∫ e' : Fin 2 → Fin 2 → ℝ, dualIntegrandR D u₃ a₃ (a : ℝ) ψ S (realMat gInf) ((y⁻¹, x), e')‖
        ≤ |(realMat gInf).det| ^ (u₃.re + 1) * |y| ^ (p - 2) *
          (max C₁ C₂ * max C₄ 0 * y ^ 2 *
            ∫ v : (Fin 2 → ℝ) × ℝ, M0 (a : ℝ) u₃.re P.centralExponent.re q₁ q₂ N y x v) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hpre0
    _ = |(realMat gInf).det| ^ (u₃.re + 1) * (max C₁ C₂ * max C₄ 0) * (|y| ^ (p - 2) * y ^ 2) *
          ∫ v : (Fin 2 → ℝ) × ℝ, M0 (a : ℝ) u₃.re P.centralExponent.re q₁ q₂ N y x v := by ring
    _ = |(realMat gInf).det| ^ (u₃.re + 1) * (max C₁ C₂ * max C₄ 0) * |y| *
          (|y| ^ (p - 1) * ∫ v : (Fin 2 → ℝ) × ℝ, M0 (a : ℝ) u₃.re P.centralExponent.re q₁ q₂ N y x v) := by
        rw [hsq]
        ring

end H1Body2

attribute [local irreducible] dualKernel dualFr majorant

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction in
open scoped Classical in

private theorem integrable_dual_zetaIntegrand
    (P₂ : RealArchParam) (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁))
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsAdmissibleTwist ℚ σ)
    (t : ℂ) (e : ℤ) (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) (hs : max c₁ u₃.re + t.re < s.re) :
    Integrable (fun p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
      dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S (h * gInf))
          (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 1)) *
        ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) p.1 : ℂˣ) : ℂ) *
        ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) (ν_mul.prod ν_add) := by

  have hfloor := RealArchParam.exists_floor_add_centralExponent_re_lt_of_dual_floor P₂ c₁ hc₁
  obtain ⟨c₀', hc₀', hc₀c₁⟩ := hfloor

  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = s.re - t.re - u₃.re := ⟨_, rfl⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : ℝ, q₁ = c₀' - 1 := ⟨_, rfl⟩
  obtain ⟨q₂, hq₂⟩ : ∃ q₂ : ℝ, q₂ = s.re - t.re - P₂.centralExponent.re := ⟨_, rfl⟩
  have hus : u₃.re + t.re < s.re := by have := le_max_right c₁ u₃.re; linarith
  have hc₁s : c₁ + t.re < s.re := by have := le_max_left c₁ u₃.re; linarith
  have hp0 : 0 < p := by rw [hp]; linarith
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha

  have hmaj := exists_integrable_majorant (a : ℝ) p u₃.re P₂.centralExponent.re q₁ q₂ ha' hp0
    (by rw [hp, hq₁]; linarith) (by rw [hp, hq₂]; linarith)
  obtain ⟨N, hM⟩ := hmaj
  have hinner := integrable_majorant_inner (a : ℝ) p u₃.re P₂.centralExponent.re q₁ q₂ N hM
  obtain ⟨hMae, hMj⟩ := hinner

  have hsch := G0.exists_schwartzMap_eq_of_mem_polyGauss3' hS
  obtain ⟨Ψ, hΨ⟩ := hsch
  have hB4 :=
    norm_integral_psi_mul_shearedInner_le S Ψ hΨ a psiInf hpsiInf (realMat gInf) (det_realMat_ne_zero gInf) N
  obtain ⟨C₄, hC₄⟩ := hB4

  have hW₁ := archDatumR_exists_forall_norm_W_le_rpow_mul_rpow_of_le D c₀' hc₀' q₁ hq₁.symm.le
  obtain ⟨C₁, hC₁⟩ := hW₁
  have hW₂ := archDatumR_exists_forall_norm_W_le_rpow_mul_rpow_of_le D c₀' hc₀' q₂ (by rw [hq₂]; linarith)
  obtain ⟨C₂, hC₂⟩ := hW₂
  have hC₁' : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ max C₁ 0 * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (P₂.centralExponent.re + 1) *
        (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₁) :=
    fun X hX => (hC₁ X hX).trans (by gcongr; exact le_max_left _ _)
  have hC₂' : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, X.det ≠ 0 →
      ‖D.W X‖ ≤ max C₂ 0 * Real.sqrt (X 1 0 ^ 2 + X 1 1 ^ 2) ^ (P₂.centralExponent.re + 1) *
        (|X.det| / (X 1 0 ^ 2 + X 1 1 ^ 2)) ^ (-q₂) :=
    fun X hX => (hC₂ X hX).trans (by gcongr; exact le_max_left _ _)

  have hdomrow := exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod u₃ a₃ a psiInf hpsiInf
    ha D S hS c₀' hc₀'
  have hdom := hdomrow.1
  have hmeas := measurable_dualIntegrandR D u₃ a₃ (a : ℝ) ha' a psiInf hpsiInf S hS (realMat gInf)

  have hid := h1_integrand_eq_dualFr D u₃ a₃ a psiInf S gInf E hE σ t e hte s
  set K : ℝ := |(realMat gInf).det| ^ (u₃.re + 1) * (max (max C₁ 0) (max C₂ 0) * max C₄ 0) with hK
  set Mj : ℝ × ℝ → ℝ :=
    fun w => ∫ v : (Fin 2 → ℝ) × ℝ, majorant (a : ℝ) p u₃.re P₂.centralExponent.re q₁ q₂ N (w, v) with hMjdef

  have hbound : ∀ y x : ℝ, y ≠ 0 →
      (Integrable fun v : (Fin 2 → ℝ) × ℝ => majorant (a : ℝ) p u₃.re P₂.centralExponent.re q₁ q₂ N ((y, x), v)) →
      ‖dualFr D u₃ a₃ a psiInf S gInf t e s y x‖ ≤ K * |y| * Mj (y, x) := fun y x hy hMv =>
    norm_dualFr_le D u₃ a₃ a ha psiInf S gInf t e s c₀' hdom hmeas N C₄ hC₄ q₁ q₂ (max C₁ 0) (max C₂ 0)
      (le_max_right _ _) hC₁' hC₂' p hp y x hy hMv

  have hFr := measurable_dualFr D u₃ a₃ a psiInf S gInf t e s hmeas
  have hrcU : Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ) :=
    measurable_realCoord_units
  have hrcA : Measurable (realCoord : InfiniteAdeleRing ℚ → ℝ) := DirectArchZetaBound.continuous_realCoord.measurable
  have hFry : ∀ y : ℝ, Measurable fun x : ℝ => dualFr D u₃ a₃ a psiInf S gInf t e s y x := fun y =>
    hFr.comp (measurable_const.prodMk measurable_id)
  have h1f : AEStronglyMeasurable
      (fun q : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
        dualFr D u₃ a₃ a psiInf S gInf t e s (realCoord (q.1 : InfiniteAdeleRing ℚ)) (realCoord q.2))
      (ν_mul.prod ν_add) :=
    (hFr.comp ((hrcU.comp measurable_fst).prodMk (hrcA.comp measurable_snd))).aestronglyMeasurable

  have hae_y : ∀ᵐ y : ℝ,
      ((∀ᵐ x : ℝ, Integrable fun v : (Fin 2 → ℝ) × ℝ =>
          majorant (a : ℝ) p u₃.re P₂.centralExponent.re q₁ q₂ N ((y, x), v)) ∧
        Integrable fun x : ℝ => Mj (y, x)) ∧ y ≠ 0 := by
    have h₁ : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, Integrable fun v : (Fin 2 → ℝ) × ℝ =>
        majorant (a : ℝ) p u₃.re P₂.centralExponent.re q₁ q₂ N ((y, x), v) := Measure.ae_ae_of_ae_prod hMae
    have h₂ : ∀ᵐ y : ℝ, Integrable fun x : ℝ => Mj (y, x) := hMj.prod_right_ae
    have h₃ : ∀ᵐ y : ℝ, y ≠ 0 := by
      rw [ae_iff]
      simp
    exact (h₁.and h₂).and h₃

  have hscalar := DirectArchZetaBound.exists_haarScalar ν_mul
  obtain ⟨κ, -, hκ⟩ := hscalar
  have hae_transport : ∀ {Q : ℝ → Prop}, (∀ᵐ y : ℝ, Q y) →
      ∀ᵐ α : (InfiniteAdeleRing ℚ)ˣ ∂ν_mul, Q (realCoord (α : InfiniteAdeleRing ℚ)) := by
    intro Q hQ
    have hac : (ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) ≪
        (volume : Measure ℝ) := (withDensity_absolutelyContinuous _ _).smul_left _
    have hQ' : ∀ᵐ y ∂(Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ)) ν_mul),
        Q y := by
      rw [hκ]
      exact hac.ae_le hQ
    exact ae_of_ae_map hrcU.aemeasurable hQ'

  have hνadd := map_realCoord_nu_add a ν_add hν_add

  have hleg1 : ∀ᵐ α : (InfiniteAdeleRing ℚ)ˣ ∂ν_mul, Integrable
      (fun x : InfiniteAdeleRing ℚ => dualFr D u₃ a₃ a psiInf S gInf t e s (realCoord (α : InfiniteAdeleRing ℚ))
        (realCoord x)) ν_add := by
    refine hae_transport (Q := fun y : ℝ => Integrable
      (fun x : InfiniteAdeleRing ℚ => dualFr D u₃ a₃ a psiInf S gInf t e s y (realCoord x)) ν_add)
      (hae_y.mono fun y hy => ?_)
    obtain ⟨⟨hyx, hMjy⟩, hy0⟩ := hy
    have hline : Integrable (fun x : ℝ => dualFr D u₃ a₃ a psiInf S gInf t e s y x) volume :=
      (hMjy.const_mul (K * |y|)).mono' (hFry y).aestronglyMeasurable (hyx.mono fun x hx => hbound y x hy0 hx)
    have hmapped : Integrable (fun x : ℝ => dualFr D u₃ a₃ a psiInf S gInf t e s y x)
        (Measure.map (realCoord : InfiniteAdeleRing ℚ → ℝ) ν_add) := by
      rw [hνadd]
      exact hline.smul_measure ENNReal.ofReal_ne_top
    exact (integrable_map_measure (hFry y).aestronglyMeasurable hrcA.aemeasurable).1 hmapped

  have hleg2 : Integrable (fun α : (InfiniteAdeleRing ℚ)ˣ => ∫ x : InfiniteAdeleRing ℚ,
      ‖dualFr D u₃ a₃ a psiInf S gInf t e s (realCoord (α : InfiniteAdeleRing ℚ)) (realCoord x)‖ ∂ν_add) ν_mul := by
    set Φ : ℝ → ℝ := fun y => ∫ x : ℝ, ‖dualFr D u₃ a₃ a psiInf S gInf t e s y x‖ with hΦ
    set κa : ℝ := (ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2))).toReal with hκa
    have hΦeq : ∀ y : ℝ,
        ∫ x : InfiniteAdeleRing ℚ, ‖dualFr D u₃ a₃ a psiInf S gInf t e s y (realCoord x)‖ ∂ν_add = κa * Φ y := by
      intro y
      have hm : AEStronglyMeasurable (fun x : ℝ => ‖dualFr D u₃ a₃ a psiInf S gInf t e s y x‖)
          (Measure.map (realCoord : InfiniteAdeleRing ℚ → ℝ) ν_add) := (hFry y).norm.aestronglyMeasurable
      rw [← integral_map hrcA.aemeasurable hm, hνadd, integral_smul_measure, smul_eq_mul]
    simp_rw [hΦeq]
    refine Integrable.const_mul ?_ κa
    have hΦmeas : Measurable Φ := hFr.norm.stronglyMeasurable.integral_prod_right'.measurable
    have hν0 : ν_mul ≠ 0 := Measure.measure_univ_ne_zero.1 (isOpen_univ.measure_ne_zero ν_mul Set.univ_nonempty)
    have hiff := AbsInvDensity.integrable_comp_iff ν_mul _ hrcU κ hκ hν0 (fun y => (Φ y : ℂ))
      (Complex.measurable_ofReal.comp hΦmeas).aestronglyMeasurable
    have hreal : Integrable (fun y : ℝ => Φ y * |y|⁻¹) volume := by
      have hdomin : Integrable (fun y : ℝ => K * ∫ x : ℝ, Mj (y, x)) volume := hMj.integral_prod_left.const_mul K
      refine hdomin.mono' (hΦmeas.mul continuous_abs.measurable.inv).aestronglyMeasurable (hae_y.mono fun y hy => ?_)
      obtain ⟨⟨hyx, hMjy⟩, hy0⟩ := hy
      have hΦle : Φ y ≤ K * |y| * ∫ x : ℝ, Mj (y, x) := by
        rw [← integral_const_mul]
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) (hMjy.const_mul _)
          (hyx.mono fun x hx => hbound y x hy0 hx)
      have hΦ0 : 0 ≤ Φ y := integral_nonneg fun x => norm_nonneg _
      have hypos : 0 < |y| := abs_pos.2 hy0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hΦ0 (inv_nonneg.2 (abs_nonneg y)))]
      calc Φ y * |y|⁻¹ ≤ (K * |y| * ∫ x : ℝ, Mj (y, x)) * |y|⁻¹ := by gcongr
        _ = K * ∫ x : ℝ, Mj (y, x) := by field_simp
    have hcplx : Integrable (fun y : ℝ => (Φ y : ℂ) * ((|y| : ℝ) : ℂ)⁻¹) volume := by
      have hc : Integrable (fun y : ℝ => ((Φ y * |y|⁻¹ : ℝ) : ℂ)) volume := hreal.ofReal
      refine hc.congr (Filter.Eventually.of_forall fun y => ?_)
      push_cast
      ring
    have hre := (hiff.2 hcplx).re
    simpa using hre

  haveI : SFinite ν_add := by
    rw [hν_add]
    infer_instance
  have hmain : Integrable
      (fun q : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
        dualFr D u₃ a₃ a psiInf S gInf t e s (realCoord (q.1 : InfiniteAdeleRing ℚ)) (realCoord q.2))
      (ν_mul.prod ν_add) :=
    (integrable_prod_iff h1f).2 ⟨hleg1, hleg2⟩

  exact (congrArg (fun F => Integrable F (ν_mul.prod ν_add)) hid).mpr hmain

end DualArchZetaBound

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction in
open scoped Classical in
private theorem DualArchZetaBound.dual_half
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁)) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
      ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ),
                IsArchZeta31ConvergentAbove ν_mul ν_add
            (dualWhittakerFn3
              (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)))
            (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) (max c₁ (uR w₀ h₀).re + t.re) := by
  have _ := hdeg
  have _ := hμ
  have _ := huR
  have _ := huC
  have _ := hω
  have _ := haInf
  have _ := hP₂
  have _ := hc₀
  intro σ hσ t e ht gInf
  unfold IsArchZeta31ConvergentAbove
  intro s hs
  exact DualArchZetaBound.integrable_dual_zetaIntegrand P₂ D (uR w₀ h₀) (aR w₀ h₀)
    E hE a psiInf hpsiInf ν_add hν_add ν_mul ha S hS c₁ hc₁ σ hσ t e ht gInf s hs

end R9_seam_and_H1

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove.LanglandsTunnell.CubicInduction in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁)) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
      ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ),
        IsArchZeta30ConvergentAbove ν_mul
            (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
            (σ.comp E) 1 (max c₀ (-(uR w₀ h₀).re) - t.re) ∧
        IsArchZeta31ConvergentAbove ν_mul ν_add
            (dualWhittakerFn3
              (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf)))
            (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) (max c₁ (uR w₀ h₀).re + t.re) :=
  fun σ hσ t e ht gInf =>
    ⟨DirectArchZetaBound.direct_half K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf
        ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS c₀ hc₀ c₁ hc₁ σ hσ t e ht gInf,
     DualArchZetaBound.dual_half K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a aInf haInf psiInf hpsiInf ν_add
        hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS c₀ hc₀ c₁ hc₁ σ hσ t e ht gInf⟩

end S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_isArchZetaConvergentAbove (solution)
