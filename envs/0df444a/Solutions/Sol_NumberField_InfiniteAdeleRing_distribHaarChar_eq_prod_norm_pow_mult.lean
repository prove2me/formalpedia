-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a02aec24-cebb-5bfd-aef9-9b15a5004b09

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult

set_option Elab.async false

set_option autoImplicit false

open MeasureTheory Complex NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace ArchModS44

theorem map_mul_left_volume_real {c : ℝ} (hc : c ≠ 0) :
    (volume : Measure ℝ).map (fun x => c * x) = ‖c‖ₑ⁻¹ • volume := by
  have h := Real.map_volume_mul_left hc
  rw [show ((c * ·) : ℝ → ℝ) = fun x => c * x from rfl] at h
  rw [h, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hc), Real.enorm_eq_ofReal_abs]

theorem det_restrictScalars_mulLeft_complex (c : ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) = normSq c := by
  rw [← LinearMap.det_toMatrix basisOneI]
  have hM : (LinearMap.toMatrix basisOneI basisOneI ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))
      = !![c.re, -c.im; c.im, c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hM, Matrix.det_fin_two_of]
  simp [normSq_apply]

theorem map_mul_left_volume_complex {c : ℂ} (hc : c ≠ 0) :
    (volume : Measure ℂ).map (fun x => c * x) = (‖c‖ₑ ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) ≠ 0 := by
    rw [det_restrictScalars_mulLeft_complex]
    exact (normSq_pos.mpr hc).ne'
  have hfun : (fun x => c * x) = ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by
    ext x; simp [LinearMap.mulLeft_apply]
  have habs : |LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ)| = ‖c‖ ^ 2 := by
    rw [det_restrictScalars_mulLeft_complex, abs_of_nonneg (normSq_nonneg c), normSq_eq_norm_sq]
  calc (volume : Measure ℂ).map (fun x => c * x)
      = volume.map ⇑((LinearMap.mulLeft ℂ c).restrictScalars ℝ) := by rw [← hfun]
    _ = ENNReal.ofReal |(LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ))⁻¹| • volume :=
        Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet
    _ = (‖c‖ₑ ^ 2)⁻¹ • volume := by
        rw [abs_inv, habs, ENNReal.ofReal_inv_of_pos (pow_pos (norm_pos_iff.mpr hc) 2),
          ENNReal.ofReal_pow (norm_nonneg c), ofReal_norm]

theorem volume_image_mul_left_real {c : ℝ} (hc : c ≠ 0) {S : Set ℝ} (hS : MeasurableSet S) :
    volume ((fun x => c * x) '' S) = ‖c‖ₑ * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_real (inv_ne_zero hc)]
  simp [Measure.smul_apply, smul_eq_mul, enorm_inv, hc]

theorem volume_image_mul_left_complex {c : ℂ} (hc : c ≠ 0) {S : Set ℂ} (hS : MeasurableSet S) :
    volume ((fun x => c * x) '' S) = ‖c‖ₑ ^ 2 * volume S := by
  have himg : (fun x => c * x) '' S = (fun x => c⁻¹ * x) ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_mul_cancel_left₀ hc] using hx
    · intro hy
      exact ⟨c⁻¹ * y, hy, by field_simp⟩
  rw [himg, ← Measure.map_apply (measurable_const_mul _) hS,
    map_mul_left_volume_complex (inv_ne_zero hc)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [enorm_inv hc, ENNReal.inv_pow, inv_inv]

variable (F : Type) [Field F] [NumberField F]

@[reducible] def placeBorel (w : InfinitePlace F) : MeasurableSpace (w.Completion) := borel _

attribute [local instance] placeBorel

scoped instance placeBorelSpace (w : InfinitePlace F) : BorelSpace (w.Completion) := ⟨rfl⟩

variable {F}

def placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) : Measure (w.Completion) :=
  (volume : Measure ℝ).map (Completion.ringEquivRealOfIsReal hw).symm

def placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) : Measure (w.Completion) :=
  (volume : Measure ℂ).map (Completion.ringEquivComplexOfIsComplex hw).symm

variable (F) in
open Classical in

def placeMeasure (w : InfinitePlace F) : Measure (w.Completion) :=
  if hw : w.IsReal then placeMeasureReal hw
  else placeMeasureComplex (not_isReal_iff_isComplex.mp hw)

scoped instance isAddHaarMeasure_placeMeasureReal {w : InfinitePlace F} (hw : w.IsReal) :
    (placeMeasureReal hw).IsAddHaarMeasure := by
  unfold placeMeasureReal
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous
    (Completion.isometryEquivRealOfIsReal hw).continuous

scoped instance isAddHaarMeasure_placeMeasureComplex {w : InfinitePlace F} (hw : w.IsComplex) :
    (placeMeasureComplex hw).IsAddHaarMeasure := by
  unfold placeMeasureComplex
  exact AddEquiv.isAddHaarMeasure_map _
    ((Completion.ringEquivComplexOfIsComplex hw).symm : ℂ ≃+* w.Completion).toAddEquiv
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
    (Completion.isometryEquivComplexOfIsComplex hw).continuous

scoped instance secondCountable_completion (w : InfinitePlace F) :
    SecondCountableTopology (w.Completion) := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isEmbedding.secondCountableTopology

omit [NumberField F] in

theorem placeMeasureReal_image_mul {w : InfinitePlace F} (hw : w.IsReal)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureReal hw ((fun x => a * x) '' S) = ‖a‖ₑ * placeMeasureReal hw S := by
  set e := Completion.ringEquivRealOfIsReal hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureReal
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_real hea (hmeas_symm hS), henorm]

omit [NumberField F] in

theorem placeMeasureComplex_image_mul {w : InfinitePlace F} (hw : w.IsComplex)
    {a : w.Completion} (ha : a ≠ 0) {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasureComplex hw ((fun x => a * x) '' S) = ‖a‖ₑ ^ 2 * placeMeasureComplex hw S := by
  set e := Completion.ringEquivComplexOfIsComplex hw with he
  have hea : e a ≠ 0 := fun h => ha (by simpa using congrArg e.symm h)
  have hmeas_symm : Measurable (⇑e.symm) :=
    (Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.measurable
  have himgS : MeasurableSet ((fun x => a * x) '' S) := by
    have heq : (fun x => a * x) '' S = (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv '' S := rfl
    rw [heq, MeasurableEquiv.measurableSet_image]
    exact hS
  have hpre : ⇑e.symm ⁻¹' ((fun x => a * x) '' S) = (fun r => e a * r) '' (⇑e.symm ⁻¹' S) := by
    ext r
    constructor
    · rintro ⟨s, hs, hsr⟩
      refine ⟨e s, by simpa using hs, ?_⟩
      have := congrArg e hsr
      simpa [map_mul] using this
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.symm t, ht, by simp [map_mul]⟩
  have hnorm : ‖e a‖ = ‖a‖ := by
    have h0 : e (0 : w.Completion) = 0 := map_zero e
    calc ‖e a‖ = dist (e a) (e 0) := by rw [h0, dist_zero_right]
      _ = dist a 0 := (Completion.isometry_extensionEmbedding w).dist_eq a 0
      _ = ‖a‖ := dist_zero_right a
  have henorm : ‖e a‖ₑ = ‖a‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, hnorm]
  unfold placeMeasureComplex
  rw [Measure.map_apply hmeas_symm himgS, Measure.map_apply hmeas_symm hS, hpre,
    volume_image_mul_left_complex hea (hmeas_symm hS), henorm]

omit [NumberField F] in

theorem placeMeasure_image_mul (w : InfinitePlace F) {a : w.Completion} (ha : a ≠ 0)
    {S : Set (w.Completion)} (hS : MeasurableSet S) :
    placeMeasure F w ((fun x => a * x) '' S) = ‖a‖ₑ ^ w.mult * placeMeasure F w S := by
  unfold placeMeasure
  split
  · next hw =>
    rw [placeMeasureReal_image_mul hw ha hS,
      show w.mult = 1 from by simp [mult, hw], pow_one]
  · next hw =>
    rw [placeMeasureComplex_image_mul (not_isReal_iff_isComplex.mp hw) ha hS,
      show w.mult = 2 from by simp [mult, hw]]

scoped instance isAddHaarMeasure_placeMeasure (w : InfinitePlace F) :
    (placeMeasure F w).IsAddHaarMeasure := by
  unfold placeMeasure
  split
  · exact isAddHaarMeasure_placeMeasureReal _
  · exact isAddHaarMeasure_placeMeasureComplex _

scoped instance sigmaCompact_completion (w : InfinitePlace F) : SigmaCompactSpace (w.Completion) :=
  inferInstance

scoped instance sigmaFinite_placeMeasure (w : InfinitePlace F) : SigmaFinite (placeMeasure F w) :=
  inferInstance

variable (F) in

def archMeasure : Measure ((w : InfinitePlace F) → w.Completion) :=
  Measure.pi (fun w => placeMeasure F w)

scoped instance isFiniteMeasureOnCompacts_archMeasure : IsFiniteMeasureOnCompacts (archMeasure F) := by
  unfold archMeasure; infer_instance

scoped instance isOpenPosMeasure_archMeasure : (archMeasure F).IsOpenPosMeasure := by
  unfold archMeasure; infer_instance

scoped instance sigmaFinite_archMeasure : SigmaFinite (archMeasure F) := by
  unfold archMeasure; infer_instance

scoped instance isAddLeftInvariant_archMeasure : (archMeasure F).IsAddLeftInvariant := by
  constructor
  intro a
  have hmeas : Measurable (fun x : (w : InfinitePlace F) → w.Completion => a + x) :=
    measurable_const.add measurable_id
  refine Eq.symm (Measure.pi_eq fun B hB => ?_)
  have hpre : (fun x : (w : InfinitePlace F) → w.Completion => a + x) ⁻¹' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w + t) ⁻¹' B w) := by
    ext x
    simp [Set.mem_pi, Pi.add_apply]
  unfold archMeasure
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hB), hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  exact measure_preimage_add (placeMeasure F w) (a w) (B w)

scoped instance isAddHaarMeasure_archMeasure : (archMeasure F).IsAddHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := inferInstance
    toIsAddLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }

omit [NumberField F] in

theorem image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (B : (w : InfinitePlace F) → Set (w.Completion)) :
    (fun x => a * x) '' Set.pi Set.univ B
      = Set.pi Set.univ (fun w => (fun t => a w * t) '' B w) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro w _
    exact ⟨y w, hy w (Set.mem_univ w), rfl⟩
  · intro hx
    choose b hb hab using fun w => hx w (Set.mem_univ w)
    refine ⟨fun w => b w, fun w _ => hb w, ?_⟩
    funext w
    exact hab w

theorem archMeasure_image_mul_pi (a : (w : InfinitePlace F) → w.Completion)
    (ha : ∀ w, a w ≠ 0) (B : (w : InfinitePlace F) → Set (w.Completion))
    (hB : ∀ w, MeasurableSet (B w)) :
    archMeasure F ((fun x => a * x) '' Set.pi Set.univ B)
      = (∏ w, ‖a w‖ₑ ^ w.mult) * archMeasure F (Set.pi Set.univ B) := by
  rw [image_mul_pi a B]
  unfold archMeasure
  rw [Measure.pi_pi, Measure.pi_pi]
  calc ∏ w, placeMeasure F w ((fun t => a w * t) '' B w)
      = ∏ w, (‖a w‖ₑ ^ w.mult * placeMeasure F w (B w)) := by
        refine Finset.prod_congr rfl fun w _ => ?_
        exact placeMeasure_image_mul w (ha w) (hB w)
    _ = (∏ w, ‖a w‖ₑ ^ w.mult) * ∏ w, placeMeasure F w (B w) := Finset.prod_mul_distrib

scoped instance properSpace_completion₀ (w : InfinitePlace F) : ProperSpace (w.Completion) :=
  AdelicBox.properSpace_completion F w

omit [NumberField F] in
theorem placeMeasure_pos_closedBall (w : InfinitePlace F) :
    0 < placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) :=
  ((Metric.isOpen_ball (x := (0 : w.Completion)) (ε := 1)).measure_pos (placeMeasure F w)
    (Metric.nonempty_ball.mpr one_pos)).trans_le
    (measure_mono Metric.ball_subset_closedBall)

omit [NumberField F] in
theorem placeMeasure_closedBall_lt_top (w : InfinitePlace F) :
    placeMeasure F w (Metric.closedBall (0 : w.Completion) 1) < ⊤ :=
  (isCompact_closedBall (0 : w.Completion) 1).measure_lt_top

variable (F) in
@[reducible] def infMS : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))

attribute [local instance] infMS

scoped instance infBorelSpace : BorelSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))

variable (F) in
@[reducible] def finBorel : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

scoped instance secondCountable_infiniteAdeles : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

variable (F) in

def infMeasure : Measure (InfiniteAdeleRing F) := archMeasure F

scoped instance isAddHaarMeasure_infMeasure : (infMeasure F).IsAddHaarMeasure :=
  inferInstanceAs ((archMeasure F).IsAddHaarMeasure)

scoped instance sigmaFinite_infMeasure : SigmaFinite (infMeasure F) :=
  inferInstanceAs (SigmaFinite (archMeasure F))

variable (F) in

def refBox : Set (InfiniteAdeleRing F) :=
  (show Set ((w : InfinitePlace F) → w.Completion) from
    Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)

variable (F) in
theorem isCompact_refBox : IsCompact (refBox F) :=
  isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) 1

variable (F) in
theorem interior_refBox_nonempty : (interior (refBox F)).Nonempty := by
  have hopen : IsOpen (show Set (InfiniteAdeleRing F) from
      (Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)) :=
    isOpen_set_pi Set.finite_univ fun w _ => Metric.isOpen_ball
  have hsub : (show Set (InfiniteAdeleRing F) from
      (Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)) ⊆ refBox F :=
    Set.pi_mono fun w _ => Metric.ball_subset_closedBall
  have hmem : (0 : InfiniteAdeleRing F) ∈ (show Set (InfiniteAdeleRing F) from
      (Set.univ.pi fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1)) :=
    fun w _ => Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)
  exact ⟨_, interior_maximal hsub hopen hmem⟩

variable (F) in
theorem infMeasure_refBox_ne_top : infMeasure F (refBox F) ≠ ⊤ := by
  show archMeasure F _ ≠ ⊤
  unfold archMeasure refBox
  rw [Measure.pi_pi]
  exact (ENNReal.prod_lt_top fun w _ => placeMeasure_closedBall_lt_top w).ne

variable (F) in
theorem infMeasure_refBox_ne_zero : infMeasure F (refBox F) ≠ 0 := by
  show archMeasure F _ ≠ 0
  unfold archMeasure refBox
  rw [Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.mpr fun w _ => (placeMeasure_pos_closedBall w).ne'

set_option synthInstance.maxHeartbeats 640000 in
scoped instance regular_infMeasure : (infMeasure F).Regular :=
  Measure.regular_of_isAddLeftInvariant (μ := infMeasure F)
    (K := refBox F) (isCompact_refBox F) (interior_refBox_nonempty F) (infMeasure_refBox_ne_top F)

omit [NumberField F] in
theorem arch_unit_ne_zero (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    (a : InfiniteAdeleRing F) w ≠ 0 := by
  intro h0
  have h := congrArg (fun x : InfiniteAdeleRing F => x w) a.mul_inv
  rw [show ((a : InfiniteAdeleRing F) * (↑a⁻¹ : InfiniteAdeleRing F)) w
      = (a : InfiniteAdeleRing F) w * (↑a⁻¹ : InfiniteAdeleRing F) w from rfl, h0, zero_mul] at h
  exact zero_ne_one h

theorem distribHaarChar_infiniteAdeleRing (a : (InfiniteAdeleRing F)ˣ) :
    (distribHaarChar (InfiniteAdeleRing F) a : ℝ) = ∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult := by
  classical
  set aArch : (w : InfinitePlace F) → w.Completion :=
    (show (w : InfinitePlace F) → w.Completion from (a : InfiniteAdeleRing F)) with haArch
  have haw : ∀ w, aArch w ≠ 0 := fun w => arch_unit_ne_zero a w
  have hsplit : (show Set ((w : InfinitePlace F) → w.Completion) from (a • refBox F)) =
      (fun x : (w : InfinitePlace F) → w.Completion => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) := by
    rw [← Set.image_smul]
    rfl
  have harch : archMeasure F ((fun x => aArch * x) ''
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1))
      = (∏ w, ‖aArch w‖ₑ ^ w.mult) * archMeasure F
        (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) :=
    archMeasure_image_mul_pi aArch haw
      (fun w => Metric.closedBall (0 : w.Completion) 1) (fun w => measurableSet_closedBall)
  have hμgs : infMeasure F (a • refBox F)
      = ((∏ w : InfinitePlace F, ‖aArch w‖₊ ^ w.mult : ℝ≥0) : ℝ≥0∞) * infMeasure F (refBox F) := by
    show archMeasure F (show Set ((w : InfinitePlace F) → w.Completion) from (a • refBox F)) =
      _ * archMeasure F (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)
    rw [hsplit, harch]
    congr 1
    rw [ENNReal.coe_finsetProd]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ENNReal.coe_pow, enorm_eq_nnnorm]
  have key := distribHaarChar_eq_of_measure_smul_eq_mul (μ := infMeasure F)
    (s := refBox F) (g := a) (infMeasure_refBox_ne_zero F) (infMeasure_refBox_ne_top F) hμgs
  rw [key]
  push_cast [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  rfl

end ArchModS44
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.ArchModS44"

end
p2m_reactivate "P2MW.S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.ArchModS44"

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (a : (InfiniteAdeleRing K)ˣ) :
    (distribHaarChar (InfiniteAdeleRing K) a : ℝ) = ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult := by
  exact ArchModS44.distribHaarChar_infiniteAdeleRing a

end S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult (solution)
