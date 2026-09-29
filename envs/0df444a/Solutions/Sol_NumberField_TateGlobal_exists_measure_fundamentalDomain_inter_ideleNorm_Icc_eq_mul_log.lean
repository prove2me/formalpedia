-- Prove2me | solution 1 for NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/449c55aa-4f99-5dc9-a010-6332706d7544

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set NumberField IsDedekindDomain NumberField.TateGlobal
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace T8SlabVolume

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant]
  (Γ : Subgroup G) [Countable Γ]
  (φ : G → ℝ) (s : ℝ → G)

theorem isFundamentalDomain_smul_of_comm {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) (g : G)
    (hg : ∀ γ ∈ Γ, γ * g = g * γ) : IsFundamentalDomain Γ (g • Ω) μ := by
  refine hΩ.image_of_equiv (MulAction.toPerm g)
    (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving (Equiv.refl _) fun γ x => ?_
  show g • ((γ : G) * x) = (γ : G) * (g • x)
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, hg γ γ.2]

def slabMeasure (Ω : Set G) : Measure ℝ := Measure.map φ (μ.restrict Ω)

variable {μ φ}

theorem slabMeasure_apply (hφ : Measurable φ) (Ω : Set G) {B : Set ℝ} (hB : MeasurableSet B) :
    slabMeasure μ φ Ω B = μ (φ ⁻¹' B ∩ Ω) := by
  rw [slabMeasure, Measure.map_apply hφ hB, Measure.restrict_apply (hφ hB)]

theorem slabMeasure_mono (Ω : Set G) {B B' : Set ℝ} (h : B ⊆ B') :
    slabMeasure μ φ Ω B ≤ slabMeasure μ φ Ω B' := measure_mono h

variable {Γ s}

theorem preimage_smul_preimage_eq (hφmul : ∀ x y, φ (x * y) = φ x + φ y)
    (hΓ : ∀ γ ∈ Γ, φ γ = 0) (B : Set ℝ) (γ : Γ) :
    (fun x : G => γ • x) ⁻¹' (φ ⁻¹' B) = φ ⁻¹' B := by
  ext x
  simp only [mem_preimage, Subgroup.smul_def, smul_eq_mul, hφmul, hΓ γ γ.2, zero_add]

theorem slabMeasure_preimage_const_add (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) (t : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    slabMeasure μ φ Ω ((fun x => t + x) ⁻¹' B) = slabMeasure μ φ Ω B := by
  have hB' : MeasurableSet ((fun x => t + x) ⁻¹' B) := measurable_const_add t hB
  rw [slabMeasure_apply hφ Ω hB', slabMeasure_apply hφ Ω hB]

  have hpre : φ ⁻¹' ((fun x => t + x) ⁻¹' B) = (fun h => s t * h) ⁻¹' (φ ⁻¹' B) := by
    ext x
    simp only [mem_preimage, hφmul, hs]
  have hΩ' : IsFundamentalDomain Γ (s t • Ω) μ := isFundamentalDomain_smul_of_comm μ Γ hΩ (s t) (hcomm t)
  have hinj : Function.Injective fun h : G => s t * h := mul_right_injective (s t)
  have hpreΩ : (fun h => s t * h) ⁻¹' (s t • Ω) = Ω := by
    rw [← image_smul]
    exact hinj.preimage_image Ω
  calc μ (φ ⁻¹' ((fun x => t + x) ⁻¹' B) ∩ Ω)
      = μ ((fun h => s t * h) ⁻¹' (φ ⁻¹' B ∩ s t • Ω)) := by
        rw [preimage_inter, hpre, hpreΩ]
    _ = μ (φ ⁻¹' B ∩ s t • Ω) := measure_preimage_mul μ (s t) _
    _ = μ (φ ⁻¹' B ∩ Ω) :=
        hΩ'.measure_set_eq hΩ (hφ hB) (preimage_smul_preimage_eq hφmul hΓ B)

theorem isAddLeftInvariant_slabMeasure (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) :
    (slabMeasure μ φ Ω).IsAddLeftInvariant := by
  refine ⟨fun t => Measure.ext fun B hB => ?_⟩
  rw [Measure.map_apply (measurable_const_add t) hB]
  exact slabMeasure_preimage_const_add hφ hφmul hΓ hs hcomm hΩ t hB

theorem isFiniteMeasureOnCompacts_slabMeasure (hφ : Measurable φ) {Ω : Set G}
    (hfin : ∀ R : ℝ, μ (φ ⁻¹' Icc (-R) R ∩ Ω) < ⊤) :
    IsFiniteMeasureOnCompacts (slabMeasure μ φ Ω) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hK.isBounded
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
  calc slabMeasure μ φ Ω K ≤ slabMeasure μ φ Ω (Icc (-R) R) := measure_mono hR
    _ = μ (φ ⁻¹' Icc (-R) R ∩ Ω) := slabMeasure_apply hφ Ω measurableSet_Icc
    _ < ⊤ := hfin R

theorem exists_measure_preimage_Icc_inter_eq (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω₀ : Set G} (hΩ₀ : IsFundamentalDomain Γ Ω₀ μ)
    (hfin : ∀ R : ℝ, μ (φ ⁻¹' Icc (-R) R ∩ Ω₀) < ⊤) :
    ∃ c : ℝ≥0, (μ ≠ 0 → c ≠ 0) ∧
      ∀ Ω : Set G, IsFundamentalDomain Γ Ω μ → ∀ a b : ℝ,
        μ (φ ⁻¹' Icc a b ∩ Ω) = (c : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  set m : Measure ℝ := slabMeasure μ φ Ω₀ with hm
  haveI : m.IsAddLeftInvariant := isAddLeftInvariant_slabMeasure hφ hφmul hΓ hs hcomm hΩ₀
  haveI : IsFiniteMeasureOnCompacts m := isFiniteMeasureOnCompacts_slabMeasure hφ hfin
  have hIcc : ∀ a b : ℝ, m (Icc a b) = (m.addHaarScalarFactor volume : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
    intro a b
    have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure m volume
      (s := Icc a b) (by rw [closure_Icc]; exact isCompact_Icc)
    rw [h, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul]
  refine ⟨m.addHaarScalarFactor volume, fun hμ hc => ?_, fun Ω hΩ a b => ?_⟩
  ·
    apply hΩ₀.measure_ne_zero hμ
    have huniv : m univ = 0 := by
      have hcov : (univ : Set ℝ) = ⋃ n : ℕ, Icc (-(n : ℝ)) n := by
        refine (eq_univ_of_forall fun x => mem_iUnion.2 ?_).symm
        obtain ⟨n, hn⟩ := exists_nat_ge |x|
        exact ⟨n, abs_le.1 hn⟩
      rw [hcov]
      refine measure_iUnion_null fun n => ?_
      rw [hIcc, hc, ENNReal.coe_zero, zero_mul]
    have := slabMeasure_apply (μ := μ) hφ Ω₀ MeasurableSet.univ
    rw [preimage_univ, univ_inter] at this
    rw [← this]
    exact huniv
  · rw [← hΩ₀.measure_set_eq hΩ (hφ measurableSet_Icc) (preimage_smul_preimage_eq hφmul hΓ _),
      ← slabMeasure_apply hφ Ω₀ measurableSet_Icc]
    exact hIcc a b

theorem measure_preimage_inter_lt_top_of_subset_iUnion_smul [IsFiniteMeasureOnCompacts μ]
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) {A C : Set G} (hC : IsCompact C)
    (hAC : A ⊆ ⋃ γ : Γ, γ • C) : μ (A ∩ Ω) < ⊤ := by
  calc μ (A ∩ Ω) ≤ μ ((⋃ γ : Γ, γ • C) ∩ Ω) := measure_mono (inter_subset_inter_left _ hAC)
    _ = μ (⋃ γ : Γ, γ • C ∩ Ω) := by rw [iUnion_inter]
    _ ≤ ∑' γ : Γ, μ (γ • C ∩ Ω) := measure_iUnion_le _
    _ = μ C := (hΩ.measure_eq_tsum C).symm
    _ < ⊤ := hC.measure_lt_top

end Abstract

section Ideles

variable (F : Type) [Field F] [NumberField F]

abbrev principalUnits : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

theorem countable_numberField : Countable F :=
  (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_units_numberField : Countable Fˣ := by
  haveI := countable_numberField F
  exact Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective

scoped instance countable_principalUnits : Countable (principalUnits F) := by
  haveI := countable_units_numberField F
  exact (MonoidHom.rangeRestrict_surjective _).countable

theorem principalUnits_eq_principalIdeles :
    principalUnits F = M4aHerbrand.principalIdeles (𝓞 F) F := rfl

def logNorm (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ := Real.log (ideleNorm F x)

theorem logNorm_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : logNorm F (x * y) = logNorm F x + logNorm F y := by
  simp only [logNorm, ideleNorm_mul]
  exact Real.log_mul (ideleNorm_pos x).ne' (ideleNorm_pos y).ne'

theorem continuous_logNorm : Continuous (logNorm F) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).log fun x => (ideleNorm_pos x).ne'

theorem ideleNorm_principal (a : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  simp only [ideleNorm]
  rw [RingHom.toMonoidHom_eq_coe] at h
  rw [h]
  rfl

theorem logNorm_principal (γ : (AdeleRing (𝓞 F) F)ˣ) (hγ : γ ∈ principalUnits F) : logNorm F γ = 0 := by
  obtain ⟨a, rfl⟩ := hγ
  simp [logNorm, ideleNorm_principal]

theorem mem_normOneIdeles_iff_logNorm (x : (AdeleRing (𝓞 F) F)ˣ) :
    x ∈ normOneIdeles F ↔ logNorm F x = 0 := by
  rw [mem_normOneIdeles_iff, logNorm]
  constructor
  · intro h; rw [h, Real.log_one]
  · intro h
    exact Real.eq_one_of_pos_of_log_eq_zero (ideleNorm_pos x) h

theorem isClosed_normOneIdeles : IsClosed (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have : (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) = logNorm F ⁻¹' {0} := by
    ext x; exact mem_normOneIdeles_iff_logNorm F x
  rw [this]
  exact isClosed_singleton.preimage (continuous_logNorm F)

scoped instance locallyCompactSpace_normOneIdeles : LocallyCompactSpace (normOneIdeles F) :=
  (isClosed_normOneIdeles F).isClosedEmbedding_subtypeVal.locallyCompactSpace

def basePlace : InfinitePlace F := Classical.arbitrary _

variable {F} in
open scoped Classical in

def toCompletion (w : InfinitePlace F) (r : ℝ) : w.Completion :=
  if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm r
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm r

variable {F} in
theorem isometry_ringEquiv_symm {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B)
    (he : Isometry e) : Isometry e.symm := fun a b => by
  rw [← he.edist_eq, e.apply_symm_apply, e.apply_symm_apply]

variable {F} in
theorem isometry_toCompletion (w : InfinitePlace F) : Isometry (toCompletion w) := by
  by_cases hw : w.IsReal
  · have h : Isometry (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm :=
      isometry_ringEquiv_symm _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
    intro a b
    simp only [toCompletion, dif_pos hw]
    exact h.edist_eq a b
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h : Isometry (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm :=
      isometry_ringEquiv_symm _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
    intro a b
    simp only [toCompletion, dif_neg hw]
    exact (h.comp Complex.isometry_ofReal).edist_eq a b

variable {F} in
theorem toCompletion_zero (w : InfinitePlace F) : toCompletion w 0 = 0 := by
  by_cases hw : w.IsReal
  · simp only [toCompletion, dif_pos hw, map_zero]
  · simp only [toCompletion, dif_neg hw, Complex.ofReal_zero, map_zero]

variable {F} in
theorem norm_toCompletion (w : InfinitePlace F) (r : ℝ) : ‖toCompletion w r‖ = |r| := by
  rw [(isometry_toCompletion w).norm_map_of_map_zero (toCompletion_zero w), Real.norm_eq_abs]

variable {F} in
theorem continuous_toCompletion (w : InfinitePlace F) : Continuous (toCompletion w) :=
  (isometry_toCompletion w).continuous

variable {F} in
theorem toCompletion_ne_zero (w : InfinitePlace F) {r : ℝ} (hr : r ≠ 0) : toCompletion w r ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_toCompletion]
  exact abs_ne_zero.mpr hr

variable {F} in

def expUnit (w : InfinitePlace F) (t : ℝ) : (w.Completion)ˣ :=
  Units.mk0 (toCompletion w (Real.exp (t / w.mult))) (toCompletion_ne_zero w (Real.exp_pos _).ne')

variable {F} in
theorem norm_expUnit (w : InfinitePlace F) (t : ℝ) :
    ‖((expUnit w t : (w.Completion)ˣ) : w.Completion)‖ = Real.exp (t / w.mult) := by
  rw [expUnit, Units.val_mk0, norm_toCompletion, abs_of_pos (Real.exp_pos _)]

variable {F} in
theorem continuous_expUnit (w : InfinitePlace F) : Continuous (expUnit w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_toCompletion w).comp (Real.continuous_exp.comp (continuous_id.div_const _))
  · have : (fun t => ((expUnit w t)⁻¹ : (w.Completion)ˣ) : ℝ → w.Completion) =
        fun t => (toCompletion w (Real.exp (t / w.mult)))⁻¹ := by
      funext t; rfl
    rw [this]
    exact ((continuous_toCompletion w).comp
      (Real.continuous_exp.comp (continuous_id.div_const _))).inv₀
      fun t => toCompletion_ne_zero w (Real.exp_pos _).ne'

def archSection (t : ℝ) : (AdeleRing (𝓞 F) F)ˣ :=
  archUnitHom (basePlace F) (expUnit (basePlace F) t)

theorem continuous_archSection : Continuous (archSection F) := by
  classical
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : Continuous fun t => ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) :
        (basePlace F).Completion) := Units.continuous_val.comp (continuous_expUnit _)
    have : (Units.val ∘ archSection F) = fun t =>
        ((Function.update (1 : InfiniteAdeleRing F) (basePlace F)
          ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) : (basePlace F).Completion), 1) :
            InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
      funext t; rfl
    rw [this]
    exact (continuous_const.update (basePlace F) h1).prodMk continuous_const
  · have h1 : Continuous fun t => (((expUnit (basePlace F) t)⁻¹ : ((basePlace F).Completion)ˣ) :
        (basePlace F).Completion) := Units.continuous_coe_inv.comp (continuous_expUnit _)
    have : (fun t => ((archSection F t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : ℝ → AdeleRing (𝓞 F) F) = fun t =>
        ((Function.update (1 : InfiniteAdeleRing F) (basePlace F)
          (((expUnit (basePlace F) t)⁻¹ : ((basePlace F).Completion)ˣ) : (basePlace F).Completion), 1) :
            InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
      funext t; rfl
    rw [this]
    exact (continuous_const.update (basePlace F) h1).prodMk continuous_const

theorem ideleNorm_archSection (t : ℝ) : ideleNorm F (archSection F t) = Real.exp t := by
  classical
  have h2 : ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl
  have h := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F
    (archSection F t) h2
  simp only [ideleNorm]
  rw [h, Finset.prod_eq_single (basePlace F)]
  · rw [show ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 (basePlace F) =
        ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) : (basePlace F).Completion) from
        NumberField.AdelicVolume.archCentralUnit_fst_self _ _,
      norm_expUnit, ← Real.exp_nat_mul, mul_div_cancel₀]
    exact Nat.cast_ne_zero.mpr (InfinitePlace.mult_pos (w := basePlace F)).ne'
  · intro w _ hw
    rw [show ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 from
      NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hw, norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem logNorm_archSection (t : ℝ) : logNorm F (archSection F t) = t := by
  rw [logNorm, ideleNorm_archSection, Real.log_exp]

theorem exists_isCompact_forall_exists_mul_eq {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [LocallyCompactSpace A] (Γ' : Subgroup A) [CompactSpace (A ⧸ Γ')] :
    ∃ K : Set A, IsCompact K ∧ ∀ z : A, ∃ γ : A, γ ∈ Γ' ∧ ∃ k ∈ K, γ * k = z := by
  have hπo : IsOpenMap (QuotientGroup.mk : A → A ⧸ Γ') := QuotientGroup.isOpenMap_coe
  have hK : ∀ y : A, ∃ K : Set A, IsCompact K ∧ K ∈ nhds y := fun y => exists_compact_mem_nhds y
  choose K hKc hKn using hK
  have hcov : (univ : Set (A ⧸ Γ')) ⊆ ⋃ y : A, QuotientGroup.mk '' interior (K y) := by
    intro q _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact mem_iUnion.2 ⟨y, y, mem_interior_iff_mem_nhds.2 (hKn y), rfl⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun y : A => QuotientGroup.mk '' interior (K y)) (fun y => hπo _ isOpen_interior) hcov
  refine ⟨⋃ y ∈ T, K y, T.isCompact_biUnion fun y _ => hKc y, fun z => ?_⟩
  obtain ⟨y, hyT, hy⟩ : ∃ y ∈ T, (QuotientGroup.mk z : A ⧸ Γ') ∈ QuotientGroup.mk '' interior (K y) := by
    simpa only [mem_iUnion, exists_prop] using hT (mem_univ (QuotientGroup.mk z))
  obtain ⟨u, hu, hπu⟩ := hy
  have hmem : u⁻¹ * z ∈ Γ' := QuotientGroup.eq.mp hπu
  refine ⟨u⁻¹ * z, hmem, u, mem_iUnion₂.2 ⟨y, hyT, interior_subset hu⟩, ?_⟩
  rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

theorem exists_isCompact_normOneIdeles_subset_iUnion_smul :
    ∃ K₁ : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact K₁ ∧
      (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) ⊆ ⋃ γ : principalUnits F, γ • K₁ := by
  haveI := NumberField.TateGlobal.compactSpace_normOneIdeleClass F
  obtain ⟨K, hK, hcov⟩ := exists_isCompact_forall_exists_mul_eq
    ((M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F))
  refine ⟨((↑) : normOneIdeles F → (AdeleRing (𝓞 F) F)ˣ) '' K, hK.image continuous_subtype_val,
    fun z hz => ?_⟩
  obtain ⟨γ, hγ, k, hk, hγk⟩ := hcov ⟨z, hz⟩
  rw [Subgroup.mem_subgroupOf] at hγ
  refine mem_iUnion.2 ⟨⟨(γ : (AdeleRing (𝓞 F) F)ˣ), hγ⟩, mem_smul_set.2 ⟨(k : (AdeleRing (𝓞 F) F)ˣ),
    ⟨k, hk, rfl⟩, ?_⟩⟩
  rw [Subgroup.smul_def, smul_eq_mul]
  exact congrArg Subtype.val hγk

theorem exists_isCompact_slab_subset_iUnion_smul (R : ℝ) :
    ∃ C : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact C ∧
      logNorm F ⁻¹' Icc (-R) R ⊆ ⋃ γ : principalUnits F, γ • C := by
  obtain ⟨K₁, hK₁, hcov⟩ := exists_isCompact_normOneIdeles_subset_iUnion_smul F
  refine ⟨K₁ * archSection F '' Icc (-R) R,
    hK₁.mul (isCompact_Icc.image (continuous_archSection F)), fun x hx => ?_⟩

  set t := logNorm F x with ht
  have hz : x * (archSection F t)⁻¹ ∈ (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) := by
    show x * (archSection F t)⁻¹ ∈ normOneIdeles F
    rw [mem_normOneIdeles_iff_logNorm, logNorm_mul,
      show logNorm F (archSection F t)⁻¹ = -t by
        have := logNorm_mul F (archSection F t) (archSection F t)⁻¹
        rw [mul_inv_cancel, logNorm_archSection] at this
        have h1 : logNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 0 := by simp [logNorm, ideleNorm, map_one]
        linarith]
    simp [ht]
  obtain ⟨γ, hγ⟩ := mem_iUnion.1 (hcov hz)
  obtain ⟨k, hk, hγk⟩ := mem_smul_set.1 hγ
  refine mem_iUnion.2 ⟨γ, mem_smul_set.2 ⟨k * archSection F t, mul_mem_mul hk ⟨t, hx, rfl⟩, ?_⟩⟩
  rw [Subgroup.smul_def, smul_eq_mul, ← mul_assoc, ← smul_eq_mul (γ : (AdeleRing (𝓞 F) F)ˣ) k,
    ← Subgroup.smul_def, hγk, inv_mul_cancel_right]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

theorem exists_measure_inter_ideleNorm_mem_Icc_eq :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain (principalUnits F) Ω ν →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          ν (Ω ∩ {x | ideleNorm F x ∈ Icc a b}) = C * ENNReal.ofReal (Real.log (b / a)) := by
  by_cases hex : ∃ Ω₀ : Set (AdeleRing (𝓞 F) F)ˣ, IsFundamentalDomain (principalUnits F) Ω₀ ν
  swap
  · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun Ω hΩ => absurd ⟨Ω, hΩ⟩ hex⟩
  obtain ⟨Ω₀, hΩ₀⟩ := hex
  have hφ : Measurable (logNorm F) := (continuous_logNorm F).measurable
  have hfin : ∀ R : ℝ, ν (logNorm F ⁻¹' Icc (-R) R ∩ Ω₀) < ⊤ := fun R => by
    obtain ⟨C, hC, hcov⟩ := exists_isCompact_slab_subset_iUnion_smul F R
    exact measure_preimage_inter_lt_top_of_subset_iUnion_smul hΩ₀ hC hcov
  obtain ⟨c, hc0, hc⟩ := exists_measure_preimage_Icc_inter_eq (μ := ν) (Γ := principalUnits F)
    (φ := logNorm F) (s := archSection F) hφ (logNorm_mul F) (logNorm_principal F)
    (logNorm_archSection F) (fun t γ _ => mul_comm _ _) hΩ₀ hfin
  have hν : ν ≠ 0 :=
    Measure.measure_univ_ne_zero.1 (IsOpen.measure_ne_zero ν isOpen_univ univ_nonempty)
  refine ⟨c, ENNReal.coe_ne_zero.2 (hc0 hν), ENNReal.coe_ne_top, fun Ω hΩ a b ha hab => ?_⟩
  have hset : Ω ∩ {x | ideleNorm F x ∈ Icc a b} = logNorm F ⁻¹' Icc (Real.log a) (Real.log b) ∩ Ω := by
    rw [inter_comm]
    congr 1
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_Icc, logNorm]
    rw [Real.log_le_log_iff ha (ideleNorm_pos x), Real.log_le_log_iff (ideleNorm_pos x) (ha.trans_le hab)]
  rw [hset, hc Ω hΩ, Real.log_div (ha.trans_le hab).ne' ha.ne']

end Ideles

end T8SlabVolume
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log.T8SlabVolume"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log.T8SlabVolume"

open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          ν (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) :=
  T8SlabVolume.exists_measure_inter_ideleNorm_mem_Icc_eq F ν

end S_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log (solution)
