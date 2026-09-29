-- Prove2me | solution 1 for NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c35bcd2b-3e1a-5bd9-a652-6106b5f6eccf

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped Pointwise ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace S30ShellLaw

section Norm

variable (M : Type) [Field M] [NumberField M]

noncomputable abbrev prin : Subgroup (AdeleRing (𝓞 M) M)ˣ :=
  (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* AdeleRing (𝓞 M) M)).range

noncomputable def logNorm (y : (AdeleRing (𝓞 M) M)ˣ) : ℝ :=
  Real.log (NumberField.TateGlobal.ideleNorm M y)

theorem prin_eq : prin M = M4aHerbrand.principalIdeles (𝓞 M) M := rfl

scoped instance countable_prin : Countable (prin M) := by
  haveI : Countable M := Countable.of_equiv _ (Module.Free.chooseBasis ℚ M).equivFun.toEquiv.symm
  haveI : Countable Mˣ := Units.val_injective.countable
  exact (Set.countable_range _).to_subtype

variable {M}

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm M (1 : (AdeleRing (𝓞 M) M)ˣ) = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (1 : (AdeleRing (𝓞 M) M)ˣ) 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (1 : (AdeleRing (𝓞 M) M)ˣ)).ne'
    (h.symm.trans (mul_one _).symm)

theorem ideleNorm_inv (u : (AdeleRing (𝓞 M) M)ˣ) :
    NumberField.TateGlobal.ideleNorm M u⁻¹ = (NumberField.TateGlobal.ideleNorm M u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel, ideleNorm_one]

theorem det_globalPoints_diagOne (η : Mˣ) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 M) M (diagOne η)) =
      Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* AdeleRing (𝓞 M) M) η := by
  apply Units.ext
  show Matrix.det ((algebraMap M (AdeleRing (𝓞 M) M)).mapMatrix
      ((diagOne η : GL (Fin 2) M) : Matrix (Fin 2) (Fin 2) M)) = algebraMap M (AdeleRing (𝓞 M) M) η
  rw [← RingHom.map_det]
  congr 1
  show Matrix.det (Matrix.diagonal ![(η : M), 1]) = (η : M)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem ideleNorm_map_algebraMap (η : Mˣ) :
    NumberField.TateGlobal.ideleNorm M
      (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* AdeleRing (𝓞 M) M) η) = 1 := by
  rw [← det_globalPoints_diagOne]
  exact AutomorphicForm.ideleNorm_det_globalPoints _

theorem ideleNorm_prin (c : prin M) :
    NumberField.TateGlobal.ideleNorm M (c : (AdeleRing (𝓞 M) M)ˣ) = 1 := by
  obtain ⟨η, hη⟩ := MonoidHom.mem_range.mp c.2
  rw [← hη]
  exact ideleNorm_map_algebraMap η

theorem logNorm_mul (u y : (AdeleRing (𝓞 M) M)ˣ) : logNorm M (u * y) = logNorm M u + logNorm M y := by
  unfold logNorm
  rw [NumberField.TateGlobal.ideleNorm_mul]
  exact Real.log_mul (NumberField.TateGlobal.ideleNorm_pos u).ne' (NumberField.TateGlobal.ideleNorm_pos y).ne'

theorem logNorm_prin (c : prin M) : logNorm M (c : (AdeleRing (𝓞 M) M)ˣ) = 0 := by
  unfold logNorm
  rw [ideleNorm_prin, Real.log_one]

variable (M) in
theorem continuous_logNorm : Continuous (logNorm M) :=
  (NumberField.TateGlobal.continuous_ideleNorm M).log fun y => (NumberField.TateGlobal.ideleNorm_pos y).ne'

variable (M) in

theorem exists_logNorm_eq (t : ℝ) : ∃ u : (AdeleRing (𝓞 M) M)ˣ, logNorm M u = t := by
  obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq M
  set x : ℝ≥0 := ⟨Real.exp t, (Real.exp_pos t).le⟩ with hx
  have hxcoe : (x : ℝ) = Real.exp t := rfl
  have hne : x ≠ 0 := by
    intro h
    have h' := congrArg (fun z : ℝ≥0 => (z : ℝ)) h
    simp only [hxcoe, NNReal.coe_zero] at h'
    exact (Real.exp_pos t).ne' h'
  refine ⟨s (Units.mk0 x hne), ?_⟩
  unfold logNorm
  rw [hs, Units.val_mk0, hxcoe, Real.log_exp]

theorem preimage_smul_prin (c : prin M) (A : Set ℝ) :
    (fun y : (AdeleRing (𝓞 M) M)ˣ => c • y) ⁻¹' (logNorm M ⁻¹' A) = logNorm M ⁻¹' A := by
  ext y
  simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, logNorm_mul, logNorm_prin, zero_add]

theorem preimage_mul_eq (u : (AdeleRing (𝓞 M) M)ˣ) (A : Set ℝ) :
    (fun y : (AdeleRing (𝓞 M) M)ˣ => u * y) ⁻¹' (logNorm M ⁻¹' A) =
      logNorm M ⁻¹' ((fun s : ℝ => logNorm M u + s) ⁻¹' A) := by
  ext y
  simp only [Set.mem_preimage, logNorm_mul]

end Norm

section Measure

variable {M : Type} [Field M] [NumberField M]
  [MeasurableSpace (AdeleRing (𝓞 M) M)ˣ] [BorelSpace (AdeleRing (𝓞 M) M)ˣ]

variable (M) in
theorem measurable_logNorm : Measurable (logNorm M) := (continuous_logNorm M).measurable

variable (ν : Measure (AdeleRing (𝓞 M) M)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 M) M)ˣ}

scoped instance smulInvariantMeasure_units : SMulInvariantMeasure (AdeleRing (𝓞 M) M)ˣ (AdeleRing (𝓞 M) M)ˣ ν :=
  ⟨fun c s _ => measure_preimage_mul ν c s⟩

theorem measure_preimage_mul_inter_eq (hΩ : IsFundamentalDomain (prin M) Ω ν) (u : (AdeleRing (𝓞 M) M)ˣ)
    {B : Set (AdeleRing (𝓞 M) M)ˣ} (hB : MeasurableSet B)
    (hBinv : ∀ c : prin M, (fun y : (AdeleRing (𝓞 M) M)ˣ => c • y) ⁻¹' B = B) :
    ν ((fun y => u * y) ⁻¹' B ∩ Ω) = ν (B ∩ Ω) := by
  have h1 : (fun y => u * y) ⁻¹' B ∩ Ω = (fun y => u * y) ⁻¹' (B ∩ u • Ω) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, ← smul_eq_mul, Set.smul_mem_smul_set_iff]
  rw [h1, measure_preimage_mul]
  exact (hΩ.measure_set_eq (hΩ.smul_of_comm u) hB hBinv).symm

theorem measure_preimage_preimage_add_inter_eq (hΩ : IsFundamentalDomain (prin M) Ω ν) (t : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ν (logNorm M ⁻¹' ((fun s : ℝ => t + s) ⁻¹' A) ∩ Ω) = ν (logNorm M ⁻¹' A ∩ Ω) := by
  obtain ⟨u, hu⟩ := exists_logNorm_eq M t
  rw [← hu, ← preimage_mul_eq]
  exact measure_preimage_mul_inter_eq ν hΩ u (measurable_logNorm M hA) (fun c => preimage_smul_prin c A)

theorem measure_preimage_Icc_inter_lt_top (hΩ : IsFundamentalDomain (prin M) Ω ν) (s t : ℝ) :
    ν (logNorm M ⁻¹' Set.Icc s t ∩ Ω) < ⊤ := by
  obtain ⟨D, -, hDF, htemp⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
      M ν
  obtain ⟨k, hint⟩ := htemp 0
  change IsFundamentalDomain (prin M) D ν at hDF
  have hZm : MeasurableSet (logNorm M ⁻¹' Set.Icc s t) := measurable_logNorm M measurableSet_Icc
  rw [hΩ.measure_set_eq hDF hZm (fun c => preimage_smul_prin c _)]
  set ε : ℝ := min (Real.exp s) (Real.exp t)⁻¹ ^ k with hε
  have hε0 : 0 < ε := pow_pos (lt_min (Real.exp_pos s) (inv_pos.mpr (Real.exp_pos t))) k
  have hsub : logNorm M ⁻¹' Set.Icc s t ⊆ {z : (AdeleRing (𝓞 M) M)ˣ |
      ε ≤ ‖min (NumberField.TateGlobal.ideleNorm M z) (NumberField.TateGlobal.ideleNorm M z)⁻¹ ^ k *
        NumberField.TateGlobal.ideleNorm M z ^ (0 : ℝ)‖} := by
    intro z hz
    obtain ⟨h₁, h₂⟩ := hz
    have hz0 : 0 < NumberField.TateGlobal.ideleNorm M z := NumberField.TateGlobal.ideleNorm_pos z
    have h₁' : Real.exp s ≤ NumberField.TateGlobal.ideleNorm M z := (Real.le_log_iff_exp_le hz0).mp h₁
    have h₂' : NumberField.TateGlobal.ideleNorm M z ≤ Real.exp t := (Real.log_le_iff_le_exp hz0).mp h₂
    have hmin : min (Real.exp s) (Real.exp t)⁻¹
        ≤ min (NumberField.TateGlobal.ideleNorm M z) (NumberField.TateGlobal.ideleNorm M z)⁻¹ :=
      le_min ((min_le_left _ _).trans h₁') ((min_le_right _ _).trans (inv_anti₀ hz0 h₂'))
    have hpow : ε ≤ min (NumberField.TateGlobal.ideleNorm M z) (NumberField.TateGlobal.ideleNorm M z)⁻¹ ^ k :=
      pow_le_pow_left₀ (le_min (Real.exp_pos s).le (inv_pos.mpr (Real.exp_pos t)).le) hmin k
    show ε ≤ ‖_‖
    rw [Real.rpow_zero, mul_one]
    exact hpow.trans (le_abs_self _)
  calc ν (logNorm M ⁻¹' Set.Icc s t ∩ D) = ν.restrict D (logNorm M ⁻¹' Set.Icc s t) :=
        (Measure.restrict_apply hZm).symm
    _ ≤ ν.restrict D {z | ε ≤ ‖min (NumberField.TateGlobal.ideleNorm M z)
          (NumberField.TateGlobal.ideleNorm M z)⁻¹ ^ k * NumberField.TateGlobal.ideleNorm M z ^ (0 : ℝ)‖} :=
        measure_mono hsub
    _ < ⊤ := Integrable.measure_norm_ge_lt_top hint hε0

theorem measure_preimage_Ioo_inter_pos (hΩ : IsFundamentalDomain (prin M) Ω ν) :
    0 < ν (logNorm M ⁻¹' Set.Ioo 0 1 ∩ Ω) := by
  set U : Set (AdeleRing (𝓞 M) M)ˣ := logNorm M ⁻¹' Set.Ioo 0 1 with hU
  have hUo : IsOpen U := (continuous_logNorm M).isOpen_preimage _ isOpen_Ioo
  have hUm : MeasurableSet U := hUo.measurableSet
  obtain ⟨u, hu⟩ := exists_logNorm_eq M (1 / 2)
  have hUne : U.Nonempty := ⟨u, by show logNorm M u ∈ Set.Ioo 0 1; rw [hu]; norm_num⟩
  have hUpos : 0 < ν U := hUo.measure_pos ν hUne
  rw [pos_iff_ne_zero] at hUpos ⊢
  intro h0
  apply hUpos
  rw [hΩ.measure_eq_tsum' U]
  refine ENNReal.tsum_eq_zero.mpr fun g => ?_
  rw [← hΩ.measure_set_eq (hΩ.smul_of_comm g) hUm (fun c => preimage_smul_prin c _)]
  exact h0

noncomputable def logPush (Ω : Set (AdeleRing (𝓞 M) M)ˣ) : Measure ℝ :=
  Measure.map (logNorm M) (ν.restrict Ω)

omit [ν.IsHaarMeasure] in
theorem logPush_apply {A : Set ℝ} (hA : MeasurableSet A) : logPush ν Ω A = ν (logNorm M ⁻¹' A ∩ Ω) := by
  unfold logPush
  rw [Measure.map_apply (measurable_logNorm M) hA, Measure.restrict_apply (measurable_logNorm M hA)]

theorem isFiniteMeasureOnCompacts_logPush (hΩ : IsFundamentalDomain (prin M) Ω ν) :
    IsFiniteMeasureOnCompacts (logPush ν Ω) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [Real.closedBall_eq_Icc] at hR
  calc logPush ν Ω K ≤ logPush ν Ω (Set.Icc (0 - R) (0 + R)) := measure_mono hR
    _ = ν (logNorm M ⁻¹' Set.Icc (0 - R) (0 + R) ∩ Ω) := logPush_apply ν measurableSet_Icc
    _ < ⊤ := measure_preimage_Icc_inter_lt_top ν hΩ _ _

theorem isAddLeftInvariant_logPush (hΩ : IsFundamentalDomain (prin M) Ω ν) :
    (logPush ν Ω).IsAddLeftInvariant := by
  refine ⟨fun t => Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply (measurable_const_add t) hA, logPush_apply ν (measurable_const_add t hA),
    logPush_apply ν hA]
  exact measure_preimage_preimage_add_inter_eq ν hΩ t hA

theorem shell_law (hΩ : IsFundamentalDomain (prin M) Ω ν) :
    ∃ V : ℝ, 0 < V ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ν.real (Ω ∩ {y | NumberField.TateGlobal.ideleNorm M y ∈ Set.Icc a b}) = V * (Real.log b - Real.log a) := by
  haveI := isFiniteMeasureOnCompacts_logPush ν hΩ
  haveI := isAddLeftInvariant_logPush ν hΩ
  set c : ℝ≥0 := (logPush ν Ω).addHaarScalarFactor volume with hc
  have hμ : logPush ν Ω = c • (volume : Measure ℝ) := Measure.isAddLeftInvariant_eq_smul _ _
  have happ : ∀ s t : ℝ, s ≤ t → ν (logNorm M ⁻¹' Set.Icc s t ∩ Ω) = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) := by
    intro s t hst
    rw [← logPush_apply ν measurableSet_Icc, hμ, Measure.smul_apply, Real.volume_Icc, ENNReal.smul_def,
      smul_eq_mul]
  have hcpos : 0 < (c : ℝ) := by
    have h1 : ν (logNorm M ⁻¹' Set.Ioo 0 1 ∩ Ω) = (c : ℝ≥0∞) := by
      rw [← logPush_apply ν measurableSet_Ioo, hμ, Measure.smul_apply, Real.volume_Ioo, ENNReal.smul_def,
        smul_eq_mul, sub_zero, ENNReal.ofReal_one, mul_one]
    have h2 := measure_preimage_Ioo_inter_pos ν hΩ
    rw [h1, ENNReal.coe_pos] at h2
    exact NNReal.coe_pos.mpr h2
  refine ⟨c, hcpos, fun a b ha hab => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hset : Ω ∩ {y | NumberField.TateGlobal.ideleNorm M y ∈ Set.Icc a b} =
      logNorm M ⁻¹' Set.Icc (Real.log a) (Real.log b) ∩ Ω := by
    rw [Set.inter_comm]
    congr 1
    ext y
    have hy : 0 < NumberField.TateGlobal.ideleNorm M y := NumberField.TateGlobal.ideleNorm_pos y
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_preimage, logNorm, Real.log_le_log_iff ha hy,
      Real.log_le_log_iff hy hb]
  rw [measureReal_def, hset, happ _ _ (Real.log_le_log ha hab), ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log ha hab))]

end Measure

end S30ShellLaw
p2m_reactivate "P2MW.S_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq.S30ShellLaw"

namespace S30HypWeight

open NumberField.AdelicHeight AutomorphicForm.WindowedSiegel

section Local

variable {K₀ : Type*} [NormedField K₀]

theorem rowMaxNorm_scalar_shape_mul {s : GL (Fin 2) K₀} {z : K₀}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = z)
    (g : GL (Fin 2) K₀) :
    rowMaxNorm ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K₀) := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  have e10 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 0
      = z * (g : Matrix (Fin 2) (Fin 2) K₀) 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  have e11 : ((s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀)) 1 1
      = z * (g : Matrix (Fin 2) (Fin 2) K₀) 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [hcoe, e10, e11, norm_mul, norm_mul, mul_max_of_nonneg _ _ (norm_nonneg z)]

theorem finLocalHeight_scalar_shape_mul {s : GL (Fin 2) K₀} {z : K₀} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K₀) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K₀) 1 1 = z)
    (g : GL (Fin 2) K₀) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)
      = (s : Matrix (Fin 2) (Fin 2) K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K₀).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hz2 : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  unfold finLocalHeight
  rw [rowMaxNorm_scalar_shape_mul h10 h11 g, hcoe, Matrix.det_mul, hdets, norm_mul, norm_pow, mul_pow,
    mul_div_mul_left _ _ hz2]

end Local
p2m_reactivate "P2MW.S_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq.S30ShellLaw"

section Adelic

variable (L : Type) [Field L] [NumberField L]

theorem adelicHeight_scalar_shape_mul {s : AutomorphicForm.AdelicGL2 (𝓞 L) L} {ζ : AdeleRing (𝓞 L) L}
    (h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = ζ)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = ζ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (s * g) = adelicHeight L g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)).det = ζ * ζ := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11, mul_zero, sub_zero]
  have hζ : IsUnit ζ := by
    have hu := Matrix.isUnits_det_units s
    rw [hdets] at hu
    exact (IsUnit.mul_iff.mp hu).1
  unfold adelicHeight
  rw [map_mul, map_mul]
  have harch : archHeight L (glArch (𝓞 L) L s * glArch (𝓞 L) L g) = archHeight L (glArch (𝓞 L) L g) := by
    refine archHeight_scalar_entries_mul L (z := ζ.1) ?_ ?_ ?_ ?_ ?_ (glArch (𝓞 L) L g)
    · intro w
      exact ((hζ.map (adeleArch (𝓞 L) L)).map (archEval L w)).ne_zero
    · rw [glArch_apply, h00]
    · rw [glArch_apply, h01]
      rfl
    · rw [glArch_apply, h10]
      rfl
    · rw [glArch_apply, h11]
  have hfin : finHeight L (glFin (𝓞 L) L s * glFin (𝓞 L) L g) = finHeight L (glFin (𝓞 L) L g) := by
    unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_shape_mul (z := ζ.2 v) ?_ ?_ ?_ ?_ ?_
      (finComponent (𝓞 L) L v (glFin (𝓞 L) L g))
    · exact ((hζ.map (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))).map
        (finAdeleEval (𝓞 L) L v)).ne_zero
    · rw [finComponent_apply, glFin_apply, h00]
    · rw [finComponent_apply, glFin_apply, h01]
      rfl
    · rw [finComponent_apply, glFin_apply, h10]
      rfl
    · rw [finComponent_apply, glFin_apply, h11]
  rw [harch, hfin]

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 L) L)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (AutomorphicForm.centralScalar (𝓞 L) L z * g) = adelicHeight L g := by
  have hcoe : ((AutomorphicForm.centralScalar (𝓞 L) L z : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
  refine adelicHeight_scalar_shape_mul L (ζ := (z : AdeleRing (𝓞 L) L)) ?_ ?_ ?_ ?_ g <;>
    simp [hcoe, Matrix.scalar_apply]

theorem adelicWeyl_mul_diagOne (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.adelicWeyl (𝓞 L) L * diagOne z =
      AutomorphicForm.centralScalar (𝓞 L) L z * diagOne z⁻¹ * AutomorphicForm.adelicWeyl (𝓞 L) L := by
  have hw : ((AutomorphicForm.adelicWeyl (𝓞 L) L : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = !![0, 1; 1, 0] := by
    ext i j
    rw [AutomorphicForm.adelicWeyl, AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map_apply,
      AutomorphicForm.gl2Weyl_val]
    fin_cases i <;> fin_cases j <;> simp
  have hc : ((AutomorphicForm.centralScalar (𝓞 L) L z : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) := rfl
  have hd : ∀ u : (AdeleRing (𝓞 L) L)ˣ, ((diagOne u : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.diagonal ![(u : AdeleRing (𝓞 L) L), 1] :=
    fun u => rfl
  apply Units.ext
  show ((AutomorphicForm.adelicWeyl (𝓞 L) L : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) * (diagOne z : AutomorphicForm.AdelicGL2 (𝓞 L) L) =
    (AutomorphicForm.centralScalar (𝓞 L) L z : AutomorphicForm.AdelicGL2 (𝓞 L) L) *
      ((diagOne z⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) *
      (AutomorphicForm.adelicWeyl (𝓞 L) L : AutomorphicForm.AdelicGL2 (𝓞 L) L)
  rw [hw, hc, hd, hd, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem adelicHeight_adelicWeyl_mul_diagOne_mul (z : (AdeleRing (𝓞 L) L)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (diagOne z * g)) =
      (NumberField.TateGlobal.ideleNorm L z)⁻¹ * adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g) := by
  rw [← mul_assoc, adelicWeyl_mul_diagOne, mul_assoc, mul_assoc, adelicHeight_centralScalar_mul,
    NumberField.AdelicHeight.adelicHeight_diagOne_mul, S30ShellLaw.ideleNorm_inv]

end Adelic
p2m_reactivate "P2MW.S_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq.S30ShellLaw"

end S30HypWeight
p2m_reactivate "P2MW.S_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq.S30ShellLaw"

open NumberField.AdelicHeight in

theorem solution
    (M L : Type) [Field M] [NumberField M] [Field L] [NumberField L]
    [MeasurableSpace (AdeleRing (𝓞 M) M)ˣ] [BorelSpace (AdeleRing (𝓞 M) M)ˣ] (νZM : Measure (AdeleRing (𝓞 M) M)ˣ)
    [νZM.IsHaarMeasure] (ΩM : Set (AdeleRing (𝓞 M) M)ˣ)
    (hΩM : IsFundamentalDomain
      (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* AdeleRing (𝓞 M) M)).range ΩM νZM)
    (θ : (AdeleRing (𝓞 M) M)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (e : ℕ) (he : 0 < e)
    (hθn : ∀ y, NumberField.TateGlobal.ideleNorm L (θ y) = NumberField.TateGlobal.ideleNorm M y ^ e) :
    ∃ V : ℝ, 0 < V ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        νZM.real (ΩM ∩ {y | NumberField.TateGlobal.ideleNorm M y ∈ Set.Icc a b}) = V * (Real.log b - Real.log a)) ∧
      ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (R : ℝ),
        adelicHeight L x * adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * x) ≤ Real.exp (2 * R) →
        IntegrableOn (fun y : (AdeleRing (𝓞 M) M)ˣ => (1 : ℝ)
            - Set.indicator {y : (AdeleRing (𝓞 M) M)ˣ | Real.exp R < adelicHeight L (diagOne (θ y) * x)}
                (fun _ => (1 : ℝ)) y
            - Set.indicator {y : (AdeleRing (𝓞 M) M)ˣ |
                Real.exp R < adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (diagOne (θ y) * x))}
              (fun _ => (1 : ℝ)) y) ΩM νZM ∧
        ∫ y in ΩM, ((1 : ℝ)
            - Set.indicator {y : (AdeleRing (𝓞 M) M)ˣ | Real.exp R < adelicHeight L (diagOne (θ y) * x)}
                (fun _ => (1 : ℝ)) y
            - Set.indicator {y : (AdeleRing (𝓞 M) M)ˣ |
                Real.exp R < adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (diagOne (θ y) * x))}
              (fun _ => (1 : ℝ)) y) ∂νZM =
          V * (2 * R - Real.log (adelicHeight L x)
            - Real.log (adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * x))) / e := by
  obtain ⟨V, hV, h1⟩ := S30ShellLaw.shell_law νZM hΩM
  refine ⟨V, hV, h1, fun x R hR => ?_⟩

  set h₁ : ℝ := adelicHeight L x with hh₁
  set h₂ : ℝ := adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * x) with hh₂
  have h₁pos : 0 < h₁ := adelicHeight_pos x
  have h₂pos : 0 < h₂ := adelicHeight_pos _
  have hepos : (0 : ℝ) < e := Nat.cast_pos.mpr he
  set α : ℝ := (Real.log h₂ - R) / e with hα
  set β : ℝ := (R - Real.log h₁) / e with hβ
  have hαβ : α ≤ β := by
    rw [hα, hβ]
    refine div_le_div_of_nonneg_right ?_ hepos.le
    have hlog : Real.log h₁ + Real.log h₂ ≤ 2 * R := by
      rw [← Real.log_mul h₁pos.ne' h₂pos.ne', ← Real.log_exp (2 * R)]
      exact Real.log_le_log (mul_pos h₁pos h₂pos) hR
    linarith
  obtain ⟨S, hS⟩ : ∃ S : Set (AdeleRing (𝓞 M) M)ˣ, S = S30ShellLaw.logNorm M ⁻¹' Set.Icc α β := ⟨_, rfl⟩
  have hSm : MeasurableSet S := hS ▸ S30ShellLaw.measurable_logNorm M measurableSet_Icc
  have hSy : ∀ y, y ∈ S ↔ α ≤ S30ShellLaw.logNorm M y ∧ S30ShellLaw.logNorm M y ≤ β := fun y => by
    rw [hS, Set.mem_preimage, Set.mem_Icc]

  have hA : ∀ y : (AdeleRing (𝓞 M) M)ˣ,
      Real.exp R < adelicHeight L (diagOne (θ y) * x) ↔ β < S30ShellLaw.logNorm M y := by
    intro y
    have hn : 0 < NumberField.TateGlobal.ideleNorm M y := NumberField.TateGlobal.ideleNorm_pos y
    rw [NumberField.AdelicHeight.adelicHeight_diagOne_mul, hθn, ← hh₁,
      ← Real.log_lt_log_iff (Real.exp_pos R) (mul_pos (pow_pos hn e) h₁pos), Real.log_exp,
      Real.log_mul (pow_pos hn e).ne' h₁pos.ne', Real.log_pow, hβ, div_lt_iff₀ hepos, S30ShellLaw.logNorm]
    constructor <;> intro h <;> linarith
  have hB : ∀ y : (AdeleRing (𝓞 M) M)ˣ,
      Real.exp R < adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (diagOne (θ y) * x)) ↔
        S30ShellLaw.logNorm M y < α := by
    intro y
    have hn : 0 < NumberField.TateGlobal.ideleNorm M y := NumberField.TateGlobal.ideleNorm_pos y
    rw [S30HypWeight.adelicHeight_adelicWeyl_mul_diagOne_mul, hθn, ← hh₂,
      ← Real.log_lt_log_iff (Real.exp_pos R) (mul_pos (inv_pos.mpr (pow_pos hn e)) h₂pos), Real.log_exp,
      Real.log_mul (inv_pos.mpr (pow_pos hn e)).ne' h₂pos.ne', Real.log_inv, Real.log_pow, hα,
      lt_div_iff₀ hepos, S30ShellLaw.logNorm]
    constructor <;> intro h <;> linarith

  have key : (fun y : (AdeleRing (𝓞 M) M)ˣ => (1 : ℝ)
      - Set.indicator {y : (AdeleRing (𝓞 M) M)ˣ | Real.exp R < adelicHeight L (diagOne (θ y) * x)}
          (fun _ => (1 : ℝ)) y
      - Set.indicator {y : (AdeleRing (𝓞 M) M)ˣ |
          Real.exp R < adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (diagOne (θ y) * x))}
        (fun _ => (1 : ℝ)) y) = S.indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hA, hB]
    by_cases hβy : β < S30ShellLaw.logNorm M y
    · rw [if_pos hβy, if_neg (not_lt.mpr (hαβ.trans hβy.le)),
        Set.indicator_of_notMem (fun h => (not_le.mpr hβy) ((hSy y).mp h).2)]
      norm_num
    · by_cases hαy : S30ShellLaw.logNorm M y < α
      · rw [if_neg hβy, if_pos hαy, Set.indicator_of_notMem (fun h => (not_le.mpr hαy) ((hSy y).mp h).1)]
        norm_num
      · rw [if_neg hβy, if_neg hαy, Set.indicator_of_mem ((hSy y).mpr ⟨not_lt.mp hαy, not_lt.mp hβy⟩)]
        norm_num
  have hfin : νZM (S ∩ ΩM) < ⊤ := hS ▸ S30ShellLaw.measure_preimage_Icc_inter_lt_top νZM hΩM α β
  have hres : νZM.restrict ΩM S = νZM (S ∩ ΩM) := Measure.restrict_apply hSm

  have hval : (νZM (S ∩ ΩM)).toReal = V * (β - α) := by
    have hset : S ∩ ΩM = ΩM ∩ {y | NumberField.TateGlobal.ideleNorm M y ∈ Set.Icc (Real.exp α) (Real.exp β)} := by
      rw [Set.inter_comm]
      congr 1
      ext y
      have hn : 0 < NumberField.TateGlobal.ideleNorm M y := NumberField.TateGlobal.ideleNorm_pos y
      simp only [hS, Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq, S30ShellLaw.logNorm,
        Real.le_log_iff_exp_le hn, Real.log_le_iff_le_exp hn]
    have h := h1 (Real.exp α) (Real.exp β) (Real.exp_pos α) (Real.exp_le_exp.mpr hαβ)
    rw [Real.log_exp, Real.log_exp, ← hset, measureReal_def] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [key, IntegrableOn, integrable_indicator_iff hSm]
    exact integrableOn_const (by rw [hres]; exact hfin.ne)
  · rw [key, integral_indicator_const (1 : ℝ) hSm, smul_eq_mul, mul_one, measureReal_def, hres, hval, hα, hβ]
    field_simp
    ring

#print axioms solution

end S_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
end P2MW
export P2MW.S_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq (solution)
