-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/eccfac11-d3f1-58d6-bda6-3a0b32a0dfc4

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_isLocalZeta31ConvergentAbove_dualWhittakerFn3_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_torusJacquetValueFn_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

section

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace WeylTranslateZeta
open LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem range_units_val_eq :
    Set.range (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, Units.val_mk0 hx⟩

private theorem measurableEmbedding_units_val :
    letI := localBorel K v
    MeasurableEmbedding (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hrange := range_units_val_eq K v
  have hne : ∀ x : Set.range (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K),
      (x : v.adicCompletion K) ≠ 0 := by
    rintro ⟨_, w, rfl⟩
    exact w.ne_zero
  refine MeasurableEmbedding.of_measurable_inverse_on_range
    (g := fun x => Units.mk0 (x : v.adicCompletion K) (hne x)) (comap_measurable _) ?_ ?_ ?_
  · rw [hrange]
    exact isClosed_singleton.measurableSet.compl
  · exact measurable_comap_iff.2 measurable_subtype_coe
  · intro u
    exact Units.ext (Units.val_mk0 _)

private theorem mulMeasure_restrict_compl_zero (μ : @Measure (v.adicCompletion K) (localBorel K v)) :
    letI := localBorel K v
    (mulMeasure μ).restrict {0}ᶜ = mulMeasure μ := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hc : MeasurableSet ({0}ᶜ : Set (v.adicCompletion K)) := isClosed_singleton.measurableSet.compl
  unfold mulMeasure
  rw [restrict_withDensity hc, Measure.restrict_restrict hc, Set.inter_self]

private theorem integral_comap_units_val (μ : @Measure (v.adicCompletion K) (localBorel K v))
    (F : v.adicCompletion K → ℂ) :
    letI := localBorel K v
    ∫ a : (v.adicCompletion K)ˣ, F (a : v.adicCompletion K) ∂(Measure.comap Units.val (mulMeasure μ)) =
      ∫ x, F x ∂(mulMeasure μ) := by
  letI := localBorel K v
  have hemb := measurableEmbedding_units_val K v
  rw [← hemb.integral_map F, hemb.map_comap (mulMeasure μ), range_units_val_eq K v,
    mulMeasure_restrict_compl_zero K v μ]

private theorem localZeta_eq_integral_units (μ : @Measure (v.adicCompletion K) (localBorel K v))
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    letI := localBorel K v
    localZeta μ f χ s =
      ∫ a : (v.adicCompletion K)ˣ,
        f a * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ s
          ∂(Measure.comap Units.val (mulMeasure μ)) := by
  letI := localBorel K v
  rw [localZeta, ← integral_comap_units_val K v μ]
  simp only [charExt_coe_units]

section Scaling

end Scaling

section MeasureClasses

private theorem selfDualConst_ne_zero :
    ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (StandardAddChar.psiLocal K v) : ℝ) / 2)) ≠ 0 := by
  have hq : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h
  exact (NNReal.rpow_pos hq).ne'

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul (Measure.addHaarMeasure (integersPositiveCompacts K v))
    (selfDualConst_ne_zero K v)

private theorem sFinite_selfDualHaarAt :
    letI := localBorel K v
    SFinite (selfDualHaarAt K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  unfold selfDualHaarAt
  infer_instance

end MeasureClasses

end WeylTranslateZeta
end

section

open Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 x y z * (iotaGL (diagUnitGL2 a) * antidiagonal3 v)

private theorem torusCellPoint_coe (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    (torusCellPoint v x y z a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; y, 1, 0; z, x, (a : v.adicCompletion ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusCellPoint, antidiagonal3_coe, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    gl3Entry v (torusCellPoint v x y z a) i j = !![1, 0, 0; y, 1, 0; z, x, (a : v.adicCompletion ℚ)] i j := by
  rw [gl3Entry, torusCellPoint_coe]

private theorem cornerEntry_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (torusCellPoint v x y z a) = z := by
  simp [cornerEntry, gl3Entry_torusCellPoint]

private theorem lowerMinor_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (torusCellPoint v x y z a) = x * y - z := by
  simp only [lowerMinor, gl3Entry_torusCellPoint]
  simp
  ring

private theorem outerMinor_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    outerMinor v (torusCellPoint v x y z a) = (a : v.adicCompletion ℚ) * y := by
  simp only [outerMinor, gl3Entry_torusCellPoint]
  simp
  ring

private theorem gl3Det_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    gl3Det v (torusCellPoint v x y z a) = (a : v.adicCompletion ℚ) := by
  rw [gl3Det, torusCellPoint_coe, Matrix.det_fin_three]
  simp

private theorem cellRatio_torusCellPoint (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    cellRatio v (torusCellPoint v x y z a) =
      ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (x * y - z)] := by
  rw [cellRatio, cornerEntry_torusCellPoint, outerMinor_torusCellPoint, lowerMinor_torusCellPoint]
  simp [gl3Entry_torusCellPoint]

private theorem cellValue_torusCellPoint (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x y z : v.adicCompletion ℚ)
    (a : (v.adicCompletion ℚ)ˣ) :
    cellValue v χ (torusCellPoint v x y z a) =
      charExt (χ 0) ((a : v.adicCompletion ℚ) / (x * y - z)) * charExt (χ 1) ((x * y - z) / z) * charExt (χ 2) z *
        ((‖(a : v.adicCompletion ℚ) / (x * y - z)‖ / ‖z‖ : ℝ) : ℂ) := by
  rw [cellValue, gl3Det_torusCellPoint, lowerMinor_torusCellPoint, cornerEntry_torusCellPoint]

section DualPoint

end DualPoint

end WeylTranslateZeta
end

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar
open scoped Topology

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def torusTranslate (a : (v.adicCompletion ℚ)ˣ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (iotaGL (diagUnitGL2 a) * antidiagonal3 v) (cellSectionOf v ν Φ)

open Classical in

private noncomputable def torusFn : v.adicCompletion ℚ → ℂ := fun t =>
  if h : t = 0 then 0 else
    jacquetValue v (torusTranslate v ν Φ (Units.mk0 t h)) * ((modulus t : ℝ) : ℂ)⁻¹

private theorem torusFn_zero : torusFn v ν Φ 0 = 0 := by
  simp [torusFn]

private theorem torusFn_coe_units (a : (v.adicCompletion ℚ)ˣ) :
    torusFn v ν Φ a = jacquetValue v (torusTranslate v ν Φ a) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp [torusFn, a.ne_zero]

private theorem jacquetTruncated3_torusTranslate (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    jacquetTruncated3 v c (torusTranslate v ν Φ a) =
      ∫ p in unipotentBall3 v c,
        psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (torusCellPoint v p.1 p.2.1 p.2.2 a)
          ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  unfold jacquetTruncated3
  congr 1

private noncomputable def torusIntegrand (a : (v.adicCompletion ℚ)ˣ)
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) : ℂ :=
  psiLocal ℚ v (-(p.1 + p.2.1)) * cellSectionOf v ν Φ (torusCellPoint v p.1 p.2.1 p.2.2 a)

private theorem jacquetTruncated3_torusTranslate_eq_integral (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    jacquetTruncated3 v c (torusTranslate v ν Φ a) =
      ∫ p in unipotentBall3 v c, torusIntegrand v ν Φ a p ∂(jacquetHaar3 v) :=
  jacquetTruncated3_torusTranslate v ν Φ c a

private theorem exists_invariance_radius (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → Φ q = Φ p := by
  classical

  have hultra : ∀ a b c : v.adicCompletion ℚ, dist a c ≤ max (dist a b) (dist b c) :=
    fun a b c => IsUltrametricDist.dist_triangle_max a b c
  have hK : IsCompact (tsupport Φ) := hΦc

  have hball : ∀ x : tsupport Φ, ∃ ε : ℝ, 0 < ε ∧ ∀ q, dist q (x : Fin 3 → v.adicCompletion ℚ) < ε → Φ q = Φ x := by
    intro x
    have hopen : IsOpen {q : Fin 3 → v.adicCompletion ℚ | Φ q = Φ x} := hΦl.isOpen_fiber (Φ x)
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen (x : Fin 3 → v.adicCompletion ℚ) rfl
    exact ⟨ε, hε, fun q hq => hsub hq⟩
  choose ε hεpos hε using hball
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover (fun x : tsupport Φ => Metric.ball (x : Fin 3 → v.adicCompletion ℚ) (ε x))
    (fun x => Metric.isOpen_ball) fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hεpos ⟨y, hy⟩)⟩

  obtain ⟨r, hr, hrJ⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ J, r < ε x := by
    by_cases hJne : J.Nonempty
    · have hinf : 0 < J.inf' hJne ε := (Finset.lt_inf'_iff hJne).mpr fun y _ => hεpos y
      exact ⟨J.inf' hJne ε / 2, half_pos hinf, fun x hx => (half_lt_self hinf).trans_le (Finset.inf'_le ε hx)⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hJne⟩
  refine ⟨r, hr, ?_⟩

  have key : ∀ p q : Fin 3 → v.adicCompletion ℚ, (∀ i, ‖q i - p i‖ ≤ r) → p ∈ tsupport Φ → Φ q = Φ p := by
    intro p q hpq hp
    obtain ⟨x, hxJ, hpx⟩ := Set.mem_iUnion₂.mp (hJ hp)
    have hpx' : dist p (x : Fin 3 → v.adicCompletion ℚ) < ε x := hpx
    have hqx : dist q (x : Fin 3 → v.adicCompletion ℚ) < ε x := by
      rw [dist_pi_lt_iff (hεpos x)] at hpx' ⊢
      intro i
      refine (hultra (q i) (p i) ((x : Fin 3 → v.adicCompletion ℚ) i)).trans_lt (max_lt ?_ (hpx' i))
      rw [dist_eq_norm]
      exact (hpq i).trans_lt (hrJ x hxJ)
    rw [hε x q hqx, hε x p hpx']
  intro p q hpq
  by_cases hp : p ∈ tsupport Φ
  · exact key p q hpq hp
  by_cases hq : q ∈ tsupport Φ
  · refine (key q p (fun i => ?_) hq).symm
    rw [norm_sub_rev]
    exact hpq i
  rw [image_eq_zero_of_notMem_tsupport hp, image_eq_zero_of_notMem_tsupport hq]

private theorem exists_support_radius (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, ∀ p : Fin 3 → v.adicCompletion ℚ, Φ p ≠ 0 → ∀ i, ‖p i‖ ≤ R := by
  have hK : IsCompact (tsupport Φ) := hΦc
  choose C hC using fun i : Fin 3 =>
    hK.exists_bound_of_continuousOn
      ((continuous_apply i).continuousOn : ContinuousOn (fun p : Fin 3 → v.adicCompletion ℚ => p i) (tsupport Φ))
  refine ⟨∑ i, max (C i) 0, fun p hp i => ?_⟩
  have hpK : p ∈ tsupport Φ := subset_tsupport Φ hp
  calc ‖p i‖ ≤ C i := hC i p hpK
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (C j) 0 :=
        Finset.single_le_sum (f := fun j => max (C j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ i)

private theorem norm_le_zpow_of_valued_le {x : v.adicCompletion ℚ} {n : ℤ} (hx : Valued.v x ≤ WithZero.exp n) :
    ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) :=
    (WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))).monotone hx
  have h2 : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (hkey.trans_eq hexp)
  rw [NumberField.FinitePlace.norm_def v x]
  exact_mod_cast h2

private theorem valued_le_of_norm_le_zpow
    {x : v.adicCompletion ℚ} {n : ℤ} (hx : ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n) :
    Valued.v x ≤ WithZero.exp n := by
  have hexp : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have hx' : (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ) ≤
      (((Ideal.absNorm v.asIdeal : NNReal) ^ n : NNReal) : ℝ) := by
    rw [NumberField.FinitePlace.norm_def v x] at hx
    exact_mod_cast hx
  have hkey : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) ≤
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) := by
    rw [hexp]
    exact NNReal.coe_le_coe.mp hx'
  have hmono := WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (v := v))
  exact hmono.le_iff_le.mp hkey

private theorem norm_eq_one_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def v u, hu, map_one, NNReal.coe_one]

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem _root_.WeylTranslateZeta.one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

p2m_export "WeylTranslateZeta" "one_lt_absNorm_real"

private theorem torusCellPoint_mem_bigCell3_iff (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ) :
    torusCellPoint v x y z a ∈ bigCell3 v ↔ z ≠ 0 ∧ x * y - z ≠ 0 := by
  rw [mem_bigCell3_iff, cornerEntry_torusCellPoint, lowerMinor_torusCellPoint]

private theorem valued_eq_one_of_valued_sub_one_le {u : v.adicCompletion ℚ} {k : ℕ} (hk : 1 ≤ k)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ))) : Valued.v u = 1 := by
  have hlt : Valued.v (u - 1) < Valued.v (1 : v.adicCompletion ℚ) := by
    rw [Valuation.map_one]
    refine lt_of_le_of_lt hu ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h := Valued.v.map_add_eq_of_lt_right hlt
  rwa [sub_add_cancel, Valuation.map_one] at h

private theorem exists_forall_charExt_mul_eq (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ k : ℕ, ∀ u w : v.adicCompletion ℚ,
      Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ)) → charExt η (u * w) = charExt η w := by
  obtain ⟨c, hc⟩ := exists_hasConductorExponentAt_of_continuous ℚ v η hη.continuous
  refine ⟨max c 1, fun u w huk => ?_⟩
  have hu1 : Valued.v u = 1 := valued_eq_one_of_valued_sub_one_le v (le_max_right c 1) huk
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  have hmem : Units.mk0 u hu0 ∈ higherUnitsAt ℚ v c := by
    rw [mem_higherUnitsAt_iff, Units.val_mk0]
    refine ⟨hu1, Or.inr (huk.trans ?_)⟩
    exact WithZero.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast le_max_left c 1))
  have hη1 : η (Units.mk0 u hu0) = 1 := hc.1 _ hmem
  by_cases hw : w = 0
  · rw [hw, mul_zero]
  have hcoe : u * w = ((Units.mk0 u hu0 * Units.mk0 w hw : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
  rw [hcoe, charExt_coe_units, map_mul, hη1, one_mul, ← charExt_coe_units, Units.val_mk0]

private theorem exists_forall_cellSectionOf_torusCellPoint_add
    (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ A₀ : ℝ, ∀ a : (v.adicCompletion ℚ)ˣ, A₀ < (modulus (a : v.adicCompletion ℚ) : ℝ) →
      ∀ ε : v.adicCompletion ℚ, Valued.v ε ≤ WithZero.exp (1 : ℤ) → ∀ x y z : v.adicCompletion ℚ,
        cellSectionOf v ν Φ (torusCellPoint v (x + ε) y z a) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  obtain ⟨k₀, hk₀⟩ := exists_forall_charExt_mul_eq v (ν 0) (hν 0)
  obtain ⟨k₁, hk₁⟩ := exists_forall_charExt_mul_eq v (ν 1) (hν 1)
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set R' : ℝ := max R 1 with hR'_def
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  have hRR' : R ≤ R' := le_max_left _ _
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le hR'1
  set k : ℕ := max (max k₀ k₁) 1 with hk_def
  have hk1 : 1 ≤ k := le_max_right _ _
  have hk₀k : k₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hk₁k : k₁ ≤ k := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨max (q * R' * R' / δ) (q ^ (k + 1) * R'), fun a ha ε hε => ?_⟩
  rw [modulus_real_eq_norm] at ha
  have haR : q * R' * R' / δ < ‖(a : v.adicCompletion ℚ)‖ := (le_max_left _ _).trans_lt ha
  have hak : q ^ (k + 1) * R' < ‖(a : v.adicCompletion ℚ)‖ := (le_max_right _ _).trans_lt ha
  have hqk : (0 : ℝ) < q ^ (k + 1) * R' := mul_pos (pow_pos hq0 _) hR'0
  have ha0 : (0 : ℝ) < ‖(a : v.adicCompletion ℚ)‖ := hqk.trans hak
  have hεn : ‖ε‖ ≤ q := by simpa using norm_le_zpow_of_valued_le v hε

  have key : ∀ (x y z ε' : v.adicCompletion ℚ), ‖ε'‖ ≤ q →
      cellSectionOf v ν Φ (torusCellPoint v x y z a) ≠ 0 →
      cellSectionOf v ν Φ (torusCellPoint v (x + ε') y z a) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
    intro x y z ε' hε' hne
    have hmem : torusCellPoint v x y z a ∈ bigCell3 v := by
      by_contra h
      exact hne (cellSectionOf_apply_of_notMem v ν Φ h)
    obtain ⟨hz, hm⟩ := (torusCellPoint_mem_bigCell3_iff v x y z a).mp hmem
    rw [cellSectionOf_apply_of_mem v ν Φ hmem] at hne
    have hΦne : Φ (cellRatio v (torusCellPoint v x y z a)) ≠ 0 := right_ne_zero_of_mul hne
    have hb := hR _ hΦne
    rw [cellRatio_torusCellPoint] at hb
    have h1 : ‖(a : v.adicCompletion ℚ) / z‖ ≤ R := by simpa using hb 1
    have h2 : ‖(a : v.adicCompletion ℚ) * y / (x * y - z)‖ ≤ R := by simpa using hb 2
    have hR0 : (0 : ℝ) ≤ R := (norm_nonneg _).trans h1
    set m : v.adicCompletion ℚ := x * y - z with hm_def
    set t : v.adicCompletion ℚ := ε' * y / m with ht_def

    have hym : ‖y / m‖ ≤ R / ‖(a : v.adicCompletion ℚ)‖ := by
      rw [le_div_iff₀ ha0]
      calc ‖y / m‖ * ‖(a : v.adicCompletion ℚ)‖ = ‖(a : v.adicCompletion ℚ) * y / m‖ := by
            rw [← norm_mul]; congr 1; ring
        _ ≤ R := h2
    have htn : ‖t‖ ≤ q * R / ‖(a : v.adicCompletion ℚ)‖ := by
      have : t = ε' * (y / m) := by rw [ht_def, mul_div_assoc]
      rw [this, norm_mul, mul_div_assoc]
      exact mul_le_mul hε' hym (norm_nonneg _) hq0.le
    have hzn : ‖(1 : v.adicCompletion ℚ) / z‖ ≤ R / ‖(a : v.adicCompletion ℚ)‖ := by
      rw [le_div_iff₀ ha0]
      calc ‖(1 : v.adicCompletion ℚ) / z‖ * ‖(a : v.adicCompletion ℚ)‖
          = ‖(a : v.adicCompletion ℚ) / z‖ := by rw [← norm_mul]; congr 1; ring
        _ ≤ R := h1
    have hδ0 : δ ≠ 0 := hδpos.ne'
    have hqR_le_δ : q * R / ‖(a : v.adicCompletion ℚ)‖ ≤ δ := by
      rw [div_le_iff₀ ha0]
      calc q * R ≤ q * R' * R' :=
            (mul_le_mul_of_nonneg_left hRR' hq0.le).trans (le_mul_of_one_le_right (mul_pos hq0 hR'0).le hR'1)
        _ = δ * (q * R' * R' / δ) := by field_simp
        _ ≤ δ * ‖(a : v.adicCompletion ℚ)‖ := mul_le_mul_of_nonneg_left haR.le hδpos.le
    have hRqR_le_δ : R * (q * R / ‖(a : v.adicCompletion ℚ)‖) ≤ δ := by
      rw [← mul_div_assoc, div_le_iff₀ ha0]
      calc R * (q * R) = q * R * R := by ring
        _ ≤ q * R' * R' := mul_le_mul (mul_le_mul_of_nonneg_left hRR' hq0.le) hRR' hR0 (mul_pos hq0 hR'0).le
        _ = δ * (q * R' * R' / δ) := by field_simp
        _ ≤ δ * ‖(a : v.adicCompletion ℚ)‖ := mul_le_mul_of_nonneg_left haR.le hδpos.le
    have ht_small : ‖t‖ ≤ q ^ (-(k : ℤ)) := by
      refine htn.trans ?_
      rw [div_le_iff₀ ha0, zpow_neg, zpow_natCast]
      calc q * R ≤ q * R' := by gcongr
        _ = (q ^ k)⁻¹ * (q ^ (k + 1) * R') := by field_simp; ring
        _ ≤ (q ^ k)⁻¹ * ‖(a : v.adicCompletion ℚ)‖ := by gcongr
    set u : v.adicCompletion ℚ := 1 + t with hu_def
    have hut : u - 1 = t := by rw [hu_def]; ring
    have hu_val : Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ)) := by
      rw [hut]
      exact valued_le_of_norm_le_zpow v ht_small
    have hu1 : Valued.v u = 1 := valued_eq_one_of_valued_sub_one_le v hk1 hu_val
    have hun : ‖u‖ = 1 := norm_eq_one_of_valued_eq_one v hu1
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, map_zero] at hu1
      exact zero_ne_one hu1
    have hm' : (x + ε') * y - z = m * u := by
      have hcancel : m * (ε' * y / m) = ε' * y := by field_simp
      rw [hu_def, ht_def, mul_add, mul_one, hcancel, hm_def]
      ring
    have hmu : m * u ≠ 0 := mul_ne_zero hm hu0
    have hmem' : torusCellPoint v (x + ε') y z a ∈ bigCell3 v :=
      (torusCellPoint_mem_bigCell3_iff v (x + ε') y z a).mpr ⟨hz, by rw [hm']; exact hmu⟩

    have hinv_val : Valued.v (u⁻¹ - 1) ≤ WithZero.exp (-(k : ℤ)) := by
      have : u⁻¹ - 1 = -(u⁻¹ * (u - 1)) := by rw [mul_sub, inv_mul_cancel₀ hu0, mul_one, neg_sub]
      rw [this, Valuation.map_neg, Valuation.map_mul, map_inv₀, hu1, inv_one, one_mul]
      exact hu_val
    have hinv_n : ‖u⁻¹ - 1‖ = ‖t‖ := by
      have : u⁻¹ - 1 = -(u⁻¹ * (u - 1)) := by rw [mul_sub, inv_mul_cancel₀ hu0, mul_one, neg_sub]
      rw [this, norm_neg, norm_mul, norm_inv, hun, inv_one, one_mul, hut]
    have hexp₀ : WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k₀ : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    have hexp₁ : WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k₁ : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

    rw [cellSectionOf_apply_of_mem v ν Φ hmem', cellSectionOf_apply_of_mem v ν Φ hmem,
      cellValue_torusCellPoint, cellValue_torusCellPoint, cellRatio_torusCellPoint, cellRatio_torusCellPoint, hm']
    have e0 : charExt (ν 0) ((a : v.adicCompletion ℚ) / (m * u)) = charExt (ν 0) ((a : v.adicCompletion ℚ) / m) := by
      rw [show (a : v.adicCompletion ℚ) / (m * u) = u⁻¹ * ((a : v.adicCompletion ℚ) / m) by field_simp]
      exact hk₀ u⁻¹ _ (hinv_val.trans hexp₀)
    have e1 : charExt (ν 1) (m * u / z) = charExt (ν 1) (m / z) := by
      rw [show m * u / z = u * (m / z) by ring]
      exact hk₁ u _ (hu_val.trans hexp₁)
    have e3 : ‖(a : v.adicCompletion ℚ) / (m * u)‖ = ‖(a : v.adicCompletion ℚ) / m‖ := by
      rw [norm_div, norm_div, norm_mul, hun, mul_one]
    have eΦ : Φ ![(x + ε') / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (m * u)] =
        Φ ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / m] := by
      refine hδ _ _ ?_
      intro i
      fin_cases i
      · show ‖(x + ε') / z - x / z‖ ≤ δ
        calc ‖(x + ε') / z - x / z‖ = ‖ε' * (1 / z)‖ := by rw [add_div, add_sub_cancel_left, mul_one_div]
          _ = ‖ε'‖ * ‖(1 : v.adicCompletion ℚ) / z‖ := norm_mul _ _
          _ ≤ q * (R / ‖(a : v.adicCompletion ℚ)‖) := mul_le_mul hε' hzn (norm_nonneg _) hq0.le
          _ = q * R / ‖(a : v.adicCompletion ℚ)‖ := by ring
          _ ≤ δ := hqR_le_δ
      · show ‖(a : v.adicCompletion ℚ) / z - (a : v.adicCompletion ℚ) / z‖ ≤ δ
        rw [sub_self, norm_zero]
        exact hδpos.le
      · show ‖(a : v.adicCompletion ℚ) * y / (m * u) - (a : v.adicCompletion ℚ) * y / m‖ ≤ δ
        calc ‖(a : v.adicCompletion ℚ) * y / (m * u) - (a : v.adicCompletion ℚ) * y / m‖
            = ‖(a : v.adicCompletion ℚ) * y / m‖ * ‖u⁻¹ - 1‖ := by rw [← norm_mul]; congr 1; field_simp
          _ = ‖(a : v.adicCompletion ℚ) * y / m‖ * ‖t‖ := by rw [hinv_n]
          _ ≤ R * (q * R / ‖(a : v.adicCompletion ℚ)‖) := mul_le_mul h2 htn (norm_nonneg _) hR0
          _ ≤ δ := hRqR_le_δ
    rw [e0, e1, e3, eΦ]

  intro x y z
  by_cases hx : cellSectionOf v ν Φ (torusCellPoint v x y z a) = 0
  · by_cases hx' : cellSectionOf v ν Φ (torusCellPoint v (x + ε) y z a) = 0
    · rw [hx, hx']
    · have hεn' : ‖-ε‖ ≤ q := by rwa [norm_neg]
      have h := key (x + ε) y z (-ε) hεn' hx'
      rw [add_neg_cancel_right] at h
      rw [← h] at hx'
      exact (hx' hx).elim
  · exact key x y z ε hεn hx

private theorem exists_forall_torusIntegrand_add_fst (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ A₀ : ℝ, ∀ a : (v.adicCompletion ℚ)ˣ, A₀ < (modulus (a : v.adicCompletion ℚ) : ℝ) →
      ∀ ε : v.adicCompletion ℚ, Valued.v ε ≤ WithZero.exp (1 : ℤ) →
        ∀ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
          torusIntegrand v ν Φ a (p.1 + ε, p.2) = psiLocal ℚ v (-ε) * torusIntegrand v ν Φ a p := by
  obtain ⟨A₀, hA₀⟩ := exists_forall_cellSectionOf_torusCellPoint_add v ν Φ hν hΦl hΦc
  refine ⟨A₀, fun a ha ε hε p => ?_⟩
  simp only [torusIntegrand]
  rw [hA₀ a ha ε hε]
  have hsum : -((p.1 + ε) + p.2.1) = -ε + -(p.1 + p.2.1) := by ring
  rw [hsum, AddChar.map_add_eq_mul, mul_assoc]

private theorem exists_forall_cellSectionOf_torusCellPoint_mul
    (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) →
      ∀ (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ),
        cellSectionOf v ν Φ (torusCellPoint v x y z (a * u)) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_invariance_radius v Φ hΦl hΦc
  obtain ⟨R, hR⟩ := exists_support_radius v Φ hΦc
  obtain ⟨k₀, hk₀⟩ := exists_forall_charExt_mul_eq v (ν 0) (hν 0)
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  set R' : ℝ := max R 1 with hR'_def
  have hR'0 : (0 : ℝ) < R' := zero_lt_one.trans_le (le_max_right _ _)
  have hRR' : R ≤ R' := le_max_left _ _

  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, q⁻¹ ^ k₁ * R' ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδpos hR'0) (inv_lt_one_of_one_lt₀ hq1)
    exact ⟨n, (le_div_iff₀ hR'0).mp hn.le⟩
  set k : ℕ := max (max k₀ k₁) 1 with hk_def
  have hk1 : 1 ≤ k := le_max_right _ _
  have hk₀k : k₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hk₁k : k₁ ≤ k := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨k, hk1, fun u hu => ?_⟩
  have hu1 : Valued.v (u : v.adicCompletion ℚ) = 1 := valued_eq_one_of_valued_sub_one_le v hk1 hu
  have hun : ‖(u : v.adicCompletion ℚ)‖ = 1 := norm_eq_one_of_valued_eq_one v hu1
  have hu_small : ‖(u : v.adicCompletion ℚ) - 1‖ * R' ≤ δ := by
    refine le_trans ?_ hk₁
    gcongr
    calc ‖(u : v.adicCompletion ℚ) - 1‖ ≤ q ^ (-(k : ℤ)) := by simpa using norm_le_zpow_of_valued_le v hu
      _ = q⁻¹ ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ ≤ q⁻¹ ^ k₁ := pow_le_pow_of_le_one (inv_nonneg.mpr hq0.le) (inv_le_one_of_one_le₀ hq1.le) hk₁k
  have hexp₀ : WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(k₀ : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

  have key : ∀ (u : (v.adicCompletion ℚ)ˣ), Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) →
      ‖(u : v.adicCompletion ℚ)‖ = 1 → ‖(u : v.adicCompletion ℚ) - 1‖ * R' ≤ δ →
      ∀ (x y z : v.adicCompletion ℚ) (a : (v.adicCompletion ℚ)ˣ),
        cellSectionOf v ν Φ (torusCellPoint v x y z a) ≠ 0 →
        cellSectionOf v ν Φ (torusCellPoint v x y z (a * u)) = cellSectionOf v ν Φ (torusCellPoint v x y z a) := by
    intro u hu hun hsmall x y z a hne
    have hmem : torusCellPoint v x y z a ∈ bigCell3 v := by
      by_contra h
      exact hne (cellSectionOf_apply_of_notMem v ν Φ h)
    obtain ⟨hz, hm⟩ := (torusCellPoint_mem_bigCell3_iff v x y z a).mp hmem
    have hmem' : torusCellPoint v x y z (a * u) ∈ bigCell3 v :=
      (torusCellPoint_mem_bigCell3_iff v x y z (a * u)).mpr ⟨hz, hm⟩
    rw [cellSectionOf_apply_of_mem v ν Φ hmem] at hne
    have hΦne : Φ (cellRatio v (torusCellPoint v x y z a)) ≠ 0 := right_ne_zero_of_mul hne
    have hb := hR _ hΦne
    rw [cellRatio_torusCellPoint] at hb
    have h1 : ‖(a : v.adicCompletion ℚ) / z‖ ≤ R := by simpa using hb 1
    have h2 : ‖(a : v.adicCompletion ℚ) * y / (x * y - z)‖ ≤ R := by simpa using hb 2
    have hbound : ∀ w : v.adicCompletion ℚ, ‖w‖ ≤ R → ‖w * (u : v.adicCompletion ℚ) - w‖ ≤ δ := by
      intro w hw
      calc ‖w * (u : v.adicCompletion ℚ) - w‖ = ‖w‖ * ‖(u : v.adicCompletion ℚ) - 1‖ := by
            rw [← norm_mul]; congr 1; ring
        _ ≤ R' * ‖(u : v.adicCompletion ℚ) - 1‖ := by gcongr; exact hw.trans hRR'
        _ = ‖(u : v.adicCompletion ℚ) - 1‖ * R' := mul_comm _ _
        _ ≤ δ := hsmall
    rw [cellSectionOf_apply_of_mem v ν Φ hmem', cellSectionOf_apply_of_mem v ν Φ hmem,
      cellValue_torusCellPoint, cellValue_torusCellPoint, cellRatio_torusCellPoint, cellRatio_torusCellPoint,
      Units.val_mul]
    have e0 : charExt (ν 0) ((a : v.adicCompletion ℚ) * u / (x * y - z)) =
        charExt (ν 0) ((a : v.adicCompletion ℚ) / (x * y - z)) := by
      rw [show (a : v.adicCompletion ℚ) * u / (x * y - z) = u * ((a : v.adicCompletion ℚ) / (x * y - z)) by ring]
      exact hk₀ u _ (hu.trans hexp₀)
    have e3 : ‖(a : v.adicCompletion ℚ) * u / (x * y - z)‖ = ‖(a : v.adicCompletion ℚ) / (x * y - z)‖ := by
      rw [norm_div, norm_div, norm_mul, hun, mul_one]
    have eΦ : Φ ![x / z, (a : v.adicCompletion ℚ) * u / z, (a : v.adicCompletion ℚ) * u * y / (x * y - z)] =
        Φ ![x / z, (a : v.adicCompletion ℚ) / z, (a : v.adicCompletion ℚ) * y / (x * y - z)] := by
      refine hδ _ _ ?_
      intro i
      fin_cases i
      · show ‖x / z - x / z‖ ≤ δ
        rw [sub_self, norm_zero]
        exact hδpos.le
      · show ‖(a : v.adicCompletion ℚ) * u / z - (a : v.adicCompletion ℚ) / z‖ ≤ δ
        have := hbound _ h1
        rwa [show (a : v.adicCompletion ℚ) / z * u = (a : v.adicCompletion ℚ) * u / z by ring] at this
      · show ‖(a : v.adicCompletion ℚ) * u * y / (x * y - z) - (a : v.adicCompletion ℚ) * y / (x * y - z)‖ ≤ δ
        have := hbound _ h2
        rwa [show (a : v.adicCompletion ℚ) * y / (x * y - z) * u = (a : v.adicCompletion ℚ) * u * y / (x * y - z) by
          ring] at this
    rw [e0, e3, eΦ]
  intro x y z a
  by_cases ha : cellSectionOf v ν Φ (torusCellPoint v x y z a) = 0
  · by_cases hau : cellSectionOf v ν Φ (torusCellPoint v x y z (a * u)) = 0
    · rw [ha, hau]
    ·
      have hinv_val : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) - 1 : v.adicCompletion ℚ) ≤ WithZero.exp (-(k : ℤ)) := by
        have : ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1 =
            -(((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1)) := by
          rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ u.ne_zero, mul_one, neg_sub]
        rw [this, Valuation.map_neg, Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one, one_mul]
        exact hu
      have hinv_n : ‖((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = 1 := by
        rw [Units.val_inv_eq_inv_val, norm_inv, hun, inv_one]
      have hinv_small : ‖((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1‖ * R' ≤ δ := by
        have : ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1 =
            -(((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1)) := by
          rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ u.ne_zero, mul_one, neg_sub]
        rw [this, norm_neg, norm_mul, hinv_n, one_mul]
        exact hu_small
      have h := key u⁻¹ hinv_val hinv_n hinv_small x y z (a * u) hau
      rw [mul_inv_cancel_right] at h
      exact absurd (h.symm.trans ha) hau
  · exact key u hu hun hu_small x y z a ha

private theorem jacquetValue_congr
    {f g : LocalGL3 v → ℂ} (h : ∀ c : ℤ, jacquetTruncated3 v c f = jacquetTruncated3 v c g) :
    jacquetValue v f = jacquetValue v g := by
  have hl : jacquetLevel v f = jacquetLevel v g := by
    unfold jacquetLevel
    simp only [h]
  unfold jacquetValue
  rw [hl, h]

private theorem jacquetValue_torusTranslate_eq_of_forall (a b : (v.adicCompletion ℚ)ˣ)
    (h : ∀ x y z : v.adicCompletion ℚ,
      cellSectionOf v ν Φ (torusCellPoint v x y z b) = cellSectionOf v ν Φ (torusCellPoint v x y z a)) :
    jacquetValue v (torusTranslate v ν Φ b) = jacquetValue v (torusTranslate v ν Φ a) := by
  refine jacquetValue_congr v fun c => ?_
  rw [jacquetTruncated3_torusTranslate_eq_integral, jacquetTruncated3_torusTranslate_eq_integral]
  congr 1
  funext p
  simp only [torusIntegrand, h]

private theorem eventually_torusFn_eq (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    ∀ᶠ t' in 𝓝 t, torusFn v ν Φ t' = torusFn v ν Φ t := by
  obtain ⟨k, hk1, hk⟩ := exists_forall_cellSectionOf_torusCellPoint_mul v ν Φ hν hΦl hΦc
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq_def
  have hq1 : (1 : ℝ) < q := one_lt_absNorm_real v
  have htn : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr ht
  have hρ : (0 : ℝ) < q ^ (-(k : ℤ)) * ‖t‖ := mul_pos (zpow_pos (zero_lt_one.trans hq1) _) htn
  have hqk : q ^ (-(k : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hq1.le (by omega)
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds t hρ) fun t' ht' => ?_
  rw [Metric.mem_ball, dist_eq_norm] at ht'
  have ht'0 : t' ≠ 0 := by
    rintro rfl
    rw [zero_sub, norm_neg] at ht'
    have : q ^ (-(k : ℤ)) * ‖t‖ ≤ ‖t‖ := by
      calc q ^ (-(k : ℤ)) * ‖t‖ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hqk htn.le
        _ = ‖t‖ := one_mul _
    exact absurd ht' (not_lt.mpr this)
  set u : (v.adicCompletion ℚ)ˣ := Units.mk0 (t' / t) (div_ne_zero ht'0 ht) with hu_def
  have hu_sub : (u : v.adicCompletion ℚ) - 1 = (t' - t) / t := by
    rw [hu_def, Units.val_mk0]
    field_simp
  have hu_norm : ‖(u : v.adicCompletion ℚ) - 1‖ ≤ q ^ (-(k : ℤ)) := by
    rw [hu_sub, norm_div, div_le_iff₀ htn]
    exact ht'.le
  have hu : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(k : ℤ)) := valued_le_of_norm_le_zpow v hu_norm
  have ht'eq : t' = t * u := by
    rw [hu_def, Units.val_mk0]
    field_simp
  have hun : ‖(u : v.adicCompletion ℚ)‖ = 1 :=
    norm_eq_one_of_valued_eq_one v (valued_eq_one_of_valued_sub_one_le v hk1 hu)
  have hmk : Units.mk0 t' ht'0 = Units.mk0 t ht * u := by
    ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, ht'eq]
  have hmod : (modulus t' : ℝ) = (modulus t : ℝ) := by
    rw [modulus_real_eq_norm, modulus_real_eq_norm, ht'eq, norm_mul, hun, mul_one]
  simp only [torusFn, dif_neg ht, dif_neg ht'0]
  rw [hmk, jacquetValue_torusTranslate_eq_of_forall v ν Φ (Units.mk0 t ht) (Units.mk0 t ht * u)
    (fun x y z => hk u hu x y z (Units.mk0 t ht)), hmod]

private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

private theorem measurableSet_unipotentBall3 (c : ℤ) :
    letI := localBorel ℚ v
    MeasurableSet (unipotentBall3 v c) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hset : unipotentBall3 v c =
      (Prod.fst ⁻¹' {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.1) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp c}) ∩
        ((fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => p.2.2) ⁻¹'
          {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (2 * c)}) := by
    ext p
    simp only [unipotentBall3, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [hset]
  exact (((isClosed_valued_le v c).measurableSet.preimage measurable_fst).inter
    ((isClosed_valued_le v c).measurableSet.preimage (measurable_fst.comp measurable_snd))).inter
    ((isClosed_valued_le v (2 * c)).measurableSet.preimage (measurable_snd.comp measurable_snd))

private theorem preimage_add_unipotentBall3 {c : ℤ} (hc : 1 ≤ c) {ε : v.adicCompletion ℚ}
    (hε : Valued.v ε ≤ WithZero.exp (1 : ℤ)) :
    (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        p + ((ε, (0 : v.adicCompletion ℚ × v.adicCompletion ℚ)))) ⁻¹' unipotentBall3 v c = unipotentBall3 v c := by
  have hε' : Valued.v ε ≤ WithZero.exp c := hε.trans (WithZero.exp_le_exp.mpr hc)
  have hε'' : Valued.v (-ε) ≤ WithZero.exp c := by rwa [Valuation.map_neg]
  ext p
  simp only [Set.mem_preimage, unipotentBall3, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, add_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    have hp : p.1 = (p.1 + ε) + -ε := by ring
    rw [hp]
    exact (Valuation.map_add _ _ _).trans (max_le h1 hε'')
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(Valuation.map_add _ _ _).trans (max_le h1 hε'), h2, h3⟩

private theorem setIntegral_unipotentBall3_add_fst {c : ℤ} (hc : 1 ≤ c) {ε : v.adicCompletion ℚ}
    (hε : Valued.v ε ≤ WithZero.exp (1 : ℤ))
    (F : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ) :
    letI := localBorel ℚ v
    ∫ p in unipotentBall3 v c, F (p.1 + ε, p.2) ∂(jacquetHaar3 v) =
      ∫ p in unipotentBall3 v c, F p ∂(jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  haveI := sFinite_selfDualHaarAt ℚ v
  have hmeas := measurableSet_unipotentBall3 v c
  have hpre := preimage_add_unipotentBall3 v hc hε
  have key : (unipotentBall3 v c).indicator (fun p => F (p.1 + ε, p.2)) =
      fun p => (unipotentBall3 v c).indicator F (p + (ε, (0 : v.adicCompletion ℚ × v.adicCompletion ℚ))) := by
    funext p
    have h := Set.indicator_comp_right (M := ℂ)
      (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        q + (ε, (0 : v.adicCompletion ℚ × v.adicCompletion ℚ))) (s := unipotentBall3 v c) (g := F) (x := p)
    rw [hpre] at h
    rw [← h]
    congr 1
    funext x
    simp only [Function.comp_apply]
    congr 1
    ext <;> simp
  unfold jacquetHaar3
  rw [← integral_indicator hmeas, ← integral_indicator hmeas, key, integral_add_right_eq_self]

private theorem bddAbove_levels_psiLocal :
    BddAbove {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLocal ℚ v x = 1} := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : v.adicCompletion ℚ, psiLocal ℚ v x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact psiLocal_ne_one ℚ v (AddChar.ext _ _ h)
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one _)
  have hv : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0
  refine ⟨WithZero.log (Valued.v x₀), fun n hn => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hx₀
  apply hn x₀
  rw [← WithZero.exp_log hv]
  exact WithZero.exp_le_exp.mpr hlt.le

private theorem exists_psiLocal_neg_ne_one :
    ∃ ε : v.adicCompletion ℚ, Valued.v ε ≤ WithZero.exp (1 : ℤ) ∧ psiLocal ℚ v (-ε) ≠ 1 := by
  have hlevel := addCharLevel_psiLocal_rat v
  rw [addCharLevel_def] at hlevel
  have h1 : (1 : ℤ) ∉ {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → psiLocal ℚ v x = 1} := by
    intro h1
    have := le_csSup (bddAbove_levels_psiLocal v) h1
    rw [hlevel] at this
    exact absurd this (by decide)
  simp only [Set.mem_setOf_eq, not_forall] at h1
  obtain ⟨x, hx, hψ⟩ := h1
  refine ⟨-x, ?_, ?_⟩
  · rwa [Valuation.map_neg]
  · rwa [neg_neg]

private theorem exists_forall_jacquetTruncated3_torusTranslate_eq_zero (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ A₀ : ℝ, ∀ a : (v.adicCompletion ℚ)ˣ, A₀ < (modulus (a : v.adicCompletion ℚ) : ℝ) →
      ∀ c : ℤ, 1 ≤ c → jacquetTruncated3 v c (torusTranslate v ν Φ a) = 0 := by
  letI := localBorel ℚ v
  obtain ⟨A₀, hA₀⟩ := exists_forall_torusIntegrand_add_fst v ν Φ hν hΦl hΦc
  obtain ⟨ε, hε, hψ⟩ := exists_psiLocal_neg_ne_one v
  refine ⟨A₀, fun a ha c hc => ?_⟩
  have h1 : jacquetTruncated3 v c (torusTranslate v ν Φ a) =
      psiLocal ℚ v (-ε) * jacquetTruncated3 v c (torusTranslate v ν Φ a) := by
    conv_lhs => rw [jacquetTruncated3_torusTranslate_eq_integral, ← setIntegral_unipotentBall3_add_fst v hc hε]
    simp_rw [hA₀ a ha ε hε]
    rw [integral_const_mul, ← jacquetTruncated3_torusTranslate_eq_integral]
  have h2 : (1 - psiLocal ℚ v (-ε)) * jacquetTruncated3 v c (torusTranslate v ν Φ a) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hψ))

private theorem exists_torusFn_eq_zero_of_lt (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → torusFn v ν Φ t = 0 := by
  obtain ⟨A₀, hA₀⟩ := exists_forall_jacquetTruncated3_torusTranslate_eq_zero v ν Φ hν hΦl hΦc
  refine ⟨A₀, fun t ht => ?_⟩
  by_cases h0 : t = 0
  · rw [h0, torusFn_zero]
  · set a : (v.adicCompletion ℚ)ˣ := Units.mk0 t h0 with ha
    have hz : ∀ c : ℤ, 1 ≤ c → jacquetTruncated3 v c (torusTranslate v ν Φ a) = 0 := hA₀ a ht
    have hconst : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
        jacquetTruncated3 v c (torusTranslate v ν Φ a) = jacquetTruncated3 v c₀ (torusTranslate v ν Φ a) :=
      ⟨1, fun c hc => by rw [hz c (by exact_mod_cast hc), hz ((1 : ℕ) : ℤ) (by norm_num)]⟩
    have hval : jacquetValue v (torusTranslate v ν Φ a) = 0 := by
      rw [← jacquetTruncated3_eq_jacquetValue v _ hconst (le_max_left (jacquetLevel v (torusTranslate v ν Φ a) : ℤ) 1)]
      exact hz _ (le_max_right _ _)
    have ht' : torusFn v ν Φ t = torusFn v ν Φ a := by simp [ha]
    rw [ht', torusFn_coe_units, hval, zero_mul]

end TorusValues

end WeylTranslateZeta
end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

open Polynomial in

private def IsLaurentInQPow (q : ℂ) (P : ℂ → ℂ) : Prop :=
  ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s)

namespace IsLaurentInQPow

variable {q : ℂ}

private theorem mul (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s * P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Q₂, m₁ + m₂, fun s => ?_⟩
  show P₁ s * P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_mul, Nat.cast_add, add_mul, Complex.cpow_add _ _ hq]
  ring

private theorem qpow_add_nat_mul_mul_pow (hq : q ≠ 0) (m k : ℕ) (s : ℂ) :
    q ^ (((m + k : ℕ) : ℂ) * s) * (q ^ (-s)) ^ k = q ^ ((m : ℂ) * s) := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

private theorem eq_of_eqOn_strip {r : ℝ} (hr : 1 < r) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow (r : ℂ) P₁)
    (h₂ : IsLaurentInQPow (r : ℂ) P₂) {σ₀ σ₁ : ℝ} (hσ : σ₀ < σ₁)
    (hagree : ∀ s : ℂ, σ₀ < s.re → s.re < σ₁ → P₁ s = P₂ s) : ∀ s : ℂ, P₁ s = P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hq0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  set D : Polynomial ℂ := Q₁ * Polynomial.X ^ m₂ - Q₂ * Polynomial.X ^ m₁ with hD

  have hkey : ∀ s : ℂ, P₁ s - P₂ s = (r : ℂ) ^ (((m₁ + m₂ : ℕ) : ℂ) * s) * D.eval ((r : ℂ) ^ (-s)) := by
    intro s
    rw [e₁ s, e₂ s, hD, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_pow, Polynomial.eval_X, ← qpow_add_nat_mul_mul_pow hq0 m₁ m₂ s,
      ← qpow_add_nat_mul_mul_pow hq0 m₂ m₁ s, Nat.add_comm m₂ m₁]
    ring

  have hroots : ∀ σ : ℝ, σ₀ < σ → σ < σ₁ → D.IsRoot ((r : ℂ) ^ (-(σ : ℂ))) := by
    intro σ hσ₀ hσ₁
    have hs : P₁ (σ : ℂ) = P₂ (σ : ℂ) := hagree (σ : ℂ) (by simpa using hσ₀) (by simpa using hσ₁)
    have hk := hkey (σ : ℂ)
    rw [sub_eq_zero.mpr hs] at hk
    have hpow : (r : ℂ) ^ (((m₁ + m₂ : ℕ) : ℂ) * (σ : ℂ)) ≠ 0 := fun h =>
      hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    exact (mul_eq_zero.mp hk.symm).resolve_left hpow

  have hinj : Function.Injective fun σ : ℝ => (r : ℂ) ^ (-(σ : ℂ)) := by
    intro a b hab
    have hab' : (r : ℂ) ^ (-(a : ℂ)) = (r : ℂ) ^ (-(b : ℂ)) := hab
    rw [← Complex.ofReal_neg, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hr0.le, ← Complex.ofReal_cpow hr0.le,
      Complex.ofReal_inj] at hab'
    have hmono : StrictMono fun t : ℝ => r ^ t := fun x y hxy => Real.rpow_lt_rpow_of_exponent_lt hr hxy
    exact neg_injective (hmono.injective hab')
  have hinf : Set.Infinite {x : ℂ | D.IsRoot x} := by
    refine Set.Infinite.mono ?_ ((Set.infinite_image_iff hinj.injOn).mpr (Set.Ioo_infinite hσ))
    rintro _ ⟨σ, ⟨hσ₀, hσ₁⟩, rfl⟩
    exact hroots σ hσ₀ hσ₁
  have hD0 : D = 0 := Polynomial.eq_zero_of_infinite_isRoot D hinf
  intro s
  have hk := hkey s
  rw [hD0, Polynomial.eval_zero, mul_zero] at hk
  exact sub_eq_zero.mp hk

end IsLaurentInQPow

namespace LaurentZetaSlot

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private noncomputable abbrev qv : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem _root_.LaurentZetaSlot.absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by
  intro h0
  have h := one_lt_absNorm_real v
  rw [h0] at h
  norm_num at h

p2m_export "LaurentZetaSlot" "absNorm_ne_zero"

private noncomputable def slotScalar (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) : ℂ :=
  by classical exact if HasConductorExponentAt ℚ v η 0 then (η (uniformizerUnit ℚ v) : ℂ) else 0

private theorem localLFactorAt_eq_inv_one_sub (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    localLFactorAt ℚ v η s = (1 - slotScalar v η * qv v ^ (-s))⁻¹ := by
  unfold localLFactorAt slotScalar
  split_ifs <;> simp

end LaurentZetaSlot
end

section

open IsDedekindDomain
open NumberField

namespace WeylTranslateZeta
open LanglandsTunnell.TateLocal

section ConductorWitness

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

private theorem exists_hasConductorExponentAt_of_isLocallyConstant (η : (w.adicCompletion K)ˣ →* ℂˣ)
    (hη : IsLocallyConstant η) : ∃ c : ℕ, HasConductorExponentAt K w η c :=
  exists_hasConductorExponentAt_of_continuous K w η hη.continuous

end ConductorWitness

section NormPowerOfConductorSum

end NormPowerOfConductorSum

end WeylTranslateZeta
end

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open NumberField.StandardAddChar
open scoped Topology
open NumberField.AdelicLevel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

section PrimalBridge

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem torusIntegrand_coe_units (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (a : (v.adicCompletion ℚ)ˣ) :
    jacquetWhittaker3 v ν Φ (iotaGL (diagUnitGL2 a) * 1 * antidiagonal3 v) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
      torusFn v ν Φ a * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s := by
  have h0 : ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero a.ne_zero
  rw [mul_one, jacquetWhittaker3_apply, torusFn_coe_units, Complex.cpow_sub _ _ h0, Complex.cpow_one]
  unfold torusTranslate
  ring

private theorem integrable_comap_units_val (F : v.adicCompletion ℚ → ℂ)
    (hF : letI := localBorel ℚ v; Integrable F (mulMeasure (selfDualHaarAt ℚ v))) :
    letI := localBorel ℚ v
    Integrable (fun a : (v.adicCompletion ℚ)ˣ => F (a : v.adicCompletion ℚ))
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
  letI := localBorel ℚ v
  have hemb := measurableEmbedding_units_val ℚ v
  have h : Integrable F (Measure.map Units.val (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) := by
    rw [hemb.map_comap, range_units_val_eq ℚ v, mulMeasure_restrict_compl_zero ℚ v]
    exact hF
  exact hemb.integrable_map_iff.mp h

private theorem localZeta30_eq_localZeta_torusFn (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    letI := localBorel ℚ v
    localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1 =
      localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s := by
  letI := localBorel ℚ v
  rw [localZeta_eq_integral_units ℚ v]
  unfold localZeta30
  congr 1
  funext a
  exact torusIntegrand_coe_units v ν Φ χ s a

private theorem integrable_torusFn_of_pos_re (hν : ∀ i, IsLocallyConstant (ν i)) (hΦl : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) (s : ℂ) (hs : 0 < s.re) :
    letI := localBorel ℚ v
    Integrable (fun x => torusFn v ν Φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hχ0 : 0 < ‖((χ (uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (χ _).ne_zero
  have hβ : ∀ i, ‖(((ν i) (uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = ‖((χ (uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖⁻¹ := by
    intro i
    have h := hu i
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul] at h
    exact eq_inv_of_mul_eq_one_left h
  let D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ :=
    fun α f a => f a - α * f (a / (uniformizerUnit ℚ v : v.adicCompletion ℚ))
  have hrec :=
    (eventually_threefold_twistedDifference_torusJacquetValueFn_eq_zero v ν hν Φ hΦl hΦc D (fun _ _ _ => rfl)
      (torusFn v ν Φ) (torusFn_zero v ν Φ) (fun a => torusFn_coe_units v ν Φ a)).1
  refine integrable_mul_charExt_mul_modulus_cpow_of_twistedDifference v
    (fun i => (((ν i) (uniformizerUnit ℚ v) : ℂˣ) : ℂ)) D (fun _ _ _ => rfl) (torusFn v ν Φ)
    (fun t ht => eventually_torusFn_eq v ν Φ hν hΦl hΦc ht) (exists_torusFn_eq_zero_of_lt v ν Φ hν hΦl hΦc) hrec χ hχ s
    (fun i => ?_)
  rw [hβ i, inv_mul_cancel₀ hχ0.ne', one_mul]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)

private theorem isLocalZeta30ConvergentAbove_of_norm_eq_one (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) {σ : ℝ} (hσ : 0 ≤ σ) :
    letI := localBorel ℚ v
    IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ 1 σ := by
  letI := localBorel ℚ v
  unfold IsLocalZeta30ConvergentAbove
  intro s hs
  have hint := integrable_comap_units_val v _
    (integrable_torusFn_of_pos_re v ν Φ hν hΦl hΦc χ hχ hu s (hσ.trans_lt hs))
  refine hint.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [charExt_coe_units]
  exact (torusIntegrand_coe_units v ν Φ χ s a).symm

end PrimalBridge

end WeylTranslateZeta
end

section

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace WeylTranslateZeta
open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_abscissa_inv_one_sub_mul_qpow_ne_zero (c : ℂ) :
    ∃ t : ℝ, ∀ w : ℂ, w.re ≠ t → (1 - c * LaurentZetaSlot.qv v ^ (-w))⁻¹ ≠ 0 := by
  have hQ1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := LaurentZetaSlot.one_lt_absNorm_real v
  have hQ0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hQ1
  have hlog : Real.log (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := (Real.log_pos hQ1).ne'
  refine ⟨Real.log ‖c‖ / Real.log (Ideal.absNorm v.asIdeal : ℝ), fun w hw => ?_⟩
  refine inv_ne_zero fun h => hw ?_
  have h1 : c * LaurentZetaSlot.qv v ^ (-w) = 1 := (sub_eq_zero.mp h).symm
  have hq : ‖LaurentZetaSlot.qv v ^ (-w)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-w).re :=
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (LaurentZetaSlot.absNorm_ne_zero v)) (-w)
  have h2 : ‖c‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-w.re) = 1 := by
    have h3 := congrArg norm h1
    rwa [norm_mul, hq, norm_one, Complex.neg_re] at h3
  have hc : ‖c‖ ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at h2
    exact zero_ne_one h2
  have h4 := congrArg Real.log h2
  rw [Real.log_mul hc (Real.rpow_pos_of_pos hQ0 _).ne', Real.log_rpow hQ0, Real.log_one] at h4
  rw [eq_div_iff hlog]
  linarith

private theorem exists_Ioo_subset_Ioo_diff_finset {α β : ℝ} (hαβ : α < β) (T : Finset ℝ) :
    ∃ α' β' : ℝ, α' < β' ∧ ∀ x : ℝ, α' < x → x < β' → (α < x ∧ x < β) ∧ x ∉ T := by
  have hinf : (Set.Ioo α β \ (T : Set ℝ)).Infinite := (Set.Ioo_infinite hαβ).diff T.finite_toSet
  obtain ⟨x, hx⟩ := hinf.nonempty
  have hopen : IsOpen (Set.Ioo α β \ (T : Set ℝ)) := isOpen_Ioo.sdiff T.finite_toSet.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  refine ⟨x - ε, x + ε, by linarith, fun y hy₁ hy₂ => ?_⟩
  have hy : y ∈ Set.Ioo α β \ (T : Set ℝ) := hball (by rw [Real.ball_eq_Ioo]; exact ⟨hy₁, hy₂⟩)
  exact ⟨hy.1, fun hyT => hy.2 (Finset.mem_coe.mpr hyT)⟩

private theorem localZetaDual31_one_sub_eq_of_isLaurentInQPow
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : Fin 3 → ℕ) (P Pd : ℂ → ℂ)
    (hP : IsLaurentInQPow (Ideal.absNorm v.asIdeal : ℂ) P) (hPd : IsLaurentInQPow (Ideal.absNorm v.asIdeal : ℂ) Pd)
    (σ₀ σ₁ : ℝ) (hσ : max σ₀ 0 < min (1 - σ₁) 1)
    (hprimal : ∀ s : ℂ, σ₀ < s.re →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1 =
        (∏ i, localLFactorAt ℚ v (ν i * χ) s) * P s)
    (hdual : ∀ s : ℂ, σ₁ < (1 - s).re →
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
        (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) * Pd s)
    (hlink : ∀ s : ℂ, σ₀ < s.re → σ₁ < (1 - s).re → 0 < s.re → s.re < 1 →
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
        (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
          ((∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) *
          ((∏ i, localLFactorAt ℚ v (ν i * χ) s)⁻¹ *
            localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1)) :
    ∀ s : ℂ, σ₁ < (1 - s).re →
      localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
        (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
          ((∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s := by

  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (LaurentZetaSlot.absNorm_ne_zero v)
  have hcol : IsLaurentInQPow (Ideal.absNorm v.asIdeal : ℂ) fun s : ℂ =>
      (∏ i, stdRootNumberAt ℚ v (ν i * χ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s)) *
        P s := by
    obtain ⟨Q, m, hQ⟩ := hP
    refine ⟨Polynomial.C ((∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (((∑ i, a i : ℕ) : ℂ) * (1 / 2))) * Polynomial.X ^ (∑ i, a i) * Q, m,
      fun s => ?_⟩
    show (∏ i, stdRootNumberAt ℚ v (ν i * χ)) * _ ^ _ * P s = _
    have hx : (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s)) =
        (Ideal.absNorm v.asIdeal : ℂ) ^ (((∑ i, a i : ℕ) : ℂ) * (1 / 2)) *
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (∑ i, a i) := by
      rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]
      congr 1
      push_cast
      ring
    rw [hQ s, hx]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring

  choose t ht using fun i : Fin 3 =>
    exists_abscissa_inv_one_sub_mul_qpow_ne_zero v (LaurentZetaSlot.slotScalar v (ν i * χ))
  choose t' ht' using fun i : Fin 3 =>
    exists_abscissa_inv_one_sub_mul_qpow_ne_zero v (LaurentZetaSlot.slotScalar v (ν i * χ)⁻¹)
  obtain ⟨α, β, hαβ, hsub⟩ := exists_Ioo_subset_Ioo_diff_finset hσ
    (Finset.univ.image t ∪ Finset.univ.image fun i => 1 - t' i)

  have hagree : ∀ s : ℂ, α < s.re → s.re < β →
      Pd s = (∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s)) * P s := by
    intro s hs₁ hs₂
    obtain ⟨⟨hlo, hhi⟩, hsT⟩ := hsub s.re hs₁ hs₂
    have h₀ : σ₀ < s.re := (le_max_left _ _).trans_lt hlo
    have h₀' : 0 < s.re := (le_max_right _ _).trans_lt hlo
    have h₁' : s.re < 1 := hhi.trans_le (min_le_right _ _)
    have h₁ : σ₁ < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith [hhi.trans_le (min_le_left _ _)]
    have hL : (∏ i, localLFactorAt ℚ v (ν i * χ) s) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      rw [LaurentZetaSlot.localLFactorAt_eq_inv_one_sub]
      refine ht i s fun hst => hsT ?_
      rw [hst]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem t (Finset.mem_univ i))
    have hLt : (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      rw [LaurentZetaSlot.localLFactorAt_eq_inv_one_sub]
      refine ht' i (1 - s) fun hst => hsT ?_
      rw [Complex.sub_re, Complex.one_re] at hst
      rw [show s.re = 1 - t' i by linarith]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i => 1 - t' i) (Finset.mem_univ i))
    have hl := hlink s h₀ h₁ h₀' h₁'
    rw [hprimal s h₀, inv_mul_cancel_left₀ hL, hdual s h₁, mul_assoc] at hl
    exact mul_left_cancel₀ hLt hl

  have hPd' : IsLaurentInQPow (((Ideal.absNorm v.asIdeal : ℝ) : ℂ)) Pd := by
    rw [Complex.ofReal_natCast]
    exact hPd
  have hcol' : IsLaurentInQPow (((Ideal.absNorm v.asIdeal : ℝ) : ℂ)) fun s : ℂ =>
      (∏ i, stdRootNumberAt ℚ v (ν i * χ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s)) *
        P s := by
    rw [Complex.ofReal_natCast]
    exact hcol
  have hall : ∀ s : ℂ, Pd s = (∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
      (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s)) * P s :=
    IsLaurentInQPow.eq_of_eqOn_strip (LaurentZetaSlot.one_lt_absNorm_real v) hPd' hcol' hαβ hagree
  intro s hs
  rw [hdual s hs, hall s]
  ring

end WeylTranslateZeta

end

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal MeasureTheory

open LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel
open WeylTranslateZeta

section

variable (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)

include hν hΦ hχ hu

private theorem primal_data :
    letI := localBorel ℚ v
    ∃ P : ℂ → ℂ,
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      ∀ s : ℂ, 0 < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1 =
          (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s := by
  letI := localBorel ℚ v
  classical
  let D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ :=
    fun α f a => f a - α * f (a / (uniformizerUnit ℚ v : v.adicCompletion ℚ))
  let c : Fin 3 → ℂ := fun i =>
    if HasConductorExponentAt ℚ v (ν i * χ) 0 then (((ν i) (uniformizerUnit ℚ v) : ℂˣ) : ℂ) else 0
  have hc₀ : ∀ i, HasConductorExponentAt ℚ v (ν i * χ) 0 →
      c i = (((ν i) (uniformizerUnit ℚ v) : ℂˣ) : ℂ) :=
    fun i h => by simp only [c, if_pos h]
  have hc₁ : ∀ i, ¬ HasConductorExponentAt ℚ v (ν i * χ) 0 → c i = 0 :=
    fun i h => by simp only [c, if_neg h]
  have hrec :=
    (eventually_threefold_twistedDifference_torusJacquetValueFn_eq_zero v ν hν Φ hΦ.1 hΦ.2 D (fun _ _ _ => rfl)
      (torusFn v ν Φ) (torusFn_zero v ν Φ) (fun a => torusFn_coe_units v ν Φ a)).2 χ hχ c hc₀ hc₁
  obtain ⟨P, hPL, hid⟩ :=
    exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference v (fun i => ν i * χ) hu χ hχ c
      (fun i h => by simp only [hc₀ i h, MonoidHom.mul_apply, Units.val_mul]) hc₁ D (fun _ _ _ => rfl) (torusFn v ν Φ)
      (fun t ht => eventually_torusFn_eq v ν Φ hν hΦ.1 hΦ.2 ht) (exists_torusFn_eq_zero_of_lt v ν Φ hν hΦ.1 hΦ.2) hrec
  exact ⟨P, hPL, fun s hs => (localZeta30_eq_localZeta_torusFn v ν Φ χ s).trans
    (hid s hs (integrable_torusFn_of_pos_re v ν Φ hν hΦ.1 hΦ.2 χ hχ hu s hs))⟩

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

private theorem dual_side (P : ℂ → ℂ)
    (hPL : ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
      P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s))
    (hid : ∀ s : ℂ, 0 < s.re →
      localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1 =
        (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s) :
    letI := localBorel ℚ v
    ∃ σ₁ : ℝ,
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)))
        χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
      ∃ a : Fin 3 → ℕ, (∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i * χ) (a i)) ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
            (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
              ((∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i * χ)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s := by
  letI := localBorel ℚ v
  obtain ⟨Pd, hPdL, hdual⟩ := exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one v ν hν Φ hΦ χ hχ hu
  have hconv₁ := isLocalZeta31ConvergentAbove_dualWhittakerFn3_of_norm_eq_one v ν Φ hν hΦ.1 hΦ.2 χ hχ hu
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hconv₀ := isLocalZeta30ConvergentAbove_of_norm_eq_one v ν Φ hν hΦ.1 hΦ.2 χ hχ hu (le_refl (0 : ℝ))
  choose a ha using fun i => exists_hasConductorExponentAt_of_isLocallyConstant ℚ v (ν i * χ)
    ((hν i).mul hχ)
  refine ⟨1 / 4, hconv₁, a, ha, ?_⟩
  refine localZetaDual31_one_sub_eq_of_isLaurentInQPow v ν Φ χ a P Pd hPL hPdL 0 (1 / 4) (by norm_num)
    (fun s hs => hid s hs) (fun s hs => hdual s (by linarith)) (fun s hs₀ hs₁ hs hs' => ?_)
  exact localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip v ν hν Φ hΦ χ hχ hu a ha 0 (1 / 4) hconv₀ hconv₁
    s hs₀ hs₁ hs hs'

end

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ 1 σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1 =
          (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)))
        χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
      ∃ a : Fin 3 → ℕ, (∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i * χ) (a i)) ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
            (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
              ((∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i * χ)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s := by
  obtain ⟨P, hPL, hid⟩ := primal_data v ν hν Φ hΦ χ hχ hu
  obtain ⟨σ₁, hconv₁, a, ha, hdual⟩ := dual_side v ν hν Φ hΦ χ hχ hu P hPL hid
  exact ⟨P, 0, σ₁, hPL, isLocalZeta30ConvergentAbove_of_norm_eq_one v ν Φ hν hΦ.1 hΦ.2 χ hχ hu le_rfl, hid,
    hconv₁, a, ha, hdual⟩

end S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3 (solution)
