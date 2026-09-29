-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/df9e3e29-a951-55e6-9872-c68f156a9b52

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue
import Theorems.Thm_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue
import Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta_tateFourier_mul_localLFactorAt_eq
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

section Part2

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdRootNumberAt HasConductorExponentAt hasConductorExponentAt_zero_iff localLFactorAt modulus modulus_ne_zero IsSchwartzBruhat tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta modulus_adicCompletion_eq_nnnorm addCharLevel_psiLocal_rat psiLocal_ne_one stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one psiLocal_eq_one_of_mem_integers"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

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

private theorem sFinite_mulMeasure_selfDualHaarAt :
    letI := localBorel K v
    SFinite (mulMeasure (selfDualHaarAt K v)) := by
  letI := localBorel K v
  haveI := sFinite_selfDualHaarAt K v
  unfold mulMeasure
  infer_instance

end MeasureClasses

end LanglandsTunnell.TateLocal
end Part2

section Part1

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

open Polynomial in
private def IsLaurentInQPow (q : ℂ) (P : ℂ → ℂ) : Prop :=
  ∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ, P s = Q.eval (q ^ (-s)) * q ^ ((m : ℂ) * s)

namespace IsLaurentInQPow

variable {q : ℂ}

private theorem qpow_add_nat_mul_mul_pow (hq : q ≠ 0) (m k : ℕ) (s : ℂ) :
    q ^ (((m + k : ℕ) : ℂ) * s) * (q ^ (-s)) ^ k = q ^ ((m : ℂ) * s) := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq]
  congr 1
  push_cast
  ring

private theorem add (hq : q ≠ 0) {P₁ P₂ : ℂ → ℂ} (h₁ : IsLaurentInQPow q P₁) (h₂ : IsLaurentInQPow q P₂) :
    IsLaurentInQPow q fun s => P₁ s + P₂ s := by
  obtain ⟨Q₁, m₁, e₁⟩ := h₁
  obtain ⟨Q₂, m₂, e₂⟩ := h₂
  refine ⟨Q₁ * Polynomial.X ^ m₂ + Q₂ * Polynomial.X ^ m₁, m₁ + m₂, fun s => ?_⟩
  show P₁ s + P₂ s = _
  rw [e₁ s, e₂ s, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_pow, Polynomial.eval_X, add_mul]
  have h₁' := qpow_add_nat_mul_mul_pow hq m₁ m₂ s
  have h₂' := qpow_add_nat_mul_mul_pow hq m₂ m₁ s
  rw [add_comm m₂ m₁] at h₂'
  rw [← h₁', ← h₂']
  ring

end IsLaurentInQPow

namespace LaurentZetaSlot

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem _root_.LaurentZetaSlot.absNorm_ne_zero : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by
  intro h0
  have h := one_lt_absNorm_real v
  rw [h0] at h
  norm_num at h

p2m_export "LaurentZetaSlot" "absNorm_ne_zero"
private def shell (j : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x = WithZero.exp (-j)}

private theorem modulus_eq_of_mem_shell {j : ℤ} {x : v.adicCompletion ℚ} (hx : x ∈ shell v j) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-j) := by
  have hnorm : ‖x‖ = ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ≥0) : ℝ) :=
    FinitePlace.norm_def v x
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x]
  apply NNReal.coe_injective
  rw [coe_nnnorm, hnorm, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have htoAdd : ∀ h : WithZero.exp (-j) ≠ (0 : WithZero (Multiplicative ℤ)),
      Multiplicative.toAdd (WithZero.unzero h) = -j := fun _ => rfl
  rw [htoAdd]

private def unitShell : Set (v.adicCompletion ℚ) := {x | Valued.v x = 1}

private theorem isAddHaarMeasure_selfDualHaarAt' : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  exact LanglandsTunnell.TateLocal.isAddHaarMeasure_selfDualHaarAt ℚ v

private theorem sFinite_mulMeasure_selfDualHaarAt' : SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by
  exact LanglandsTunnell.TateLocal.sFinite_mulMeasure_selfDualHaarAt ℚ v

attribute [local instance] sFinite_mulMeasure_selfDualHaarAt'

private theorem isClopen_shell (j : ℤ) : IsClopen (shell v j) := by
  obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp (-j))
  have hset : shell v j = {x | Valued.v.restrict x = Valued.v.restrict x₀} := by
    ext x
    simp only [shell, Set.mem_setOf_eq, Valuation.restrict_inj, hx₀]
  have hne : Valued.v.restrict x₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v x₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero, hx₀] at h1
    exact WithZero.exp_ne_zero h1
  rw [hset]
  exact Valued.isClopen_sphere _ hne

private theorem unitShell_eq_shell_zero : unitShell v = shell v 0 := by
  simp only [unitShell, shell, neg_zero, WithZero.exp_zero]

private theorem modulus_eq_one_of_mem_unitShell {x : v.adicCompletion ℚ} (hx : x ∈ unitShell v) : modulus x = 1 := by
  rw [unitShell_eq_shell_zero] at hx
  rw [modulus_eq_of_mem_shell v hx, neg_zero, zpow_zero]

private theorem isClopen_unitShell : IsClopen (unitShell v) := by
  rw [unitShell_eq_shell_zero]
  exact isClopen_shell v 0

private theorem measurableSet_unitShell : MeasurableSet (unitShell v) :=
  (isClopen_unitShell v).isOpen.measurableSet

private theorem unitShell_subset_integers : unitShell v ⊆ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  fun x hx => by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hx

private theorem isCompact_unitShell : IsCompact (unitShell v) := by
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    rw [← coe_integersPositiveCompacts ℚ v]
    exact (integersPositiveCompacts ℚ v).isCompact
  exact hO.of_isClosed_subset (isClopen_unitShell v).isClosed (unitShell_subset_integers v)

private theorem
    mulMeasure_unitShell : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) = selfDualHaarAt ℚ v (unitShell v) := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_unitShell v),
    Measure.restrict_restrict (measurableSet_unitShell v)]
  have hsub : unitShell v ∩ {(0 : v.adicCompletion ℚ)}ᶜ = unitShell v := by
    refine Set.inter_eq_left.mpr fun x hx => ?_
    rintro rfl
    simp [unitShell] at hx
  rw [hsub]
  calc ∫⁻ x in unitShell v, ((modulus x : ℝ≥0∞))⁻¹ ∂(selfDualHaarAt ℚ v)
      = ∫⁻ _ in unitShell v, (1 : ℝ≥0∞) ∂(selfDualHaarAt ℚ v) := by
        refine setLIntegral_congr_fun (measurableSet_unitShell v) fun x hx => ?_
        rw [modulus_eq_one_of_mem_unitShell v hx]
        simp
    _ = selfDualHaarAt ℚ v (unitShell v) := by simp

private theorem mulMeasure_unitShell_lt_top : mulMeasure (selfDualHaarAt ℚ v) (unitShell v) < ⊤ := by
  haveI := isAddHaarMeasure_selfDualHaarAt' v
  rw [mulMeasure_unitShell]
  exact (isCompact_unitShell v).measure_lt_top

private scoped instance isFiniteMeasure_restrict_unitShell :
    IsFiniteMeasure ((mulMeasure (selfDualHaarAt ℚ v)).restrict (unitShell v)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact mulMeasure_unitShell_lt_top v⟩

private theorem isLocallyConstant_inv (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    IsLocallyConstant (⇑χ⁻¹ : (v.adicCompletion ℚ)ˣ → ℂˣ) := by
  have h : (⇑χ⁻¹ : (v.adicCompletion ℚ)ˣ → ℂˣ) = fun x => (χ x)⁻¹ := by
    funext x
    simp
  rw [h]
  exact IsLocallyConstant.comp hχ fun y : ℂˣ => y⁻¹

private theorem exists_mem_shell {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ j : ℤ, x ∈ shell v j := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨-WithZero.log (Valued.v x), ?_⟩
  show Valued.v x = WithZero.exp (- -WithZero.log (Valued.v x))
  rw [neg_neg, WithZero.exp_log hv]

end LaurentZetaSlot
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part5

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 gl3AmbientRightTranslate transposeInv3 iotaGL LocalGL3 diagUnitGL2 jacquetValue cellSectionOf jacquetWhittaker3 jacquetWhittaker3_apply antidiagonal3 tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue localZeta_tateFourier_mul_localLFactorAt_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def torusTranslate (a : (v.adicCompletion ℚ)ˣ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (iotaGL (diagUnitGL2 a) * antidiagonal3 v) (cellSectionOf v ν Φ)

open Classical in
private noncomputable def torusFn : v.adicCompletion ℚ → ℂ := fun t =>
  if h : t = 0 then 0 else
    jacquetValue v (torusTranslate v ν Φ (Units.mk0 t h)) * ((modulus t : ℝ) : ℂ)⁻¹

private theorem torusFn_coe_units (a : (v.adicCompletion ℚ)ˣ) :
    torusFn v ν Φ a = jacquetValue v (torusTranslate v ν Φ a) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp [torusFn, a.ne_zero]

private theorem modulus_real_eq_norm (x : v.adicCompletion ℚ) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

private theorem _root_.LanglandsTunnell.CubicInduction.one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

p2m_export "LanglandsTunnell.CubicInduction" "one_lt_absNorm_real"
private theorem isClosed_valued_le (n : ℤ) : IsClosed {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  rw [hset]
  exact Valued.isClosed_closedBall _ _

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

end TorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part5
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part6

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 gl3AmbientRightTranslate transposeInv3 iotaGL LocalGL3 diagUnitGL2 jacquetValue cellSectionOf jacquetWhittaker3 jacquetWhittaker3_apply antidiagonal3 tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue localZeta_tateFourier_mul_localLFactorAt_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section DualTorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private noncomputable def dualPoint (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v :=
  longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
    antidiagonal3 v

private noncomputable def dualTranslate (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) : LocalGL3 v → ℂ :=
  gl3AmbientRightTranslate (R := ℂ) (dualPoint v a x) (cellSectionOf v ν Φ)

private theorem dualWhittakerFn3_apply_eq_jacquetValue (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v))
        (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) =
      jacquetValue v (dualTranslate v ν Φ a x) := by
  rfl

open Classical in
private noncomputable def dualFn : v.adicCompletion ℚ → ℂ := fun t =>
  letI := localBorel ℚ v
  if h : t = 0 then 0 else
    (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ (Units.mk0 t h) x) ∂(selfDualHaarAt ℚ v)) *
      ((modulus t : ℝ) : ℂ)⁻¹

private theorem dualFn_coe_units (a : (v.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ v
    dualFn v ν Φ a =
      (∫ x : v.adicCompletion ℚ, jacquetValue v (dualTranslate v ν Φ a x) ∂(selfDualHaarAt ℚ v)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
  simp [dualFn, a.ne_zero]

end DualTorusValues
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part6
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part10

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open NumberField.StandardAddChar
open NumberField.AdelicLevel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdRootNumberAt HasConductorExponentAt hasConductorExponentAt_zero_iff localLFactorAt modulus modulus_ne_zero IsSchwartzBruhat tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta modulus_adicCompletion_eq_nnnorm addCharLevel_psiLocal_rat psiLocal_ne_one stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one psiLocal_eq_one_of_mem_integers"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section RootNumber

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

private theorem stdRootNumberAt_eq_one_of_unramified (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (h0 : HasConductorExponentAt ℚ v η 0) (hu : ‖(η (uniformizerUnit ℚ v) : ℂ)‖ = 1) :
    stdRootNumberAt ℚ v η = 1 :=
  stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero ℚ v η h0 hu (addCharLevel_psiLocal_rat v)
    (psiLocal_ne_one ℚ v)

end RootNumber
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part10
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part12

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open NumberField.StandardAddChar
open NumberField.AdelicLevel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdRootNumberAt HasConductorExponentAt hasConductorExponentAt_zero_iff localLFactorAt modulus modulus_ne_zero IsSchwartzBruhat tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta modulus_adicCompletion_eq_nnnorm addCharLevel_psiLocal_rat psiLocal_ne_one stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one psiLocal_eq_one_of_mem_integers"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section GaussProductViaRootNumbers

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

private theorem hasConductorExponentAt_inv {η : (w.adicCompletion K)ˣ →* ℂˣ} {a : ℕ}
    (hη : HasConductorExponentAt K w η a) : HasConductorExponentAt K w η⁻¹ a := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.inv_apply, hη.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hη.2 m hm
    exact ⟨u, hu, by rwa [MonoidHom.inv_apply, Ne, inv_eq_one]⟩

private theorem norm_inv_apply_uniformizerUnit {η : (w.adicCompletion K)ˣ →* ℂˣ}
    (hu : ‖(η (uniformizerUnit K w) : ℂ)‖ = 1) : ‖(η⁻¹ (uniformizerUnit K w) : ℂ)‖ = 1 := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]

end GaussProductViaRootNumbers
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section GaussProductRat

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

end GaussProductRat
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part12
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part13

set_option autoImplicit false

open IsDedekindDomain
open NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts selfDualHaarAt stdRootNumberAt HasConductorExponentAt hasConductorExponentAt_zero_iff localLFactorAt modulus modulus_ne_zero IsSchwartzBruhat tateFourier charExt charExt_of_ne_zero charExt_coe_units mulMeasure localZeta modulus_adicCompletion_eq_nnnorm addCharLevel_psiLocal_rat psiLocal_ne_one stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one psiLocal_eq_one_of_mem_integers"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

section ConductorWitness

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

end ConductorWitness
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section NormPowerAssembly

private theorem prod_cpow_natCast_mul_eq (q : ℂ) (hq : q ≠ 0) (a : Fin 3 → ℕ) (s : ℂ) :
    ∏ i, q ^ ((a i : ℂ) * (1 / 2 - s)) = q ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s)) := by
  rw [Fin.prod_univ_three, Fin.sum_univ_three, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
  congr 1
  ring

end NormPowerAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part13
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part15

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 gl3AmbientRightTranslate transposeInv3 iotaGL LocalGL3 diagUnitGL2 jacquetValue cellSectionOf jacquetWhittaker3 jacquetWhittaker3_apply antidiagonal3 tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue localZeta_tateFourier_mul_localLFactorAt_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem integrable_mulMeasure_of_integrable_comap_units (G : v.adicCompletion ℚ → ℂ)
    (hG : Integrable (fun a : (v.adicCompletion ℚ)ˣ => G a)
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) :
    Integrable G (mulMeasure (selfDualHaarAt ℚ v)) := by
  have hemb : MeasurableEmbedding (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) :=
    measurableEmbedding_units_val ℚ v
  have hres : (mulMeasure (selfDualHaarAt ℚ v)).restrict {0}ᶜ = mulMeasure (selfDualHaarAt ℚ v) :=
    mulMeasure_restrict_compl_zero ℚ v _
  rw [← hres, ← range_units_val_eq ℚ v, ← hemb.map_comap (mulMeasure (selfDualHaarAt ℚ v)), hemb.integrable_map_iff]
  exact hG

private theorem integrable_torusFn_mul_charExt_of_convergentAbove
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (σ₀ : ℝ)
    (h₀ : IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ 1 σ₀)
    (s : ℂ) (hs₀ : σ₀ < s.re) :
    Integrable (fun x => torusFn v ν Φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v)) := by
  have h : Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
      jacquetWhittaker3 v ν Φ (iotaGL (diagUnitGL2 a) * 1 * antidiagonal3 v) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := h₀ s hs₀
  have hfun : (fun a : (v.adicCompletion ℚ)ˣ =>
      torusFn v ν Φ a * charExt χ a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s) =
      fun a : (v.adicCompletion ℚ)ˣ =>
        jacquetWhittaker3 v ν Φ (iotaGL (diagUnitGL2 a) * 1 * antidiagonal3 v) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) := by
    funext a
    have hm : ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (modulus_ne_zero a.ne_zero))
    rw [torusFn_coe_units, charExt_coe_units, mul_one, Complex.cpow_sub s 1 hm, Complex.cpow_one,
      show jacquetWhittaker3 v ν Φ (iotaGL (diagUnitGL2 a) * antidiagonal3 v) =
        jacquetValue v (torusTranslate v ν Φ a) from rfl]
    ring
  have h2 : Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
      torusFn v ν Φ a * charExt χ a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    rw [hfun]
    exact h
  exact integrable_mulMeasure_of_integrable_comap_units v
    (fun x => torusFn v ν Φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) h2

private theorem integrable_dualFn_mul_charExt_inv_of_convergentAbove
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (σ₁ : ℝ)
    (h₁ : IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)))
      χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁)
    (s : ℂ) (hs₁ : σ₁ < (1 - s).re) :
    Integrable (fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure (selfDualHaarAt ℚ v)) := by
  have h : Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      jacquetValue v (dualTranslate v ν Φ p.1 p.2) * ((χ⁻¹ p.1 : ℂˣ) : ℂ) *
        ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1))
      ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))).prod (selfDualHaarAt ℚ v)) := h₁ (1 - s) hs₁
  haveI : SFinite (selfDualHaarAt ℚ v) := sFinite_selfDualHaarAt ℚ v
  have h2 : Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
      ∫ y, jacquetValue v (dualTranslate v ν Φ a y) * ((χ⁻¹ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂(selfDualHaarAt ℚ v))
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := h.integral_prod_left
  have hfun : (fun a : (v.adicCompletion ℚ)ˣ =>
      dualFn v ν Φ a * charExt χ⁻¹ a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s)) =
      fun a : (v.adicCompletion ℚ)ˣ =>
        ∫ y, jacquetValue v (dualTranslate v ν Φ a y) * ((χ⁻¹ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1) ∂(selfDualHaarAt ℚ v) := by
    funext a
    have hm : ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (modulus_ne_zero a.ne_zero))
    rw [integral_mul_const, integral_mul_const, charExt_coe_units, Complex.cpow_sub (1 - s) 1 hm, Complex.cpow_one,
      show dualFn v ν Φ a = (∫ x, jacquetValue v (dualTranslate v ν Φ a x) ∂(selfDualHaarAt ℚ v)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ from dualFn_coe_units v ν Φ a]
    ring
  have h3 : Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
      dualFn v ν Φ a * charExt χ⁻¹ a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s))
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    rw [hfun]
    exact h2
  exact integrable_mulMeasure_of_integrable_comap_units v
    (fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)) h3

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part15
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part17

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 gl3AmbientRightTranslate transposeInv3 iotaGL LocalGL3 diagUnitGL2 jacquetValue cellSectionOf jacquetWhittaker3 jacquetWhittaker3_apply antidiagonal3 tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue localZeta_tateFourier_mul_localLFactorAt_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def truncChar (c : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  if Valued.v t ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v t : ℂ) else 0

private noncomputable def gaussIntegral (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ) (c : ℤ) : ℂ :=
  localZeta (selfDualHaarAt ℚ v) (fun t => truncChar v c (-t)) η z

private noncomputable def coupledIntegral (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c : ℤ) : ℂ :=
  ∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      Φ ![p.1, p.2.1, p.2.2] *
        (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
        (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
        (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
        truncChar v c (p.2.2 / (p.2.1 - p.1 * p.2.2))
    ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
end Part17
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 gl3AmbientRightTranslate transposeInv3 iotaGL LocalGL3 diagUnitGL2 jacquetValue cellSectionOf jacquetWhittaker3 jacquetWhittaker3_apply antidiagonal3 tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue localZeta_tateFourier_mul_localLFactorAt_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal"

section TorusSide

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

end TorusSide
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section DualSide

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

private theorem localZetaDual31_eq_localZeta_dualFn' (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
      localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s) := by
  rw [localZeta_eq_integral_units ℚ v]
  unfold localZetaDual31 localZeta31
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hM : ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 := by
    rw [modulus_real_eq_norm]
    exact_mod_cast (norm_pos_iff.mpr a.ne_zero).ne'
  simp only [dualWhittakerFn3_apply_eq_jacquetValue]
  rw [dualFn_coe_units, Complex.cpow_sub _ _ hM, Complex.cpow_one, div_eq_mul_inv]
  ring

private theorem localZetaDual31_eq_localZeta_dualFn (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    letI := localBorel ℚ v
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
      localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s) := by
  exact localZetaDual31_eq_localZeta_dualFn' v ν Φ χ s

end DualSide
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

section Part24
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localZeta31 localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 gl3AmbientRightTranslate transposeInv3 iotaGL LocalGL3 diagUnitGL2 jacquetValue cellSectionOf jacquetWhittaker3 jacquetWhittaker3_apply antidiagonal3 tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue localZeta_tateFourier_mul_localLFactorAt_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem tendsto_gaussIntegral_mul_coupledIntegral_localZeta_torusFn
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hint : Integrable (fun x => torusFn v ν Φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v))) :
    Filter.Tendsto
      (fun c : ℤ => charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c *
        coupledIntegral v ν Φ χ s c)
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s)) := by
  exact tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue v ν hν Φ hΦl hΦc (torusFn v ν Φ)
    (torusFn_coe_units v ν Φ) χ hχ hu s hs hs' hint

private theorem tendsto_gaussIntegral_mul_coupledIntegral_localZeta_dualFn
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hint : Integrable (fun x => dualFn v ν Φ x * charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s))
      (mulMeasure (selfDualHaarAt ℚ v))) :
    Filter.Tendsto
      (fun c : ℤ => gaussIntegral v (ν 0 * χ)⁻¹ (1 - s) c * gaussIntegral v (ν 1 * χ)⁻¹ (1 - s) c *
        coupledIntegral v ν Φ χ s c)
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s))) := by
  exact tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue v ν hν Φ hΦl hΦc χ hχ hu s hs hs'
    (dualFn v ν Φ) (dualFn_coe_units v ν Φ) hint

section Closing

open Filter NumberField.StandardAddChar

private scoped instance instBorelSpaceLink : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v

private scoped instance instIsAddHaarLink : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt ℚ v

private def levelBall (c : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v x ≤ WithZero.exp (-c)}

private def negOneCoset (c : ℤ) : Set (v.adicCompletion ℚ) := {x | Valued.v (1 + x) ≤ WithZero.exp (-c)}

private noncomputable def cosetInd (c : ℤ) (x : v.adicCompletion ℚ) : ℂ :=
  if Valued.v (1 + x) ≤ WithZero.exp (-c) then 1 else 0

private theorem localZeta_const_mul (μ : Measure (v.adicCompletion ℚ)) (b : ℂ) (f : v.adicCompletion ℚ → ℂ)
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ) :
    localZeta μ (fun t => b * f t) η z = b * localZeta μ f η z := by
  simp only [localZeta, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun t => by ring)

private theorem psiLocal_eq_one_of_valued_le_one {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) :
    psiLocal ℚ v x = 1 := by
  apply psiLocal_eq_one_of_mem_integers
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact hx

private theorem isOpen_valued_le (n : ℤ) : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n} := by
  obtain ⟨y₀, hy₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp n}
      = {x | Valued.v.restrict x ≤ Valued.v.restrict y₀} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Valuation.restrict_le_iff, hy₀]
  have hne : Valued.v.restrict y₀ ≠ 0 := by
    intro h0
    have h1 : Valued.v y₀ = Valued.v (0 : v.adicCompletion ℚ) :=
      (Valuation.restrict_inj Valued.v).mp (by rw [h0, map_zero])
    rw [map_zero, hy₀] at h1
    exact WithZero.exp_ne_zero h1
  rw [hset]
  exact Valued.isOpen_closedBall _ hne

private theorem measurableSet_levelBall (c : ℤ) : MeasurableSet (levelBall v c) :=
  (isClosed_valued_le v (-c)).measurableSet

private theorem valued_eq_one_of_valued_one_add_le {c : ℤ} (hc : 1 ≤ c) {x : v.adicCompletion ℚ}
    (hx : Valued.v (1 + x) ≤ WithZero.exp (-c)) : Valued.v x = 1 := by
  have hlt : Valued.v (1 + x) < Valued.v (-1 : v.adicCompletion ℚ) := by
    rw [Valuation.map_neg, map_one, ← WithZero.exp_zero]
    exact hx.trans_lt (WithZero.exp_lt_exp.2 (by omega))
  have hx' : x = 1 + x + -1 := by ring
  rw [hx']
  exact (Valued.v.map_add_eq_of_lt_right hlt).trans (by rw [Valuation.map_neg, map_one])

private theorem levelBall_real_pos {c : ℤ} (hc : 0 ≤ c) : 0 < (selfDualHaarAt ℚ v).real (levelBall v c) := by
  have hpos : 0 < selfDualHaarAt ℚ v (levelBall v c) := by
    refine (isOpen_valued_le v (-c)).measure_pos _ ⟨0, ?_⟩
    show Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp (-c)
    rw [map_zero]
    exact zero_le'
  have hlt : selfDualHaarAt ℚ v (levelBall v c) < ⊤ := by
    have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [← coe_integersPositiveCompacts ℚ v]
      exact (integersPositiveCompacts ℚ v).isCompact
    refine (hO.of_isClosed_subset (isClosed_valued_le v (-c)) fun x hx => ?_).measure_lt_top
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
    refine le_trans hx ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by omega)
  rw [Measure.real, ENNReal.toReal_pos_iff]
  exact ⟨hpos, hlt⟩

private theorem integral_indicator_levelBall_psiLocal (c : ℤ) (y : v.adicCompletion ℚ) :
    ∫ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v) =
      if Valued.v y ≤ WithZero.exp c then ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) else 0 := by
  have hBm := measurableSet_levelBall v c
  split_ifs with hy
  · have h1 : Set.EqOn (fun x => (psiLocal ℚ v (x * y) : ℂ)) (fun _ => 1) (levelBall v c) := by
      intro x hx
      show (psiLocal ℚ v (x * y) : ℂ) = 1
      apply psiLocal_eq_one_of_valued_le_one v
      rw [map_mul]
      calc Valued.v x * Valued.v y ≤ WithZero.exp (-c) * WithZero.exp c := mul_le_mul' hx hy
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    rw [integral_indicator hBm, setIntegral_congr_fun hBm h1, setIntegral_const, Complex.real_smul, mul_one]
  · push Not at hy
    obtain ⟨ε, hε, hψ⟩ := exists_psiLocal_neg_ne_one v
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact not_lt_zero hy
    obtain ⟨j, hj⟩ := LaurentZetaSlot.exists_mem_shell v hy0
    have hvy : Valued.v y = WithZero.exp (-j) := hj
    have hcj : c + 1 ≤ -j := by
      have h := hy
      rw [hvy, WithZero.exp_lt_exp] at h
      omega
    set x₀ : v.adicCompletion ℚ := -ε / y with hx₀
    have hx₀B : x₀ ∈ levelBall v c := by
      show Valued.v x₀ ≤ WithZero.exp (-c)
      calc Valued.v x₀ = Valued.v ε * (Valued.v y)⁻¹ := by
            rw [hx₀, map_div₀, Valuation.map_neg, div_eq_mul_inv]
        _ = Valued.v ε * WithZero.exp j := by rw [hvy, WithZero.exp_neg, inv_inv]
        _ ≤ WithZero.exp 1 * WithZero.exp j := mul_le_mul_left hε _
        _ = WithZero.exp (1 + j) := (WithZero.exp_add _ _).symm
        _ ≤ WithZero.exp (-c) := WithZero.exp_le_exp.2 (by omega)
    have hxy : x₀ * y = -ε := by rw [hx₀, div_mul_cancel₀ _ hy0]
    have hshift : ∀ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) (x₀ + x) =
        (psiLocal ℚ v (-ε) : ℂ) * (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x := by
      intro x
      by_cases hx : x ∈ levelBall v c
      · have hx' : x₀ + x ∈ levelBall v c := by
          show Valued.v (x₀ + x) ≤ WithZero.exp (-c)
          exact (Valuation.map_add _ _ _).trans (max_le hx₀B hx)
        rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, add_mul, hxy, AddChar.map_add_eq_mul]
      · have hx' : x₀ + x ∉ levelBall v c := by
          intro h
          apply hx
          show Valued.v x ≤ WithZero.exp (-c)
          have hxx : x = x₀ + x - x₀ := by ring
          rw [hxx]
          exact (Valuation.map_sub _ _ _).trans (max_le h hx₀B)
        rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
    have hI : ∫ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v) =
        (psiLocal ℚ v (-ε) : ℂ) *
          ∫ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v) := by
      calc ∫ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v)
          = ∫ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) (x₀ + x) ∂(selfDualHaarAt ℚ v) :=
            (integral_add_left_eq_self _ x₀).symm
        _ = ∫ x, (psiLocal ℚ v (-ε) : ℂ) *
              (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v) :=
            integral_congr_ae (Eventually.of_forall hshift)
        _ = _ := integral_const_mul _ _
    have hzero : (1 - (psiLocal ℚ v (-ε) : ℂ)) *
        ∫ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v) = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd (sub_eq_zero.1 h).symm hψ
    · exact h

private theorem tateFourier_cosetInd (c : ℤ) (y : v.adicCompletion ℚ) :
    tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (cosetInd v c) y =
      ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) * truncChar v c (-y) := by
  unfold tateFourier
  have hshift : ∀ x, cosetInd v c (-1 + x) * (psiLocal ℚ v ((-1 + x) * y) : ℂ) =
      (psiLocal ℚ v (-y) : ℂ) * (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x := by
    intro x
    have hx : (1 : v.adicCompletion ℚ) + (-1 + x) = x := add_neg_cancel_left 1 x
    rw [show (-1 + x) * y = -y + x * y by ring, AddChar.map_add_eq_mul]
    simp only [cosetInd, hx, Set.indicator_apply, levelBall, Set.mem_setOf_eq]
    split_ifs <;> ring
  calc ∫ x, cosetInd v c x * psiLocal ℚ v (x * y) ∂(selfDualHaarAt ℚ v)
      = ∫ x, cosetInd v c (-1 + x) * psiLocal ℚ v ((-1 + x) * y) ∂(selfDualHaarAt ℚ v) :=
        (integral_add_left_eq_self (μ := selfDualHaarAt ℚ v)
          (fun x => cosetInd v c x * psiLocal ℚ v (x * y)) (-1)).symm
    _ = ∫ x, (psiLocal ℚ v (-y) : ℂ) *
          (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v) :=
        integral_congr_ae (Eventually.of_forall hshift)
    _ = (psiLocal ℚ v (-y) : ℂ) *
          ∫ x, (levelBall v c).indicator (fun x => (psiLocal ℚ v (x * y) : ℂ)) x ∂(selfDualHaarAt ℚ v) :=
        integral_const_mul _ _
    _ = _ := by
        rw [integral_indicator_levelBall_psiLocal]
        simp only [truncChar, Valuation.map_neg]
        split_ifs <;> ring

private theorem mass_mul_gaussIntegral (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ) (c : ℤ) :
    ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) * gaussIntegral v η z c =
      localZeta (selfDualHaarAt ℚ v) (tateFourier (psiLocal ℚ v) (selfDualHaarAt ℚ v) (cosetInd v c)) η z := by
  rw [gaussIntegral, ← localZeta_const_mul]
  congr 1
  funext t
  exact (tateFourier_cosetInd v c t).symm

private theorem isSchwartzBruhat_cosetInd {c : ℤ} (hc : 1 ≤ c) : IsSchwartzBruhat (cosetInd v c) := by
  have hcl : IsClosed (negOneCoset v c) :=
    (isClosed_valued_le v (-c)).preimage (continuous_const.add continuous_id)
  have hop : IsOpen (negOneCoset v c) :=
    (isOpen_valued_le v (-c)).preimage (continuous_const.add continuous_id)
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : Valued.v (1 + x) ≤ WithZero.exp (-c)
    · refine ⟨negOneCoset v c, hop, hx, fun y hy => ?_⟩
      have hy' : Valued.v (1 + y) ≤ WithZero.exp (-c) := hy
      simp only [cosetInd, if_pos hx, if_pos hy']
    · refine ⟨(negOneCoset v c)ᶜ, hcl.isOpen_compl, hx, fun y hy => ?_⟩
      have hy' : ¬ Valued.v (1 + y) ≤ WithZero.exp (-c) := hy
      simp only [cosetInd, if_neg hx, if_neg hy']
  · refine HasCompactSupport.intro (LaurentZetaSlot.isCompact_unitShell v) fun x hx => ?_
    have hx' : ¬ Valued.v (1 + x) ≤ WithZero.exp (-c) := fun h => hx (valued_eq_one_of_valued_one_add_le v hc h)
    simp only [cosetInd, if_neg hx']

private theorem mulMeasure_real_negOneCoset {c : ℤ} (hc : 1 ≤ c) :
    (mulMeasure (selfDualHaarAt ℚ v)).real (negOneCoset v c) = (selfDualHaarAt ℚ v).real (levelBall v c) := by
  have hCm : MeasurableSet (negOneCoset v c) :=
    ((isClosed_valued_le v (-c)).preimage (continuous_const.add continuous_id)).measurableSet
  have h1 : mulMeasure (selfDualHaarAt ℚ v) (negOneCoset v c) = selfDualHaarAt ℚ v (negOneCoset v c) := by
    rw [mulMeasure, withDensity_apply _ hCm, Measure.restrict_restrict hCm]
    have hsub : negOneCoset v c ∩ {(0 : v.adicCompletion ℚ)}ᶜ = negOneCoset v c := by
      refine Set.inter_eq_left.mpr fun x hx h0 => ?_
      have h1 : Valued.v x = 1 := valued_eq_one_of_valued_one_add_le v hc hx
      rw [Set.mem_singleton_iff.mp h0, map_zero] at h1
      exact zero_ne_one h1
    rw [hsub]
    calc ∫⁻ x in negOneCoset v c, ((modulus x : ENNReal))⁻¹ ∂(selfDualHaarAt ℚ v)
        = ∫⁻ _ in negOneCoset v c, (1 : ENNReal) ∂(selfDualHaarAt ℚ v) := by
          refine setLIntegral_congr_fun hCm fun x hx => ?_
          rw [LaurentZetaSlot.modulus_eq_one_of_mem_unitShell v (valued_eq_one_of_valued_one_add_le v hc hx)]
          simp
      _ = selfDualHaarAt ℚ v (negOneCoset v c) := by simp
  have h2 : selfDualHaarAt ℚ v (negOneCoset v c) = selfDualHaarAt ℚ v (levelBall v c) := by
    show selfDualHaarAt ℚ v ((fun h => (1 : v.adicCompletion ℚ) + h) ⁻¹' levelBall v c) = _
    exact measure_preimage_add (selfDualHaarAt ℚ v) 1 (levelBall v c)
  rw [Measure.real, Measure.real, h1, h2]

private theorem localZeta_cosetInd (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) {a : ℕ}
    (ha : HasConductorExponentAt ℚ v η a) {c : ℤ} (hc : 1 ≤ c) (hac : (a : ℤ) ≤ c) (z : ℂ) :
    localZeta (selfDualHaarAt ℚ v) (cosetInd v c) η z =
      ((η (-1) : ℂˣ) : ℂ) * ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) := by
  have hCm : MeasurableSet (negOneCoset v c) :=
    ((isClosed_valued_le v (-c)).preimage (continuous_const.add continuous_id)).measurableSet
  have hpt : ∀ x, cosetInd v c x * charExt η x * ((modulus x : ℝ) : ℂ) ^ z =
      (negOneCoset v c).indicator (fun _ => ((η (-1) : ℂˣ) : ℂ)) x := by
    intro x
    by_cases hx : Valued.v (1 + x) ≤ WithZero.exp (-c)
    · have hx1 : Valued.v x = 1 := valued_eq_one_of_valued_one_add_le v hc hx
      have hx0 : x ≠ 0 := fun h => by
        rw [h, map_zero] at hx1
        exact zero_ne_one hx1
      have hneg : η (Units.mk0 (-x) (neg_ne_zero.2 hx0)) = 1 := by
        apply ha.1
        refine ⟨?_, Or.inr ?_⟩
        · rw [Units.val_mk0, Valuation.map_neg, hx1]
        · rw [Units.val_mk0, show -x - 1 = -(1 + x) by ring, Valuation.map_neg]
          exact hx.trans (WithZero.exp_le_exp.2 (by omega))
      have hchar : charExt η x = ((η (-1) : ℂˣ) : ℂ) := by
        rw [charExt_of_ne_zero η hx0]
        have hu : Units.mk0 x hx0 = -1 * Units.mk0 (-x) (neg_ne_zero.2 hx0) := by
          ext
          simp
        rw [hu, map_mul, hneg, mul_one]
      have hmod : modulus x = 1 := LaurentZetaSlot.modulus_eq_one_of_mem_unitShell v hx1
      have hmem : x ∈ negOneCoset v c := hx
      rw [Set.indicator_of_mem hmem, hchar, hmod]
      simp only [cosetInd, if_pos hx, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one]
    · have hmem : x ∉ negOneCoset v c := hx
      rw [Set.indicator_of_notMem hmem]
      simp only [cosetInd, if_neg hx, zero_mul]
  simp only [localZeta, hpt]
  rw [integral_indicator_const _ hCm, mulMeasure_real_negOneCoset v hc, Complex.real_smul, mul_comm]

private theorem localLFactorAt_ne_zero (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) (z : ℂ) (hz : 0 < z.re) :
    localLFactorAt ℚ v η z ≠ 0 := by
  unfold localLFactorAt
  split_ifs with h
  · refine inv_ne_zero (sub_ne_zero.2 fun h1 => ?_)
    have hn : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-z)‖ < 1 := by
      rw [norm_mul, hη1, one_mul,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (LaurentZetaSlot.absNorm_ne_zero v)), Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (LaurentZetaSlot.one_lt_absNorm_real v) (by linarith)
    rw [← h1, norm_one] at hn
    exact lt_irrefl _ hn
  · exact one_ne_zero

private theorem apply_neg_one_mul_self (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    ((η (-1) : ℂˣ) : ℂ) * ((η (-1) : ℂˣ) : ℂ) = 1 := by
  rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]

private theorem inv_apply_neg_one (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    ((η⁻¹ (-1) : ℂˣ) : ℂ) = ((η (-1) : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact (eq_inv_of_mul_eq_one_right (apply_neg_one_mul_self v η)).symm

private theorem gaussIntegral_inv_mul_localLFactorAt (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    {a : ℕ} (ha : HasConductorExponentAt ℚ v η a) {c : ℤ} (hc : 1 ≤ c) (hac : (a : ℤ) ≤ c)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    gaussIntegral v η⁻¹ (1 - s) c * localLFactorAt ℚ v η s =
      stdRootNumberAt ℚ v η * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - s)) *
        localLFactorAt ℚ v η⁻¹ (1 - s) * ((η (-1) : ℂˣ) : ℂ) := by
  have hm0 : ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (levelBall_real_pos v (by omega)).ne'
  have hT := localZeta_tateFourier_mul_localLFactorAt_eq v η hη hη1 a ha (cosetInd v c)
    (isSchwartzBruhat_cosetInd v hc) s hs hs'
  rw [← mass_mul_gaussIntegral, localZeta_cosetInd v η ha hc hac] at hT
  apply mul_left_cancel₀ hm0
  calc ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) * (gaussIntegral v η⁻¹ (1 - s) c * localLFactorAt ℚ v η s)
      = ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) * gaussIntegral v η⁻¹ (1 - s) c *
          localLFactorAt ℚ v η s := by ring
    _ = _ := hT
    _ = _ := by ring

private theorem gaussIntegral_mul_localLFactorAt_inv (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    (hη1 : ‖((η (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    {a : ℕ} (ha : HasConductorExponentAt ℚ v η a) {c : ℤ} (hc : 1 ≤ c) (hac : (a : ℤ) ≤ c)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    gaussIntegral v η s c * localLFactorAt ℚ v η⁻¹ (1 - s) =
      stdRootNumberAt ℚ v η⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ ((a : ℂ) * (1 / 2 - (1 - s))) *
        localLFactorAt ℚ v η s * ((η (-1) : ℂˣ) : ℂ) := by
  have hm0 : ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (levelBall_real_pos v (by omega)).ne'
  have hs1 : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hs1' : (1 - s).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hT := localZeta_tateFourier_mul_localLFactorAt_eq v η⁻¹ (LaurentZetaSlot.isLocallyConstant_inv v η hη)
    (norm_inv_apply_uniformizerUnit ℚ v hη1) a (hasConductorExponentAt_inv ℚ v ha) (cosetInd v c)
    (isSchwartzBruhat_cosetInd v hc) (1 - s) hs1 hs1'
  have hηη : η⁻¹⁻¹ = η := by
    ext u
    simp
  have hss : (1 : ℂ) - (1 - s) = s := sub_sub_cancel 1 s
  rw [hηη, hss, ← mass_mul_gaussIntegral,
    localZeta_cosetInd v η⁻¹ (hasConductorExponentAt_inv ℚ v ha) hc hac, inv_apply_neg_one] at hT
  apply mul_left_cancel₀ hm0
  calc ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) * (gaussIntegral v η s c * localLFactorAt ℚ v η⁻¹ (1 - s))
      = ((selfDualHaarAt ℚ v).real (levelBall v c) : ℂ) * gaussIntegral v η s c *
          localLFactorAt ℚ v η⁻¹ (1 - s) := by ring
    _ = _ := hT
    _ = _ := by ring

private theorem gauss_products_eq {G₀ G₁ G₂ L₀ L₁ L₂ M₀ M₁ M₂ e₀ e₁ e₂ e₂' Q₀ Q₁ Q₂ Q₂' s₀ s₁ s₂ : ℂ}
    (h₀ : G₀ * L₀ = e₀ * Q₀ * M₀ * s₀) (h₁ : G₁ * L₁ = e₁ * Q₁ * M₁ * s₁)
    (h₂ : G₂ * M₂ = e₂' * Q₂' * L₂ * s₂) (hQ : Q₂ * Q₂' = 1) (he : e₂ * e₂' = s₂) (hs : s₂ * s₂ = 1)
    (hL₀ : L₀ ≠ 0) (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0) (hM₂ : M₂ ≠ 0) :
    G₀ * G₁ = M₀ * M₁ * M₂ * (e₀ * e₁ * e₂ * (Q₀ * Q₁ * Q₂)) * ((L₀ * L₁ * L₂)⁻¹ * (s₀ * s₁ * G₂)) := by
  have hQ₂ : Q₂ ≠ 0 := left_ne_zero_of_mul_eq_one hQ
  have hQ' : Q₂' = Q₂⁻¹ := eq_inv_of_mul_eq_one_right hQ
  have hG₀ : G₀ = e₀ * Q₀ * M₀ * s₀ * L₀⁻¹ := (eq_mul_inv_iff_mul_eq₀ hL₀).2 h₀
  have hG₁ : G₁ = e₁ * Q₁ * M₁ * s₁ * L₁⁻¹ := (eq_mul_inv_iff_mul_eq₀ hL₁).2 h₁
  have hG₂ : e₂ * G₂ = Q₂⁻¹ * L₂ * M₂⁻¹ := by
    have h3 : e₂ * G₂ * M₂ = Q₂⁻¹ * L₂ := by
      calc e₂ * G₂ * M₂ = e₂ * (G₂ * M₂) := by ring
        _ = e₂ * (e₂' * Q₂' * L₂ * s₂) := by rw [h₂]
        _ = (e₂ * e₂') * s₂ * (Q₂' * L₂) := by ring
        _ = (s₂ * s₂) * (Q₂' * L₂) := by rw [he]
        _ = Q₂⁻¹ * L₂ := by rw [hs, one_mul, hQ']
    exact (eq_mul_inv_iff_mul_eq₀ hM₂).2 h3
  calc G₀ * G₁ = (e₀ * Q₀ * M₀ * s₀ * L₀⁻¹) * (e₁ * Q₁ * M₁ * s₁ * L₁⁻¹) := by rw [hG₀, hG₁]
    _ = M₀ * M₁ * M₂ * (e₀ * e₁ * (Q₀ * Q₁ * Q₂)) * ((L₀ * L₁ * L₂)⁻¹ * (s₀ * s₁)) * (Q₂⁻¹ * L₂ * M₂⁻¹) := by
        field_simp
    _ = _ := by
        rw [← hG₂]
        ring

end Closing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot"

private theorem localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip_aux
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (a : Fin 3 → ℕ) (ha : ∀ i, HasConductorExponentAt ℚ v (ν i * χ) (a i))
    (σ₀ σ₁ : ℝ)
    (h₀ : IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ 1 σ₀)
    (h₁ : IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)))
      χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁)
    (s : ℂ) (hs₀ : σ₀ < s.re) (hs₁ : σ₁ < (1 - s).re) (hs : 0 < s.re) (hs' : s.re < 1) :
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
      (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
        ((∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) *
        ((∏ i, localLFactorAt ℚ v (ν i * χ) s)⁻¹ *
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1) := by
  have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (LaurentZetaSlot.absNorm_ne_zero v)
  have hνχ : ∀ i, IsLocallyConstant (ν i * χ) := fun i => (hν i).mul hχ

  have hintP := integrable_torusFn_mul_charExt_of_convergentAbove v ν Φ χ σ₀ h₀ s hs₀
  have hintD := integrable_dualFn_mul_charExt_inv_of_convergentAbove v ν Φ χ σ₁ h₁ s hs₁

  have hP := tendsto_gaussIntegral_mul_coupledIntegral_localZeta_torusFn v ν hν Φ hΦ.1 hΦ.2 χ hχ hu s hs hs' hintP
  have hD := tendsto_gaussIntegral_mul_coupledIntegral_localZeta_dualFn v ν hν Φ hΦ.1 hΦ.2 χ hχ hu s hs hs' hintD

  set K : ℂ := (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
      ((∏ i, stdRootNumberAt ℚ v (ν i * χ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) *
      (∏ i, localLFactorAt ℚ v (ν i * χ) s)⁻¹ with hK

  have hce : ∀ η : (v.adicCompletion ℚ)ˣ →* ℂˣ, charExt η (-1 : v.adicCompletion ℚ) = ((η (-1) : ℂˣ) : ℂ) := by
    intro η
    rw [show (-1 : v.adicCompletion ℚ) = (((-1 : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) by simp,
      charExt_coe_units]
  have hsign : (((ν 0 * χ) (-1) : ℂˣ) : ℂ) * (((ν 1 * χ) (-1) : ℂˣ) : ℂ) =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) := by
    rw [hce, hce, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul]
    linear_combination (((ν 0) (-1) : ℂˣ) : ℂ) * (((ν 1) (-1) : ℂˣ) : ℂ) * apply_neg_one_mul_self v χ

  have hA : ∀ c : ℤ, ((1 + (a 0 + a 1 + a 2) : ℕ) : ℤ) ≤ c →
      gaussIntegral v (ν 0 * χ)⁻¹ (1 - s) c * gaussIntegral v (ν 1 * χ)⁻¹ (1 - s) c =
        K * (charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c) := by
    intro c hc
    push_cast at hc
    have hc1 : (1 : ℤ) ≤ c := by omega
    have hca : ∀ i : Fin 3, ((a i : ℕ) : ℤ) ≤ c := by
      intro i
      fin_cases i
      · show ((a 0 : ℕ) : ℤ) ≤ c
        omega
      · show ((a 1 : ℕ) : ℤ) ≤ c
        omega
      · show ((a 2 : ℕ) : ℤ) ≤ c
        omega
    have h0 := gaussIntegral_inv_mul_localLFactorAt v (ν 0 * χ) (hνχ 0) (hu 0) (ha 0) hc1 (hca 0) s hs hs'
    have h1 := gaussIntegral_inv_mul_localLFactorAt v (ν 1 * χ) (hνχ 1) (hu 1) (ha 1) hc1 (hca 1) s hs hs'
    have h2 := gaussIntegral_mul_localLFactorAt_inv v (ν 2 * χ) (hνχ 2) (hu 2) (ha 2) hc1 (hca 2) s hs hs'
    have hQ : (Ideal.absNorm v.asIdeal : ℂ) ^ ((a 2 : ℂ) * (1 / 2 - s)) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ ((a 2 : ℂ) * (1 / 2 - (1 - s))) = 1 := by
      rw [← Complex.cpow_add _ _ hq, show (a 2 : ℂ) * (1 / 2 - s) + (a 2 : ℂ) * (1 / 2 - (1 - s)) = 0 by ring,
        Complex.cpow_zero]
    have he : stdRootNumberAt ℚ v (ν 2 * χ) * stdRootNumberAt ℚ v (ν 2 * χ)⁻¹ =
        (((ν 2 * χ) (-1) : ℂˣ) : ℂ) := by
      rcases Nat.eq_zero_or_pos (a 2) with ha0 | hpos
      · have h00 : HasConductorExponentAt ℚ v (ν 2 * χ) 0 := ha0 ▸ ha 2
        rw [stdRootNumberAt_eq_one_of_unramified v _ h00 (hu 2),
          stdRootNumberAt_eq_one_of_unramified v _ (hasConductorExponentAt_inv ℚ v h00)
            (norm_inv_apply_uniformizerUnit ℚ v (hu 2)), one_mul,
          (hasConductorExponentAt_zero_iff ℚ v).1 h00 (-1) (by simp), Units.val_one]
      · exact stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one ℚ v (ν 2 * χ) (a 2) hpos (ha 2) (hu 2)
    have hL : ∀ i, localLFactorAt ℚ v (ν i * χ) s ≠ 0 := fun i => localLFactorAt_ne_zero v (ν i * χ) (hu i) s hs
    have hM2 : localLFactorAt ℚ v (ν 2 * χ)⁻¹ (1 - s) ≠ 0 :=
      localLFactorAt_ne_zero v (ν 2 * χ)⁻¹ (norm_inv_apply_uniformizerUnit ℚ v (hu 2)) (1 - s)
        (by rw [Complex.sub_re, Complex.one_re]; linarith)
    rw [gauss_products_eq h0 h1 h2 hQ he (apply_neg_one_mul_self v (ν 2 * χ)) (hL 0) (hL 1) (hL 2) hM2, hsign, hK,
      ← prod_cpow_natCast_mul_eq _ hq a s]
    simp only [Fin.prod_univ_three]
    ring

  have hEv : (fun c : ℤ => gaussIntegral v (ν 0 * χ)⁻¹ (1 - s) c * gaussIntegral v (ν 1 * χ)⁻¹ (1 - s) c *
        coupledIntegral v ν Φ χ s c) =ᶠ[Filter.atTop]
      fun c : ℤ => K * (charExt (ν 0) (-1) * charExt (ν 1) (-1) * gaussIntegral v (ν 2 * χ) s c *
        coupledIntegral v ν Φ χ s c) :=
    Filter.eventually_atTop.2 ⟨((1 + (a 0 + a 1 + a 2) : ℕ) : ℤ), fun c hc => by beta_reduce; rw [hA c hc]; ring⟩
  have hlim : localZeta (selfDualHaarAt ℚ v) (dualFn v ν Φ) χ⁻¹ (1 - s) =
      K * localZeta (selfDualHaarAt ℚ v) (torusFn v ν Φ) χ s :=
    tendsto_nhds_unique hD ((hP.const_mul K).congr' hEv.symm)

  rw [localZetaDual31_eq_localZeta_dualFn v ν Φ χ s, hlim, ← localZeta30_eq_localZeta_torusFn v ν Φ χ s, hK]
  ring

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell"

end Part24
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LaurentZetaSlot P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.CubicInduction"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.CubicInduction in
open IsDedekindDomain NumberField _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip.LanglandsTunnell.TateLocal MeasureTheory in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (a : Fin 3 → ℕ) (ha : ∀ i, HasConductorExponentAt ℚ v (ν i * χ) (a i))
    (σ₀ σ₁ : ℝ)
    (h₀ : IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ 1 σ₀)
    (h₁ : IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)))
      χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁)
    (s : ℂ) (hs₀ : σ₀ < s.re) (hs₁ : σ₁ < (1 - s).re) (hs : 0 < s.re) (hs' : s.re < 1) :
    localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
      (∏ i, localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
        ((∏ i, stdRootNumberAt ℚ v (ν i * χ)) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) *
        ((∏ i, localLFactorAt ℚ v (ν i * χ) s)⁻¹ *
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1) := by
  exact localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip_aux v ν hν Φ hΦ χ hχ hu a ha σ₀ σ₁ h₀ h₁ s hs₀ hs₁ hs
    hs'

end S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip (solution)
