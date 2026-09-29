-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4e920ad5-9b8e-5940-89fc-9224622fcec3

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

section
set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero.LanglandsTunnell.TateLocal"
open scoped NNReal ENNReal

namespace LaurentLocalZeta

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

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

private theorem measurableSet_shell (j : ℤ) : MeasurableSet (shell v j) :=
  (isClopen_shell v j).isOpen.measurableSet

private theorem shell_subset_compl_zero (j : ℤ) : shell v j ⊆ ({0}ᶜ : Set (v.adicCompletion ℚ)) := by
  intro x hx
  have hx' : Valued.v x = WithZero.exp (-j) := hx
  intro h0
  rw [Set.mem_singleton_iff.mp h0, map_zero] at hx'
  exact WithZero.exp_ne_zero hx'.symm

end LaurentLocalZeta
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero.LanglandsTunnell.TateLocal"
open NumberField.StandardAddChar
open scoped Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TorusValues

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)

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

end LanglandsTunnell.CubicInduction
end

section
set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def localBorel borelSpace_localBorel integersPositiveCompacts selfDualHaarAt higherUnitsAt mem_higherUnitsAt_iff modulus charExt charExt_coe_units mulMeasure addCharLevel_psiLocal_rat exists_hasConductorExponentAt_of_continuous modulus_adicCompletion_eq_nnnorm psiLocal_ne_one"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

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

end MeasureClasses

end LanglandsTunnell.TateLocal
end

section
set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero.LanglandsTunnell.TateLocal"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.borelSpace_localBorel"
namespace CubicInduction
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gaussShell_eq_shell (j : ℤ) :
    {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} = LaurentLocalZeta.shell v (-j) := by
  ext t
  simp only [Set.mem_setOf_eq, LaurentLocalZeta.shell, neg_neg]

private theorem gaussShell_preimage_add {j : ℤ} (hj : 1 < j) {ε : v.adicCompletion ℚ}
    (hε : Valued.v ε ≤ WithZero.exp (1 : ℤ)) :
    (fun t : v.adicCompletion ℚ => t + ε) ⁻¹' {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} =
      {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} := by
  have hlt : Valued.v ε < WithZero.exp j := lt_of_le_of_lt hε (WithZero.exp_lt_exp.mpr hj)
  have hneg : Valued.v (-ε) < WithZero.exp j := by rwa [Valuation.map_neg]
  ext t
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro h
    have ht : t = (t + ε) + -ε := by ring
    rw [ht, Valuation.map_add_eq_of_lt_left]
    · exact h
    · rw [h]; exact hneg
  · intro h
    rw [Valuation.map_add_eq_of_lt_left]
    · exact h
    · rw [h]; exact hlt

private theorem setIntegral_shell_add {j : ℤ} (hj : 1 < j) {ε : v.adicCompletion ℚ}
    (hε : Valued.v ε ≤ WithZero.exp (1 : ℤ)) (F : v.adicCompletion ℚ → ℂ) :
    ∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j}, F (t + ε) ∂(selfDualHaarAt ℚ v) =
      ∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j}, F t ∂(selfDualHaarAt ℚ v) := by
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt ℚ v
  have hmeas : MeasurableSet {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} := by
    rw [gaussShell_eq_shell]
    exact LaurentLocalZeta.measurableSet_shell v (-j)
  have hpre := gaussShell_preimage_add v hj hε
  have hmain : {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j}.indicator (fun t => F (t + ε)) =
      fun t => {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j}.indicator F (t + ε) := by
    funext t
    have h := Set.indicator_comp_right (M := ℂ) (fun s : v.adicCompletion ℚ => s + ε)
      (s := {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j}) (g := F) (x := t)
    rw [hpre] at h
    exact h
  rw [← integral_indicator hmeas, ← integral_indicator hmeas, hmain, integral_add_right_eq_self]

private theorem gaussShell_mulMeasure_restrict (j : ℤ) :
    ∃ c : ENNReal, (mulMeasure (selfDualHaarAt ℚ v)).restrict {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} =
      c • (selfDualHaarAt ℚ v).restrict {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} := by
  rw [gaussShell_eq_shell]
  refine ⟨(((Ideal.absNorm v.asIdeal : NNReal) ^ (-(-j)) : NNReal) : ENNReal)⁻¹, ?_⟩
  have hmeas := LaurentLocalZeta.measurableSet_shell v (-j)
  have hsub := LaurentLocalZeta.shell_subset_compl_zero v (-j)
  unfold mulMeasure
  rw [restrict_withDensity hmeas, Measure.restrict_restrict hmeas, Set.inter_eq_left.mpr hsub,
    ← withDensity_const]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hmeas] with t ht
  rw [LaurentLocalZeta.modulus_eq_of_mem_shell v ht]

private theorem gaussShell_integrand_add {k : ℕ} (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hk : ∀ u w : v.adicCompletion ℚ,
      Valued.v (u - 1) ≤ WithZero.exp (-(k : ℤ)) → charExt η (u * w) = charExt η w)
    {ε : v.adicCompletion ℚ} (hε : Valued.v ε ≤ WithZero.exp (1 : ℤ)) {j : ℤ} (hj : 1 < j)
    (hjk : (k : ℤ) + 1 ≤ j) (z : ℂ) {t : v.adicCompletion ℚ} (ht : Valued.v t = WithZero.exp j) :
    (NumberField.StandardAddChar.psiLocal ℚ v (-(t + ε)) : ℂ) * charExt η (t + ε) *
        ((modulus (t + ε) : ℝ) : ℂ) ^ z =
      (NumberField.StandardAddChar.psiLocal ℚ v (-ε) : ℂ) *
        ((NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at ht
    exact WithZero.exp_ne_zero ht.symm
  have htε : Valued.v (t + ε) = Valued.v t := by
    have h := gaussShell_preimage_add v hj hε
    have hmem : t ∈ {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} := ht
    rw [← h] at hmem
    exact hmem.trans ht.symm
  have hchar : charExt η (t + ε) = charExt η t := by
    have hu : t + ε = (1 + ε / t) * t := by field_simp
    rw [hu]
    refine hk _ _ ?_
    rw [add_sub_cancel_left, Valuation.map_div, ht]
    calc Valued.v ε / WithZero.exp j ≤ WithZero.exp (1 : ℤ) / WithZero.exp j := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          gcongr
      _ = WithZero.exp (1 - j) := by rw [← WithZero.exp_sub]
      _ ≤ WithZero.exp (-(k : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have hmod : modulus (t + ε) = modulus t := by
    have h₁ : t + ε ∈ LaurentLocalZeta.shell v (-j) := by
      show Valued.v (t + ε) = WithZero.exp (-(-j))
      rw [neg_neg, htε, ht]
    have h₂ : t ∈ LaurentLocalZeta.shell v (-j) := by
      show Valued.v t = WithZero.exp (-(-j))
      rw [neg_neg, ht]
    rw [LaurentLocalZeta.modulus_eq_of_mem_shell v h₁, LaurentLocalZeta.modulus_eq_of_mem_shell v h₂]
  rw [neg_add, AddChar.map_add_eq_mul, hchar, hmod]
  ring

private theorem exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ c₁ : ℕ, ∀ z : ℂ, ∀ j : ℤ, (c₁ : ℤ) < j →
      ∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
          (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z
        ∂(mulMeasure (selfDualHaarAt ℚ v)) = 0 := by
  obtain ⟨k, hk⟩ := exists_forall_charExt_mul_eq v η hη
  obtain ⟨ε, hε, hψ⟩ := exists_psiLocal_neg_ne_one v
  refine ⟨max k 1, fun z j hj => ?_⟩
  have hj1 : 1 < j := lt_of_le_of_lt (by exact_mod_cast le_max_right k 1) hj
  have hjk : (k : ℤ) + 1 ≤ j := by
    have : (k : ℤ) ≤ ((max k 1 : ℕ) : ℤ) := by exact_mod_cast le_max_left k 1
    omega
  obtain ⟨c, hc⟩ := gaussShell_mulMeasure_restrict v j
  rw [hc, integral_smul_measure]
  have hmeas : MeasurableSet {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j} := by
    rw [gaussShell_eq_shell]
    exact LaurentLocalZeta.measurableSet_shell v (-j)
  have h1 : (∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
        (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z
        ∂(selfDualHaarAt ℚ v)) =
      (NumberField.StandardAddChar.psiLocal ℚ v (-ε) : ℂ) *
        ∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
          (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z
          ∂(selfDualHaarAt ℚ v) := by
    conv_lhs => rw [← setIntegral_shell_add v hj1 hε
      (fun t => (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z)]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hmeas fun t ht => ?_
    exact gaussShell_integrand_add v η hk hε hj1 hjk z ht
  have h2 : (1 - (NumberField.StandardAddChar.psiLocal ℚ v (-ε) : ℂ)) *
      ∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
        (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z
        ∂(selfDualHaarAt ℚ v) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  rw [(mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hψ)), smul_zero]

end LanglandsTunnell.CubicInduction
end

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero.LanglandsTunnell.TateLocal _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero.LanglandsTunnell.CubicInduction in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    ∃ c₁ : ℕ, ∀ z : ℂ, ∀ j : ℤ, (c₁ : ℤ) < j →
      ∫ t in {t : v.adicCompletion ℚ | Valued.v t = WithZero.exp j},
          (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) * charExt η t * ((modulus t : ℝ) : ℂ) ^ z
        ∂(mulMeasure (selfDualHaarAt ℚ v)) = 0 :=
  exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero v η hη

end S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_setIntegral_shell_psiLocal_mul_charExt_mul_cpow_eq_zero (solution)
