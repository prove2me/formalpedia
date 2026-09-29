-- Prove2me | solution 1 for LanglandsTunnell.Converse.CuspSynthesis.exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e1e7accd-be55-5242-b5b1-98f4d30d2c7e

import Definitions.Def_LanglandsTunnell_JLSynthesis
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_JLData
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_GaussTwist
import Theorems.Thm_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
import Theorems.Thm_LanglandsTunnell_Converse_FinWhittakerDatum_exists_norm_Wf_globalPoints_diagOne_mul_le
import Theorems.Thm_LanglandsTunnell_Converse_exists_archParams_of_continuous
import Theorems.Thm_LanglandsTunnell_Converse_exists_isJLTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
set_option Elab.async false
set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse"

noncomputable section

namespace FourierUniq

open Complex MeasureTheory Filter Topology

private def e (x : ℝ) : ℂ := exp (2 * Real.pi * I * x)

end FourierUniq

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace Fourier
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.Fourier

end

section

open scoped WithZero

namespace LocalWhittaker

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

private def IsIntegral (K : GL (Fin 2) F) : Prop := ∀ i j : Fin 2, v ((K : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1

end LocalWhittaker

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LocalWhittaker"
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

private def compAt (w : HeightOneSpectrum (𝓞 K)) : AdelicGL2 (𝓞 K) K →* GL (Fin 2) (w.adicCompletion K) :=
  (finComponent (𝓞 K) K w).comp (glFin (𝓞 K) K)

private theorem compAt_apply (w : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (compAt w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j
      = (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w := rfl

private theorem compAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt v (placeEmbed K v h) = h := by
  show finComponent (𝓞 K) K v (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = h
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem compAt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v)
    (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt w (placeEmbed K v h) = 1 := by
  show finComponent (𝓞 K) K w (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

private theorem isIntegral_compAt_of_mem_integral {g : AdelicGL2 (𝓞 K) K} {w : HeightOneSpectrum (𝓞 K)}
    (hg : ∀ i j : Fin 2, (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
      ∈ w.adicCompletionIntegers K) : LocalWhittaker.IsIntegral Valued.v (compAt w g) := fun i j => by
  rw [compAt_apply]
  exact (mem_adicCompletionIntegers _ _ _).mp (hg i j)

private theorem isIntegral_compAt_inv_of_mem_integral {g : AdelicGL2 (𝓞 K) K} {w : HeightOneSpectrum (𝓞 K)}
    (hg : ∀ i j : Fin 2, (glFin (𝓞 K) K g⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
      ∈ w.adicCompletionIntegers K) : LocalWhittaker.IsIntegral Valued.v (compAt w g)⁻¹ := by
  rw [← map_inv]
  exact isIntegral_compAt_of_mem_integral hg

private theorem placeEmbed_mem_of_isIntegral (v : HeightOneSpectrum (𝓞 K)) {M : Ideal (𝓞 K)} (hM : ¬ v.asIdeal ∣ M)
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : LocalWhittaker.IsIntegral Valued.v k)
    (hk' : LocalWhittaker.IsIntegral Valued.v k⁻¹) :
    placeEmbed K v k ∈ levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K := by
  have hMbot : M ≠ ⊥ := by
    rintro rfl
    exact hM (dvd_zero _)
  have hbound : idealBound (𝓞 K) M v = 1 := idealBound_eq_one_of_not_dvd hMbot hM
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) ∈ levelOne (𝓞 K) K M
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    refine ⟨⟨fun i j => hk i j, ?_, ?_⟩, ⟨fun i j => hk' i j, ?_, ?_⟩⟩
    · rw [hbound]; exact hk 1 0
    · rw [hbound]; exact (Valuation.map_sub _ _ _).trans (max_le (hk 1 1) (by simp))
    · rw [hbound]; exact hk' 1 0
    · rw [hbound]; exact (Valuation.map_sub _ _ _).trans (max_le (hk' 1 1) (by simp))
  · show finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) ∈ finiteAdelicGL2Subgroup K
    rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_finEmbed _ _ _

end FiniteWhittaker

end

namespace LocalWhittaker

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section MapSurj

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {L : Type*} [Field L] [Algebra R L]
  [IsFractionRing R L] (v : HeightOneSpectrum R)

private def toIntegersMatrix {g : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)}
    (hg : ∀ i j, Valued.v (g i j) ≤ 1) : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers L) :=
  fun i j => ⟨g i j, (mem_adicCompletionIntegers R L v).mpr (hg i j)⟩

private theorem toIntegersMatrix_map {g : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)}
    (hg : ∀ i j, Valued.v (g i j) ≤ 1) :
    (toIntegersMatrix v hg).map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) = g := by
  ext i j
  rfl

private theorem mapMatrix_injective :
    Function.Injective
      ((algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)).mapMatrix :
        Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers L) →+* Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) :=
  fun _ _ h => Matrix.map_injective (fun _ _ h' => Subtype.ext h') h

private theorem exists_map_eq_of_isIntegral {g : GL (Fin 2) (v.adicCompletion L)}
    (hg : IsIntegral Valued.v g) (hg' : IsIntegral Valued.v g⁻¹) :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers L),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) k = g := by
  have hA := toIntegersMatrix_map v hg
  have hB := toIntegersMatrix_map v hg'
  have hmul : (toIntegersMatrix v hg).map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L))
      * (toIntegersMatrix v hg').map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) = 1 := by
    rw [hA, hB]
    exact Units.mul_inv g
  have hmul' : (toIntegersMatrix v hg').map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L))
      * (toIntegersMatrix v hg).map (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L)) = 1 := by
    rw [hA, hB]
    exact Units.inv_mul g
  have hAB : toIntegersMatrix v hg * toIntegersMatrix v hg' = 1 := by
    apply mapMatrix_injective v
    rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
    exact hmul
  have hBA : toIntegersMatrix v hg' * toIntegersMatrix v hg = 1 := by
    apply mapMatrix_injective v
    rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
    exact hmul'
  refine ⟨⟨toIntegersMatrix v hg, toIntegersMatrix v hg', hAB, hBA⟩, ?_⟩
  ext i j
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map]
  exact congrFun (congrFun hA i) j

end MapSurj

end LocalWhittaker

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LocalWhittaker"
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

section IntegralInvariance

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem not_dvd_top (v : HeightOneSpectrum (𝓞 K)) : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) := fun h =>
  v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))

private theorem wf_mul_placeEmbed_of_isIntegral (dF : FinWhittakerDatum K S Pi) (w : HeightOneSpectrum (𝓞 K))
    {k : GL (Fin 2) (w.adicCompletion K)} (hk : LocalWhittaker.IsIntegral Valued.v k)
    (hk' : LocalWhittaker.IsIntegral Valued.v k⁻¹) (g : AdelicGL2 (𝓞 K) K) :
    dF.Wf (g * placeEmbed K w k) = dF.Wf g := by
  by_cases hw : w ∈ S
  · exact dF.blind_at w hw k g
  · obtain ⟨k₀, rfl⟩ := LocalWhittaker.exists_map_eq_of_isIntegral w hk hk'
    exact dF.integral_right w hw k₀ g

private theorem isIntegral_compAt_of_mem_levelTop {u : AdelicGL2 (𝓞 K) K} (hu : u ∈ levelOne (𝓞 K) K ⊤)
    (w : HeightOneSpectrum (𝓞 K)) :
    LocalWhittaker.IsIntegral Valued.v (compAt w u) ∧ LocalWhittaker.IsIntegral Valued.v (compAt w u)⁻¹ := by
  rw [mem_levelOne_iff] at hu
  obtain ⟨h1, h2⟩ := hu
  refine ⟨isIntegral_compAt_of_mem_integral fun i j => h1.integral i j w,
    isIntegral_compAt_inv_of_mem_integral fun i j => ?_⟩
  rw [map_inv]
  exact h2.integral i j w

private theorem isLevelOneMatrix_of_top {N₀ : Ideal (𝓞 K)} (hN₀ : N₀ ≠ ⊥) {m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hm : IsLevelOneMatrix (𝓞 K) K ⊤ (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (hcomp : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → finComponent (𝓞 K) K w m = 1) :
    IsLevelOneMatrix (𝓞 K) K N₀ (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  have hentry : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → ∀ i j : Fin 2,
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
        = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
    intro w hw i j
    have h := congrArg
      (fun x : GL (Fin 2) (w.adicCompletion K) => (x : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) (hcomp w hw)
    simpa only [finComponent_apply, Units.val_one] using h
  refine ⟨⟨hm.integral, fun w => ?_⟩, fun w => ?_⟩
  · by_cases hw : w.asIdeal ∣ N₀
    · rw [hentry w hw 1 0, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le'
    · rw [idealBound_eq_one_of_not_dvd hN₀ hw]
      exact (mem_adicCompletionIntegers _ _ _).mp (hm.integral 1 0 w)
  · by_cases hw : w.asIdeal ∣ N₀
    · rw [coe_sub_apply, coe_one_apply, hentry w hw 1 1, Matrix.one_apply_eq, sub_self, map_zero]
      exact zero_le'
    · rw [idealBound_eq_one_of_not_dvd hN₀ hw, coe_sub_apply, coe_one_apply]
      exact (Valuation.map_sub _ _ _).trans
        (max_le ((mem_adicCompletionIntegers _ _ _).mp (hm.integral 1 1 w)) (by simp))

private theorem mem_levelOne_of_forall_compAt {N₀ : Ideal (𝓞 K)} (hN₀ : N₀ ≠ ⊥) {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K ⊤) (hcomp : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → compAt w u = 1) :
    u ∈ levelOne (𝓞 K) K N₀ := by
  rw [mem_levelOne_iff] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  refine ⟨isLevelOneMatrix_of_top hN₀ h1 hcomp, ?_⟩
  have h2' : IsLevelOneMatrix (𝓞 K) K ⊤ ((glFin (𝓞 K) K u⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
    rw [map_inv]; exact h2
  have := isLevelOneMatrix_of_top hN₀ h2' fun w hw => by
    show compAt w u⁻¹ = 1
    rw [map_inv, hcomp w hw, inv_one]
  rwa [map_inv] at this

private theorem wf_mul_eq_of_forall_compAt (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) {N₀ : Ideal (𝓞 K)}
    (hN₀ : N₀ ≠ ⊥)
    (hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N₀ ⊓ finiteAdelicGL2Subgroup K,
      dF.Wf (g * u) = dF.Wf g)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ u ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K,
      (∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → w ∉ T → compAt w u = 1) → dF.Wf (g * u) = dF.Wf g := by
  classical
  refine Finset.induction_on T ?_ ?_
  · intro u hu hcomp
    obtain ⟨hu₁, hu₂⟩ := Subgroup.mem_inf.mp hu
    exact hlevel g u (Subgroup.mem_inf.mpr
      ⟨mem_levelOne_of_forall_compAt hN₀ hu₁ fun w hw => hcomp w hw (Finset.notMem_empty w), hu₂⟩)
  · intro w₁ T hw₁T ih u hu hcomp
    obtain ⟨hk, hk'⟩ := isIntegral_compAt_of_mem_levelTop (Subgroup.mem_inf.mp hu).1 w₁
    set u₁ := u * (placeEmbed K w₁ (compAt w₁ u))⁻¹ with hu₁_def
    have hu₁ : u₁ ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K :=
      Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (placeEmbed_mem_of_isIntegral w₁ (not_dvd_top w₁) hk hk'))
    have hcomp₁ : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N₀ → w ∉ T → compAt w u₁ = 1 := by
      intro w hwN hwT
      by_cases hww : w = w₁
      · subst hww
        rw [hu₁_def, map_mul, map_inv, compAt_placeEmbed_self, mul_inv_cancel]
      · have hw : compAt w u = 1 := hcomp w hwN (by
          rw [Finset.mem_insert, not_or]
          exact ⟨hww, hwT⟩)
        rw [hu₁_def, map_mul, map_inv, compAt_placeEmbed_of_ne hww, inv_one, mul_one, hw]
    have hu_eq : u = u₁ * placeEmbed K w₁ (compAt w₁ u) := (inv_mul_cancel_right u _).symm
    rw [hu_eq, ← mul_assoc, wf_mul_placeEmbed_of_isIntegral dF w₁ hk hk', ih u₁ hu₁ hcomp₁]

private theorem wf_mul_of_mem_integral (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K) : dF.Wf (g * u) = dF.Wf g := by
  classical
  obtain ⟨N₀, hN₀, hlevel⟩ := dF.level_right
  have hfin : {w : HeightOneSpectrum (𝓞 K) | w.asIdeal ∣ N₀}.Finite :=
    Ideal.finite_factors (by rw [Submodule.zero_eq_bot]; exact hN₀)
  exact wf_mul_eq_of_forall_compAt dF g hN₀ hlevel hfin.toFinset u hu
    fun w hw hwT => absurd (hfin.mem_toFinset.mpr hw) hwT

end IntegralInvariance

end FiniteWhittaker

end

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace Ideles
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

private theorem val_mul_inv_fst_apply (z : 𝔸ˣ) (w : InfinitePlace K) :
    (z : 𝔸).1 w * ((z⁻¹ : 𝔸ˣ) : 𝔸).1 w = 1 :=
  congrArg (fun x : 𝔸 => x.1 w) z.mul_inv

private theorem val_inv_mul_fst_apply (z : 𝔸ˣ) (w : InfinitePlace K) :
    ((z⁻¹ : 𝔸ˣ) : 𝔸).1 w * (z : 𝔸).1 w = 1 :=
  congrArg (fun x : 𝔸 => x.1 w) z.inv_mul

private def archUnitAt (w : InfinitePlace K) (z : 𝔸ˣ) : (w.Completion)ˣ where
  val := (z : 𝔸).1 w
  inv := ((z⁻¹ : 𝔸ˣ) : 𝔸).1 w
  val_inv := val_mul_inv_fst_apply z w
  inv_val := val_inv_mul_fst_apply z w

private theorem archUnitAt_val (w : InfinitePlace K) (z : 𝔸ˣ) :
    (archUnitAt w z : w.Completion) = (z : 𝔸).1 w := rfl

end LanglandsTunnell.Converse.Ideles

end

end

section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal"
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

namespace FiniteWhittaker

section TorusGeneric

variable {A : Type*} [CommRing A]

private theorem map_diagOne {B : Type*} [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagOne a) = diagOne (Units.map (f : A →* B) a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change f.mapMatrix (diagOne a : Matrix (Fin 2) (Fin 2) A) i j = _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

end TorusGeneric

section TorusComponents

variable {K : Type} [Field K] [NumberField K]

private theorem globalPoints_diagOne (α : Kˣ) :
    globalPoints (𝓞 K) K (diagOne α) = diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) :=
  map_diagOne _ α

private theorem archComponent_glArch_diagOne (w : InfinitePlace K) (a : (AdeleRing (𝓞 K) K)ˣ) :
    archComponent K w (glArch (𝓞 K) K (diagOne a)) = diagOne (archUnitAt w a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archComponent_apply, glArch_apply, diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [archUnitAt_val] <;> rfl

end TorusComponents

end FiniteWhittaker

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open AutomorphicForm.SmoothCusp

variable {K : Type} [Field K] [NumberField K]

section CentreAndTopology

open scoped WithZero

private theorem continuous_componentMatrix_apply (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 K) K => componentMatrix v g i j :=
  (Units.continuous_val.comp ((continuous_finComponent (R := 𝓞 K) (K := K) v).comp
    (continuous_glFin (R := 𝓞 K) (K := K)))).matrix_elem i j

private theorem setOf_v_le_mem_nhds {v : HeightOneSpectrum (𝓞 K)} {t y : v.adicCompletion K} (ht : t ≠ 0)
    (hy : Valued.v y ≤ Valued.v t) : {z : v.adicCompletion K | Valued.v z ≤ Valued.v t} ∈ nhds y :=
  Filter.mem_of_superset (ball_mem_nhds (𝓞 K) K v y t ht) fun z hz => by
    rw [Set.mem_setOf_eq, ← sub_add_cancel z y]
    exact Valuation.map_add_le _ (le_of_lt hz) hy

private theorem setOf_memZK0At_mem_nhds (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) {g : AdelicGL2 (𝓞 K) K}
    (hg : MemZK0At v m g) : {g' : AdelicGL2 (𝓞 K) K | MemZK0At v m g'} ∈ nhds g := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have ht : componentMatrix v g 1 1 ≠ 0 := (Valuation.ne_zero_iff _).mp h1
  obtain ⟨t', ht'⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v (componentMatrix v g 1 1) * WithZero.exp (-(m : ℤ)))
  have ht'0 : t' ≠ 0 := fun h => by
    rw [h, map_zero] at ht'
    exact mul_ne_zero h1 WithZero.exp_ne_zero ht'.symm
  have n11 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 1 1) = Valued.v (componentMatrix v g 1 1)}
      ∈ nhds g :=
    (continuous_componentMatrix_apply v 1 1).continuousAt.preimage_mem_nhds (Valued.locally_const h1)
  have n00 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 0 0) = Valued.v (componentMatrix v g 1 1)}
      ∈ nhds g := by
    have h0 : Valued.v (componentMatrix v g 0 0) ≠ 0 := h2 ▸ h1
    have := (continuous_componentMatrix_apply v 0 0).continuousAt.preimage_mem_nhds (Valued.locally_const h0)
    rw [h2] at this
    exact this
  have n01 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 0 1) ≤ Valued.v (componentMatrix v g 1 1)}
      ∈ nhds g :=
    (continuous_componentMatrix_apply v 0 1).continuousAt.preimage_mem_nhds (setOf_v_le_mem_nhds ht h3)
  have n10 : {g' : AdelicGL2 (𝓞 K) K | Valued.v (componentMatrix v g' 1 0) ≤ Valued.v t'} ∈ nhds g :=
    (continuous_componentMatrix_apply v 1 0).continuousAt.preimage_mem_nhds
      (setOf_v_le_mem_nhds ht'0 (ht'.symm ▸ h4))
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem n11 n00) (Filter.inter_mem n01 n10)) ?_
  rintro g' ⟨⟨e11, e00⟩, e01, e10⟩
  simp only [Set.mem_setOf_eq] at e11 e00 e01 e10 ⊢
  refine ⟨e11 ▸ h1, e00.trans e11.symm, e11.symm ▸ e01, ?_⟩
  rw [e11, ← ht']
  exact e10

private theorem isOpen_kZeroSet (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ) :
    IsOpen (kZeroSet S m) := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hS : kZeroSet S m = ⋂ v : ↥S, {g' | MemZK0At v.1 (m v) g'} := by
    ext g'
    simp only [kZeroSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hS, Filter.iInter_mem]
  exact fun v => setOf_memZK0At_mem_nhds v.1 (m v) (hg v)

end CentreAndTopology

section
section GaussFixedVector

open scoped WithZero
open UnramifiedWhittaker

private theorem charExt_one_add (v : HeightOneSpectrum (𝓞 K)) {χ : (v.adicCompletion K)ˣ →* ℂˣ} {m : ℕ}
    (hχ : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → IsOneMod K v m u → χ u = 1)
    (hm : 1 ≤ m) {s : v.adicCompletion K} (hs : Valued.v s ≤ WithZero.exp (-(m : ℤ))) :
    TateLocal.charExt χ (1 + s) = 1 := by
  have hs1 : Valued.v s < 1 :=
    hs.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have h1 : Valued.v (1 + s) = 1 := Valuation.map_one_add_of_lt _ hs1
  have hne : (1 + s) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero] at h1; exact h1)
  have hu1 : Valued.v (((Units.mk0 (1 + s) hne : (v.adicCompletion K)ˣ) : v.adicCompletion K)) = 1 := by
    rw [Units.val_mk0]; exact h1
  have hu2 : IsOneMod K v m (Units.mk0 (1 + s) hne) := by
    show Valued.v (((Units.mk0 (1 + s) hne : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) ≤
      WithZero.exp (-(m : ℤ))
    rw [Units.val_mk0, add_sub_cancel_left]; exact hs
  have key : χ (Units.mk0 (1 + s) hne) = 1 := hχ (Units.mk0 (1 + s) hne) hu1 hu2
  rw [TateLocal.charExt_of_ne_zero χ hne, key, Units.val_one]

end GaussFixedVector
end
section
section GaussFixedVector

open scoped WithZero
open UnramifiedWhittaker

private theorem charExt_mul_of_ne_zero (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    {a b : v.adicCompletion K} (ha : a ≠ 0) (hb : b ≠ 0) :
    TateLocal.charExt χ (a * b) = TateLocal.charExt χ a * TateLocal.charExt χ b := by
  rw [TateLocal.charExt_of_ne_zero χ (mul_ne_zero ha hb), Units.mk0_mul, map_mul, Units.val_mul,
    TateLocal.charExt_of_ne_zero χ ha, TateLocal.charExt_of_ne_zero χ hb]

end GaussFixedVector
end
section
section TestPoint

open UnramifiedWhittaker NumberField.InfinitePlace
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem realComponent_eq_map (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    realComponent w hw g = ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivRealOfIsReal hw) :=
  Matrix.ext fun _ _ => rfl

end TestPoint
end
section
section TestPoint

open UnramifiedWhittaker NumberField.InfinitePlace
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem complexComponent_eq_map (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw g = ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivComplexOfIsComplex hw) :=
  Matrix.ext fun _ _ => rfl

end TestPoint
end
section
section SeriesCoefficient

open NumberField.InfinitePlace

private theorem det_realComponent_ne_zero (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    (realComponent w hw g).det ≠ 0 := by
  rw [realComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr
    ((Matrix.isUnit_iff_isUnit_det _).mp (AdelicLevel.archComponent K w (glArch (𝓞 K) K g)).isUnit).ne_zero

end SeriesCoefficient
end
section
section SeriesCoefficient

open NumberField.InfinitePlace

private theorem det_complexComponent_ne_zero (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    (complexComponent w hw g).det ≠ 0 := by
  rw [complexComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr
    ((Matrix.isUnit_iff_isUnit_det _).mp (AdelicLevel.archComponent K w (glArch (𝓞 K) K g)).isUnit).ne_zero

end SeriesCoefficient
end
section
section GaussCoefficient
open scoped Classical
open scoped WithZero
p2m_open "LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace AutomorphicForm.GaussTwist"
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private noncomputable def seriesTerm (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) (α : Kˣ) : ℂ :=
  d.a α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)
    * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)

end GaussCoefficient
end
section
section GaussCoefficient
open scoped Classical
open scoped WithZero
p2m_open "LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace AutomorphicForm.GaussTwist"
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
private theorem jlSeries'_eq_tsum_seriesTerm (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) :
    jlSeries' d archR archC dR dC dF g = ∑' α : Kˣ, seriesTerm d archR archC dR dC dF g α := by
  simp only [jlSeries', whittakerSeries, seriesTerm]

end GaussCoefficient
end
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open MeasureTheory Topology

section TorusInterchange

private theorem continuousOn_tsum_of_locally_summable {ι X : Type*} [TopologicalSpace X] {term : ι → X → ℂ}
    {D : Set X} (hcont : ∀ i, ContinuousOn (term i) D)
    (hloc : ∀ x ∈ D, ∃ U ∈ 𝓝 x, ∃ M : ι → ℝ, Summable M ∧ ∀ i, ∀ y ∈ D ∩ U, ‖term i y‖ ≤ M i) :
    ContinuousOn (fun x => ∑' i, term i x) D := by
  intro x hx
  obtain ⟨U, hU, M, hM, hbound⟩ := hloc x hx
  have hDU : ContinuousOn (fun x => ∑' i, term i x) (D ∩ U) :=
    continuousOn_tsum (fun i => (hcont i).mono Set.inter_subset_left) hM fun i y hy => hbound i y hy
  exact (hDU x ⟨hx, mem_of_mem_nhds hU⟩).mono_of_mem_nhdsWithin (inter_mem_nhdsWithin D hU)

end TorusInterchange

section LatticeWeight

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in

private noncomputable def archLatticeWeight (k N : ℕ) (ξ : K) : ℝ :=
  (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k
    * (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + |(NumberField.mixedEmbedding K ξ).1 w|) ^ (-(N : ℝ)))
    * ∏ w : {w : InfinitePlace K // w.IsComplex}, (1 + ‖(NumberField.mixedEmbedding K ξ).2 w‖) ^ (-(2 * N : ℝ))

private def integralAfter (δ : 𝓞 K) : Set Kˣ :=
  {α | ∃ β : 𝓞 K, (β : K) = (δ : K) * (α : K)}

private theorem mem_spanSingleton_inv_of_mem_integralAfter {δ : 𝓞 K} (hδ : δ ≠ 0) {α : Kˣ}
    (hα : α ∈ integralAfter δ) :
    (α : K) ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹) := by
  obtain ⟨β, hβ⟩ := hα
  have hδK : (δ : K) ≠ 0 := by exact_mod_cast hδ
  refine (FractionalIdeal.mem_spanSingleton (S := nonZeroDivisors (𝓞 K))).2 ⟨β, ?_⟩
  rw [Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap, hβ, mul_comm ((δ : K)) _, mul_assoc,
    mul_inv_cancel₀ hδK, mul_one]

private theorem exists_summable_archLatticeWeight_subtype (δ : 𝓞 K) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Summable fun ξ : {ξ : K // ξ ≠ 0 ∧ ξ ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹)} =>
        archLatticeWeight k N ξ.1 := by
  obtain ⟨N₀, hN₀⟩ := NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg K
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹)) k 0 1 one_pos
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨C, hC⟩ := hN₀ N hN
  refine (hC 1 le_rfl).1.congr fun ξ => ?_
  simp only [archLatticeWeight, one_mul]

private theorem exists_summable_archLatticeWeight (δ : 𝓞 K) (hδ : δ ≠ 0) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Summable fun α : Kˣ => (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight k N (α : K)) α := by
  obtain ⟨N₀, hN₀⟩ := exists_summable_archLatticeWeight_subtype δ k
  refine ⟨N₀, fun N hN => ?_⟩
  rw [← summable_subtype_iff_indicator]
  have hf : Function.Injective fun α : {α : Kˣ // α ∈ integralAfter δ} =>
      (⟨(α.1 : K), α.1.ne_zero, mem_spanSingleton_inv_of_mem_integralAfter hδ α.2⟩ :
        {ξ : K // ξ ≠ 0 ∧ ξ ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((δ : K)⁻¹)}) :=
    fun a b hab => Subtype.ext (Units.ext (congrArg Subtype.val hab))
  have h := (hN₀ N hN).comp_injective hf
  exact h

end LatticeWeight

section Absorption

variable {K : Type} [Field K] [NumberField K]

private theorem prod_one_add_rpow_le_archLatticeWeight (k N : ℕ) (ξ : K) :
    (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k * ∏ w : InfinitePlace K, (1 + w ξ) ^ (-(2 * N : ℝ))
      ≤ archLatticeWeight k N ξ := by
  classical
  classical
  unfold archLatticeWeight
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)

  have hsplit : ∏ w : InfinitePlace K, (1 + w ξ) ^ (-(2 * N : ℝ))
      = (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + w.1 ξ) ^ (-(2 * N : ℝ)))
        * ∏ w : {w : InfinitePlace K // w.IsComplex}, (1 + w.1 ξ) ^ (-(2 * N : ℝ)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => w.IsReal)]
    congr 1
    exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => (InfinitePlace.not_isReal_iff_isComplex)) _ _
      fun w => rfl
  rw [hsplit]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · refine Finset.prod_le_prod ?_ ?_
    · intro w _
      exact (Real.rpow_pos_of_pos (by linarith [apply_nonneg w.1 ξ]) _).le
    intro w _
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal, ← Real.norm_eq_abs,
      InfinitePlace.norm_embedding_of_isReal w.2 ξ]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [apply_nonneg w.1 ξ]) (by linarith)
  · refine le_of_eq (Finset.prod_congr rfl fun w _ => ?_)
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]

private theorem one_le_abs_norm_of_ne_zero {β : 𝓞 K} (hβ : β ≠ 0) : (1 : ℝ) ≤ |Algebra.norm ℚ (β : K)| := by
  have h : Algebra.norm ℤ β ≠ 0 := (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hβ
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs h
  rw [← Algebra.coe_norm_int β]
  exact_mod_cast h1

private theorem exists_le_archLatticeWeight (δ : 𝓞 K) (hδ : δ ≠ 0) {κ σ : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    {k : ℕ} (hk : κ ≤ k) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ α : Kˣ, α ∈ integralAfter δ →
      |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
          * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))
        ≤ C * archLatticeWeight k N (α : K) := by
  classical
  have hδ1 : (1 : ℝ) ≤ |Algebra.norm ℚ (δ : K)| := one_le_abs_norm_of_ne_zero hδ
  refine ⟨2 * N + ⌈σ⌉₊, |Algebra.norm ℚ (δ : K)| ^ (κ + σ), by positivity, fun α hα => ?_⟩
  obtain ⟨β, hβ⟩ := hα
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hβ
    exact mul_ne_zero (by exact_mod_cast hδ) (α.ne_zero) hβ.symm
  have hαpos : ∀ w : InfinitePlace K, 0 < w (α : K) := fun w => InfinitePlace.pos_iff.mpr α.ne_zero
  have hW := prod_one_add_rpow_le_archLatticeWeight (K := K) k N (α : K)
  have hβnorm : (1 : ℝ) ≤ |Algebra.norm ℚ (β : K)| := one_le_abs_norm_of_ne_zero hβ0
  rw [hβ, map_mul, abs_mul, Rat.cast_mul] at hβnorm
  have hmult : ∏ w : InfinitePlace K, w (α : K) ^ InfinitePlace.mult w
      ≤ (∏ w : InfinitePlace K, w (α : K)) * ∏ w : InfinitePlace K, (1 + w (α : K)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod ?_ ?_
    · intro w _
      exact pow_nonneg (hαpos w).le _
    intro w _
    unfold InfinitePlace.mult
    split_ifs <;> simp only [pow_one, pow_two] <;> nlinarith [hαpos w]
  rw [InfinitePlace.prod_eq_abs_norm] at hmult
  have hmult' : ((|Algebra.norm ℚ (α : K)| : ℚ) : ℝ)
      ≤ (∏ w : InfinitePlace K, w (α : K)) * ∏ w : InfinitePlace K, (1 + w (α : K)) := by
    exact_mod_cast hmult
  have hδα : ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ)
      = ((|Algebra.norm ℚ (δ : K)| : ℚ) : ℝ) * ((|Algebra.norm ℚ (α : K)| : ℚ) : ℝ) := by
    rw [map_mul, abs_mul, Rat.cast_mul]
  rw [hδα]
  set nδ : ℝ := ((|Algebra.norm ℚ (δ : K)| : ℚ) : ℝ) with hnδ
  set nα : ℝ := ((|Algebra.norm ℚ (α : K)| : ℚ) : ℝ) with hnα
  set P : ℝ := ∏ w : InfinitePlace K, w (α : K) with hP
  set Q : ℝ := ∏ w : InfinitePlace K, (1 + w (α : K)) with hQ
  have hδpos : 0 < nδ := by linarith
  have hα0 : 0 ≤ nα := by rw [hnα]; exact Rat.cast_nonneg.mpr (abs_nonneg _)
  have hPpos : 0 < P := Finset.prod_pos fun w _ => hαpos w
  have hQpos : 0 < Q := Finset.prod_pos fun w _ => by linarith [hαpos w]

  have hN1 : (nδ * nα) ^ κ ≤ nδ ^ κ * (max 1 nα) ^ k := by
    rw [Real.mul_rpow hδpos.le hα0]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hδpos.le _)
    calc nα ^ κ ≤ (max 1 nα) ^ κ := Real.rpow_le_rpow hα0 (le_max_right _ _) hκ
      _ ≤ (max 1 nα) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hk
      _ = (max 1 nα) ^ k := Real.rpow_natCast _ _

  have hPinv : P⁻¹ ≤ nδ * Q := by
    rw [inv_le_iff_one_le_mul₀ hPpos]
    calc (1 : ℝ) ≤ nδ * nα := hβnorm
      _ ≤ nδ * (P * Q) := mul_le_mul_of_nonneg_left hmult' hδpos.le
      _ = nδ * Q * P := by ring
  have hN2 : ∏ w : InfinitePlace K, (w (α : K)) ^ (-σ) ≤ nδ ^ σ * Q ^ σ := by
    rw [Real.finsetProd_rpow Finset.univ (fun w : InfinitePlace K => w (α : K)) (fun w _ => (hαpos w).le) (-σ),
      ← hP, Real.rpow_neg hPpos.le, ← Real.inv_rpow hPpos.le, ← Real.mul_rpow hδpos.le hQpos.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hPpos.le) hPinv hσ

  have hN3 : Q ^ σ * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ))
      ≤ ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(2 * N : ℝ)) := by
    have hQ1 : ∀ w : InfinitePlace K, (1 : ℝ) ≤ 1 + w (α : K) := fun w => by linarith [hαpos w]
    have hsplit : ∀ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ))
        = (1 + w (α : K)) ^ (-(2 * N : ℝ)) * ((1 + w (α : K)) ^ (-(⌈σ⌉₊ : ℝ))) := fun w => by
      rw [← Real.rpow_add (by linarith [hαpos w])]
      congr 1
      push_cast
      ring
    simp only [hsplit, Finset.prod_mul_distrib]
    rw [Real.finsetProd_rpow Finset.univ (fun w : InfinitePlace K => 1 + w (α : K)) (fun w _ => by linarith [hαpos w])
      (-(⌈σ⌉₊ : ℝ)), ← hQ]
    set A : ℝ := ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(2 * N : ℝ)) with hA
    have hA0 : 0 ≤ A := Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [hαpos w]) _).le
    have hQ1' : (1 : ℝ) ≤ Q :=
      calc (1 : ℝ) = ∏ _w : InfinitePlace K, (1 : ℝ) := Finset.prod_const_one.symm
        _ ≤ Q := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => hQ1 w
    have hQQ : Q ^ (-(⌈σ⌉₊ : ℝ)) * Q ^ σ ≤ 1 := by
      rw [← Real.rpow_add hQpos]
      calc Q ^ (-(⌈σ⌉₊ : ℝ) + σ) ≤ Q ^ (0 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hQ1' (by linarith [Nat.le_ceil σ])
        _ = 1 := Real.rpow_zero Q
    calc Q ^ σ * (A * Q ^ (-(⌈σ⌉₊ : ℝ))) = A * (Q ^ (-(⌈σ⌉₊ : ℝ)) * Q ^ σ) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hQQ hA0
      _ = A := mul_one A

  have hδκσ : nδ ^ (κ + σ) = nδ ^ κ * nδ ^ σ := Real.rpow_add hδpos _ _
  have hPσ : 0 ≤ ∏ w : InfinitePlace K, (w (α : K)) ^ (-σ) :=
    Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (hαpos w) _).le
  have hM0 : 0 ≤ ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [hαpos w]) _).le
  have hQσ : 0 ≤ Q ^ σ := Real.rpow_nonneg hQpos.le _
  rw [hδκσ]
  calc (nδ * nα) ^ κ * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
        * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ))
      ≤ nδ ^ κ * (max 1 nα) ^ k * (nδ ^ σ * Q ^ σ)
          * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hN1 hN2 hPσ (by positivity)) hM0
    _ = nδ ^ κ * nδ ^ σ * ((max 1 nα) ^ k
          * (Q ^ σ * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-((2 * N + ⌈σ⌉₊ : ℕ) : ℝ)))) := by ring
    _ ≤ nδ ^ κ * nδ ^ σ * ((max 1 nα) ^ k * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(2 * N : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN3 (by positivity)) (by positivity)
    _ ≤ nδ ^ κ * nδ ^ σ * archLatticeWeight k N (α : K) := mul_le_mul_of_nonneg_left hW (by positivity)

end Absorption

section LocalMajorant

variable {K : Type} [Field K] [NumberField K]

private theorem archLatticeWeight_nonneg (k N : ℕ) (ξ : K) : 0 ≤ archLatticeWeight k N ξ := by
  classical
  unfold archLatticeWeight
  refine mul_nonneg (mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) ?_) ?_
  · exact Finset.prod_nonneg fun w _ => Real.rpow_nonneg (by positivity) _
  · exact Finset.prod_nonneg fun w _ => Real.rpow_nonneg (by positivity) _

private theorem exists_local_majorant {G : Type*} [TopologicalSpace G] (δ : 𝓞 K) (hδ : δ ≠ 0)
    (coef : Kˣ → ℂ) (eps : G → ℂ) (X Y : G → Kˣ → ℂ) (g₀ : G)
    (hcoef : ∃ Cb : ℝ, ∀ α, ‖coef α‖ ≤ Cb) (heps : ∀ g, ‖eps g‖ ≤ 1)
    (hY : ∃ V ∈ 𝓝 g₀, ∃ C κ : ℝ, 0 ≤ κ ∧ ∀ g ∈ V, ∀ α : Kˣ, coef α * Y g α ≠ 0 →
      α ∈ integralAfter δ ∧ ‖Y g α‖ ≤ C * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ)
    (hX : ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ V ∈ 𝓝 g₀, ∃ A : ℝ, ∀ g ∈ V, ∀ α : Kˣ,
      ‖X g α‖ ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
        * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))) :
    ∃ V ∈ 𝓝 g₀, ∃ b : Kˣ → ℝ, Summable b ∧ (∀ α, 0 ≤ b α) ∧
      ∀ g ∈ V, ∀ α : Kˣ, ‖coef α * eps g * X g α * Y g α‖ ≤ b α := by
  obtain ⟨Cb, hCb⟩ := hcoef
  obtain ⟨V₁, hV₁, C, κ, hκ, hY⟩ := hY
  obtain ⟨σ, hσ, hX⟩ := hX
  obtain ⟨N₀, hN₀⟩ := exists_summable_archLatticeWeight δ hδ ⌈κ⌉₊
  obtain ⟨M, C₂, hC₂, habs⟩ := exists_le_archLatticeWeight δ hδ hκ hσ (Nat.le_ceil κ) N₀
  obtain ⟨V₂, hV₂, A, hA⟩ := hX M
  have hwt0 : ∀ α : Kˣ, 0 ≤ (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) α :=
    fun α => Set.indicator_nonneg (s := integralAfter δ) (f := fun β : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (β : K))
      (fun β _ => archLatticeWeight_nonneg ⌈κ⌉₊ N₀ (β : K)) α
  set wt : Kˣ → ℝ := fun α => (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) α with hwt
  set D : ℝ := max Cb 0 * max C 0 * max A 0 * C₂ with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, fun α => D * wt α, (hN₀ N₀ le_rfl).mul_left D,
    fun α => mul_nonneg hD0 (hwt0 α), fun g hg α => ?_⟩
  by_cases h0 : coef α * Y g α = 0
  · have : coef α * eps g * X g α * Y g α = 0 := by
      rcases mul_eq_zero.1 h0 with h | h <;> simp [h]
    rw [this, norm_zero]
    exact mul_nonneg hD0 (hwt0 α)
  obtain ⟨hmem, hYb⟩ := hY g hg.1 α h0
  have hwtα : wt α = archLatticeWeight ⌈κ⌉₊ N₀ (α : K) := by
    simp only [hwt, Set.indicator_of_mem hmem]
  have hαpos : ∀ w : InfinitePlace K, 0 < w (α : K) := fun w => InfinitePlace.pos_iff.mpr α.ne_zero
  have hn0 : (0 : ℝ) ≤ ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ) ^ κ := by positivity
  set P : ℝ := (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
    * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)) with hP
  have hP0 : 0 ≤ P :=
    mul_nonneg (Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (hαpos w) _).le)
      (Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [hαpos w]) _).le)
  have hXb : ‖X g α‖ ≤ max A 0 * P := by
    refine (hA g hg.2 α).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hP0
  have hYb' : ‖Y g α‖ ≤ max C 0 * ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ) ^ κ :=
    hYb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)
  have hcb : ‖coef α‖ ≤ max Cb 0 := (hCb α).trans (le_max_left _ _)
  show _ ≤ D * wt α
  rw [hwtα, hD]
  calc ‖coef α * eps g * X g α * Y g α‖ = ‖coef α‖ * ‖eps g‖ * ‖X g α‖ * ‖Y g α‖ := by
        simp only [norm_mul]
    _ ≤ max Cb 0 * 1 * (max A 0 * P) * (max C 0 * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ) := by
        gcongr
        exact heps g
    _ = max Cb 0 * max C 0 * max A 0
          * (|Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
            * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))) := by rw [hP]; ring
    _ ≤ max Cb 0 * max C 0 * max A 0 * (C₂ * archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) :=
        mul_le_mul_of_nonneg_left (habs α hmem) (by positivity)
    _ = max Cb 0 * max C 0 * max A 0 * C₂ * archLatticeWeight ⌈κ⌉₊ N₀ (α : K) := by ring

end LocalMajorant

section TermContinuity

variable {K : Type} [Field K] [NumberField K]

private theorem exists_nhds_forall_wf_mul_eq {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi) (g₀ : AdelicGL2 (𝓞 K) K) :
    ∃ V ∈ 𝓝 g₀, ∀ (x : AdelicGL2 (𝓞 K) K), ∀ g ∈ V, dF.Wf (x * g) = dF.Wf (x * g₀) := by
  refine ⟨(fun g : AdelicGL2 (𝓞 K) K => g₀⁻¹ * g) ⁻¹' (levelOne (𝓞 K) K ⊤ : Set (AdelicGL2 (𝓞 K) K)), ?_, ?_⟩
  · refine ((isOpen_levelOne (𝓞 K) K top_ne_bot).preimage (continuous_const_mul _)).mem_nhds ?_
    show g₀⁻¹ * g₀ ∈ levelOne (𝓞 K) K ⊤
    rw [inv_mul_cancel]
    exact one_mem _
  intro x g hg
  have hkmem : g₀⁻¹ * g ∈ levelOne (𝓞 K) K ⊤ := hg
  have hgk : g = g₀ * (g₀⁻¹ * g) := (mul_inv_cancel_left g₀ g).symm
  rw [hgk, ← mul_assoc, dF.finite_dependent (x * g₀ * (g₀⁻¹ * g))
    (x * g₀ * AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K (g₀⁻¹ * g)))
    (by simp only [map_mul, AdelicDock.glFin_finEmbed])]
  refine FiniteWhittaker.wf_mul_of_mem_integral dF _ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [AdelicDock.finEmbed_mem_levelOne_iff]
    exact hkmem
  · exact (mem_finiteAdelicGL2Subgroup_iff _ _).mpr (AdelicDock.glArch_finEmbed _ _ _)

private theorem wf_eventuallyEq_mul {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi) (x g₀ : AdelicGL2 (𝓞 K) K) :
    ∀ᶠ g in 𝓝 g₀, dF.Wf (x * g) = dF.Wf (x * g₀) := by
  obtain ⟨V, hV, hVeq⟩ := exists_nhds_forall_wf_mul_eq dF g₀
  filter_upwards [hV] with g hg using hVeq x g hg

private theorem charExt_eq_of_isOneMod {v : HeightOneSpectrum (𝓞 K)} {χ : (v.adicCompletion K)ˣ →* ℂˣ} {n : ℕ}
    (hχ : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → IsOneMod K v n u → χ u = 1)
    (hn : 1 ≤ n) {x₀ x : v.adicCompletion K} (hx₀ : x₀ ≠ 0)
    (hx : Valued.v (x / x₀ - 1) ≤ WithZero.exp (-(n : ℤ))) : TateLocal.charExt χ x = TateLocal.charExt χ x₀ := by
  have h1 : TateLocal.charExt χ (1 + (x / x₀ - 1)) = 1 := charExt_one_add v hχ hn hx
  have hne : (1 + (x / x₀ - 1)) ≠ 0 := fun h => by
    rw [h, TateLocal.charExt_zero] at h1
    exact zero_ne_one h1
  have hxeq : x = x₀ * (1 + (x / x₀ - 1)) := by
    field_simp
    ring
  rw [hxeq, charExt_mul_of_ne_zero v χ hx₀ hne, h1, mul_one]

private theorem epsChar_eventuallyEq {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (d : JLData K S epsS ω) {g₀ : AdelicGL2 (𝓞 K) K} (hg₀ : g₀ ∈ kZeroSet S d.m) :
    ∀ᶠ g in 𝓝 g₀, d.epsChar g = d.epsChar g₀ := by
  have hopen : ∀ᶠ g in 𝓝 g₀, g ∈ kZeroSet S d.m := (isOpen_kZeroSet S d.m).mem_nhds hg₀
  have hfac : ∀ v : ↥S, ∀ᶠ g in 𝓝 g₀,
      TateLocal.charExt (localChar ω v.1) (componentMatrix v.1 g 1 1)
          = TateLocal.charExt (localChar ω v.1) (componentMatrix v.1 g₀ 1 1) ∧
        TateLocal.charExt (epsS v.1) (componentMatrix v.1 g 0 0 / componentMatrix v.1 g 1 1)
          = TateLocal.charExt (epsS v.1) (componentMatrix v.1 g₀ 0 0 / componentMatrix v.1 g₀ 1 1) := by
    intro v
    obtain ⟨hd, had, -, -⟩ := hg₀ v
    have hd0 : componentMatrix v.1 g₀ 1 1 ≠ 0 := (Valuation.ne_zero_iff _).mp hd
    have ha0 : componentMatrix v.1 g₀ 0 0 ≠ 0 := (Valuation.ne_zero_iff _).mp (had ▸ hd)
    have ht : ((localOf K v.1 d.A : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) ≠ 0 := Units.ne_zero _
    have key : ∀ F : AdelicGL2 (𝓞 K) K → v.1.adicCompletion K, ContinuousAt F g₀ → F g₀ ≠ 0 →
        ∀ᶠ g in 𝓝 g₀, Valued.v (F g / F g₀ - 1) ≤ WithZero.exp (-(d.m v : ℤ)) := by
      intro F hF hF0
      have hc : ContinuousAt (fun g => F g / F g₀ - 1) g₀ := (hF.div_const _).sub continuousAt_const
      have h0 : {z : v.1.adicCompletion K |
          Valued.v z ≤ Valued.v ((localOf K v.1 d.A : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)}
            ∈ 𝓝 ((fun g => F g / F g₀ - 1) g₀) := by
        simp only [div_self hF0, sub_self]
        exact setOf_v_le_mem_nhds ht (by simp)
      filter_upwards [hc.preimage_mem_nhds h0] with g hg
      simpa only [Set.mem_preimage, Set.mem_setOf_eq, d.A_ord v] using hg
    have h11 := key (fun g => componentMatrix v.1 g 1 1) (continuous_componentMatrix_apply v.1 1 1).continuousAt hd0
    have hr := key (fun g => componentMatrix v.1 g 0 0 / componentMatrix v.1 g 1 1)
      ((continuous_componentMatrix_apply v.1 0 0).continuousAt.div
        (continuous_componentMatrix_apply v.1 1 1).continuousAt hd0) (div_ne_zero ha0 hd0)
    filter_upwards [h11, hr] with g hg1 hg2
    exact ⟨charExt_eq_of_isOneMod (d.central_level v) (d.m_pos v) hd0 hg1,
      charExt_eq_of_isOneMod (d.epsS_level v) (d.m_pos v) (div_ne_zero ha0 hd0) hg2⟩
  filter_upwards [hopen, Filter.eventually_all.2 hfac] with g hg hfg
  have hg' : ∀ v : ↥S, MemZK0At v.1 (d.m v) g := hg
  have hg₀' : ∀ v : ↥S, MemZK0At v.1 (d.m v) g₀ := hg₀
  unfold JLData.epsChar
  rw [if_pos hg', if_pos hg₀']
  exact Finset.prod_congr rfl fun v _ => by rw [(hfg v).1, (hfg v).2]

end TermContinuity

section FiniteTransport

variable {K : Type} [Field K] [NumberField K]

open LanglandsTunnell.TateLocal NumberField.StandardAddChar

private theorem exists_nhds_wf_bound {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (coef : Kˣ → ℂ)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (g₀ : AdelicGL2 (𝓞 K) K) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∃ V ∈ 𝓝 g₀, ∃ C κ : ℝ, 0 ≤ κ ∧ ∀ g ∈ V, ∀ α : Kˣ,
      coef α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g) ≠ 0 →
        α ∈ integralAfter δ ∧
          ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)‖ ≤ C * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ := by
  obtain ⟨δ, hδ, C, κ, hκ, hrow⟩ := FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le K S Pi hgrow dF g₀
    (fun v => addCharLevel (psiLocal K v.1))
  obtain ⟨V, hV, hVeq⟩ := exists_nhds_forall_wf_mul_eq dF g₀
  refine ⟨δ, hδ, V, hV, C, κ, hκ, fun g hg α hne => ?_⟩
  have hcoef : coef α ≠ 0 := left_ne_zero_of_mul hne
  have hW : dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g) ≠ 0 := right_ne_zero_of_mul hne
  have htrans : dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g) = dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g₀) :=
    hVeq _ g hg
  have hval : ∀ v : ↥S,
      Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
        ≤ WithZero.exp (addCharLevel (psiLocal K v.1)) := by
    by_contra h
    exact hcoef (hfloor α (not_forall.mp h))
  rw [htrans] at hW ⊢
  obtain ⟨β, hβ, hbound⟩ := hrow α hval hW
  refine ⟨⟨β, hβ⟩, ?_⟩
  rwa [hβ] at hbound

end FiniteTransport

section Assembly

variable {K : Type} [Field K] [NumberField K]

open LanglandsTunnell.TateLocal NumberField.StandardAddChar

private theorem exists_local_majorant_of_data {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    {Pi : HeckeEigensystem K ℂ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (coef : Kˣ → ℂ) (hcoef : ∃ C : ℝ, ∀ α, ‖coef α‖ ≤ C)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (heps : ∀ g : AdelicGL2 (𝓞 K) K, ‖d.epsChar g‖ ≤ 1)
    (harch : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ V ∈ 𝓝 g₀, ∃ A : ℝ, ∀ g ∈ V, ∀ α : Kˣ,
      ‖archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ)) * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)))
    (h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) (hh : Continuous h) (g₀ : AdelicGL2 (𝓞 K) K) :
    ∃ V ∈ 𝓝 g₀, ∃ b : Kˣ → ℝ, Summable b ∧ (∀ α, 0 ≤ b α) ∧ ∀ g ∈ V, ∀ α : Kˣ,
      ‖coef α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g)
        * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ b α := by
  obtain ⟨δ, hδ, V, hV, C, κ, hκ, hbound⟩ := exists_nhds_wf_bound dF hgrow coef hfloor (h g₀)
  refine exists_local_majorant δ hδ coef d.epsChar
    (fun g α => archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g))
    (fun g α => dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)) g₀ hcoef heps
    ⟨h ⁻¹' V, hh.continuousAt.preimage_mem_nhds hV, C, κ, hκ, fun g hg α => hbound (h g) hg α⟩ ?_
  obtain ⟨σ, hσ, hM⟩ := harch (h g₀)
  refine ⟨σ, hσ, fun M => ?_⟩
  obtain ⟨W, hW, A, hA⟩ := hM M
  exact ⟨h ⁻¹' W, hh.continuousAt.preimage_mem_nhds hW, A, fun g hg α => hA (h g) hg α⟩

private theorem continuousOn_tsum_of_data {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    {Pi : HeckeEigensystem K ℂ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (coef : Kˣ → ℂ) (hcoef : ∃ C : ℝ, ∀ α, ‖coef α‖ ≤ C)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (heps : ∀ g : AdelicGL2 (𝓞 K) K, ‖d.epsChar g‖ ≤ 1)
    (harch : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ V ∈ 𝓝 g₀, ∃ A : ℝ, ∀ g ∈ V, ∀ α : Kˣ,
      ‖archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ)) * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)))
    (hcont : Continuous (archW' archR archC dR dC)) (h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K)
    (hh : Continuous h) :
    ContinuousOn (fun g : AdelicGL2 (𝓞 K) K => ∑' α : Kˣ, coef α * d.epsChar g
      * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g)
      * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)) (kZeroSet S d.m) := by
  refine continuousOn_tsum_of_locally_summable (fun α => ?_) (fun g₀ _ => ?_)
  · intro g hg
    have h1 : ∀ᶠ g' in 𝓝 g, coef α * d.epsChar g' * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g')
          * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g')
        = coef α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g')
          * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g) := by
      filter_upwards [epsChar_eventuallyEq d hg,
        (hh.tendsto g).eventually (wf_eventuallyEq_mul dF (globalPoints (𝓞 K) K (diagOne α)) (h g))] with g' he hw
      simp only [he, hw]
    have h2 : ContinuousAt (fun g' => coef α * d.epsChar g
        * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g')
        * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)) g :=
      (continuousAt_const.mul (hcont.comp (continuous_const.mul hh)).continuousAt).mul continuousAt_const
    exact (h2.congr_of_eventuallyEq h1).continuousWithinAt
  · obtain ⟨V, hV, b, hb, -, hle⟩ :=
      exists_local_majorant_of_data d archR archC dR dC dF coef hcoef hfloor hgrow heps harch h hh g₀
    exact ⟨V, hV, b, hb, fun α g hg => hle g hg.2 α⟩

private theorem summable_norm_seriesTerm_of_majorant {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    {Pi : HeckeEigensystem K ℂ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (heps : ∀ g : AdelicGL2 (𝓞 K) K, ‖d.epsChar g‖ ≤ 1)
    (harch : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ V ∈ 𝓝 g₀, ∃ A : ℝ, ∀ g ∈ V, ∀ α : Kˣ,
      ‖archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ)) * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)))
    (g : AdelicGL2 (𝓞 K) K) :
    Summable fun α : Kˣ =>
      ‖d.a α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)
        * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)‖ := by
  obtain ⟨V, hV, b, hb, -, hle⟩ := exists_local_majorant_of_data d archR archC dR dC dF d.a
    (d.bounded.imp fun _ h α => (h α).1) (fun α h => (d.floor α h).1) hgrow heps harch id continuous_id g
  exact Summable.of_nonneg_of_le (fun α => norm_nonneg _) (fun α => hle g (mem_of_mem_nhds hV) α) hb

private theorem continuousOn_series_of_majorant {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    {Pi : HeckeEigensystem K ℂ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (heps : ∀ g : AdelicGL2 (𝓞 K) K, ‖d.epsChar g‖ ≤ 1)
    (harch : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ V ∈ 𝓝 g₀, ∃ A : ℝ, ∀ g ∈ V, ∀ α : Kˣ,
      ‖archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ)) * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)))
    (hcont : Continuous (archW' archR archC dR dC)) :
    ContinuousOn (jlSeries' d archR archC dR dC dF) (kZeroSet S d.m) := by
  have hrw : jlSeries' d archR archC dR dC dF = fun g => ∑' α : Kˣ, seriesTerm d archR archC dR dC dF g α :=
    funext fun g => jlSeries'_eq_tsum_seriesTerm d archR archC dR dC dF g
  rw [hrw]
  exact continuousOn_tsum_of_data d archR archC dR dC dF d.a (d.bounded.imp fun _ h α => (h α).1)
    (fun α h => (d.floor α h).1) hgrow heps harch hcont id continuous_id

end Assembly

section GrowthExponent

variable {K : Type} [Field K] [NumberField K]

private theorem two_le_absNorm_real (v : HeightOneSpectrum (𝓞 K)) : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem norm_b_eq_absNorm (Pi : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : ‖Pi.b v‖ = (Ideal.absNorm v.asIdeal : ℝ) := by
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith [two_le_absNorm_real (K := K) v]
  obtain ⟨-, -, hωu⟩ := id hω
  have hunit : ‖((ω (uniformizerIdele K v) : ℂˣ) : ℂ)‖ = 1 := hωu _
  rw [hωb v hv, HeckeEigensystem.twist_b, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN _), ← Real.rpow_natCast, ← Real.rpow_mul hN.le] at hunit
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    rw [show -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [hpow] at hunit
  field_simp at hunit
  linarith [hunit, norm_nonneg (Pi.b v)]

private theorem exists_growth_exponent (Pi : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC) :
    ∃ κ : ℝ, ∀ v ∉ S, ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ := by
  classical

  obtain ⟨μ, hμ, hunr⟩ := exists_isJLTwist K S epsS d.m d.epsS_level
  obtain ⟨⟨-, hcont, hunit⟩, -⟩ := id hμ
  obtain ⟨uR, aR, uC, kC, hcR, hcC⟩ := exists_archParams_of_continuous K μ hcont
  obtain ⟨R, hR⟩ := hnice
  have hD := hR μ hμ uR aR uC kC hcR hcC
  dsimp only at hD
  obtain ⟨-, hconv, -⟩ := hD
  set D := twistedDatum K (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    S archR archC μ uR aR uC kC with hDdef

  have h2 := (hconv 2 (by norm_num [hDdef, twistedDatum])).1

  have hcof := Filter.eventually_cofinite.1 ((Metric.tendsto_nhds.1 h2.tendsto_cofinite_zero) 1 one_pos)
  set F₁ := hcof.toFinset with hF₁
  set B : ℝ := 1 + ∑ i ∈ F₁, ‖Pi.a i.1‖ with hB
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ i ∈ F₁, ‖Pi.a i.1‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  refine ⟨max 4 (Real.logb 2 B), fun v hv => ?_⟩
  have hN2 := two_le_absNorm_real (K := K) v
  have hNpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hNnat : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast hNpos
  have hκ0 : (0 : ℝ) ≤ max 4 (Real.logb 2 B) := le_trans (by norm_num) (le_max_left _ _)

  have hN4 : (Ideal.absNorm v.asIdeal : ℝ) ^ (4 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ max 4 (Real.logb 2 B) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hNB : B ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ max 4 (Real.logb 2 B) := by
    calc B = (2 : ℝ) ^ Real.logb 2 B := (Real.rpow_logb (by norm_num) (by norm_num) hBpos).symm
      _ ≤ (2 : ℝ) ^ max 4 (Real.logb 2 B) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_right _ _)
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ max 4 (Real.logb 2 B) := Real.rpow_le_rpow (by norm_num) hN2 hκ0
  have hb : ‖Pi.b v‖ = (Ideal.absNorm v.asIdeal : ℝ) := norm_b_eq_absNorm Pi S ω hω hωb hv
  refine ⟨?_, ?_⟩
  swap
  · rw [hb]
    calc (Ideal.absNorm v.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ ≤ _ := hN4
  by_cases hmem : (⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) ∈ F₁
  ·
    have hle : ‖Pi.a v‖ ≤ B := by
      have := Finset.single_le_sum (f := fun i : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => ‖Pi.a i.1‖)
        (fun i _ => norm_nonneg _) hmem
      simp only at this
      linarith
    exact hle.trans hNB
  ·
    have hnear : dist ‖(D.euler ⟨v, hv⟩).eval ((D.norm ⟨v, hv⟩ : ℂ) ^ (-(2 : ℂ))) - 1‖ 0 < 1 := by
      have := hmem
      rw [hF₁, Set.Finite.mem_toFinset] at this
      simpa using this
    rw [Real.dist_0_eq_abs, abs_norm, hDdef] at hnear
    simp only [twistedDatum] at hnear
    rw [if_pos (hunr v hv)] at hnear
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow, HeckeEigensystem.twist_a, HeckeEigensystem.twist_b] at hnear

    set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef
    set c : ℂ := ((N ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hc
    set m : ℂ := ((μ (uniformizerIdele K v) : ℂˣ) : ℂ) with hm
    set m₂ : ℂ := (((μ (uniformizerIdele K v)) ^ 2 : ℂˣ) : ℂ) with hm₂
    set x : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ)) with hx
    have hxn : ‖x‖ = N ^ (-(2 : ℝ)) := by
      rw [hx, Complex.norm_natCast_cpow_of_pos hNnat, hNdef]
      simp
    have hμ1 : ‖m‖ = 1 := hunit _
    have hμ2 : ‖m₂‖ = 1 := by
      rw [hm₂, Units.val_pow_eq_pow_val, norm_pow]
      exact by rw [← hm, hμ1, one_pow]
    have hbn : ‖c ^ 2 * Pi.b v‖ = 1 := by
      obtain ⟨-, -, hωu⟩ := id hω
      have := hωu (uniformizerIdele K v)
      rwa [hωb v hv, HeckeEigensystem.twist_b] at this
    have hcn : ‖c‖ = N ^ (-(1 / 2 : ℝ)) := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hNpos _)]

    have hkey : ‖c‖ * ‖Pi.a v‖ * ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by
      have hsplit : m * (c * Pi.a v) * x
          = -((1 - m * (c * Pi.a v) * x + m₂ * (c ^ 2 * Pi.b v) * x ^ 2) - 1) + m₂ * (c ^ 2 * Pi.b v) * x ^ 2 := by
        ring
      have hL : ‖m * (c * Pi.a v) * x‖ = ‖c‖ * ‖Pi.a v‖ * ‖x‖ := by
        rw [norm_mul, norm_mul, norm_mul, hμ1, one_mul]
      have hR' : ‖m₂ * (c ^ 2 * Pi.b v) * x ^ 2‖ = ‖x‖ ^ 2 := by
        rw [norm_mul, norm_mul, hμ2, hbn, norm_pow, one_mul, one_mul]
      rw [← hL, hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, hR']
      exact add_le_add hnear.le le_rfl
    rw [hcn, hxn] at hkey

    have hx4 : (N ^ (-(2 : ℝ))) ^ 2 ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hprod : N ^ (-(1 / 2 : ℝ)) * N ^ (-(2 : ℝ)) = (N ^ ((5 : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_neg hNpos.le]; norm_num
    have hfive : N ^ ((5 : ℝ) / 2) * 2 ≤ N ^ (4 : ℝ) := by
      calc N ^ ((5 : ℝ) / 2) * 2 ≤ N ^ ((5 : ℝ) / 2) * N ^ (1 : ℝ) := by
            rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hN2 (Real.rpow_pos_of_pos hNpos _).le
        _ = N ^ ((7 : ℝ) / 2) := by rw [← Real.rpow_add hNpos]; norm_num
        _ ≤ N ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hpos52 : 0 < N ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hNpos _
    have ha : ‖Pi.a v‖ ≤ N ^ ((5 : ℝ) / 2) * 2 := by
      have h1 : ‖Pi.a v‖ * (N ^ ((5 : ℝ) / 2))⁻¹ ≤ 2 := by
        have := hkey
        rw [mul_comm _ ‖Pi.a v‖, mul_assoc, hprod] at this
        linarith
      rwa [← div_eq_mul_inv, div_le_iff₀ hpos52, mul_comm] at h1
    exact ha.trans (hfive.trans hN4)

end GrowthExponent

section EpsBound

variable {K : Type} [Field K] [NumberField K] {S : Finset (HeightOneSpectrum (𝓞 K))}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem norm_localChar_eq_one {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 K) K μ)
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) : ‖((localChar μ v u : ℂˣ) : ℂ)‖ = 1 :=
  hμ _

private theorem norm_epsS_eq_one_of_valuation_eq_one (d : JLData K S epsS ω) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ S) (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ‖((epsS v u : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨μ, hμ, -⟩ := exists_isJLTwist K S epsS d.m d.epsS_level
  obtain ⟨⟨-, -, hunit⟩, hS⟩ := hμ
  have h := congrArg (fun x : ℂˣ => ‖(x : ℂ)‖) (hS v hv u hu)
  simp only [Units.val_mul, norm_mul, Units.val_one, norm_one] at h
  rwa [norm_localChar_eq_one hunit, one_mul] at h

private theorem norm_epsChar_le_one (d : JLData K S epsS ω) (hω : IsAdmissibleTwist K ω) (g : AdelicGL2 (𝓞 K) K) :
    ‖d.epsChar g‖ ≤ 1 := by
  obtain ⟨-, -, hωu⟩ := hω
  unfold JLData.epsChar
  split_ifs with hg
  · rw [norm_prod]
    refine Finset.prod_le_one (fun v _ => norm_nonneg _) (fun v _ => ?_)
    obtain ⟨hd, had, -, -⟩ := hg v
    have hd0 : componentMatrix v.1 g 1 1 ≠ 0 := fun h => hd (by rw [h, map_zero])
    have ha0 : componentMatrix v.1 g 0 0 ≠ 0 := fun h => hd (by rw [← had, h, map_zero])
    have hx0 : componentMatrix v.1 g 0 0 / componentMatrix v.1 g 1 1 ≠ 0 := div_ne_zero ha0 hd0
    rw [norm_mul, TateLocal.charExt_of_ne_zero _ hd0, TateLocal.charExt_of_ne_zero _ hx0,
      norm_localChar_eq_one hωu, one_mul]
    refine le_of_eq (norm_epsS_eq_one_of_valuation_eq_one d v.2 _ ?_)
    rw [Units.val_mk0, map_div₀, had, div_self hd]
  · simp

end EpsBound

end LanglandsTunnell.Converse.CuspSynthesis

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section ArchContinuity

open NumberField.InfinitePlace
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem continuous_realComponent (w : InfinitePlace K) (hw : w.IsReal) : Continuous (realComponent w hw) := by
  have hc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
      ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp
      ((AdelicLevel.continuous_archComponent K w).comp (AdelicLevel.continuous_glArch (𝓞 K) K))
  have he : Continuous (Completion.ringEquivRealOfIsReal hw) :=
    (Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  have hfun : realComponent w hw = fun g : AdelicGL2 (𝓞 K) K =>
      (((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivRealOfIsReal hw)) :=
    funext (realComponent_eq_map w hw)
  rw [hfun]
  exact hc.matrix_map he

private theorem continuous_complexComponent (w : InfinitePlace K) (hw : w.IsComplex) :
    Continuous (complexComponent w hw) := by
  have hc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
      ((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp
      ((AdelicLevel.continuous_archComponent K w).comp (AdelicLevel.continuous_glArch (𝓞 K) K))
  have he : Continuous (Completion.ringEquivComplexOfIsComplex hw) :=
    (Completion.isometry_extensionEmbedding (v := w)).continuous
  have hfun : complexComponent w hw = fun g : AdelicGL2 (𝓞 K) K =>
      (((AdelicLevel.archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).map (Completion.ringEquivComplexOfIsComplex hw)) :=
    funext (complexComponent_eq_map w hw)
  rw [hfun]
  exact hc.matrix_map he

private theorem isOpen_glSetR : IsOpen ArchR.glSet := by
  have h : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M.det :=
    (continuous_id : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M).matrix_det
  exact isOpen_ne_fun h continuous_const

private theorem isOpen_glSetC : IsOpen ArchC.glSet := by
  have h : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => M.det :=
    (continuous_id : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => M).matrix_det
  exact isOpen_ne_fun h continuous_const

private theorem continuous_W_realComponent {P : RealArchParam} (D : ArchDatumR P) (w : InfinitePlace K)
    (hw : w.IsReal) : Continuous fun g : AdelicGL2 (𝓞 K) K => D.W (realComponent w hw g) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hmem : realComponent w hw g ∈ ArchR.glSet := det_realComponent_ne_zero w hw g
  have h1 : ContinuousAt (ArchR.asPi D.W) (realComponent w hw g) :=
    D.smooth.continuousOn.continuousAt (isOpen_glSetR.mem_nhds hmem)
  exact h1.comp (continuous_realComponent w hw).continuousAt

private theorem continuous_W_complexComponent {P : ComplexArchParam} (D : ArchDatumC P) (w : InfinitePlace K)
    (hw : w.IsComplex) : Continuous fun g : AdelicGL2 (𝓞 K) K => D.W (complexComponent w hw g) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hmem : complexComponent w hw g ∈ ArchC.glSet := det_complexComponent_ne_zero w hw g
  have h1 : ContinuousAt (ArchC.asPi D.W) (complexComponent w hw g) :=
    D.smooth.continuousOn.continuousAt (isOpen_glSetC.mem_nhds hmem)
  exact h1.comp (continuous_complexComponent w hw).continuousAt

private theorem continuous_archW (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) :
    Continuous (archW archR archC dR dC) := by
  unfold archW
  refine continuous_finset_prod _ fun w _ => ?_
  by_cases hw : w.IsReal
  · simp only [dif_pos hw]
    exact continuous_W_realComponent (dR w hw) w hw
  · simp only [dif_neg hw]
    exact continuous_W_complexComponent (dC w (InfinitePlace.not_isReal_iff_isComplex.mp hw)) w _

private theorem continuous_archNormFactor : Continuous (archNormFactor (K := K)) := by
  unfold archNormFactor
  refine continuous_finset_prod _ fun w _ => ?_
  by_cases hw : w.IsReal
  · simp only [dif_pos hw]
    refine Continuous.inv₀ ?_ fun g => ?_
    · exact Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (continuous_abs.comp (continuous_realComponent w hw).matrix_det))
    · exact Complex.ofReal_ne_zero.2
        (Real.sqrt_ne_zero'.2 (abs_pos.2 (det_realComponent_ne_zero w hw g)))
  · simp only [dif_neg hw]
    refine Continuous.inv₀ ?_ fun g => ?_
    · exact Complex.continuous_ofReal.comp (continuous_norm.comp (continuous_complexComponent w _).matrix_det)
    · exact Complex.ofReal_ne_zero.2
        (norm_ne_zero_iff.2 (det_complexComponent_ne_zero w (InfinitePlace.not_isReal_iff_isComplex.mp hw) g))

private theorem continuous_archW' (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) :
    Continuous (archW' archR archC dR dC) := by
  have h : archW' archR archC dR dC = fun g => archW archR archC dR dC g * archNormFactor g := rfl
  rw [h]
  exact (continuous_archW archR archC dR dC).mul continuous_archNormFactor

end ArchContinuity

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

section ArchProfileBounds

open Matrix

namespace ArchIwasawa

section Generic

variable {A : Type*} [CommRing A]

private theorem diagOne_mul_unip_mul (t x : A) (M : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (!![1, x; 0, 1] * M) = !![1, t * x; 0, 1] * (!![t, 0; 0, 1] * M) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagOne_mul_smul (t r : A) (M : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (r • M) = r • (!![t, 0; 0, 1] * M) :=
  Matrix.mul_smul _ _ _

private theorem diagOne_mul_diagOne_mul (t y : A) (k : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (!![y, 0; 0, 1] * k) = !![t * y, 0; 0, 1] * k := by
  rw [← Matrix.mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagOne_mul_iwasawa (t x r y : A) (k : Matrix (Fin 2) (Fin 2) A) :
    !![t, 0; 0, 1] * (!![1, x; 0, 1] * (r • (!![y, 0; 0, 1] * k)))
      = !![1, t * x; 0, 1] * (r • (!![t * y, 0; 0, 1] * k)) := by
  rw [diagOne_mul_unip_mul, diagOne_mul_smul, diagOne_mul_diagOne_mul]

end Generic

namespace Real

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.rowNorm : ℝ := √(g 1 0 ^ 2 + g 1 1 ^ 2)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "rowNorm"

private noncomputable def kOf : Matrix (Fin 2) (Fin 2) ℝ := (rowNorm g)⁻¹ • !![g 1 1, -g 1 0; g 1 0, g 1 1]

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.yOf : ℝ := g.det / rowNorm g ^ 2

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "yOf"

private noncomputable def xOf : ℝ := (g 0 0 * g 1 0 + g 0 1 * g 1 1) / rowNorm g ^ 2

variable {g}

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.rowNorm_sq : rowNorm g ^ 2 = g 1 0 ^ 2 + g 1 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "rowNorm_sq"
private theorem rowNorm_nonneg : 0 ≤ rowNorm g := Real.sqrt_nonneg _

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.rowNorm_pos (hg : g.det ≠ 0) : 0 < rowNorm g := by
  apply Real.sqrt_pos.mpr
  by_contra h
  have h0 : g 1 0 = 0 ∧ g 1 1 = 0 := by
    constructor <;> nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
  apply hg
  rw [Matrix.det_fin_two, h0.1, h0.2]
  ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "rowNorm_pos"
private theorem rowNorm_ne_zero (hg : g.det ≠ 0) : rowNorm g ≠ 0 := (rowNorm_pos hg).ne'

private theorem kOf_mem (hg : g.det ≠ 0) : kOf g ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  have hr := rowNorm_ne_zero hg
  have hsq := rowNorm_sq (g := g)
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem eq_unip_mul (hg : g.det ≠ 0) :
    g = !![1, xOf g; 0, 1] * (rowNorm g • (!![yOf g, 0; 0, 1] * kOf g)) := by
  have hr := rowNorm_ne_zero hg
  have hsq := rowNorm_sq (g := g)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, xOf, yOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem abs_yOf : |yOf g| = |g.det| / rowNorm g ^ 2 := by
  rw [yOf, abs_div, abs_pow, abs_of_nonneg rowNorm_nonneg]

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.yOf_ne_zero (hg : g.det ≠ 0) : yOf g ≠ 0 :=
  div_ne_zero hg (pow_ne_zero 2 (rowNorm_ne_zero hg))

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "yOf_ne_zero"

private theorem diagOne_mul_eq (hg : g.det ≠ 0) (t : ℝ) :
    !![t, 0; 0, 1] * g = !![1, t * xOf g; 0, 1] * (rowNorm g • (!![t * yOf g, 0; 0, 1] * kOf g)) := by
  conv_lhs => rw [eq_unip_mul hg]
  exact diagOne_mul_iwasawa t (xOf g) (rowNorm g) (yOf g) (kOf g)

private theorem continuous_rowNorm : Continuous fun g : Matrix (Fin 2) (Fin 2) ℝ => rowNorm g := by
  unfold rowNorm
  fun_prop

private theorem continuous_absYOf_on :
    ContinuousOn (fun g : Matrix (Fin 2) (Fin 2) ℝ => |yOf g|) {g | g.det ≠ 0} := by
  have h : ∀ g ∈ {g : Matrix (Fin 2) (Fin 2) ℝ | g.det ≠ 0}, |yOf g| = |g.det| / rowNorm g ^ 2 := fun g _ => abs_yOf
  refine ContinuousOn.congr ?_ h
  apply ContinuousOn.div (by fun_prop) (continuous_rowNorm.pow 2).continuousOn
  intro g hg
  exact pow_ne_zero 2 (rowNorm_ne_zero hg)

end Real

namespace Complex

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.rowNorm : ℝ := √(‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "rowNorm"

private noncomputable def kOf : Matrix (Fin 2) (Fin 2) ℂ :=
  ((rowNorm g : ℝ) : ℂ)⁻¹ • !![(starRingEnd ℂ) (g 1 1), -(starRingEnd ℂ) (g 1 0); g 1 0, g 1 1]

private noncomputable def _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.yOf : ℂ := g.det / ((rowNorm g : ℝ) : ℂ) ^ 2

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "yOf"

private noncomputable def xOf : ℂ :=
  (g 0 0 * (starRingEnd ℂ) (g 1 0) + g 0 1 * (starRingEnd ℂ) (g 1 1)) / ((rowNorm g : ℝ) : ℂ) ^ 2

variable {g}

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.rowNorm_sq : rowNorm g ^ 2 = ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 :=
  _root_.Real.sq_sqrt (by positivity)

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "rowNorm_sq"
private theorem rowNorm_nonneg : 0 ≤ rowNorm g := _root_.Real.sqrt_nonneg _

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.rowNorm_pos (hg : g.det ≠ 0) : 0 < rowNorm g := by
  apply _root_.Real.sqrt_pos.mpr
  by_contra h
  have h0 : g 1 0 = 0 ∧ g 1 1 = 0 := by
    constructor <;> rw [← norm_eq_zero] <;> nlinarith [norm_nonneg (g 1 0), norm_nonneg (g 1 1)]
  apply hg
  rw [Matrix.det_fin_two, h0.1, h0.2]
  ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "rowNorm_pos"
private theorem rowNorm_ne_zero (hg : g.det ≠ 0) : rowNorm g ≠ 0 := (rowNorm_pos hg).ne'

open ComplexConjugate in
private theorem ofReal_rowNorm_sq : ((rowNorm g : ℝ) : ℂ) ^ 2 = conj (g 1 0) * g 1 0 + conj (g 1 1) * g 1 1 := by
  rw [Complex.conj_mul', Complex.conj_mul', ← Complex.ofReal_pow, rowNorm_sq]
  push_cast
  ring

private theorem kOf_mem (hg : g.det ≠ 0) : kOf g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hr : ((rowNorm g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero hg)
  have hsq := ofReal_rowNorm_sq (g := g)
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem eq_unip_mul (hg : g.det ≠ 0) :
    g = !![1, xOf g; 0, 1] * (((rowNorm g : ℝ) : ℂ) • (!![yOf g, 0; 0, 1] * kOf g)) := by
  have hr : ((rowNorm g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero hg)
  have hsq := ofReal_rowNorm_sq (g := g)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kOf, xOf, yOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    field_simp <;> (try rw [hsq]) <;> ring

private theorem norm_yOf : ‖yOf g‖ = ‖g.det‖ / rowNorm g ^ 2 := by
  rw [yOf, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg rowNorm_nonneg]

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.yOf_ne_zero (hg : g.det ≠ 0) : yOf g ≠ 0 :=
  div_ne_zero hg (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero hg)))

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "yOf_ne_zero"

private theorem diagOne_mul_eq (hg : g.det ≠ 0) (t : ℂ) :
    !![t, 0; 0, 1] * g
      = !![1, t * xOf g; 0, 1] * (((rowNorm g : ℝ) : ℂ) • (!![t * yOf g, 0; 0, 1] * kOf g)) := by
  conv_lhs => rw [eq_unip_mul hg]
  exact diagOne_mul_iwasawa t (xOf g) _ (yOf g) (kOf g)

private theorem continuous_rowNorm : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => rowNorm g := by
  unfold rowNorm
  fun_prop

private theorem continuous_normYOf_on :
    ContinuousOn (fun g : Matrix (Fin 2) (Fin 2) ℂ => ‖yOf g‖) {g | g.det ≠ 0} := by
  have h : ∀ g ∈ {g : Matrix (Fin 2) (Fin 2) ℂ | g.det ≠ 0}, ‖yOf g‖ = ‖g.det‖ / rowNorm g ^ 2 :=
    fun g _ => norm_yOf
  refine ContinuousOn.congr ?_ h
  apply ContinuousOn.div (by fun_prop) (continuous_rowNorm.pow 2).continuousOn
  intro g hg
  exact pow_ne_zero 2 (rowNorm_ne_zero hg)

end Complex

end ArchIwasawa

namespace ArchIwasawa

private theorem rpow_neg_le_rpow_neg_max {s σ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : s ^ (-σ) ≤ s ^ (-(max σ 0)) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 (by have := le_max_left σ 0; linarith)

namespace Real

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.exists_profile_bound (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (ψ : ℝ → ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (χ : ℝ → ℂ) (hχ : ContinuousOn (fun z : ℝ => ‖χ z‖) (Set.Ioi 0))
    (hunip : ∀ (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), W (!![1, x; 0, 1] * g) = ψ x * W g)
    (hcent : ∀ (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), 0 < z → W (z • g) = χ z * W g)
    (hzero : ∃ C σ : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
      y ≠ 0 → |y| ≤ 1 → ‖W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-σ))
    (htop : ∀ N : ℕ, ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
      1 ≤ |y| → ‖W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-(N : ℝ)))
    (Kc : Set (Matrix (Fin 2) (Fin 2) ℝ)) (hKc : IsCompact Kc) (hdet : ∀ g ∈ Kc, g.det ≠ 0) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ Kc, ∀ t : ℝ, t ≠ 0 →
      (|t| * |yOf g| ≤ 1 → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₀ * (|t| * |yOf g|) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ |t| * |yOf g| → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₁ N * (|t| * |yOf g|) ^ (-(N : ℝ))) := by
  obtain ⟨Cz, σz, hz⟩ := hzero
  choose Ct ht using htop
  have hcont : ContinuousOn (fun g : Matrix (Fin 2) (Fin 2) ℝ => ‖χ (rowNorm g)‖) Kc :=
    hχ.comp continuous_rowNorm.continuousOn fun g hg => rowNorm_pos (hdet g hg)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  have hB' : ∀ g ∈ Kc, ‖χ (rowNorm g)‖ ≤ max B 0 := fun g hg => by
    have := hB g hg
    rw [Real.norm_eq_abs, abs_norm] at this
    exact this.trans (le_max_left _ _)
  have key : ∀ g ∈ Kc, ∀ t : ℝ,
      ‖W (!![t, 0; 0, 1] * g)‖ = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := by
    intro g hg t
    rw [diagOne_mul_eq (hdet g hg) t, hunip, hcent _ _ (rowNorm_pos (hdet g hg)), norm_mul, norm_mul, hψ, one_mul]
  refine ⟨max σz 0, max B 0 * max Cz 0, fun N => max B 0 * max (Ct N) 0, le_max_right _ _, ?_⟩
  intro g hg t ht0
  have hy0 : t * yOf g ≠ 0 := mul_ne_zero ht0 (yOf_ne_zero (hdet g hg))
  have hs : |t * yOf g| = |t| * |yOf g| := abs_mul t (yOf g)
  have hspos : 0 < |t| * |yOf g| := by rw [← hs]; exact abs_pos.mpr hy0
  have hk := kOf_mem (hdet g hg)
  constructor
  · intro hs1
    have h1 := hz (t * yOf g) (kOf g) hk hy0 (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * (max Cz 0 * (|t| * |yOf g|) ^ (-(max σz 0))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _) (le_max_right _ _)
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Cz * (|t| * |yOf g|) ^ (-σz) := h1
            _ ≤ max Cz 0 * (|t| * |yOf g|) ^ (-σz) := by
                gcongr; exact le_max_left _ _
            _ ≤ max Cz 0 * (|t| * |yOf g|) ^ (-(max σz 0)) :=
                mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg_max hspos hs1) (le_max_right _ _)
      _ = max B 0 * max Cz 0 * (|t| * |yOf g|) ^ (-(max σz 0)) := by ring
  · intro N hs1
    have h1 := ht N (t * yOf g) (kOf g) hk (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * (max (Ct N) 0 * (|t| * |yOf g|) ^ (-(N : ℝ))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _) (le_max_right _ _)
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Ct N * (|t| * |yOf g|) ^ (-(N : ℝ)) := h1
            _ ≤ max (Ct N) 0 * (|t| * |yOf g|) ^ (-(N : ℝ)) := by
                gcongr; exact le_max_left _ _
      _ = max B 0 * max (Ct N) 0 * (|t| * |yOf g|) ^ (-(N : ℝ)) := by ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "exists_profile_bound"
end Real

end ArchIwasawa

namespace ArchIwasawa
namespace Complex

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.exists_profile_bound (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (ψ : ℂ → ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (χ : ℂ → ℂ) (hχ : ContinuousOn (fun r : ℝ => ‖χ (r : ℂ)‖) (Set.Ioi 0))
    (hunip : ∀ (x : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), W (!![1, x; 0, 1] * g) = ψ x * W g)
    (hcent : ∀ (z : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), z ≠ 0 → W (z • g) = χ z * W g)
    (hzero : ∃ C σ : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      z ≠ 0 → ‖z‖ ≤ 1 → ‖W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-σ))
    (htop : ∀ N : ℕ, ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      1 ≤ ‖z‖ → ‖W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ)))
    (Kc : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hKc : IsCompact Kc) (hdet : ∀ g ∈ Kc, g.det ≠ 0) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ Kc, ∀ t : ℂ, t ≠ 0 →
      (‖t‖ * ‖yOf g‖ ≤ 1 → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₀ * (‖t‖ * ‖yOf g‖) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ ‖t‖ * ‖yOf g‖ → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₁ N * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ))) := by
  obtain ⟨Cz, σz, hz⟩ := hzero
  choose Ct ht using htop
  have hcont : ContinuousOn (fun g : Matrix (Fin 2) (Fin 2) ℂ => ‖χ ((rowNorm g : ℝ) : ℂ)‖) Kc :=
    hχ.comp continuous_rowNorm.continuousOn fun g hg => rowNorm_pos (hdet g hg)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  have hB' : ∀ g ∈ Kc, ‖χ ((rowNorm g : ℝ) : ℂ)‖ ≤ max B 0 := fun g hg => by
    have := hB g hg
    rw [Real.norm_eq_abs, abs_norm] at this
    exact this.trans (le_max_left _ _)
  have key : ∀ g ∈ Kc, ∀ t : ℂ,
      ‖W (!![t, 0; 0, 1] * g)‖ = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := by
    intro g hg t
    rw [diagOne_mul_eq (hdet g hg) t, hunip, hcent _ _ (Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero (hdet g hg))),
      norm_mul, norm_mul, hψ, one_mul]
  refine ⟨max σz 0, max B 0 * max Cz 0, fun N => max B 0 * max (Ct N) 0, le_max_right _ _, ?_⟩
  intro g hg t ht0
  have hy0 : t * yOf g ≠ 0 := mul_ne_zero ht0 (yOf_ne_zero (hdet g hg))
  have hs : ‖t * yOf g‖ = ‖t‖ * ‖yOf g‖ := norm_mul t (yOf g)
  have hspos : 0 < ‖t‖ * ‖yOf g‖ := by rw [← hs]; exact norm_pos_iff.mpr hy0
  have hk := kOf_mem (hdet g hg)
  constructor
  · intro hs1
    have h1 := hz (t * yOf g) (kOf g) hk hy0 (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * (max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _) (le_max_right _ _)
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Cz * (‖t‖ * ‖yOf g‖) ^ (-σz) := h1
            _ ≤ max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-σz) := by
                gcongr; exact le_max_left _ _
            _ ≤ max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0)) :=
                mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg_max hspos hs1) (le_max_right _ _)
      _ = max B 0 * max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0)) := by ring
  · intro N hs1
    have h1 := ht N (t * yOf g) (kOf g) hk (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * (max (Ct N) 0 * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _) (le_max_right _ _)
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Ct N * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := h1
            _ ≤ max (Ct N) 0 * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := by
                gcongr; exact le_max_left _ _
      _ = max B 0 * max (Ct N) 0 * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := by ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "exists_profile_bound"
end ArchIwasawa.Complex

private theorem norm_exp_two_pi_I_mul (x : ℝ) : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x)‖ = 1 := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * x = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := norm_exp_two_pi_I_mul x

private theorem norm_psiC (z : ℂ) : ‖ArchC.psi z‖ = 1 := norm_exp_two_pi_I_mul (2 * z.re)

private theorem norm_centralChar_mul {P : RealArchParam} {z : ℝ} (hz : 0 < z) :
    ‖ArchR.centralChar P z * ((|z| : ℝ) : ℂ)‖ = z ^ P.centralExponent.re * z := by
  have hite : (if P.centralSign = 0 then (1 : ℂ) else ((SignType.sign z : ℝ) : ℂ)) = 1 := by
    rw [sign_pos hz]
    simp
  rw [ArchR.centralChar, ArchR.quasiChar, hite, mul_one, norm_mul, abs_of_pos hz, Complex.norm_cpow_eq_rpow_re_of_pos hz,
    Complex.norm_real, Real.norm_of_nonneg hz.le]

private theorem continuousOn_norm_centralChar_mul (P : RealArchParam) :
    ContinuousOn (fun z : ℝ => ‖ArchR.centralChar P z * ((|z| : ℝ) : ℂ)‖) (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => z ^ P.centralExponent.re * z) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const fun z hz => Or.inl (Set.mem_Ioi.mp hz).ne').mul continuousOn_id
  exact h.congr fun z hz => norm_centralChar_mul (Set.mem_Ioi.mp hz)

private theorem norm_centralCharC_mul {P : ComplexArchParam} {r : ℝ} (hr : 0 < r) :
    ‖ArchC.centralChar P r * ((‖(r : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ = r ^ (2 * P.centralExponent).re * r ^ 2 := by
  have hnr : ‖(r : ℂ)‖ = r := Complex.norm_of_nonneg hr.le
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [ArchC.centralChar, ArchC.quasiChar, hnr, div_self hr0, _root_.one_zpow, mul_one, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg r)]

private theorem continuousOn_norm_centralCharC_mul (P : ComplexArchParam) :
    ContinuousOn (fun r : ℝ => ‖ArchC.centralChar P r * ((‖(r : ℂ)‖ ^ 2 : ℝ) : ℂ)‖) (Set.Ioi 0) := by
  have h : ContinuousOn (fun r : ℝ => r ^ (2 * P.centralExponent).re * r ^ 2) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const fun r hr => Or.inl (Set.mem_Ioi.mp hr).ne').mul (continuousOn_id.pow 2)
  exact h.congr fun r hr => norm_centralCharC_mul (Set.mem_Ioi.mp hr)

private theorem norm_asPi_zero (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ = ‖W (!![y, 0; 0, 1] * k)‖ := by
  rw [norm_iteratedFDerivWithin_zero]
  rfl

private theorem norm_asPiC_zero (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖iteratedFDerivWithin ℝ 0 (ArchC.asPi W) ArchC.glSet (ArchC.diagOneMulCoords z k)‖ = ‖W (!![z, 0; 0, 1] * k)‖ := by
  rw [norm_iteratedFDerivWithin_zero]
  rfl

namespace ArchDatumR p2m_export "LanglandsTunnell.Converse.ArchDatumR" "decay_zero W unip_law decay_top smooth central_law" end ArchDatumR
namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.zero_bound {P : RealArchParam} (D : ArchDatumR P) :
    ∃ C σ : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ → y ≠ 0 → |y| ≤ 1 →
      ‖D.W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-σ) := by
  obtain ⟨C, σ, h⟩ := D.decay_zero 0
  exact ⟨C, σ, fun y k hk hy hy1 => (norm_asPi_zero D.W y k).symm.trans_le (h y k hk hy hy1)⟩

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.zero_bound"
namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.top_bound {P : RealArchParam} (D : ArchDatumR P) (N : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ → 1 ≤ |y| →
      ‖D.W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-(N : ℝ)) := by
  obtain ⟨C, h⟩ := D.decay_top 0 N
  exact ⟨C, fun y k hk hy => (norm_asPi_zero D.W y k).symm.trans_le (h y k hk hy)⟩

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.top_bound"
namespace ArchDatumC p2m_export "LanglandsTunnell.Converse.ArchDatumC" "central_law unip_law W decay_zero decay_top smooth" end ArchDatumC
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.zero_bound {P : ComplexArchParam} (D : ArchDatumC P) :
    ∃ C σ : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ → z ≠ 0 → ‖z‖ ≤ 1 →
      ‖D.W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-σ) := by
  obtain ⟨C, σ, h⟩ := D.decay_zero 0
  exact ⟨C, σ, fun z k hk hz hz1 => (norm_asPiC_zero D.W z k).symm.trans_le (h z k hk hz hz1)⟩

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.zero_bound"
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.top_bound {P : ComplexArchParam} (D : ArchDatumC P) (N : ℕ) :
    ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ → 1 ≤ ‖z‖ →
      ‖D.W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨C, h⟩ := D.decay_top 0 N
  exact ⟨C, fun z k hk hz => (norm_asPiC_zero D.W z k).symm.trans_le (h z k hk hz)⟩

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.top_bound"

namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.two_regime {P : RealArchParam} (D : ArchDatumR P) {K : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (hK : IsCompact K) (hdet : ∀ g ∈ K, g.det ≠ 0) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ K, ∀ t : ℝ, t ≠ 0 →
      (|t| * |ArchIwasawa.Real.yOf g| ≤ 1 →
        ‖D.W (ArchR.diagOne t * g)‖ ≤ C₀ * (|t| * |ArchIwasawa.Real.yOf g|) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ |t| * |ArchIwasawa.Real.yOf g| →
        ‖D.W (ArchR.diagOne t * g)‖ ≤ C₁ N * (|t| * |ArchIwasawa.Real.yOf g|) ^ (-(N : ℝ))) :=
  ArchIwasawa.Real.exists_profile_bound D.W ArchR.psi norm_psi (fun z => ArchR.centralChar P z * ((|z| : ℝ) : ℂ))
    (continuousOn_norm_centralChar_mul P) D.unip_law (fun z g hz => D.central_law z g hz.ne') D.zero_bound
    D.top_bound K hK hdet

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.two_regime"
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.two_regime {P : ComplexArchParam} (D : ArchDatumC P) {K : Set (Matrix (Fin 2) (Fin 2) ℂ)}
    (hK : IsCompact K) (hdet : ∀ g ∈ K, g.det ≠ 0) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ K, ∀ t : ℂ, t ≠ 0 →
      (‖t‖ * ‖ArchIwasawa.Complex.yOf g‖ ≤ 1 →
        ‖D.W (ArchC.diagOne t * g)‖ ≤ C₀ * (‖t‖ * ‖ArchIwasawa.Complex.yOf g‖) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ ‖t‖ * ‖ArchIwasawa.Complex.yOf g‖ →
        ‖D.W (ArchC.diagOne t * g)‖ ≤ C₁ N * (‖t‖ * ‖ArchIwasawa.Complex.yOf g‖) ^ (-(N : ℝ))) :=
  ArchIwasawa.Complex.exists_profile_bound D.W ArchC.psi norm_psiC (fun z => ArchC.centralChar P z * ((‖z‖ ^ 2 : ℝ) : ℂ))
    (continuousOn_norm_centralCharC_mul P) D.unip_law D.central_law D.zero_bound D.top_bound K hK hdet

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.two_regime"

private theorem exists_pos_bounds {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K) {φ : X → ℝ}
    (hφ : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ m₁ m₂ : ℝ, 0 < m₁ ∧ 0 < m₂ ∧ ∀ x ∈ K, m₁ ≤ φ x ∧ φ x ≤ m₂ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφ
  rcases K.eq_empty_or_nonempty with hKe | hne
  · exact ⟨1, 1, one_pos, one_pos, fun x hx => by simp [hKe] at hx⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hφ
  refine ⟨φ x₀, max B 1, hpos x₀ hx₀, lt_max_of_lt_right one_pos, fun x hx => ⟨isMinOn_iff.mp hmin x hx, ?_⟩⟩
  have h := hB x hx
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

private theorem exists_low_const {m₁ σ : ℝ} (hm₁ : 0 < m₁) (hσ : 0 ≤ σ) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ r : ℝ, m₁ ≤ ρ → 0 < r → r * ρ ≤ 1 →
      (r * ρ) ^ (-σ) ≤ K * r ^ (-σ) * (1 + r) ^ (-(M : ℝ)) := by
  have hL : 0 < 1 + m₁⁻¹ := by positivity
  have hM : -(M : ℝ) ≤ 0 := by simp
  refine ⟨m₁ ^ (-σ) * (1 + m₁⁻¹) ^ (M : ℝ), by positivity, fun ρ r hρ hr hs => ?_⟩
  have hr1 : r ≤ m₁⁻¹ := by
    have h : r * m₁ ≤ 1 := (mul_le_mul_of_nonneg_left hρ hr.le).trans hs
    rw [← one_div]
    exact (le_div_iff₀ hm₁).mpr h
  have h1 : (r * ρ) ^ (-σ) ≤ (r * m₁) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (mul_le_mul_of_nonneg_left hρ hr.le) (neg_nonpos.mpr hσ)
  have h3 : (1 + m₁⁻¹) ^ (-(M : ℝ)) ≤ (1 + r) ^ (-(M : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hM
  have h4 : (1 + m₁⁻¹) ^ (M : ℝ) * (1 + m₁⁻¹) ^ (-(M : ℝ)) = 1 := by
    rw [← Real.rpow_add hL, add_neg_cancel, Real.rpow_zero]
  calc (r * ρ) ^ (-σ) ≤ (r * m₁) ^ (-σ) := h1
    _ = r ^ (-σ) * m₁ ^ (-σ) * ((1 + m₁⁻¹) ^ (M : ℝ) * (1 + m₁⁻¹) ^ (-(M : ℝ))) := by
        rw [h4, mul_one, Real.mul_rpow hr.le hm₁.le]
    _ ≤ r ^ (-σ) * m₁ ^ (-σ) * ((1 + m₁⁻¹) ^ (M : ℝ) * (1 + r) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
    _ = _ := by ring

private theorem exists_high_const {m₁ m₂ σ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ r : ℝ, m₁ ≤ ρ → ρ ≤ m₂ → 0 < r → 1 ≤ r * ρ →
      (r * ρ) ^ (-((M + ⌈σ⌉₊ : ℕ) : ℝ)) ≤ K * r ^ (-σ) * (1 + r) ^ (-(M : ℝ)) := by
  have h1m : 0 < 1 + m₂ := by positivity
  have hM : -(M : ℝ) ≤ 0 := by simp
  have hn : -((M : ℝ) + ⌈σ⌉₊) ≤ 0 := neg_nonpos.mpr (by positivity)
  have ha : σ ≤ (⌈σ⌉₊ : ℝ) := Nat.le_ceil σ
  refine ⟨m₁ ^ (-((M : ℝ) + ⌈σ⌉₊)) * ((1 + m₂) ^ (M : ℝ) * m₂ ^ ((⌈σ⌉₊ : ℝ) - σ)), by positivity,
    fun ρ r hρ₁ hρ₂ hr hs => ?_⟩
  rw [Nat.cast_add]
  have hrm₂ : 1 ≤ r * m₂ := hs.trans (mul_le_mul_of_nonneg_left hρ₂ hr.le)
  have hrm : m₂⁻¹ ≤ r := by
    rw [← one_div]
    exact (div_le_iff₀ hm₂).mpr hrm₂
  have h1r : 1 + r ≤ (1 + m₂) * r := by nlinarith [hrm₂]
  have h1 : (r * ρ) ^ (-((M : ℝ) + ⌈σ⌉₊)) ≤ r ^ (-((M : ℝ) + ⌈σ⌉₊)) * m₁ ^ (-((M : ℝ) + ⌈σ⌉₊)) :=
    (Real.rpow_le_rpow_of_nonpos (by positivity) (mul_le_mul_of_nonneg_left hρ₁ hr.le) hn).trans_eq
      (Real.mul_rpow hr.le hm₁.le)
  have h2 : r ^ (-((M : ℝ) + ⌈σ⌉₊)) = r ^ (-(M : ℝ)) * (r ^ (-σ) * r ^ (σ - ⌈σ⌉₊)) := by
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]
    congr 1
    ring
  have h3 : r ^ (σ - ⌈σ⌉₊) ≤ m₂ ^ ((⌈σ⌉₊ : ℝ) - σ) := by
    calc r ^ (σ - ⌈σ⌉₊) ≤ m₂⁻¹ ^ (σ - ⌈σ⌉₊) := Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hm₂) hrm (by linarith)
      _ = m₂ ^ ((⌈σ⌉₊ : ℝ) - σ) := by
        rw [Real.inv_rpow hm₂.le, ← Real.rpow_neg hm₂.le]
        congr 1
        ring
  have h4 : r ^ (-(M : ℝ)) ≤ (1 + m₂) ^ (M : ℝ) * (1 + r) ^ (-(M : ℝ)) := by
    have h5 : ((1 + m₂) * r) ^ (-(M : ℝ)) ≤ (1 + r) ^ (-(M : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1r hM
    rw [Real.mul_rpow h1m.le hr.le] at h5
    have h6 : (1 + m₂) ^ (M : ℝ) * (1 + m₂) ^ (-(M : ℝ)) = 1 := by
      rw [← Real.rpow_add h1m, add_neg_cancel, Real.rpow_zero]
    calc r ^ (-(M : ℝ)) = (1 + m₂) ^ (M : ℝ) * ((1 + m₂) ^ (-(M : ℝ)) * r ^ (-(M : ℝ))) := by
          rw [← mul_assoc, h6, one_mul]
      _ ≤ (1 + m₂) ^ (M : ℝ) * (1 + r) ^ (-(M : ℝ)) := mul_le_mul_of_nonneg_left h5 (by positivity)
  calc (r * ρ) ^ (-((M : ℝ) + ⌈σ⌉₊))
      ≤ r ^ (-((M : ℝ) + ⌈σ⌉₊)) * m₁ ^ (-((M : ℝ) + ⌈σ⌉₊)) := h1
    _ = r ^ (-(M : ℝ)) * (r ^ (-σ) * r ^ (σ - ⌈σ⌉₊)) * m₁ ^ (-((M : ℝ) + ⌈σ⌉₊)) := by rw [h2]
    _ ≤ (1 + m₂) ^ (M : ℝ) * (1 + r) ^ (-(M : ℝ)) * (r ^ (-σ) * m₂ ^ ((⌈σ⌉₊ : ℝ) - σ))
          * m₁ ^ (-((M : ℝ) + ⌈σ⌉₊)) := by gcongr
    _ = _ := by ring

private theorem repackage {m₁ m₂ σ : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hσ : 0 ≤ σ) (C₀ C₁ : ℝ) (M : ℕ) :
    ∃ A : ℝ, ∀ ρ r v : ℝ, m₁ ≤ ρ → ρ ≤ m₂ → 0 < r →
      (r * ρ ≤ 1 → v ≤ C₀ * (r * ρ) ^ (-σ)) →
      (1 ≤ r * ρ → v ≤ C₁ * (r * ρ) ^ (-((M + ⌈σ⌉₊ : ℕ) : ℝ))) →
      v ≤ A * r ^ (-σ) * (1 + r) ^ (-(M : ℝ)) := by
  obtain ⟨K₀, hK₀, h₀⟩ := exists_low_const hm₁ hσ M
  obtain ⟨K₁, hK₁, h₁⟩ := exists_high_const (σ := σ) hm₁ hm₂ M
  refine ⟨max C₀ 0 * K₀ + max C₁ 0 * K₁, fun ρ r v hρ₁ hρ₂ hr hlow hhigh => ?_⟩
  have hρ : 0 < ρ := hm₁.trans_le hρ₁
  have e : (max C₀ 0 * K₀ + max C₁ 0 * K₁) * r ^ (-σ) * (1 + r) ^ (-(M : ℝ))
      = max C₀ 0 * (K₀ * r ^ (-σ) * (1 + r) ^ (-(M : ℝ))) + max C₁ 0 * (K₁ * r ^ (-σ) * (1 + r) ^ (-(M : ℝ))) := by
    ring
  have hX : 0 ≤ max C₀ 0 * (K₀ * r ^ (-σ) * (1 + r) ^ (-(M : ℝ))) := by positivity
  have hY : 0 ≤ max C₁ 0 * (K₁ * r ^ (-σ) * (1 + r) ^ (-(M : ℝ))) := by positivity
  rw [e]
  rcases le_total (r * ρ) 1 with hs | hs
  · refine ((hlow hs).trans ?_).trans (le_add_of_nonneg_right hY)
    exact mul_le_mul (le_max_left _ _) (h₀ ρ r hρ₁ hr hs) (by positivity) (le_max_right _ _)
  · refine ((hhigh hs).trans ?_).trans (le_add_of_nonneg_left hX)
    exact mul_le_mul (le_max_left _ _) (h₁ ρ r hρ₁ hρ₂ hr hs) (by positivity) (le_max_right _ _)

namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in

private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.exists_profile_bound {P : RealArchParam} (D : ArchDatumR P) {C : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (hC : IsCompact C) (hdet : ∀ g ∈ C, g.det ≠ 0) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ A : ℝ, ∀ g ∈ C, ∀ y : ℝ, y ≠ 0 →
      ‖D.W (ArchR.diagOne y * g)‖ ≤ A * |y| ^ (-σ) * (1 + |y|) ^ (-(M : ℝ)) := by
  obtain ⟨σ, C₀, C₁, hσ, hreg⟩ := D.two_regime hC hdet
  obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := exists_pos_bounds hC (ArchIwasawa.Real.continuous_absYOf_on.mono hdet)
    fun g hg => abs_pos.mpr (ArchIwasawa.Real.yOf_ne_zero (hdet g hg))
  refine ⟨σ, hσ, fun M => ?_⟩
  obtain ⟨A, hA⟩ := repackage hm₁ hm₂ hσ C₀ (C₁ (M + ⌈σ⌉₊)) M
  refine ⟨A, fun g hg y hy => ?_⟩
  obtain ⟨hlow, hhigh⟩ := hreg g hg y hy
  exact hA _ _ _ (hm g hg).1 (hm g hg).2 (abs_pos.mpr hy) hlow (hhigh _)

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.exists_profile_bound"
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in

private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.exists_profile_bound {P : ComplexArchParam} (D : ArchDatumC P) {C : Set (Matrix (Fin 2) (Fin 2) ℂ)}
    (hC : IsCompact C) (hdet : ∀ g ∈ C, g.det ≠ 0) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ A : ℝ, ∀ g ∈ C, ∀ z : ℂ, z ≠ 0 →
      ‖D.W (ArchC.diagOne z * g)‖ ≤ A * ‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(M : ℝ)) := by
  obtain ⟨σ, C₀, C₁, hσ, hreg⟩ := D.two_regime hC hdet
  obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := exists_pos_bounds hC (ArchIwasawa.Complex.continuous_normYOf_on.mono hdet)
    fun g hg => norm_pos_iff.mpr (ArchIwasawa.Complex.yOf_ne_zero (hdet g hg))
  refine ⟨σ, hσ, fun M => ?_⟩
  obtain ⟨A, hA⟩ := repackage hm₁ hm₂ hσ C₀ (C₁ (M + ⌈σ⌉₊)) M
  refine ⟨A, fun g hg z hz => ?_⟩
  obtain ⟨hlow, hhigh⟩ := hreg g hg z hz
  exact hA _ _ _ (hm g hg).1 (hm g hg).2 (norm_pos_iff.mpr hz) hlow (hhigh _)

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.exists_profile_bound"
end ArchProfileBounds

open Topology

section ProfileAssembly

private theorem rpow_neg_mul_le_of_le {x σ σ' : ℝ} (hx : 0 < x) (hσ' : σ' ≤ σ) {n : ℕ} (hn : σ - σ' ≤ n)
    (M : ℕ) :
    x ^ (-σ') * (1 + x) ^ (-((M + n : ℕ) : ℝ)) ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := by
  have h1x : 0 < 1 + x := by linarith
  have hpow : x ^ (σ - σ') ≤ (1 + x) ^ (n : ℝ) := by
    calc x ^ (σ - σ') ≤ (1 + x) ^ (σ - σ') :=
          Real.rpow_le_rpow hx.le (by linarith) (by linarith)
      _ ≤ (1 + x) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hn
  have hsplit : x ^ (-σ') = x ^ (-σ) * x ^ (σ - σ') := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hsplit' : (1 + x) ^ (-((M + n : ℕ) : ℝ)) = (1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹ := by
    rw [← Real.rpow_neg h1x.le, ← Real.rpow_add h1x]; congr 1; push_cast; ring
  rw [hsplit, hsplit']
  have hpos : 0 < (1 + x) ^ (n : ℝ) := Real.rpow_pos_of_pos h1x _
  have hxσ : 0 ≤ x ^ (-σ) := (Real.rpow_pos_of_pos hx _).le
  have hM : 0 ≤ (1 + x) ^ (-(M : ℝ)) := (Real.rpow_pos_of_pos h1x _).le
  calc x ^ (-σ) * x ^ (σ - σ') * ((1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹)
      = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * (x ^ (σ - σ') / (1 + x) ^ (n : ℝ)) := by ring
    _ ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * 1 := by
          gcongr
          exact (div_le_one hpos).mpr hpow
    _ = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := mul_one _

private theorem norm_prod_le_of_forall_le {ι : Type*} [Fintype ι] (f : ι → ℂ) (A x : ι → ℝ) (σ : ℝ) (M : ℕ)
    (hf : ∀ i, ‖f i‖ ≤ A i * (x i ^ (-σ) * (1 + x i) ^ (-(M : ℝ)))) :
    ‖∏ i, f i‖ ≤ (∏ i, A i) * (∏ i, x i ^ (-σ)) * ∏ i, (1 + x i) ^ (-(M : ℝ)) := by
  rw [norm_prod, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hf i

private theorem exists_profile_of_forall_index {ι G β : Type*} [Fintype ι] [TopologicalSpace G]
    (f : ι → G → β → ℂ) (x : ι → β → ℝ) (hx : ∀ i b, 0 < x i b) (g₀ : G)
    (h : ∀ i, ∃ σ : ℝ, 0 ≤ σ ∧ ∃ U ∈ 𝓝 g₀, ∀ N : ℕ, ∃ A : ℝ, ∀ g ∈ U, ∀ b,
      ‖f i g b‖ ≤ A * (x i b ^ (-σ) * (1 + x i b) ^ (-(N : ℝ)))) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ V ∈ 𝓝 g₀, ∃ A : ℝ, ∀ g ∈ V, ∀ b,
      ‖∏ i, f i g b‖ ≤ A * (∏ i, x i b ^ (-σ)) * ∏ i, (1 + x i b) ^ (-(M : ℝ)) := by
  choose σ hσ U hU hA using h
  choose A hAle using hA
  set σtot : ℝ := ∑ i, σ i with hσtot
  have hσtot_nonneg : 0 ≤ σtot := Finset.sum_nonneg fun i _ => hσ i
  refine ⟨σtot, hσtot_nonneg, fun M => ?_⟩
  set n : ℕ := ⌈σtot⌉₊ with hn
  refine ⟨⋂ i, U i, Filter.iInter_mem.mpr hU, ∏ i, max (A i (M + n)) 0, fun g hg b => ?_⟩
  have hgi : ∀ i, g ∈ U i := Set.mem_iInter.mp hg
  refine norm_prod_le_of_forall_le (fun i => f i g b) (fun i => max (A i (M + n)) 0) (fun i => x i b) σtot M
    fun i => ?_
  have hσi : σ i ≤ σtot := Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
  have hgap : σtot - σ i ≤ (n : ℝ) := by
    have := Nat.le_ceil σtot
    linarith [hσ i]
  have hnonneg : 0 ≤ x i b ^ (-σ i) * (1 + x i b) ^ (-((M + n : ℕ) : ℝ)) :=
    mul_nonneg (Real.rpow_pos_of_pos (hx i b) _).le (Real.rpow_pos_of_pos (by linarith [hx i b]) _).le
  calc ‖f i g b‖ ≤ A i (M + n) * (x i b ^ (-σ i) * (1 + x i b) ^ (-((M + n : ℕ) : ℝ))) :=
        hAle i (M + n) g (hgi i) b
    _ ≤ max (A i (M + n)) 0 * (x i b ^ (-σ i) * (1 + x i b) ^ (-((M + n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg
    _ ≤ max (A i (M + n)) 0 * (x i b ^ (-σtot) * (1 + x i b) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left (rpow_neg_mul_le_of_le (hx i b) hσi hgap M) (le_max_right _ _)

end ProfileAssembly

open Topology

section ProfilePlaceIdentities

private theorem det_diagOneR_mul (y : ℝ) (m : Matrix (Fin 2) (Fin 2) ℝ) : (ArchR.diagOne y * m).det = y * m.det := by
  rw [Matrix.det_mul, ArchR.diagOne, Matrix.det_fin_two_of]; ring

private theorem det_diagOneC_mul (z : ℂ) (m : Matrix (Fin 2) (Fin 2) ℂ) : (ArchC.diagOne z * m).det = z * m.det := by
  rw [Matrix.det_mul, ArchC.diagOne, Matrix.det_fin_two_of]; ring

private theorem exists_compact_nhds_of_det_ne_zero {G 𝕜 : Type*} [TopologicalSpace G] [RCLike 𝕜] [LocallyCompactSpace 𝕜]
    (c : G → Matrix (Fin 2) (Fin 2) 𝕜) (hc : Continuous c) (g₀ : G) (h₀ : (c g₀).det ≠ 0) :
    ∃ Kc : Set (Matrix (Fin 2) (Fin 2) 𝕜), IsCompact Kc ∧ (∀ m ∈ Kc, m.det ≠ 0) ∧
      ∃ U ∈ 𝓝 g₀, ∀ g ∈ U, c g ∈ Kc := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) 𝕜) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → 𝕜))
  have hopen : IsOpen {m : Matrix (Fin 2) (Fin 2) 𝕜 | m.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  obtain ⟨Kc, hKn, hKsub, hKc⟩ :=
    local_compact_nhds (x := c g₀) (n := {m : Matrix (Fin 2) (Fin 2) 𝕜 | m.det ≠ 0}) (hopen.mem_nhds h₀)
  exact ⟨Kc, hKc, fun m hm => hKsub hm, c ⁻¹' Kc, hc.continuousAt.preimage_mem_nhds hKn, fun _ hg => hg⟩

private theorem exists_bound_inv_sqrt_abs_det (Kc : Set (Matrix (Fin 2) (Fin 2) ℝ)) (hKc : IsCompact Kc)
    (hdet : ∀ m ∈ Kc, m.det ≠ 0) : ∃ B : ℝ, ∀ m ∈ Kc, (Real.sqrt |m.det|)⁻¹ ≤ B := by
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (f := fun m : Matrix (Fin 2) (Fin 2) ℝ => (Real.sqrt |m.det|)⁻¹)
    (ContinuousOn.inv₀ (continuous_id.matrix_det.abs.sqrt.continuousOn) fun m hm =>
      (Real.sqrt_pos.mpr (abs_pos.mpr (hdet m hm))).ne')
  exact ⟨B, fun m hm => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB m hm))⟩

private theorem exists_bound_inv_norm_det (Kc : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hKc : IsCompact Kc)
    (hdet : ∀ m ∈ Kc, m.det ≠ 0) : ∃ B : ℝ, ∀ m ∈ Kc, ‖m.det‖⁻¹ ≤ B := by
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (f := fun m : Matrix (Fin 2) (Fin 2) ℂ => ‖m.det‖⁻¹)
    (ContinuousOn.inv₀ continuous_id.matrix_det.norm.continuousOn fun m hm => (norm_pos_iff.mpr (hdet m hm)).ne')
  exact ⟨B, fun m hm => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB m hm))⟩

private theorem real_factor_bound (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) {σ A B : ℝ} {N : ℕ} {m : Matrix (Fin 2) (Fin 2) ℝ}
    {y : ℝ} (hy : y ≠ 0) (hW : ‖W (ArchR.diagOne y * m)‖ ≤ A * (|y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ))))
    (hB : (Real.sqrt |m.det|)⁻¹ ≤ B) :
    ‖W (ArchR.diagOne y * m) * ((Real.sqrt |(ArchR.diagOne y * m).det| : ℝ) : ℂ)⁻¹‖
      ≤ max A 0 * B * (|y| ^ (-(σ + 1 / 2)) * (1 + |y|) ^ (-(N : ℝ))) := by
  have hay : 0 < |y| := abs_pos.mpr hy
  have hsqy : 0 < Real.sqrt |y| := Real.sqrt_pos.mpr hay
  have hBnn : 0 ≤ B := (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans hB
  have hnorm : ‖(((Real.sqrt |(ArchR.diagOne y * m).det| : ℝ) : ℂ))⁻¹‖ = (Real.sqrt |y|)⁻¹ * (Real.sqrt |m.det|)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), det_diagOneR_mul, abs_mul,
      Real.sqrt_mul (abs_nonneg y), mul_inv]
  have hsq : (Real.sqrt |y|)⁻¹ = |y| ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hay.le]
  have hsplit : |y| ^ (-(σ + 1 / 2)) = |y| ^ (-σ) * |y| ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hay]; congr 1; ring
  have hprof : 0 ≤ |y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ)) :=
    mul_nonneg (Real.rpow_pos_of_pos hay _).le (Real.rpow_pos_of_pos (by linarith) _).le
  have hW' : ‖W (ArchR.diagOne y * m)‖ ≤ max A 0 * (|y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ))) :=
    hW.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hprof)
  rw [norm_mul, hnorm]
  calc ‖W (ArchR.diagOne y * m)‖ * ((Real.sqrt |y|)⁻¹ * (Real.sqrt |m.det|)⁻¹)
      ≤ (max A 0 * (|y| ^ (-σ) * (1 + |y|) ^ (-(N : ℝ)))) * ((Real.sqrt |y|)⁻¹ * B) := by
        gcongr
    _ = max A 0 * B * ((|y| ^ (-σ) * |y| ^ (-(1 / 2 : ℝ))) * (1 + |y|) ^ (-(N : ℝ))) := by rw [hsq]; ring
    _ = max A 0 * B * (|y| ^ (-(σ + 1 / 2)) * (1 + |y|) ^ (-(N : ℝ))) := by rw [hsplit]

private theorem complex_factor_bound (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) {σ A B : ℝ} {N : ℕ} {m : Matrix (Fin 2) (Fin 2) ℂ}
    {z : ℂ} (hz : z ≠ 0) (hW : ‖W (ArchC.diagOne z * m)‖ ≤ A * (‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ))))
    (hB : ‖m.det‖⁻¹ ≤ B) :
    ‖W (ArchC.diagOne z * m) * ((‖(ArchC.diagOne z * m).det‖ : ℝ) : ℂ)⁻¹‖
      ≤ max A 0 * B * (‖z‖ ^ (-(σ + 1)) * (1 + ‖z‖) ^ (-(N : ℝ))) := by
  have haz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hBnn : 0 ≤ B := (inv_nonneg.mpr (norm_nonneg _)).trans hB
  have hnorm : ‖(((‖(ArchC.diagOne z * m).det‖ : ℝ) : ℂ))⁻¹‖ = ‖z‖⁻¹ * ‖m.det‖⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), det_diagOneC_mul, norm_mul,
      mul_inv]
  have hinv : ‖z‖⁻¹ = ‖z‖ ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]
  have hsplit : ‖z‖ ^ (-(σ + 1)) = ‖z‖ ^ (-σ) * ‖z‖ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add haz]; congr 1; ring
  have hprof : 0 ≤ ‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ)) :=
    mul_nonneg (Real.rpow_pos_of_pos haz _).le (Real.rpow_pos_of_pos (by linarith) _).le
  have hW' : ‖W (ArchC.diagOne z * m)‖ ≤ max A 0 * (‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ))) :=
    hW.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hprof)
  rw [norm_mul, hnorm]
  calc ‖W (ArchC.diagOne z * m)‖ * (‖z‖⁻¹ * ‖m.det‖⁻¹)
      ≤ (max A 0 * (‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(N : ℝ)))) * (‖z‖⁻¹ * B) := by
        gcongr
    _ = max A 0 * B * ((‖z‖ ^ (-σ) * ‖z‖ ^ (-(1 : ℝ))) * (1 + ‖z‖) ^ (-(N : ℝ))) := by rw [hinv]; ring
    _ = max A 0 * B * (‖z‖ ^ (-(σ + 1)) * (1 + ‖z‖) ^ (-(N : ℝ))) := by rw [hsplit]

end ProfilePlaceIdentities

namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis"

section ArchProfile

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private noncomputable def archFactorAt (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  if hw : w.IsReal then
    (dR w hw).W (realComponent w hw g) * ((Real.sqrt |(realComponent w hw g).det| : ℝ) : ℂ)⁻¹
  else
    (dC w (not_isReal_iff_isComplex.mp hw)).W (complexComponent w (not_isReal_iff_isComplex.mp hw) g)
      * ((‖(complexComponent w (not_isReal_iff_isComplex.mp hw) g).det‖ : ℝ) : ℂ)⁻¹

private theorem archW'_eq_prod_archFactorAt (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) (g : AdelicGL2 (𝓞 K) K) :
    archW' archR archC dR dC g = ∏ w : InfinitePlace K, archFactorAt archR archC dR dC w g := by
  unfold archW' archW archNormFactor archFactorAt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  split_ifs <;> rfl

private theorem realComponent_globalPoints_diagOne_mul (w : InfinitePlace K) (hw : w.IsReal) (α : Kˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    realComponent w hw (globalPoints (𝓞 K) K (diagOne α) * g)
      = ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K))) * realComponent w hw g := by
  rw [realComponent_eq_map, realComponent_eq_map, FiniteWhittaker.globalPoints_diagOne, map_mul, map_mul,
    FiniteWhittaker.archComponent_glArch_diagOne, Units.val_mul, Matrix.map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, diagOne_coe_apply]
  exact NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw _

private theorem complexComponent_globalPoints_diagOne_mul (w : InfinitePlace K) (hw : w.IsComplex) (α : Kˣ)
    (g : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw (globalPoints (𝓞 K) K (diagOne α) * g)
      = ArchC.diagOne (ringEquivComplexOfIsComplex hw (algebraMap K w.Completion (α : K)))
          * complexComponent w hw g := by
  rw [complexComponent_eq_map, complexComponent_eq_map, FiniteWhittaker.globalPoints_diagOne, map_mul, map_mul,
    FiniteWhittaker.archComponent_glArch_diagOne, Units.val_mul, Matrix.map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchC.diagOne, diagOne_coe_apply]
  exact NumberField.InfinitePlace.Completion.extensionEmbedding_coe (v := w) _

omit [NumberField K] in

private theorem abs_ringEquivReal_algebraMap (w : InfinitePlace K) (hw : w.IsReal) (x : K) :
    |ringEquivRealOfIsReal hw (algebraMap K w.Completion x)| = w x := by
  have h1 := (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
    (algebraMap K w.Completion x)
  rw [Real.norm_eq_abs] at h1
  rw [ringEquivRealOfIsReal_apply, h1,
    show algebraMap K w.Completion x = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) from rfl,
    Completion.norm_coe, RingEquiv.apply_symm_apply]

omit [NumberField K] in

private theorem norm_ringEquivComplex_algebraMap (w : InfinitePlace K) (hw : w.IsComplex) (x : K) :
    ‖ringEquivComplexOfIsComplex hw (algebraMap K w.Completion x)‖ = w x := by
  have h1 := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (algebraMap K w.Completion x)
  rw [ringEquivComplexOfIsComplex_apply, h1,
    show algebraMap K w.Completion x = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) from rfl,
    Completion.norm_coe, RingEquiv.apply_symm_apply]

private theorem exists_profile_archFactorAt (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (g₀ : AdelicGL2 (𝓞 K) K) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∃ U ∈ 𝓝 g₀, ∀ N : ℕ, ∃ A : ℝ, ∀ g ∈ U, ∀ α : Kˣ,
      ‖archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * ((w (α : K)) ^ (-σ) * (1 + w (α : K)) ^ (-(N : ℝ))) := by
  by_cases hw : w.IsReal
  · obtain ⟨Kc, hKc, hdet, U, hU, hmem⟩ := exists_compact_nhds_of_det_ne_zero (realComponent w hw)
      (continuous_realComponent w hw) g₀ (det_realComponent_ne_zero w hw g₀)
    obtain ⟨B, hB⟩ := exists_bound_inv_sqrt_abs_det Kc hKc hdet
    obtain ⟨σ, hσ, hprof⟩ := (dR w hw).exists_profile_bound hKc hdet
    refine ⟨σ + 1 / 2, by linarith, U, hU, fun N => ?_⟩
    obtain ⟨A, hA⟩ := hprof N
    refine ⟨max A 0 * B, fun g hg α => ?_⟩
    have hyw : |ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K))| = w (α : K) :=
      abs_ringEquivReal_algebraMap w hw (α : K)
    have hy0 : ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)) ≠ 0 := by
      intro h
      have := hyw
      rw [h, abs_zero] at this
      exact (w.pos_iff.mpr (Units.ne_zero α)).ne this
    have hfac : archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * g)
        = (dR w hw).W (ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)))
              * realComponent w hw g)
          * ((Real.sqrt |(ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)))
              * realComponent w hw g).det| : ℝ) : ℂ)⁻¹ := by
      rw [archFactorAt, dif_pos hw, realComponent_globalPoints_diagOne_mul]
    rw [hfac, ← hyw]
    exact real_factor_bound (dR w hw).W hy0 (by simpa only [mul_assoc] using hA _ (hmem g hg) _ hy0)
      (hB _ (hmem g hg))
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    obtain ⟨Kc, hKc, hdet, U, hU, hmem⟩ := exists_compact_nhds_of_det_ne_zero (complexComponent w hw')
      (continuous_complexComponent w hw') g₀ (det_complexComponent_ne_zero w hw' g₀)
    obtain ⟨B, hB⟩ := exists_bound_inv_norm_det Kc hKc hdet
    obtain ⟨σ, hσ, hprof⟩ := (dC w hw').exists_profile_bound hKc hdet
    refine ⟨σ + 1, by linarith, U, hU, fun N => ?_⟩
    obtain ⟨A, hA⟩ := hprof N
    refine ⟨max A 0 * B, fun g hg α => ?_⟩
    have hzw : ‖ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K))‖ = w (α : K) :=
      norm_ringEquivComplex_algebraMap w hw' (α : K)
    have hz0 : ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)) ≠ 0 := by
      intro h
      have := hzw
      rw [h, norm_zero] at this
      exact (w.pos_iff.mpr (Units.ne_zero α)).ne this
    have hfac : archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * g)
        = (dC w hw').W (ArchC.diagOne (ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)))
              * complexComponent w hw' g)
          * ((‖(ArchC.diagOne (ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)))
              * complexComponent w hw' g).det‖ : ℝ) : ℂ)⁻¹ := by
      rw [archFactorAt, dif_neg hw, complexComponent_globalPoints_diagOne_mul]
    rw [hfac, ← hzw]
    exact complex_factor_bound (dC w hw').W hz0 (by simpa only [mul_assoc] using hA _ (hmem g hg) _ hz0)
      (hB _ (hmem g hg))

private theorem exists_profile_archW' (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw)) :
    ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ V ∈ 𝓝 g₀, ∃ A : ℝ, ∀ g ∈ V, ∀ α : Kˣ,
      ‖archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ)) * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)) := by
  intro g₀
  have hx : ∀ (w : InfinitePlace K) (α : Kˣ), 0 < w (α : K) := fun w α => w.pos_iff.mpr (Units.ne_zero α)
  have h := exists_profile_of_forall_index
    (fun (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) (α : Kˣ) =>
      archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * g))
    (fun (w : InfinitePlace K) (α : Kˣ) => w (α : K)) hx g₀
    (fun w => exists_profile_archFactorAt archR archC dR dC w g₀)
  simpa only [archW'_eq_prod_archFactorAt] using h

end ArchProfile

end CuspSynthesis

end LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
open AutomorphicForm.SmoothCusp
variable {K : Type} [Field K] [NumberField K]

private theorem summable_norm_seriesTerm
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (g : AdelicGL2 (𝓞 K) K) :
    Summable fun α : Kˣ =>
      ‖d.a α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)
        * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)‖ := by
  exact summable_norm_seriesTerm_of_majorant d archR archC dR dC dF
    (exists_growth_exponent Pi S archR archC epsS ω hω hωb d hnice) (norm_epsChar_le_one d hω)
    (exists_profile_archW' archR archC dR dC) g

private theorem continuousOn_series
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC) :
    ContinuousOn (jlSeries' d archR archC dR dC dF) (kZeroSet S d.m) := by
  exact continuousOn_series_of_majorant d archR archC dR dC dF
    (exists_growth_exponent Pi S archR archC epsS ω hω hωb d hnice) (norm_epsChar_le_one d hω)
    (exists_profile_archW' archR archC dR dC) (continuous_archW' archR archC dR dC)

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LocalWhittaker"
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal NumberField.AdelicVolume
open MeasureTheory
open scoped WithZero Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

section Translate

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

private theorem wf_mul_of_glFin_mem_top (dF : FinWhittakerDatum K S Pi) (x : AdelicGL2 (𝓞 K) K)
    {y : AdelicGL2 (𝓞 K) K} (hy : glFin (𝓞 K) K y ∈ finiteLevelOne (𝓞 K) K ⊤) : dF.Wf (x * y) = dF.Wf x := by
  have hfin : glFin (𝓞 K) K (x * y) = glFin (𝓞 K) K (x * finEmbed (𝓞 K) K (glFin (𝓞 K) K y)) := by
    rw [map_mul, map_mul, glFin_finEmbed]
  rw [dF.finite_dependent _ _ hfin]
  refine wf_mul_of_mem_integral dF x (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [mem_levelOne_iff, glFin_finEmbed]
    exact hy
  · exact (mem_finiteAdelicGL2Subgroup_iff K _).mpr (glArch_finEmbed (𝓞 K) K _)

end Translate

end FiniteWhittaker

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

open LanglandsTunnell.TateLocal NumberField.StandardAddChar

section CosetCover

private theorem exists_wf_bound_on_principal {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (coef : Kˣ → ℂ)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) (D : Set (AdelicGL2 (𝓞 K) K))
    (hD : ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∀ g ∈ D, ∃ t ∈ T, ∃ u ∈ levelOne (𝓞 K) K ⊤, h g = t * u) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∃ V ∈ Filter.principal D, ∃ C κ : ℝ, 0 ≤ κ ∧ ∀ g ∈ V, ∀ α : Kˣ,
      coef α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g) ≠ 0 →
        α ∈ integralAfter δ ∧
          ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ C * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ := by
  classical
  obtain ⟨T, hT⟩ := hD
  choose δt hδt Vt hVt Ct κt hκt hbt using
    fun t : AdelicGL2 (𝓞 K) K => exists_nhds_wf_bound dF hgrow coef hfloor t
  refine ⟨∏ t ∈ T, δt t, Finset.prod_ne_zero_iff.mpr fun t _ => hδt t, D, Filter.mem_principal_self D,
    ∑ t ∈ T, |Ct t|, ∑ t ∈ T, κt t, Finset.sum_nonneg fun t _ => hκt t, fun g hg α hne => ?_⟩
  obtain ⟨t, ht, u, hu, hgu⟩ := hT g hg

  have htrans : dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)
      = dF.Wf (globalPoints (𝓞 K) K (diagOne α) * t) := by
    rw [hgu, ← mul_assoc]
    exact FiniteWhittaker.wf_mul_of_glFin_mem_top dF _ hu
  rw [htrans] at hne ⊢
  obtain ⟨⟨β, hβ⟩, hbound⟩ := hbt t t (mem_of_mem_nhds (hVt t)) α hne

  have hprod : (∏ s ∈ T, δt s) = δt t * ∏ s ∈ T.erase t, δt s := (Finset.mul_prod_erase T δt ht).symm
  have hrest : (∏ s ∈ T.erase t, δt s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hδt s
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hβ
    exact mul_ne_zero (by exact_mod_cast hδt t) α.ne_zero hβ.symm

  have hx1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) := by
    rw [← hβ]
    exact one_le_abs_norm_of_ne_zero hβ0
  have hx0 : (0 : ℝ) ≤ ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) := zero_le_one.trans hx1
  have hr1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K)| : ℚ) : ℝ) :=
    one_le_abs_norm_of_ne_zero hrest
  have hK : (((δt t * ∏ s ∈ T.erase t, δt s : 𝓞 K) : K) * (α : K))
      = ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K) * ((δt t : K) * (α : K)) := by
    push_cast
    ring
  have hyq : |Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))|
      = |Algebra.norm ℚ ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K)| * |Algebra.norm ℚ ((δt t : K) * (α : K))| := by
    rw [← abs_mul, ← map_mul, hprod, hK]
  have hy : ((|Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))| : ℚ) : ℝ)
      = ((|Algebra.norm ℚ ((∏ s ∈ T.erase t, δt s : 𝓞 K) : K)| : ℚ) : ℝ)
        * ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) := by
    rw [hyq, Rat.cast_mul]
  have hxy : ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ)
      ≤ ((|Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))| : ℚ) : ℝ) := by
    rw [hy]
    exact le_mul_of_one_le_left hx0 hr1
  have hβ' : (β : K) = (δt t : K) * (α : K) := hβ
  refine ⟨⟨(∏ s ∈ T.erase t, δt s) * β, ?_⟩, ?_⟩
  · rw [hprod]
    push_cast
    first
      | (rw [hβ']; ring1)
      | (simp only [hβ']; ring1)
      | (rw [hβ]; ring1)
      | (simp only [hβ]; ring1)
  · calc ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * t)‖
        ≤ Ct t * ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) ^ κt t := hbound
      _ ≤ (∑ s ∈ T, |Ct s|) * ((|Algebra.norm ℚ ((δt t : K) * (α : K))| : ℚ) : ℝ) ^ κt t :=
          mul_le_mul_of_nonneg_right
            ((le_abs_self (Ct t)).trans (Finset.single_le_sum (fun s _ => abs_nonneg (Ct s)) ht))
            (Real.rpow_nonneg hx0 _)
      _ ≤ (∑ s ∈ T, |Ct s|)
            * ((|Algebra.norm ℚ (((∏ s ∈ T, δt s : 𝓞 K) : K) * (α : K))| : ℚ) : ℝ) ^ ∑ s ∈ T, κt s := by
          refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun s _ => abs_nonneg (Ct s))
          exact (Real.rpow_le_rpow hx0 hxy (hκt t)).trans
            (Real.rpow_le_rpow_of_exponent_le (hx1.trans hxy) (Finset.single_le_sum (fun s _ => hκt s) ht))

end CosetCover

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

open LanglandsTunnell.TateLocal NumberField.StandardAddChar

section UniformMajorant

private theorem exists_uniform_majorant {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    (dF : FinWhittakerDatum K S Pi) (coef : Kˣ → ℂ) (hcoef : ∃ Cb : ℝ, ∀ α, ‖coef α‖ ≤ Cb)
    (hfloor : ∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (eps : AdelicGL2 (𝓞 K) K → ℂ) (heps : ∀ g, ‖eps g‖ ≤ 1)
    (h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) (D : Set (AdelicGL2 (𝓞 K) K))
    (hD : ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∀ g ∈ D, ∃ t ∈ T, ∃ u ∈ levelOne (𝓞 K) K ⊤, h g = t * u)
    (X : ℕ → AdelicGL2 (𝓞 K) K → Kˣ → ℂ) (H : ℕ → AdelicGL2 (𝓞 K) K → ℝ)
    (hH : ∀ M : ℕ, ∀ g ∈ D, 0 ≤ H M g)
    (hX : ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ A : ℝ, ∀ g ∈ D, ∀ α : Kˣ,
      ‖X M g α‖ ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
        * (∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))) * H M g) :
    ∃ M : ℕ, ∃ C : ℝ, ∀ g ∈ D,
      (Summable fun α : Kˣ => ‖coef α * eps g * X M g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖) ∧
      ∑' α : Kˣ, ‖coef α * eps g * X M g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ C * H M g := by
  classical
  obtain ⟨Cb, hCb⟩ := hcoef
  obtain ⟨δ, hδ, V, hV, C, κ, hκ, hY⟩ := exists_wf_bound_on_principal dF hgrow coef hfloor h D hD
  have hDV : D ⊆ V := Filter.mem_principal.1 hV
  obtain ⟨σ, hσ, hX⟩ := hX
  obtain ⟨N₀, hN₀⟩ := exists_summable_archLatticeWeight δ hδ ⌈κ⌉₊
  obtain ⟨M, C₂, hC₂, habs⟩ := exists_le_archLatticeWeight δ hδ hκ hσ (Nat.le_ceil κ) N₀
  obtain ⟨A, hA⟩ := hX M
  have hwt0 : ∀ α : Kˣ, 0 ≤ (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) α :=
    fun α => Set.indicator_nonneg (s := integralAfter δ) (f := fun β : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (β : K))
      (fun β _ => archLatticeWeight_nonneg ⌈κ⌉₊ N₀ (β : K)) α
  set wt : Kˣ → ℝ := fun α => (integralAfter δ).indicator (fun α : Kˣ => archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) α
    with hwt
  have hwts : Summable wt := hN₀ N₀ le_rfl
  set Dc : ℝ := max Cb 0 * max C 0 * max A 0 * C₂ with hDc
  have hDc0 : 0 ≤ Dc := by positivity
  refine ⟨M, Dc * ∑' α : Kˣ, wt α, fun g hg => ?_⟩
  have hHg : 0 ≤ H M g := hH M g hg

  have hterm : ∀ α : Kˣ,
      ‖coef α * eps g * X M g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ Dc * wt α * H M g := by
    intro α
    by_cases h0 : coef α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g) = 0
    · have : coef α * eps g * X M g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g) = 0 := by
        rcases mul_eq_zero.1 h0 with h | h <;> simp [h]
      rw [this, norm_zero]
      exact mul_nonneg (mul_nonneg hDc0 (hwt0 α)) hHg
    obtain ⟨hmem, hYb⟩ := hY g (hDV hg) α h0
    have hwtα : wt α = archLatticeWeight ⌈κ⌉₊ N₀ (α : K) := by
      simp only [hwt, Set.indicator_of_mem hmem]
    have hαpos : ∀ w : InfinitePlace K, 0 < w (α : K) := fun w => InfinitePlace.pos_iff.mpr α.ne_zero
    have hn0 : (0 : ℝ) ≤ ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ) ^ κ := by positivity
    set P : ℝ := (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
      * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)) with hP
    have hP0 : 0 ≤ P :=
      mul_nonneg (Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (hαpos w) _).le)
        (Finset.prod_nonneg fun w _ => (Real.rpow_pos_of_pos (by linarith [hαpos w]) _).le)
    have hXb : ‖X M g α‖ ≤ max A 0 * P * H M g := by
      refine (hA g hg α).trans ?_
      rw [hP, mul_assoc A]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0) hHg
    have hYb' : ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖
        ≤ max C 0 * ((|Algebra.norm ℚ ((δ : K) * (α : K))| : ℚ) : ℝ) ^ κ :=
      hYb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)
    have hcb : ‖coef α‖ ≤ max Cb 0 := (hCb α).trans (le_max_left _ _)
    rw [hwtα, hDc]
    calc ‖coef α * eps g * X M g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖
        = ‖coef α‖ * ‖eps g‖ * ‖X M g α‖ * ‖dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ := by
          simp only [norm_mul]
      _ ≤ max Cb 0 * 1 * (max A 0 * P * H M g) * (max C 0 * |Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ) := by
          gcongr
          exact heps g
      _ = max Cb 0 * max C 0 * max A 0
            * (|Algebra.norm ℚ ((δ : K) * (α : K))| ^ κ * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ))
              * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ))) * H M g := by rw [hP]; ring
      _ ≤ max Cb 0 * max C 0 * max A 0 * (C₂ * archLatticeWeight ⌈κ⌉₊ N₀ (α : K)) * H M g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (habs α hmem) (by positivity)) hHg
      _ = max Cb 0 * max C 0 * max A 0 * C₂ * archLatticeWeight ⌈κ⌉₊ N₀ (α : K) * H M g := by ring
  have hbound : Summable fun α : Kˣ => Dc * wt α * H M g := (hwts.mul_left Dc).mul_right (H M g)
  have hsum : Summable fun α : Kˣ =>
      ‖coef α * eps g * X M g α * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ :=
    Summable.of_nonneg_of_le (fun α => norm_nonneg _) hterm hbound
  refine ⟨hsum, (hsum.tsum_le_tsum hterm hbound).trans (le_of_eq ?_)⟩
  rw [tsum_mul_right, tsum_mul_left]

end UniformMajorant

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

section SiegelArithmetic
open Matrix

namespace ProfileArith

private theorem rpow_neg_mul_le_of_le {x σ σ' : ℝ} (hx : 0 < x) (hσ' : σ' ≤ σ) {n : ℕ} (hn : σ - σ' ≤ n)
    (M : ℕ) :
    x ^ (-σ') * (1 + x) ^ (-((M + n : ℕ) : ℝ)) ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := by
  have h1x : 0 < 1 + x := by linarith
  have hpow : x ^ (σ - σ') ≤ (1 + x) ^ (n : ℝ) := by
    calc x ^ (σ - σ') ≤ (1 + x) ^ (σ - σ') :=
          Real.rpow_le_rpow hx.le (by linarith) (by linarith)
      _ ≤ (1 + x) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hn
  have hsplit : x ^ (-σ') = x ^ (-σ) * x ^ (σ - σ') := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hsplit' : (1 + x) ^ (-((M + n : ℕ) : ℝ)) = (1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹ := by
    rw [← Real.rpow_neg h1x.le, ← Real.rpow_add h1x]; congr 1; push_cast; ring
  rw [hsplit, hsplit']
  have hpos : 0 < (1 + x) ^ (n : ℝ) := Real.rpow_pos_of_pos h1x _
  have hxσ : 0 ≤ x ^ (-σ) := (Real.rpow_pos_of_pos hx _).le
  have hM : 0 ≤ (1 + x) ^ (-(M : ℝ)) := (Real.rpow_pos_of_pos h1x _).le
  calc x ^ (-σ) * x ^ (σ - σ') * ((1 + x) ^ (-(M : ℝ)) * ((1 + x) ^ (n : ℝ))⁻¹)
      = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * (x ^ (σ - σ') / (1 + x) ^ (n : ℝ)) := by ring
    _ ≤ x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) * 1 := by
          gcongr
          exact (div_le_one hpos).mpr hpow
    _ = x ^ (-σ) * (1 + x) ^ (-(M : ℝ)) := mul_one _

private theorem le_profile_of_le_small {F x s B x₁ : ℝ} (hx : 0 < x) (hxx₁ : x ≤ x₁) (hB : 0 ≤ B) (M : ℕ)
    (h : F ≤ B * x ^ (-s)) :
    F ≤ B * (1 + x₁) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by
  have h1x : 0 < 1 + x := by linarith
  have h1x₁ : 0 < 1 + x₁ := by linarith
  have hxs : 0 ≤ x ^ (-s) := (Real.rpow_pos_of_pos hx _).le
  have hratio : 1 ≤ (1 + x₁) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg h1x.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos h1x _), one_mul]
    exact Real.rpow_le_rpow h1x.le (by linarith) (Nat.cast_nonneg M)
  calc F ≤ B * x ^ (-s) := h
    _ = B * x ^ (-s) * 1 := (mul_one _).symm
    _ ≤ B * x ^ (-s) * ((1 + x₁) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hB hxs)
    _ = B * (1 + x₁) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by ring

private theorem rpow_neg_add_le_large {x s : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    x ^ (-(s + M)) ≤ (2 : ℝ) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have h1x : 0 < 1 + x := by linarith
  have hsplit : x ^ (-(s + M)) = x ^ (-s) * x ^ (-(M : ℝ)) := by
    rw [← Real.rpow_add hx0]; congr 1; ring

  have hkey : x ^ (-(M : ℝ)) ≤ (2 : ℝ) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ)) := by
    have h2x : (1 + x) ^ (M : ℝ) ≤ (2 * x) ^ (M : ℝ) :=
      Real.rpow_le_rpow h1x.le (by linarith) (Nat.cast_nonneg M)
    rw [Real.mul_rpow (by norm_num) hx0.le] at h2x
    rw [Real.rpow_neg hx0.le, Real.rpow_neg h1x.le]
    have hxM : 0 < x ^ (M : ℝ) := Real.rpow_pos_of_pos hx0 _
    have h1xM : 0 < (1 + x) ^ (M : ℝ) := Real.rpow_pos_of_pos h1x _
    rw [← div_eq_mul_inv, le_div_iff₀ h1xM, inv_mul_eq_div, div_le_iff₀ hxM]
    linarith
  rw [hsplit]
  have hxs : 0 ≤ x ^ (-s) := (Real.rpow_pos_of_pos hx0 _).le
  calc x ^ (-s) * x ^ (-(M : ℝ)) ≤ x ^ (-s) * ((2 : ℝ) ^ (M : ℝ) * (1 + x) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey hxs
    _ = (2 : ℝ) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by ring

private theorem exists_profile_of_two_regime {σ p y₀ C₀ : ℝ} (C₁ : ℕ → ℝ) (hσ : 0 ≤ σ) (_hp : 0 ≤ p) (hy₀ : 0 < y₀)
    (M : ℕ) :
    ∃ A : ℝ, ∀ (F x Y : ℝ), 0 < x → y₀ ≤ Y →
      (x * Y ≤ 1 → F ≤ C₀ * Y ^ p * (x * Y) ^ (-σ)) →
      (∀ N : ℕ, 1 ≤ x * Y → F ≤ C₁ N * Y ^ p * (x * Y) ^ (-(N : ℝ))) →
      F ≤ A * x ^ (-(max σ p)) * (1 + x) ^ (-(M : ℝ)) := by
  set s : ℝ := max σ p with hs_def
  have hs : 0 ≤ s := le_trans hσ (le_max_left _ _)
  have hσs : σ ≤ s := le_max_left _ _
  have hps : p ≤ s := le_max_right _ _

  set n : ℕ := ⌈s⌉₊ with hn_def
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  set N₀ : ℕ := n + M with hN₀_def
  have hN₀ : s + M ≤ (N₀ : ℝ) := by simp only [hN₀_def, Nat.cast_add]; linarith

  set B₀ : ℝ := max C₀ 0 * (max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1) * (1 + y₀⁻¹) ^ (M : ℝ) with hB₀
  set B₂ : ℝ := max (C₁ N₀) 0 * (2 : ℝ) ^ (M : ℝ) * max (y₀ ^ (p - N₀ : ℝ)) 1 with hB₂
  set B₃ : ℝ := max (C₁ N₀) 0 * (2 : ℝ) ^ (M : ℝ) with hB₃
  refine ⟨max (max B₀ B₂) B₃, fun F x Y hx hY hsmall hlarge => ?_⟩
  have hY0 : 0 < Y := lt_of_lt_of_le hy₀ hY
  have hxY : 0 < x * Y := mul_pos hx hY0
  have hxs : 0 ≤ x ^ (-s) := (Real.rpow_pos_of_pos hx _).le
  have h1x : 0 < 1 + x := by linarith
  have h1xM : 0 ≤ (1 + x) ^ (-(M : ℝ)) := (Real.rpow_pos_of_pos h1x _).le
  have hprof : 0 ≤ x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := mul_nonneg hxs h1xM
  have hAB : ∀ {B : ℝ}, B ≤ max (max B₀ B₂) B₃ → F ≤ B * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) →
      F ≤ max (max B₀ B₂) B₃ * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by
    intro B hB h
    calc F ≤ B * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := h
      _ = B * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) := by ring
      _ ≤ max (max B₀ B₂) B₃ * (x ^ (-s) * (1 + x) ^ (-(M : ℝ))) :=
          mul_le_mul_of_nonneg_right hB hprof
      _ = max (max B₀ B₂) B₃ * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by ring
  have hy₀inv : 0 < y₀⁻¹ := inv_pos.mpr hy₀
  rcases le_or_gt (x * Y) 1 with hreg | hreg
  ·
    have hYx : Y ≤ x⁻¹ := by
      rw [← one_div, le_div_iff₀ hx, mul_comm]
      exact hreg
    have hxle : x ≤ y₀⁻¹ := (le_inv_comm₀ hx hy₀).mpr (hY.trans hYx)
    have hF := hsmall hreg

    have hrew : Y ^ p * (x * Y) ^ (-σ) = x ^ (-σ) * Y ^ (p - σ) := by
      rw [Real.mul_rpow hx.le hY0.le, Real.rpow_sub hY0, Real.rpow_neg hY0.le, div_eq_mul_inv]; ring

    have hcore : x ^ (-σ) * Y ^ (p - σ) ≤
        (max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1) * x ^ (-s) := by
      have hxσ : 0 < x ^ (-σ) := Real.rpow_pos_of_pos hx _
      have hxs' : 0 < x ^ (-s) := Real.rpow_pos_of_pos hx _

      have hxsplit : x ^ (-σ) = x ^ (-s) * x ^ (s - σ) := by
        rw [← Real.rpow_add hx]; congr 1; ring
      have hxsσ : x ^ (s - σ) ≤ max ((y₀⁻¹) ^ (s - σ)) 1 :=
        le_trans (Real.rpow_le_rpow hx.le hxle (by linarith)) (le_max_left _ _)
      rcases le_or_gt p σ with hpσ | hpσ
      ·
        have hYp : Y ^ (p - σ) ≤ max (y₀ ^ (p - σ)) 1 :=
          le_trans (Real.rpow_le_rpow_of_nonpos hy₀ hY (by linarith)) (le_max_left _ _)
        calc x ^ (-σ) * Y ^ (p - σ) = x ^ (-s) * (x ^ (s - σ) * Y ^ (p - σ)) := by rw [hxsplit]; ring
          _ ≤ x ^ (-s) * (max ((y₀⁻¹) ^ (s - σ)) 1 * max (y₀ ^ (p - σ)) 1) := by
              apply mul_le_mul_of_nonneg_left _ hxs'.le
              exact mul_le_mul hxsσ hYp (Real.rpow_pos_of_pos hY0 _).le (le_max_of_le_right zero_le_one)
          _ = (max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1) * x ^ (-s) := by ring
      ·
        have hsp : s = p := max_eq_right hpσ.le
        have hYp : Y ^ (p - σ) ≤ (x⁻¹) ^ (p - σ) := Real.rpow_le_rpow hY0.le hYx (by linarith)
        have hcomb : x ^ (-σ) * (x⁻¹) ^ (p - σ) = x ^ (-p) := by
          rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
          have hexp : -σ + -(p - σ) = -p := by ring
          rw [hexp]
        calc x ^ (-σ) * Y ^ (p - σ) ≤ x ^ (-σ) * (x⁻¹) ^ (p - σ) :=
              mul_le_mul_of_nonneg_left hYp hxσ.le
          _ = x ^ (-p) := hcomb
          _ = 1 * x ^ (-s) := by rw [hsp, one_mul]
          _ ≤ (max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1) * x ^ (-s) := by
              apply mul_le_mul_of_nonneg_right _ hxs
              exact one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _)
    have hK : 0 ≤ max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1 :=
      mul_nonneg (le_max_of_le_right zero_le_one) (le_max_of_le_right zero_le_one)
    have hstep : F ≤ (max C₀ 0 * (max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1)) * x ^ (-s) := by
      calc F ≤ C₀ * Y ^ p * (x * Y) ^ (-σ) := hF
        _ = C₀ * (x ^ (-σ) * Y ^ (p - σ)) := by rw [mul_assoc, hrew]
        _ ≤ max C₀ 0 * (x ^ (-σ) * Y ^ (p - σ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (mul_nonneg (Real.rpow_pos_of_pos hx _).le (Real.rpow_pos_of_pos hY0 _).le)
        _ ≤ max C₀ 0 * ((max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1) * x ^ (-s)) :=
            mul_le_mul_of_nonneg_left hcore (le_max_right _ _)
        _ = (max C₀ 0 * (max (y₀ ^ (p - σ)) 1 * max ((y₀⁻¹) ^ (s - σ)) 1)) * x ^ (-s) := by ring
    have hfin := le_profile_of_le_small hx hxle (mul_nonneg (le_max_right _ _) hK) M hstep
    exact hAB (le_trans (le_max_left B₀ B₂) (le_max_left _ _)) hfin
  ·
    have hF := hlarge N₀ hreg.le
    have hC : 0 ≤ max (C₁ N₀) 0 := le_max_right _ _

    have hrew : Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) = (x * Y) ^ (p - N₀) * x ^ (-p) := by
      have e1 : (x * Y) ^ (p - N₀) = x ^ p * Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) := by
        rw [sub_eq_add_neg, Real.rpow_add hxY, Real.mul_rpow hx.le hY0.le]
      have e2 : x ^ p * x ^ (-p) = 1 := by
        rw [Real.rpow_neg hx.le]
        exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hx _).ne'
      calc Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) = Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) * (x ^ p * x ^ (-p)) := by
            rw [e2, mul_one]
        _ = (x * Y) ^ (p - N₀) * x ^ (-p) := by rw [e1]; ring
    have hF' : F ≤ max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := by
      calc F ≤ C₁ N₀ * Y ^ p * (x * Y) ^ (-(N₀ : ℝ)) := hF
        _ = C₁ N₀ * (Y ^ p * (x * Y) ^ (-(N₀ : ℝ))) := by ring
        _ ≤ max (C₁ N₀) 0 * (Y ^ p * (x * Y) ^ (-(N₀ : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (mul_nonneg (Real.rpow_pos_of_pos hY0 _).le (Real.rpow_pos_of_pos hxY _).le)
        _ = max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := by rw [hrew]
    have hpN₀ : p - N₀ ≤ 0 := by linarith
    rcases le_or_gt x 1 with hx1 | hx1
    ·
      have h1 : (x * Y) ^ (p - N₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hreg.le hpN₀
      have h2 : x ^ (-p) ≤ x ^ (-s) := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
      have hstep : F ≤ max (C₁ N₀) 0 * x ^ (-s) := by
        calc F ≤ max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := hF'
          _ ≤ max (C₁ N₀) 0 * (1 * x ^ (-s)) := by
              apply mul_le_mul_of_nonneg_left _ hC
              exact mul_le_mul h1 h2 (Real.rpow_pos_of_pos hx _).le zero_le_one
          _ = max (C₁ N₀) 0 * x ^ (-s) := by ring
      have hfin := le_profile_of_le_small hx hx1 hC M hstep

      have h11 : (1 + (1 : ℝ)) = 2 := by norm_num
      rw [h11] at hfin
      exact hAB (le_max_right _ _) hfin
    ·

      have hxy₀ : 0 < x * y₀ := mul_pos hx hy₀
      have h1 : (x * Y) ^ (p - N₀) ≤ (x * y₀) ^ (p - N₀) :=
        Real.rpow_le_rpow_of_nonpos hxy₀ (by gcongr) hpN₀
      have hcomb : (x * y₀) ^ (p - N₀) * x ^ (-p) = y₀ ^ (p - N₀ : ℝ) * x ^ (-(N₀ : ℝ)) := by
        rw [Real.mul_rpow hx.le hy₀.le, mul_right_comm, ← Real.rpow_add hx]
        have hexp : p - N₀ + -p = -(N₀ : ℝ) := by ring
        rw [hexp, mul_comm]
      have hN : x ^ (-(N₀ : ℝ)) ≤ x ^ (-(s + M)) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have hlarge' := rpow_neg_add_le_large (s := s) hx1.le M
      have hy₀p : y₀ ^ (p - N₀ : ℝ) ≤ max (y₀ ^ (p - N₀ : ℝ)) 1 := le_max_left _ _
      have hy₀p0 : 0 ≤ y₀ ^ (p - N₀ : ℝ) := (Real.rpow_pos_of_pos hy₀ _).le
      have h2M : 0 ≤ (2 : ℝ) ^ (M : ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
      have hstep : F ≤ B₂ * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by
        calc F ≤ max (C₁ N₀) 0 * ((x * Y) ^ (p - N₀) * x ^ (-p)) := hF'
          _ ≤ max (C₁ N₀) 0 * ((x * y₀) ^ (p - N₀) * x ^ (-p)) := by
              apply mul_le_mul_of_nonneg_left _ hC
              exact mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hx _).le
          _ = max (C₁ N₀) 0 * (y₀ ^ (p - N₀ : ℝ) * x ^ (-(N₀ : ℝ))) := by rw [hcomb]
          _ ≤ max (C₁ N₀) 0 * (max (y₀ ^ (p - N₀ : ℝ)) 1 * ((2 : ℝ) ^ (M : ℝ) * x ^ (-s) * (1 + x) ^ (-(M : ℝ)))) := by
              apply mul_le_mul_of_nonneg_left _ hC
              exact mul_le_mul hy₀p (hN.trans hlarge') (Real.rpow_pos_of_pos hx _).le
                (le_max_of_le_right zero_le_one)
          _ = B₂ * x ^ (-s) * (1 + x) ^ (-(M : ℝ)) := by rw [hB₂]; ring
      exact hAB (le_trans (le_max_right B₀ B₂) (le_max_left _ _)) hstep

end ProfileArith

namespace ProfileArith

private theorem exists_rpow_le_mul_rpow {D₁ D₂ y₀ : ℝ} (hD₁ : 0 < D₁) (hy₀ : 0 < y₀) (q : ℝ) :
    ∃ B p : ℝ, 0 ≤ p ∧ ∀ r D y : ℝ, 0 < r → D₁ ≤ D → D ≤ D₂ → y₀ ≤ y → r ^ 2 = D / y →
      r ^ q ≤ B * y ^ p := by

  have hsplit : ∀ r D y : ℝ, 0 < r → 0 < D → 0 < y → r ^ 2 = D / y →
      r ^ q = D ^ (q / 2) * y ^ (-(q / 2)) := by
    intro r D y hr hD hy h
    have h1 : r ^ q = (r ^ (2 : ℝ)) ^ (q / 2) := by
      rw [← Real.rpow_mul hr.le]; congr 1; ring
    rw [h1, Real.rpow_two, h, Real.div_rpow hD.le hy.le, Real.rpow_neg hy.le, div_eq_mul_inv]
  rcases le_or_gt 0 q with hq | hq
  ·
    refine ⟨D₂ ^ (q / 2) * y₀ ^ (-(q / 2)), 0, le_rfl, fun r D y hr hD₁D hDD₂ hy₀y h => ?_⟩
    have hD : 0 < D := lt_of_lt_of_le hD₁ hD₁D
    have hy : 0 < y := lt_of_lt_of_le hy₀ hy₀y
    rw [hsplit r D y hr hD hy h, Real.rpow_zero, mul_one]
    have hDle : D ^ (q / 2) ≤ D₂ ^ (q / 2) := Real.rpow_le_rpow hD.le hDD₂ (by linarith)
    have hyle : y ^ (-(q / 2)) ≤ y₀ ^ (-(q / 2)) := Real.rpow_le_rpow_of_nonpos hy₀ hy₀y (by linarith)
    have hD₂ : 0 < D₂ := lt_of_lt_of_le hD (hDD₂)
    exact mul_le_mul hDle hyle (Real.rpow_pos_of_pos hy _).le (Real.rpow_pos_of_pos hD₂ _).le
  ·
    refine ⟨D₁ ^ (q / 2), -(q / 2), by linarith, fun r D y hr hD₁D hDD₂ hy₀y h => ?_⟩
    have hD : 0 < D := lt_of_lt_of_le hD₁ hD₁D
    have hy : 0 < y := lt_of_lt_of_le hy₀ hy₀y
    rw [hsplit r D y hr hD hy h]
    have hDle : D ^ (q / 2) ≤ D₁ ^ (q / 2) := Real.rpow_le_rpow_of_nonpos hD₁ hD₁D (by linarith)
    exact mul_le_mul_of_nonneg_right hDle (Real.rpow_pos_of_pos hy _).le

end ProfileArith

namespace ArchIwasawa

namespace Real

private theorem abs_yOf_mul_ge (m x : Matrix (Fin 2) (Fin 2) ℝ) (hm : m.det ≠ 0) (hx : x.det ≠ 0) :
    |yOf m| * (|x.det| / (x 0 0 ^ 2 + x 0 1 ^ 2 + x 1 0 ^ 2 + x 1 1 ^ 2)) ≤ |yOf (m * x)| := by
  have hmx : (m * x).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hm hx
  have hX : 0 < x 0 0 ^ 2 + x 0 1 ^ 2 + x 1 0 ^ 2 + x 1 1 ^ 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h00 : x 0 0 = 0 := by nlinarith [sq_nonneg (x 0 0), sq_nonneg (x 0 1), sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    have h10 : x 1 0 = 0 := by nlinarith [sq_nonneg (x 0 0), sq_nonneg (x 0 1), sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
    apply hx
    rw [Matrix.det_fin_two, h00, h10]
    ring
  have hA : 0 < rowNorm m ^ 2 := pow_pos (rowNorm_pos hm) 2
  have hR : 0 < rowNorm (m * x) ^ 2 := pow_pos (rowNorm_pos hmx) 2

  have e10 : (m * x) 1 0 = m 1 0 * x 0 0 + m 1 1 * x 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (m * x) 1 1 = m 1 0 * x 0 1 + m 1 1 * x 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]

  have hCS : rowNorm (m * x) ^ 2 ≤ rowNorm m ^ 2 * (x 0 0 ^ 2 + x 0 1 ^ 2 + x 1 0 ^ 2 + x 1 1 ^ 2) := by
    rw [rowNorm_sq, rowNorm_sq, e10, e11]
    nlinarith [sq_nonneg (m 1 0 * x 1 0 - m 1 1 * x 0 0), sq_nonneg (m 1 0 * x 1 1 - m 1 1 * x 0 1),
      sq_nonneg (m 1 0 * x 0 0 + m 1 1 * x 1 0), sq_nonneg (m 1 0 * x 0 1 + m 1 1 * x 1 1),
      sq_nonneg (m 1 0), sq_nonneg (m 1 1), sq_nonneg (x 0 0), sq_nonneg (x 0 1), sq_nonneg (x 1 0), sq_nonneg (x 1 1)]
  rw [abs_yOf, abs_yOf, Matrix.det_mul, abs_mul, div_mul_div_comm]
  have hnum : 0 ≤ |m.det| * |x.det| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact div_le_div_of_nonneg_left hnum hR hCS

end Real

namespace Complex

private theorem norm_yOf_mul_ge (m x : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.det ≠ 0) (hx : x.det ≠ 0) :
    ‖yOf m‖ * (‖x.det‖ / (‖x 0 0‖ ^ 2 + ‖x 0 1‖ ^ 2 + ‖x 1 0‖ ^ 2 + ‖x 1 1‖ ^ 2)) ≤ ‖yOf (m * x)‖ := by
  have hmx : (m * x).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hm hx
  have hX : 0 < ‖x 0 0‖ ^ 2 + ‖x 0 1‖ ^ 2 + ‖x 1 0‖ ^ 2 + ‖x 1 1‖ ^ 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h00 : x 0 0 = 0 := by
      rw [← norm_eq_zero]
      nlinarith [norm_nonneg (x 0 0), norm_nonneg (x 0 1), norm_nonneg (x 1 0), norm_nonneg (x 1 1),
        sq_nonneg ‖x 0 0‖, sq_nonneg ‖x 0 1‖, sq_nonneg ‖x 1 0‖, sq_nonneg ‖x 1 1‖]
    have h10 : x 1 0 = 0 := by
      rw [← norm_eq_zero]
      nlinarith [norm_nonneg (x 0 0), norm_nonneg (x 0 1), norm_nonneg (x 1 0), norm_nonneg (x 1 1),
        sq_nonneg ‖x 0 0‖, sq_nonneg ‖x 0 1‖, sq_nonneg ‖x 1 0‖, sq_nonneg ‖x 1 1‖]
    apply hx
    rw [Matrix.det_fin_two, h00, h10]
    ring
  have hR : 0 < rowNorm (m * x) ^ 2 := pow_pos (rowNorm_pos hmx) 2
  have e10 : (m * x) 1 0 = m 1 0 * x 0 0 + m 1 1 * x 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (m * x) 1 1 = m 1 0 * x 0 1 + m 1 1 * x 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]

  have hcs : ∀ a b p q : ℂ, ‖a * p + b * q‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
    intro a b p q
    have h1 : ‖a * p + b * q‖ ≤ ‖a‖ * ‖p‖ + ‖b‖ * ‖q‖ := by
      calc ‖a * p + b * q‖ ≤ ‖a * p‖ + ‖b * q‖ := norm_add_le _ _
        _ = ‖a‖ * ‖p‖ + ‖b‖ * ‖q‖ := by rw [norm_mul, norm_mul]
    have h0 : 0 ≤ ‖a‖ * ‖p‖ + ‖b‖ * ‖q‖ := by positivity
    calc ‖a * p + b * q‖ ^ 2 ≤ (‖a‖ * ‖p‖ + ‖b‖ * ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
          nlinarith [sq_nonneg (‖a‖ * ‖q‖ - ‖b‖ * ‖p‖), h0]
  have hCS : rowNorm (m * x) ^ 2 ≤ rowNorm m ^ 2 * (‖x 0 0‖ ^ 2 + ‖x 0 1‖ ^ 2 + ‖x 1 0‖ ^ 2 + ‖x 1 1‖ ^ 2) := by
    rw [rowNorm_sq, rowNorm_sq, e10, e11]
    have c1 := hcs (m 1 0) (m 1 1) (x 0 0) (x 1 0)
    have c2 := hcs (m 1 0) (m 1 1) (x 0 1) (x 1 1)
    nlinarith [c1, c2, sq_nonneg ‖m 1 0‖, sq_nonneg ‖m 1 1‖]
  rw [norm_yOf, norm_yOf, Matrix.det_mul, norm_mul, div_mul_div_comm]
  have hnum : 0 ≤ ‖m.det‖ * ‖x.det‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  exact div_le_div_of_nonneg_left hnum hR hCS

end Complex

end ArchIwasawa

namespace ArchIwasawa

namespace Real

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Real.exists_profile_bound_on (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (ψ : ℝ → ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (χ : ℝ → ℂ)
    (hunip : ∀ (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), W (!![1, x; 0, 1] * g) = ψ x * W g)
    (hcent : ∀ (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), 0 < z → W (z • g) = χ z * W g)
    (hzero : ∃ C σ : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
      y ≠ 0 → |y| ≤ 1 → ‖W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-σ))
    (htop : ∀ N : ℕ, ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
      1 ≤ |y| → ‖W (!![y, 0; 0, 1] * k)‖ ≤ C * |y| ^ (-(N : ℝ)))
    (Sm : Set (Matrix (Fin 2) (Fin 2) ℝ)) (hdet : ∀ g ∈ Sm, g.det ≠ 0)
    (B p : ℝ) (hχB : ∀ g ∈ Sm, ‖χ (rowNorm g)‖ ≤ B * |yOf g| ^ p) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ Sm, ∀ t : ℝ, t ≠ 0 →
      (|t| * |yOf g| ≤ 1 → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₀ * |yOf g| ^ p * (|t| * |yOf g|) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ |t| * |yOf g| → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₁ N * |yOf g| ^ p * (|t| * |yOf g|) ^ (-(N : ℝ))) := by
  obtain ⟨Cz, σz, hz⟩ := hzero
  choose Ct ht using htop
  have hB' : ∀ g ∈ Sm, ‖χ (rowNorm g)‖ ≤ max B 0 * |yOf g| ^ p := fun g hg =>
    (hχB g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  have key : ∀ g ∈ Sm, ∀ t : ℝ,
      ‖W (!![t, 0; 0, 1] * g)‖ = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := by
    intro g hg t
    rw [diagOne_mul_eq (hdet g hg) t, hunip, hcent _ _ (rowNorm_pos (hdet g hg)), norm_mul, norm_mul, hψ, one_mul]
  refine ⟨max σz 0, max B 0 * max Cz 0, fun N => max B 0 * max (Ct N) 0, le_max_right _ _, ?_⟩
  intro g hg t ht0
  have hy0 : t * yOf g ≠ 0 := mul_ne_zero ht0 (yOf_ne_zero (hdet g hg))
  have hs : |t * yOf g| = |t| * |yOf g| := abs_mul t (yOf g)
  have hspos : 0 < |t| * |yOf g| := by rw [← hs]; exact abs_pos.mpr hy0
  have hk := kOf_mem (hdet g hg)
  constructor
  · intro hs1
    have h1 := hz (t * yOf g) (kOf g) hk hy0 (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * |yOf g| ^ p * (max Cz 0 * (|t| * |yOf g|) ^ (-(max σz 0))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Cz * (|t| * |yOf g|) ^ (-σz) := h1
            _ ≤ max Cz 0 * (|t| * |yOf g|) ^ (-σz) := by
                gcongr; exact le_max_left _ _
            _ ≤ max Cz 0 * (|t| * |yOf g|) ^ (-(max σz 0)) :=
                mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg_max hspos hs1) (le_max_right _ _)
      _ = max B 0 * max Cz 0 * |yOf g| ^ p * (|t| * |yOf g|) ^ (-(max σz 0)) := by ring
  · intro N hs1
    have h1 := ht N (t * yOf g) (kOf g) hk (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ (rowNorm g)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * |yOf g| ^ p * (max (Ct N) 0 * (|t| * |yOf g|) ^ (-(N : ℝ))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Ct N * (|t| * |yOf g|) ^ (-(N : ℝ)) := h1
            _ ≤ max (Ct N) 0 * (|t| * |yOf g|) ^ (-(N : ℝ)) := by
                gcongr; exact le_max_left _ _
      _ = max B 0 * max (Ct N) 0 * |yOf g| ^ p * (|t| * |yOf g|) ^ (-(N : ℝ)) := by ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Real" "exists_profile_bound_on"
end Real

namespace Complex

private theorem _root_.LanglandsTunnell.Converse.ArchIwasawa.Complex.exists_profile_bound_on (W : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (ψ : ℂ → ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (χ : ℂ → ℂ)
    (hunip : ∀ (x : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), W (!![1, x; 0, 1] * g) = ψ x * W g)
    (hcent : ∀ (z : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ), z ≠ 0 → W (z • g) = χ z * W g)
    (hzero : ∃ C σ : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      z ≠ 0 → ‖z‖ ≤ 1 → ‖W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-σ))
    (htop : ∀ N : ℕ, ∃ C : ℝ, ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      1 ≤ ‖z‖ → ‖W (!![z, 0; 0, 1] * k)‖ ≤ C * ‖z‖ ^ (-(N : ℝ)))
    (Sm : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hdet : ∀ g ∈ Sm, g.det ≠ 0)
    (B p : ℝ) (hχB : ∀ g ∈ Sm, ‖χ ((rowNorm g : ℝ) : ℂ)‖ ≤ B * ‖yOf g‖ ^ p) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ Sm, ∀ t : ℂ, t ≠ 0 →
      (‖t‖ * ‖yOf g‖ ≤ 1 → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₀ * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ ‖t‖ * ‖yOf g‖ → ‖W (!![t, 0; 0, 1] * g)‖ ≤ C₁ N * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ))) := by
  obtain ⟨Cz, σz, hz⟩ := hzero
  choose Ct ht using htop
  have hB' : ∀ g ∈ Sm, ‖χ ((rowNorm g : ℝ) : ℂ)‖ ≤ max B 0 * ‖yOf g‖ ^ p := fun g hg =>
    (hχB g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  have key : ∀ g ∈ Sm, ∀ t : ℂ,
      ‖W (!![t, 0; 0, 1] * g)‖ = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := by
    intro g hg t
    rw [diagOne_mul_eq (hdet g hg) t, hunip, hcent _ _ (Complex.ofReal_ne_zero.mpr (rowNorm_ne_zero (hdet g hg))),
      norm_mul, norm_mul, hψ, one_mul]
  refine ⟨max σz 0, max B 0 * max Cz 0, fun N => max B 0 * max (Ct N) 0, le_max_right _ _, ?_⟩
  intro g hg t ht0
  have hy0 : t * yOf g ≠ 0 := mul_ne_zero ht0 (yOf_ne_zero (hdet g hg))
  have hs : ‖t * yOf g‖ = ‖t‖ * ‖yOf g‖ := norm_mul t (yOf g)
  have hspos : 0 < ‖t‖ * ‖yOf g‖ := by rw [← hs]; exact norm_pos_iff.mpr hy0
  have hk := kOf_mem (hdet g hg)
  constructor
  · intro hs1
    have h1 := hz (t * yOf g) (kOf g) hk hy0 (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * ‖yOf g‖ ^ p * (max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Cz * (‖t‖ * ‖yOf g‖) ^ (-σz) := h1
            _ ≤ max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-σz) := by
                gcongr; exact le_max_left _ _
            _ ≤ max Cz 0 * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0)) :=
                mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg_max hspos hs1) (le_max_right _ _)
      _ = max B 0 * max Cz 0 * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-(max σz 0)) := by ring
  · intro N hs1
    have h1 := ht N (t * yOf g) (kOf g) hk (by rw [hs]; exact hs1)
    rw [hs] at h1
    calc ‖W (!![t, 0; 0, 1] * g)‖
        = ‖χ ((rowNorm g : ℝ) : ℂ)‖ * ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ := key g hg t
      _ ≤ max B 0 * ‖yOf g‖ ^ p * (max (Ct N) 0 * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ))) := by
          apply mul_le_mul (hB' g hg) _ (norm_nonneg _)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
          calc ‖W (!![t * yOf g, 0; 0, 1] * kOf g)‖ ≤ Ct N * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := h1
            _ ≤ max (Ct N) 0 * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := by
                gcongr; exact le_max_left _ _
      _ = max B 0 * max (Ct N) 0 * ‖yOf g‖ ^ p * (‖t‖ * ‖yOf g‖) ^ (-(N : ℝ)) := by ring

p2m_export "LanglandsTunnell.Converse.ArchIwasawa.Complex" "exists_profile_bound_on"
end Complex

end ArchIwasawa

end SiegelArithmetic

end LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

section ArchProfileBounds
open Matrix

namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.two_regime_on {P : RealArchParam} (D : ArchDatumR P) {Sm : Set (Matrix (Fin 2) (Fin 2) ℝ)}
    (hdet : ∀ g ∈ Sm, g.det ≠ 0) (B p : ℝ)
    (hχB : ∀ g ∈ Sm, ‖ArchR.centralChar P (ArchIwasawa.Real.rowNorm g) * ((|ArchIwasawa.Real.rowNorm g| : ℝ) : ℂ)‖
      ≤ B * |ArchIwasawa.Real.yOf g| ^ p) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ Sm, ∀ t : ℝ, t ≠ 0 →
      (|t| * |ArchIwasawa.Real.yOf g| ≤ 1 →
        ‖D.W (ArchR.diagOne t * g)‖
          ≤ C₀ * |ArchIwasawa.Real.yOf g| ^ p * (|t| * |ArchIwasawa.Real.yOf g|) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ |t| * |ArchIwasawa.Real.yOf g| →
        ‖D.W (ArchR.diagOne t * g)‖
          ≤ C₁ N * |ArchIwasawa.Real.yOf g| ^ p * (|t| * |ArchIwasawa.Real.yOf g|) ^ (-(N : ℝ))) :=
  ArchIwasawa.Real.exists_profile_bound_on D.W ArchR.psi norm_psi (fun z => ArchR.centralChar P z * ((|z| : ℝ) : ℂ))
    D.unip_law (fun z g hz => D.central_law z g hz.ne') D.zero_bound D.top_bound Sm hdet B p hχB

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.two_regime_on"
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in
private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.two_regime_on {P : ComplexArchParam} (D : ArchDatumC P)
    {Sm : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hdet : ∀ g ∈ Sm, g.det ≠ 0) (B p : ℝ)
    (hχB : ∀ g ∈ Sm, ‖ArchC.centralChar P ((ArchIwasawa.Complex.rowNorm g : ℝ) : ℂ)
        * ((‖((ArchIwasawa.Complex.rowNorm g : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)‖
      ≤ B * ‖ArchIwasawa.Complex.yOf g‖ ^ p) :
    ∃ (σ C₀ : ℝ) (C₁ : ℕ → ℝ), 0 ≤ σ ∧ ∀ g ∈ Sm, ∀ t : ℂ, t ≠ 0 →
      (‖t‖ * ‖ArchIwasawa.Complex.yOf g‖ ≤ 1 →
        ‖D.W (ArchC.diagOne t * g)‖
          ≤ C₀ * ‖ArchIwasawa.Complex.yOf g‖ ^ p * (‖t‖ * ‖ArchIwasawa.Complex.yOf g‖) ^ (-σ)) ∧
      (∀ N : ℕ, 1 ≤ ‖t‖ * ‖ArchIwasawa.Complex.yOf g‖ →
        ‖D.W (ArchC.diagOne t * g)‖
          ≤ C₁ N * ‖ArchIwasawa.Complex.yOf g‖ ^ p * (‖t‖ * ‖ArchIwasawa.Complex.yOf g‖) ^ (-(N : ℝ))) :=
  ArchIwasawa.Complex.exists_profile_bound_on D.W ArchC.psi norm_psiC
    (fun z => ArchC.centralChar P z * ((‖z‖ ^ 2 : ℝ) : ℂ)) D.unip_law D.central_law D.zero_bound D.top_bound
    Sm hdet B p hχB

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.two_regime_on"
namespace ArchDatumR
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumR" in

private theorem _root_.LanglandsTunnell.Converse.ArchDatumR.exists_profile_bound_on {P : RealArchParam} (D : ArchDatumR P)
    {Sm : Set (Matrix (Fin 2) (Fin 2) ℝ)} (hdet : ∀ g ∈ Sm, g.det ≠ 0) {D₁ D₂ y₀ : ℝ} (hD₁ : 0 < D₁) (hy₀ : 0 < y₀)
    (hwin : ∀ g ∈ Sm, D₁ ≤ |g.det| ∧ |g.det| ≤ D₂) (hfloor : ∀ g ∈ Sm, y₀ ≤ |ArchIwasawa.Real.yOf g|) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ A : ℝ, ∀ g ∈ Sm, ∀ y : ℝ, y ≠ 0 →
      ‖D.W (ArchR.diagOne y * g)‖ ≤ A * |y| ^ (-σ) * (1 + |y|) ^ (-(M : ℝ)) := by
  obtain ⟨Bχ, p, hp, hBχ⟩ := ProfileArith.exists_rpow_le_mul_rpow hD₁ hy₀ (P.centralExponent.re + 1)
  have hχB : ∀ g ∈ Sm,
      ‖ArchR.centralChar P (ArchIwasawa.Real.rowNorm g) * ((|ArchIwasawa.Real.rowNorm g| : ℝ) : ℂ)‖
        ≤ Bχ * |ArchIwasawa.Real.yOf g| ^ p := by
    intro g hg
    have hr := ArchIwasawa.Real.rowNorm_pos (hdet g hg)
    rw [norm_centralChar_mul hr, ← Real.rpow_add_one hr.ne']
    refine hBχ _ _ _ hr (hwin g hg).1 (hwin g hg).2 (hfloor g hg) ?_
    have hd : |g.det| ≠ 0 := abs_ne_zero.mpr (hdet g hg)
    rw [ArchIwasawa.Real.abs_yOf, div_div_eq_mul_div, mul_div_cancel_left₀ _ hd]
  obtain ⟨σ, C₀, C₁, hσ, hreg⟩ := D.two_regime_on hdet Bχ p hχB
  refine ⟨max σ p, le_max_of_le_left hσ, fun M => ?_⟩
  obtain ⟨A, hA⟩ := ProfileArith.exists_profile_of_two_regime (σ := σ) (p := p) (y₀ := y₀) (C₀ := C₀) C₁ hσ hp hy₀ M
  refine ⟨A, fun g hg y hy => ?_⟩
  obtain ⟨hlow, hhigh⟩ := hreg g hg y hy
  exact hA _ _ _ (abs_pos.mpr hy) (hfloor g hg) hlow hhigh

end ArchDatumR
p2m_export "LanglandsTunnell.Converse" "ArchDatumR.exists_profile_bound_on"
namespace ArchDatumC
p2m_open_scoped "LanglandsTunnell.Converse.ArchDatumC" in

private theorem _root_.LanglandsTunnell.Converse.ArchDatumC.exists_profile_bound_on {P : ComplexArchParam} (D : ArchDatumC P)
    {Sm : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hdet : ∀ g ∈ Sm, g.det ≠ 0) {D₁ D₂ y₀ : ℝ} (hD₁ : 0 < D₁) (hy₀ : 0 < y₀)
    (hwin : ∀ g ∈ Sm, D₁ ≤ ‖g.det‖ ∧ ‖g.det‖ ≤ D₂) (hfloor : ∀ g ∈ Sm, y₀ ≤ ‖ArchIwasawa.Complex.yOf g‖) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ A : ℝ, ∀ g ∈ Sm, ∀ z : ℂ, z ≠ 0 →
      ‖D.W (ArchC.diagOne z * g)‖ ≤ A * ‖z‖ ^ (-σ) * (1 + ‖z‖) ^ (-(M : ℝ)) := by
  obtain ⟨Bχ, p, hp, hBχ⟩ := ProfileArith.exists_rpow_le_mul_rpow hD₁ hy₀ ((2 * P.centralExponent).re + 2)
  have hχB : ∀ g ∈ Sm,
      ‖ArchC.centralChar P ((ArchIwasawa.Complex.rowNorm g : ℝ) : ℂ)
          * ((‖((ArchIwasawa.Complex.rowNorm g : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)‖
        ≤ Bχ * ‖ArchIwasawa.Complex.yOf g‖ ^ p := by
    intro g hg
    have hr := ArchIwasawa.Complex.rowNorm_pos (hdet g hg)
    rw [norm_centralCharC_mul hr, ← Real.rpow_two, ← Real.rpow_add hr]
    refine hBχ _ _ _ hr (hwin g hg).1 (hwin g hg).2 (hfloor g hg) ?_
    have hd : ‖g.det‖ ≠ 0 := norm_ne_zero_iff.mpr (hdet g hg)
    rw [ArchIwasawa.Complex.norm_yOf, div_div_eq_mul_div, mul_div_cancel_left₀ _ hd]
  obtain ⟨σ, C₀, C₁, hσ, hreg⟩ := D.two_regime_on hdet Bχ p hχB
  refine ⟨max σ p, le_max_of_le_left hσ, fun M => ?_⟩
  obtain ⟨A, hA⟩ := ProfileArith.exists_profile_of_two_regime (σ := σ) (p := p) (y₀ := y₀) (C₀ := C₀) C₁ hσ hp hy₀ M
  refine ⟨A, fun g hg z hz => ?_⟩
  obtain ⟨hlow, hhigh⟩ := hreg g hg z hz
  exact hA _ _ _ (norm_pos_iff.mpr hz) (hfloor g hg) hlow hhigh

end ArchDatumC
p2m_export "LanglandsTunnell.Converse" "ArchDatumC.exists_profile_bound_on"

private theorem exists_profile_of_forall_mem {ι X J : Type*} [Fintype ι] (F : ι → X → J → ℂ) (x : ι → J → ℝ)
    (hx : ∀ i b, 0 < x i b) (D : Set X)
    (h : ∀ i, ∃ σ : ℝ, 0 ≤ σ ∧ ∀ N : ℕ, ∃ A : ℝ, ∀ g ∈ D, ∀ b, ‖F i g b‖ ≤ A * ((x i b) ^ (-σ) * (1 + x i b) ^ (-(N :
        ℝ)))) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ A : ℝ, ∀ g ∈ D, ∀ b,
      ‖∏ i, F i g b‖ ≤ A * (∏ i, (x i b) ^ (-σ)) * ∏ i, (1 + x i b) ^ (-(M : ℝ)) := by
  choose σ hσ hA using h
  choose A hAle using hA
  set σtot : ℝ := ∑ i, σ i with hσtot
  have hσtot_nonneg : 0 ≤ σtot := Finset.sum_nonneg fun i _ => hσ i
  refine ⟨σtot, hσtot_nonneg, fun M => ?_⟩
  set n : ℕ := ⌈σtot⌉₊ with hn
  refine ⟨∏ i, max (A i (M + n)) 0, fun g hg b => ?_⟩
  refine norm_prod_le_of_forall_le (fun i => F i g b) (fun i => max (A i (M + n)) 0) (fun i => x i b) σtot M
    fun i => ?_
  have hσi : σ i ≤ σtot := Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)
  have hgap : σtot - σ i ≤ (n : ℝ) := by
    have := Nat.le_ceil σtot
    linarith [hσ i]
  have hnonneg : 0 ≤ x i b ^ (-σ i) * (1 + x i b) ^ (-((M + n : ℕ) : ℝ)) :=
    mul_nonneg (Real.rpow_pos_of_pos (hx i b) _).le (Real.rpow_pos_of_pos (by linarith [hx i b]) _).le
  calc ‖F i g b‖ ≤ A i (M + n) * (x i b ^ (-σ i) * (1 + x i b) ^ (-((M + n : ℕ) : ℝ))) :=
        hAle i (M + n) g hg b
    _ ≤ max (A i (M + n)) 0 * (x i b ^ (-σ i) * (1 + x i b) ^ (-((M + n : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg
    _ ≤ max (A i (M + n)) 0 * (x i b ^ (-σtot) * (1 + x i b) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left (rpow_neg_mul_le_of_le (hx i b) hσi hgap M) (le_max_right _ _)

end ArchProfileBounds

end LanglandsTunnell.Converse

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_zero TateLocal.charExt_of_ne_zero RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchR.diagOne ArchR.psi ArchR.glSet ArchR.asPi ArchR.diagOneMulCoords ArchR.quasiChar ArchR.centralChar ArchDatumR ArchC.diagOne ArchC.psi ArchC.glSet ArchC.asPi ArchC.diagOneMulCoords ArchC.quasiChar ArchC.centralChar ArchDatumC FinWhittakerDatum whittakerSeries componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm localOf IsOneMod JLData IsJLNice IsAdmissibleTwist twistedDatum FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le exists_archParams_of_continuous exists_isJLTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet archNormFactor archW' jlSeries'"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicVolume
open scoped Classical
variable {K : Type} [Field K] [NumberField K]

section SiegelBound

private theorem realComponent_mul (w : InfinitePlace K) (hw : w.IsReal) (s x : AdelicGL2 (𝓞 K) K) :
    realComponent w hw (s * x) = realComponent w hw s * realComponent w hw x := by
  rw [realComponent_eq_map, realComponent_eq_map, realComponent_eq_map, map_mul, map_mul, Units.val_mul,
    ← RingEquiv.coe_toRingHom, Matrix.map_mul]

private theorem complexComponent_mul (w : InfinitePlace K) (hw : w.IsComplex) (s x : AdelicGL2 (𝓞 K) K) :
    complexComponent w hw (s * x) = complexComponent w hw s * complexComponent w hw x := by
  rw [complexComponent_eq_map, complexComponent_eq_map, complexComponent_eq_map, map_mul, map_mul, Units.val_mul,
    ← RingEquiv.coe_toRingHom, Matrix.map_mul]

private theorem norm_ringEquivReal (w : InfinitePlace K) (hw : w.IsReal) (z : w.Completion) :
    ‖ringEquivRealOfIsReal hw z‖ = ‖z‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) z

private theorem norm_ringEquivComplex (w : InfinitePlace K) (hw : w.IsComplex) (z : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw z‖ = ‖z‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) z

private theorem abs_det_realComponent (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    |(realComponent w hw g).det| = archDetNorm w g := by
  rw [realComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    RingEquiv.coe_toRingHom, ← Real.norm_eq_abs, norm_ringEquivReal, archDetNorm]

private theorem norm_det_complexComponent (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    ‖(complexComponent w hw g).det‖ = archDetNorm w g := by
  rw [complexComponent_eq_map, ← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    RingEquiv.coe_toRingHom, norm_ringEquivComplex, archDetNorm]

private theorem abs_yOf_realComponent (w : InfinitePlace K) (hw : w.IsReal) (g : AdelicGL2 (𝓞 K) K) :
    |ArchIwasawa.Real.yOf (realComponent w hw g)| = localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [ArchIwasawa.Real.abs_yOf, ArchIwasawa.Real.rowNorm_sq, abs_det_realComponent, archDetNorm, localHeight,
      rowNormSq,
    realComponent_eq_map, Matrix.map_apply, Matrix.map_apply,
    ← sq_abs (ringEquivRealOfIsReal hw _), ← sq_abs (ringEquivRealOfIsReal hw _), ← Real.norm_eq_abs,
    ← Real.norm_eq_abs, norm_ringEquivReal, norm_ringEquivReal]

private theorem norm_yOf_complexComponent (w : InfinitePlace K) (hw : w.IsComplex) (g : AdelicGL2 (𝓞 K) K) :
    ‖ArchIwasawa.Complex.yOf (complexComponent w hw g)‖ = localHeight (archComponent K w (glArch (𝓞 K) K g)) := by
  rw [ArchIwasawa.Complex.norm_yOf, ArchIwasawa.Complex.rowNorm_sq, norm_det_complexComponent, archDetNorm,
      localHeight,
    rowNormSq, complexComponent_eq_map, Matrix.map_apply, Matrix.map_apply, norm_ringEquivComplex,
        norm_ringEquivComplex]

private theorem exists_siegel_bounds_real (w : InfinitePlace K) (hw : w.IsReal) {c u d₁ d₂ : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) (x : AdelicGL2 (𝓞 K) K) :
    ∃ D₁ D₂ y₀ : ℝ, 0 < D₁ ∧ 0 < y₀ ∧ ∀ s ∈ centreCutSiegelSet K c u d₁ d₂,
      (D₁ ≤ |(realComponent w hw (s * x)).det| ∧ |(realComponent w hw (s * x)).det| ≤ D₂) ∧
      y₀ ≤ |ArchIwasawa.Real.yOf (realComponent w hw (s * x))| := by
  set rx := realComponent w hw x with hrx
  have hdx : rx.det ≠ 0 := det_realComponent_ne_zero w hw x
  have hX : 0 < rx 0 0 ^ 2 + rx 0 1 ^ 2 + rx 1 0 ^ 2 + rx 1 1 ^ 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h00 : rx 0 0 = 0 := by nlinarith [sq_nonneg (rx 0 0), sq_nonneg (rx 0 1), sq_nonneg (rx 1 0), sq_nonneg (rx 1
        1)]
    have h01 : rx 0 1 = 0 := by nlinarith [sq_nonneg (rx 0 0), sq_nonneg (rx 0 1), sq_nonneg (rx 1 0), sq_nonneg (rx 1
        1)]
    have h10 : rx 1 0 = 0 := by nlinarith [sq_nonneg (rx 0 0), sq_nonneg (rx 0 1), sq_nonneg (rx 1 0), sq_nonneg (rx 1
        1)]
    have h11 : rx 1 1 = 0 := by nlinarith [sq_nonneg (rx 0 0), sq_nonneg (rx 0 1), sq_nonneg (rx 1 0), sq_nonneg (rx 1
        1)]
    exact hdx (by rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring)
  have hκ : 0 < |rx.det| / (rx 0 0 ^ 2 + rx 0 1 ^ 2 + rx 1 0 ^ 2 + rx 1 1 ^ 2) :=
    div_pos (abs_pos.mpr hdx) hX
  refine ⟨d₁ * |rx.det|, d₂ * |rx.det|, c * (|rx.det| / (rx 0 0 ^ 2 + rx 0 1 ^ 2 + rx 1 0 ^ 2 + rx 1 1 ^ 2)),
    mul_pos hd₁ (abs_pos.mpr hdx), mul_pos hc hκ, fun s hs => ?_⟩
  obtain ⟨-, hheight, -, hdet⟩ := mem_centreCutSiegelSet_iff.mp hs
  have hdet_s : archDetNorm w s ∈ Set.Icc d₁ d₂ := hdet w
  have hsplit : |(realComponent w hw (s * x)).det| = archDetNorm w s * |rx.det| := by
    rw [realComponent_mul, Matrix.det_mul, abs_mul, abs_det_realComponent]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hsplit]; exact mul_le_mul_of_nonneg_right hdet_s.1 (abs_nonneg _)
  · rw [hsplit]; exact mul_le_mul_of_nonneg_right hdet_s.2 (abs_nonneg _)
  · rw [realComponent_mul]
    refine le_trans ?_ (ArchIwasawa.Real.abs_yOf_mul_ge _ _ (det_realComponent_ne_zero w hw s) hdx)
    rw [abs_yOf_realComponent]
    exact mul_le_mul_of_nonneg_right (hheight w) hκ.le

private theorem exists_siegel_bounds_complex (w : InfinitePlace K) (hw : w.IsComplex) {c u d₁ d₂ : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) (x : AdelicGL2 (𝓞 K) K) :
    ∃ D₁ D₂ y₀ : ℝ, 0 < D₁ ∧ 0 < y₀ ∧ ∀ s ∈ centreCutSiegelSet K c u d₁ d₂,
      (D₁ ≤ ‖(complexComponent w hw (s * x)).det‖ ∧ ‖(complexComponent w hw (s * x)).det‖ ≤ D₂) ∧
      y₀ ≤ ‖ArchIwasawa.Complex.yOf (complexComponent w hw (s * x))‖ := by
  set rx := complexComponent w hw x with hrx
  have hdx : rx.det ≠ 0 := det_complexComponent_ne_zero w hw x
  have hX : 0 < ‖rx 0 0‖ ^ 2 + ‖rx 0 1‖ ^ 2 + ‖rx 1 0‖ ^ 2 + ‖rx 1 1‖ ^ 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hn : ∀ i j, ‖rx i j‖ = 0 := by
      intro i j
      have hij := sq_nonneg ‖rx i j‖
      have hall : ‖rx 0 0‖ ^ 2 = 0 ∧ ‖rx 0 1‖ ^ 2 = 0 ∧ ‖rx 1 0‖ ^ 2 = 0 ∧ ‖rx 1 1‖ ^ 2 = 0 := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          nlinarith [sq_nonneg ‖rx 0 0‖, sq_nonneg ‖rx 0 1‖, sq_nonneg ‖rx 1 0‖, sq_nonneg ‖rx 1 1‖]
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
        [exact pow_eq_zero_iff (two_ne_zero) |>.mp hall.1; exact pow_eq_zero_iff (two_ne_zero) |>.mp hall.2.1;
         exact pow_eq_zero_iff (two_ne_zero) |>.mp hall.2.2.1; exact pow_eq_zero_iff (two_ne_zero) |>.mp hall.2.2.2]
    exact hdx (by rw [Matrix.det_fin_two, norm_eq_zero.mp (hn 0 0), norm_eq_zero.mp (hn 0 1), norm_eq_zero.mp (hn 1 0),
      norm_eq_zero.mp (hn 1 1)]; ring)
  have hκ : 0 < ‖rx.det‖ / (‖rx 0 0‖ ^ 2 + ‖rx 0 1‖ ^ 2 + ‖rx 1 0‖ ^ 2 + ‖rx 1 1‖ ^ 2) :=
    div_pos (norm_pos_iff.mpr hdx) hX
  refine ⟨d₁ * ‖rx.det‖, d₂ * ‖rx.det‖, c * (‖rx.det‖ / (‖rx 0 0‖ ^ 2 + ‖rx 0 1‖ ^ 2 + ‖rx 1 0‖ ^ 2 + ‖rx 1 1‖ ^ 2)),
    mul_pos hd₁ (norm_pos_iff.mpr hdx), mul_pos hc hκ, fun s hs => ?_⟩
  obtain ⟨-, hheight, -, hdet⟩ := mem_centreCutSiegelSet_iff.mp hs
  have hdet_s : archDetNorm w s ∈ Set.Icc d₁ d₂ := hdet w
  have hsplit : ‖(complexComponent w hw (s * x)).det‖ = archDetNorm w s * ‖rx.det‖ := by
    rw [complexComponent_mul, Matrix.det_mul, norm_mul, norm_det_complexComponent]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hsplit]; exact mul_le_mul_of_nonneg_right hdet_s.1 (norm_nonneg _)
  · rw [hsplit]; exact mul_le_mul_of_nonneg_right hdet_s.2 (norm_nonneg _)
  · rw [complexComponent_mul]
    refine le_trans ?_ (ArchIwasawa.Complex.norm_yOf_mul_ge _ _ (det_complexComponent_ne_zero w hw s) hdx)
    rw [norm_yOf_complexComponent]
    exact mul_le_mul_of_nonneg_right (hheight w) hκ.le

private theorem exists_profile_archFactorAt_on_siegel (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) (x : AdelicGL2 (𝓞 K) K) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ N : ℕ, ∃ A : ℝ, ∀ g ∈ (· * x) '' centreCutSiegelSet K c u d₁ d₂, ∀ α : Kˣ,
      ‖archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * ((w (α : K)) ^ (-σ) * (1 + w (α : K)) ^ (-(N : ℝ))) := by
  by_cases hw : w.IsReal
  · obtain ⟨D₁, D₂, y₀, hD₁, hy₀, hS⟩ := exists_siegel_bounds_real w hw hc hd₁ x
    set Sm : Set (Matrix (Fin 2) (Fin 2) ℝ) := (fun s => realComponent w hw (s * x)) '' centreCutSiegelSet K c u d₁ d₂
      with hSm
    have hdet : ∀ m ∈ Sm, m.det ≠ 0 := by
      rintro _ ⟨s, -, rfl⟩; exact det_realComponent_ne_zero w hw _
    have hwin : ∀ m ∈ Sm, D₁ ≤ |m.det| ∧ |m.det| ≤ D₂ := by
      rintro _ ⟨s, hs, rfl⟩; exact (hS s hs).1
    have hfloor : ∀ m ∈ Sm, y₀ ≤ |ArchIwasawa.Real.yOf m| := by
      rintro _ ⟨s, hs, rfl⟩; exact (hS s hs).2
    obtain ⟨σ, hσ, hprof⟩ := (dR w hw).exists_profile_bound_on hdet hD₁ hy₀ hwin hfloor
    have hB : ∀ m ∈ Sm, (Real.sqrt |m.det|)⁻¹ ≤ (Real.sqrt D₁)⁻¹ := fun m hm =>
      inv_anti₀ (Real.sqrt_pos.mpr hD₁) (Real.sqrt_le_sqrt (hwin m hm).1)
    refine ⟨σ + 1 / 2, by linarith, fun N => ?_⟩
    obtain ⟨A, hA⟩ := hprof N
    refine ⟨max A 0 * (Real.sqrt D₁)⁻¹, ?_⟩
    rintro _ ⟨s, hs, rfl⟩ α
    have hmem : realComponent w hw (s * x) ∈ Sm := ⟨s, hs, rfl⟩
    have hyw : |ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K))| = w (α : K) :=
      abs_ringEquivReal_algebraMap w hw (α : K)
    have hy0 : ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)) ≠ 0 := by
      intro h
      have := hyw
      rw [h, abs_zero] at this
      exact (w.pos_iff.mpr (Units.ne_zero α)).ne this
    have hfac : archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * (s * x))
        = (dR w hw).W (ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)))
              * realComponent w hw (s * x))
          * ((Real.sqrt |(ArchR.diagOne (ringEquivRealOfIsReal hw (algebraMap K w.Completion (α : K)))
              * realComponent w hw (s * x)).det| : ℝ) : ℂ)⁻¹ := by
      rw [archFactorAt, dif_pos hw, realComponent_globalPoints_diagOne_mul]
    rw [hfac, ← hyw]
    exact real_factor_bound (dR w hw).W hy0 (by simpa only [mul_assoc] using hA _ hmem _ hy0) (hB _ hmem)
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    obtain ⟨D₁, D₂, y₀, hD₁, hy₀, hS⟩ := exists_siegel_bounds_complex w hw' hc hd₁ x
    set Sm : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
      (fun s => complexComponent w hw' (s * x)) '' centreCutSiegelSet K c u d₁ d₂ with hSm
    have hdet : ∀ m ∈ Sm, m.det ≠ 0 := by
      rintro _ ⟨s, -, rfl⟩; exact det_complexComponent_ne_zero w hw' _
    have hwin : ∀ m ∈ Sm, D₁ ≤ ‖m.det‖ ∧ ‖m.det‖ ≤ D₂ := by
      rintro _ ⟨s, hs, rfl⟩; exact (hS s hs).1
    have hfloor : ∀ m ∈ Sm, y₀ ≤ ‖ArchIwasawa.Complex.yOf m‖ := by
      rintro _ ⟨s, hs, rfl⟩; exact (hS s hs).2
    obtain ⟨σ, hσ, hprof⟩ := (dC w hw').exists_profile_bound_on hdet hD₁ hy₀ hwin hfloor
    have hB : ∀ m ∈ Sm, ‖m.det‖⁻¹ ≤ D₁⁻¹ := fun m hm => inv_anti₀ hD₁ (hwin m hm).1
    refine ⟨σ + 1, by linarith, fun N => ?_⟩
    obtain ⟨A, hA⟩ := hprof N
    refine ⟨max A 0 * D₁⁻¹, ?_⟩
    rintro _ ⟨s, hs, rfl⟩ α
    have hmem : complexComponent w hw' (s * x) ∈ Sm := ⟨s, hs, rfl⟩
    have hzw : ‖ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K))‖ = w (α : K) :=
      norm_ringEquivComplex_algebraMap w hw' (α : K)
    have hz0 : ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)) ≠ 0 := by
      intro h
      have := hzw
      rw [h, norm_zero] at this
      exact (w.pos_iff.mpr (Units.ne_zero α)).ne this
    have hfac : archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * (s * x))
        = (dC w hw').W (ArchC.diagOne (ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)))
              * complexComponent w hw' (s * x))
          * ((‖(ArchC.diagOne (ringEquivComplexOfIsComplex hw' (algebraMap K w.Completion (α : K)))
              * complexComponent w hw' (s * x)).det‖ : ℝ) : ℂ)⁻¹ := by
      rw [archFactorAt, dif_neg hw, complexComponent_globalPoints_diagOne_mul]
    rw [hfac, ← hzw]
    exact complex_factor_bound (dC w hw').W hz0 (by simpa only [mul_assoc] using hA _ hmem _ hz0) (hB _ hmem)

private theorem exists_profile_archW'_on_siegel (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) (x : AdelicGL2 (𝓞 K) K) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ M : ℕ, ∃ A : ℝ, ∀ g ∈ (· * x) '' centreCutSiegelSet K c u d₁ d₂, ∀ α : Kˣ,
      ‖archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)‖
        ≤ A * (∏ w : InfinitePlace K, (w (α : K)) ^ (-σ)) * ∏ w : InfinitePlace K, (1 + w (α : K)) ^ (-(M : ℝ)) := by
  have hx : ∀ (w : InfinitePlace K) (α : Kˣ), 0 < w (α : K) := fun w α => w.pos_iff.mpr (Units.ne_zero α)
  have h := exists_profile_of_forall_mem
    (fun (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K) (α : Kˣ) =>
      archFactorAt archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * g))
    (fun (w : InfinitePlace K) (α : Kˣ) => w (α : K)) hx ((· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun w => exists_profile_archFactorAt_on_siegel archR archC dR dC w hc hd₁ x)
  simpa only [archW'_eq_prod_archFactorAt] using h

private theorem exists_finset_cover_siegel_mul (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∀ s ∈ centreCutSiegelSet K c u d₁ d₂,
      ∃ t ∈ T, ∃ v ∈ levelOne (𝓞 K) K ⊤, s * x = t * v := by
  set U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
    (finiteLevelOne (𝓞 K) K ⊤ : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) with hU
  have hUo : IsOpen U := isOpen_finiteLevelOne (𝓞 K) K top_ne_bot
  have hKc : IsCompact ((fun k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => k * glFin (𝓞 K) K x) ''
      (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :=
    (isCompact_finiteLevelZero (𝓞 K) K ⊤).image (continuous_mul_right _)
  obtain ⟨T₀, hT₀⟩ := hKc.elim_finite_subcover (fun y : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (y * ·) '' U)
    (fun y => isOpenMap_mul_left y U hUo) (fun z hz => Set.mem_iUnion.mpr ⟨z, 1, one_mem _, mul_one z⟩)
  refine ⟨T₀.image (AdelicDock.finEmbed (𝓞 K) K), fun s hs => ?_⟩
  have hsK : glFin (𝓞 K) K (s * x) ∈ (fun k : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => k * glFin (𝓞 K) K x) ''
      (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :=
    ⟨glFin (𝓞 K) K s, (mem_centreCutSiegelSet_iff.mp hs).1, by simp only [map_mul]⟩
  obtain ⟨y, hyT, k, hkU, hyk⟩ := Set.mem_iUnion₂.mp (hT₀ hsK)
  refine ⟨AdelicDock.finEmbed (𝓞 K) K y, Finset.mem_image_of_mem _ hyT,
    (AdelicDock.finEmbed (𝓞 K) K y)⁻¹ * (s * x), ?_,
    (mul_inv_cancel_left _ _).symm⟩
  rw [mem_levelOne_iff, map_mul, map_inv, AdelicDock.glFin_finEmbed, ← hyk, inv_mul_cancel_left]
  exact hkU

private theorem jlSeries'_bounded_on_siegel_mul {S : Finset (HeightOneSpectrum (𝓞 K))}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    {Pi : HeckeEigensystem K ℂ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (heps : ∀ g : AdelicGL2 (𝓞 K) K, ‖d.epsChar g‖ ≤ 1)
    {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) (x : AdelicGL2 (𝓞 K) K) :
    ∃ C : ℝ, ∀ g ∈ (· * x) '' centreCutSiegelSet K c u d₁ d₂, ‖jlSeries' d archR archC dR dC dF g‖ ≤ C := by
  obtain ⟨σ, hσ, hprof⟩ := exists_profile_archW'_on_siegel archR archC dR dC hc hd₁ x
  obtain ⟨M, C, hC⟩ := exists_uniform_majorant dF d.a (d.bounded.imp fun _ h α => (h α).1)
    (fun α h => (d.floor α h).1) hgrow d.epsChar heps id ((· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (by
      obtain ⟨T, hT⟩ := exists_finset_cover_siegel_mul c u d₁ d₂ x
      refine ⟨T, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact hT s hs)
    (fun _ g α => archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)) (fun _ _ => 1)
    (fun _ _ _ => zero_le_one)
    ⟨σ, hσ, fun M => by
      obtain ⟨A, hA⟩ := hprof M
      exact ⟨A, fun g hg α => by simpa only [mul_one] using hA g hg α⟩⟩
  refine ⟨C, fun g hg => ?_⟩
  have hterm := hC g hg
  simp only [id] at hterm
  rw [jlSeries'_eq_tsum_seriesTerm]
  calc ‖∑' α : Kˣ, seriesTerm d archR archC dR dC dF g α‖
      ≤ ∑' α : Kˣ, ‖seriesTerm d archR archC dR dC dF g α‖ := norm_tsum_le_tsum_norm hterm.1
    _ ≤ C * 1 := hterm.2
    _ = C := mul_one C

end SiegelBound

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse LanglandsTunnell.TateLocal NumberField.StandardAddChar"
open Topology

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell _root_.LanglandsTunnell.Converse _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse _root_.LanglandsTunnell.Converse.CuspSynthesis _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.LanglandsTunnell.Converse.CuspSynthesis in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC) :
    (∀ g : AdelicGL2 (𝓞 K) K, jlSeries' d archR archC dR dC dF g =
      ∑' α : Kˣ, d.a α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)
        * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)) ∧
    (∃ κ : ℝ, ∀ v ∉ S,
        ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, ‖d.epsChar g‖ ≤ 1) ∧
    (∀ coef : Kˣ → ℂ, (∃ C : ℝ, ∀ α, ‖coef α‖ ≤ C) →
      (∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
        ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0) →
      ∀ h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K, Continuous h → ∀ g₀ : AdelicGL2 (𝓞 K) K,
        ∃ V ∈ 𝓝 g₀, ∃ b : Kˣ → ℝ, Summable b ∧ (∀ α, 0 ≤ b α) ∧ ∀ g ∈ V, ∀ α : Kˣ,
          ‖coef α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g)
            * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ b α) ∧
    (∀ c u d₁ d₂ : ℝ, 0 < c → 0 < d₁ → ∀ x : AdelicGL2 (𝓞 K) K, ∃ C : ℝ,
      ∀ g ∈ (· * x) '' centreCutSiegelSet K c u d₁ d₂, ‖jlSeries' d archR archC dR dC dF g‖ ≤ C) ∧
    ContinuousOn (jlSeries' d archR archC dR dC dF) (kZeroSet S d.m) ∧
    Continuous (archW' archR archC dR dC) :=
  ⟨fun g => jlSeries'_eq_tsum_seriesTerm d archR archC dR dC dF g,
   exists_growth_exponent Pi S archR archC epsS ω hω hωb d hnice,
   norm_epsChar_le_one d hω,
   fun coef hcoef hfloor h hh g₀ => exists_local_majorant_of_data d archR archC dR dC dF coef hcoef hfloor
     (exists_growth_exponent Pi S archR archC epsS ω hω hωb d hnice)
     (norm_epsChar_le_one d hω) (exists_profile_archW' archR archC dR dC) h hh g₀,
   fun c u d₁ d₂ hc hd₁ x => jlSeries'_bounded_on_siegel_mul d archR archC dR dC dF
     (exists_growth_exponent Pi S archR archC epsS ω hω hωb d hnice) (norm_epsChar_le_one d hω) hc hd₁ x,
   continuousOn_series K Pi S archR archC epsS ω hω hωb d dR dC dF hnice,
   continuous_archW' archR archC dR dC⟩

end S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
end P2MW
export P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice (solution)
