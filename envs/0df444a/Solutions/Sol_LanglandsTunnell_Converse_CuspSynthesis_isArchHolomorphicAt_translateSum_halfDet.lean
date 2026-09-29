-- Prove2me | solution 1 for LanglandsTunnell.Converse.CuspSynthesis.isArchHolomorphicAt_translateSum_halfDet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d6e69ad8-03dc-5e52-9e95-08f12edd5a7f

import Definitions.Def_LanglandsTunnell_JLSynthesis
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Theorems.Thm_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
import Definitions.Def_LanglandsTunnell_JLData
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_GaussTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet
p2m_attr_erase "instance" "instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
set_option Elab.async false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse"

noncomputable section

namespace FourierUniq

open Complex MeasureTheory Filter Topology

private def e (x : ℝ) : ℂ := exp (2 * Real.pi * I * x)

section Line

variable {ι : Type*}

end Line

section Space

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

end Space

end FourierUniq

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace Fourier
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

open Complex MeasureTheory Filter Topology
p2m_open "NumberField NumberField.InfinitePlace LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.FourierUniq"

variable (K : Type) [Field K] [NumberField K]

open scoped Classical

variable {K}

end LanglandsTunnell.Converse.Fourier

end

section

open scoped WithZero

namespace LocalWhittaker

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

end LocalWhittaker

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LocalWhittaker"
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

private def compAt (w : HeightOneSpectrum (𝓞 K)) : AdelicGL2 (𝓞 K) K →* GL (Fin 2) (w.adicCompletion K) :=
  (finComponent (𝓞 K) K w).comp (glFin (𝓞 K) K)

end FiniteWhittaker

end

namespace LocalWhittaker

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section MapSurj

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {L : Type*} [Field L] [Algebra R L]
  [IsFractionRing R L] (v : HeightOneSpectrum R)

end MapSurj

end LocalWhittaker

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LocalWhittaker"
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

section IntegralInvariance

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

end IntegralInvariance

end FiniteWhittaker

end

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LocalWhittaker"
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

private theorem ext_of_glArch_of_compAt {x y : AdelicGL2 (𝓞 K) K} (harch : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K), compAt w x = compAt w y) : x = y := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K ?_ ?_)
  · exact congrArg Units.val harch
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun w => ?_
    exact congrArg Units.val (hfin w)

end FiniteWhittaker

end

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open NumberField.AdelicVolume NumberField.TateGlobal
open Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace Ideles
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

section Continuity

open scoped RestrictedProduct

end Continuity

end LanglandsTunnell.Converse.Ideles

end

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
p2m_open "AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LocalWhittaker"
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal NumberField.AdelicVolume
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

section Centre

end Centre

section SCharacter

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

end SCharacter

section Series

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

end Series

end FiniteWhittaker

end

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

open AutomorphicForm.SmoothCusp

variable {K : Type} [Field K] [NumberField K]

section WeakApproximation

open scoped WithZero

end WeakApproximation

section Components

open scoped WithZero

end Components

section CentreAndTopology

open scoped WithZero

end CentreAndTopology

section Extend

private def InvOn (D : Set (AdelicGL2 (𝓞 K) K)) (f : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ D → globalPoints (𝓞 K) K γ * g ∈ D →
    f (globalPoints (𝓞 K) K γ * g) = f g

variable {D : Set (AdelicGL2 (𝓞 K) K)}
  {hD : ∀ g : AdelicGL2 (𝓞 K) K, ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * g ∈ D}
  {f : AdelicGL2 (𝓞 K) K → ℂ}

private theorem InvOn.eq_of_mem (hf : InvOn D f) {γ₁ γ₂ : GL (Fin 2) K} {g : AdelicGL2 (𝓞 K) K}
    (h₁ : globalPoints (𝓞 K) K γ₁ * g ∈ D) (h₂ : globalPoints (𝓞 K) K γ₂ * g ∈ D) :
    f (globalPoints (𝓞 K) K γ₁ * g) = f (globalPoints (𝓞 K) K γ₂ * g) := by
  have key : globalPoints (𝓞 K) K (γ₁ * γ₂⁻¹) * (globalPoints (𝓞 K) K γ₂ * g) =
      globalPoints (𝓞 K) K γ₁ * g := by
    rw [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have h := hf (γ₁ * γ₂⁻¹) _ h₂ (by rw [key]; exact h₁)
  rw [key] at h
  exact h

private theorem extend_apply_of_mem (hf : InvOn D f) {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ D) :
    extendByRationalPoints D hD f g = f g := by
  have h1 : globalPoints (𝓞 K) K 1 * g ∈ D := by rwa [map_one, one_mul]
  have h := hf.eq_of_mem (Classical.choose_spec (hD g)) h1
  rw [map_one, one_mul] at h
  exact h

private theorem extend_mul_left (hf : InvOn D f) (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    extendByRationalPoints D hD f (globalPoints (𝓞 K) K γ * g) = extendByRationalPoints D hD f g := by
  unfold extendByRationalPoints
  have h₁ := Classical.choose_spec (hD (globalPoints (𝓞 K) K γ * g))
  have h₂ := Classical.choose_spec (hD g)
  rw [← mul_assoc, ← map_mul] at h₁ ⊢
  exact hf.eq_of_mem h₁ h₂

end Extend

section ArchCentre

open NumberField NumberField.InfinitePlace AutomorphicForm NumberField.TateGlobal Complex

end ArchCentre

section ArchDictionary

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.TateGlobal Complex

end ArchDictionary

section
section TorusModel
open LanglandsTunnell.Converse.Ideles

end TorusModel
end
section
section TorusModel
open LanglandsTunnell.Converse.Ideles

end TorusModel
end
section
section TorusModel
open LanglandsTunnell.Converse.Ideles

end TorusModel
end
section
section TorusModel
open LanglandsTunnell.Converse.Ideles

end TorusModel
end
section
section TorusModel
open LanglandsTunnell.Converse.Ideles

end TorusModel
end
section
section TorusModel
open LanglandsTunnell.Converse.Ideles

end TorusModel
end
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

end TorusClass
end
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

end TorusClass
end
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

end TorusClass
end
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

end TorusClass
end
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

end TorusClass
end
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

end TorusClass
end
section
section TorusClass
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

end TorusClass
end
section
section GaussFixedVector

open scoped WithZero
open UnramifiedWhittaker

end GaussFixedVector
end
section
section GaussFixedVector

open scoped WithZero
open UnramifiedWhittaker

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

end SeriesCoefficient
end
section
section SeriesCoefficient

open NumberField.InfinitePlace

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

end GaussCoefficient
end
end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section EigenClauses

open AutomorphicForm.SmoothCusp FiniteWhittaker
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem epsChar_mul_of_forall_compAt_eq_one (d : JLData K S epsS ω) {ρ : AdelicGL2 (𝓞 K) K}
    (hρ : ∀ w ∈ S, compAt w ρ = 1) (g : AdelicGL2 (𝓞 K) K) : d.epsChar (g * ρ) = d.epsChar g := by
  have h : ∀ w : ↥S, componentMatrix w.1 (g * ρ) = componentMatrix w.1 g := fun w => by
    show ((compAt w.1 (g * ρ) : GL (Fin 2) (w.1.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion K))
      = ((compAt w.1 g : GL (Fin 2) (w.1.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion K))
    rw [map_mul, hρ w.1 w.2, mul_one]
  unfold JLData.epsChar
  exact if_congr (by simp only [MemZK0At, h]) (by simp only [h]) rfl

private theorem mul_mem_kZeroSet_of_forall_compAt_eq_one (m : ↥S → ℕ) {ρ : AdelicGL2 (𝓞 K) K}
    (hρ : ∀ w ∈ S, compAt w ρ = 1) {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ kZeroSet S m) : g * ρ ∈ kZeroSet S m := by
  intro w
  have h : componentMatrix w.1 (g * ρ) = componentMatrix w.1 g := by
    show ((compAt w.1 (g * ρ) : GL (Fin 2) (w.1.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion K))
      = ((compAt w.1 g : GL (Fin 2) (w.1.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion K))
    rw [map_mul, hρ w.1 w.2, mul_one]
  have hgw := hg w
  simp only [MemZK0At] at hgw ⊢
  rw [h]
  exact hgw

end EigenClauses

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section ArchInclusionComponents

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

private theorem glFin_mul_adelicArchGLInclAt (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K)
    (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (g * AutomorphicForm.adelicArchGLInclAt K w k) = glFin (𝓞 K) K g := by
  rw [map_mul, AutomorphicForm.adelicArchGLInclAt, MonoidHom.comp_apply, AutomorphicForm.glFin_adelicArchGLIncl,
    mul_one]

private theorem archComponent_glArch_mul_adelicArchGLInclAt (w : InfinitePlace K) (g : AdelicGL2 (𝓞 K) K)
    (k : GL (Fin 2) w.Completion) :
    AdelicLevel.archComponent K w (glArch (𝓞 K) K (g * AutomorphicForm.adelicArchGLInclAt K w k))
      = AdelicLevel.archComponent K w (glArch (𝓞 K) K g) * k := by
  rw [map_mul, AutomorphicForm.adelicArchGLInclAt, MonoidHom.comp_apply, AutomorphicForm.glArch_adelicArchGLIncl,
    map_mul, AutomorphicForm.archComponent_archGLIncl_self]

private theorem archComponent_glArch_mul_adelicArchGLInclAt_of_ne {w' w : InfinitePlace K} (hne : w' ≠ w)
    (g : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    AdelicLevel.archComponent K w' (glArch (𝓞 K) K (g * AutomorphicForm.adelicArchGLInclAt K w k))
      = AdelicLevel.archComponent K w' (glArch (𝓞 K) K g) := by
  rw [map_mul, AutomorphicForm.adelicArchGLInclAt, MonoidHom.comp_apply, AutomorphicForm.glArch_adelicArchGLIncl,
    map_mul, AutomorphicForm.archComponent_archGLIncl_of_ne K hne, mul_one]

private theorem realComponent_mul_adelicArchGLInclAt (w : InfinitePlace K) (hw : w.IsReal)
    (g : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    realComponent w hw (g * AutomorphicForm.adelicArchGLInclAt K w k)
      = realComponent w hw g
          * ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map (ringEquivRealOfIsReal hw) := by
  rw [realComponent_eq_map, realComponent_eq_map, archComponent_glArch_mul_adelicArchGLInclAt, Units.val_mul,
    Matrix.map_mul]

private theorem realComponent_mul_adelicArchGLInclAt_of_ne {w' w : InfinitePlace K} (hne : w' ≠ w)
    (hw' : w'.IsReal) (g : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    realComponent w' hw' (g * AutomorphicForm.adelicArchGLInclAt K w k) = realComponent w' hw' g := by
  rw [realComponent_eq_map, realComponent_eq_map, archComponent_glArch_mul_adelicArchGLInclAt_of_ne hne]

private theorem complexComponent_mul_adelicArchGLInclAt_of_ne {w' w : InfinitePlace K} (hne : w' ≠ w)
    (hw' : w'.IsComplex) (g : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    complexComponent w' hw' (g * AutomorphicForm.adelicArchGLInclAt K w k) = complexComponent w' hw' g := by
  rw [complexComponent_eq_map, complexComponent_eq_map, archComponent_glArch_mul_adelicArchGLInclAt_of_ne hne]

end ArchInclusionComponents

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section WeightConjunct

open AutomorphicForm.SmoothCusp FiniteWhittaker
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem compAt_mul_adelicArchGLInclAt (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)
    (w : InfinitePlace K) (x : GL (Fin 2) w.Completion) : compAt v (g * adelicArchGLInclAt K w x) = compAt v g := by
  simp only [compAt, MonoidHom.comp_apply, glFin_mul_adelicArchGLInclAt]

private theorem compAt_adelicArchGLInclAt (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K)
    (x : GL (Fin 2) w.Completion) : compAt v (adelicArchGLInclAt K w x) = 1 := by
  have h := compAt_mul_adelicArchGLInclAt v 1 w x
  rwa [one_mul, map_one] at h

private theorem adelicArchGLInclAt_mul_of_glArch_eq_one {y : AdelicGL2 (𝓞 K) K} (hy : glArch (𝓞 K) K y = 1)
    (w : InfinitePlace K) (x : GL (Fin 2) w.Completion) :
    adelicArchGLInclAt K w x * y = y * adelicArchGLInclAt K w x := by
  refine ext_of_glArch_of_compAt (by rw [map_mul, map_mul, hy, mul_one, one_mul]) fun v => ?_
  rw [map_mul, map_mul, compAt_adelicArchGLInclAt, mul_one, one_mul]

private theorem mul_adelicArchGLInclAt_mem_kZeroSet_iff {S : Finset (HeightOneSpectrum (𝓞 K))} (m : ↥S → ℕ)
    (w : InfinitePlace K) (x : GL (Fin 2) w.Completion) (g : AdelicGL2 (𝓞 K) K) :
    g * adelicArchGLInclAt K w x ∈ kZeroSet S m ↔ g ∈ kZeroSet S m := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := mul_mem_kZeroSet_of_forall_compAt_eq_one m (fun v _ => compAt_adelicArchGLInclAt v w x⁻¹) h
    rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h'
  · exact mul_mem_kZeroSet_of_forall_compAt_eq_one m (fun v _ => compAt_adelicArchGLInclAt v w x) h

private theorem coe_glEquivOfRingEquiv {L M : Type} [NormedField L] [NormedField M] (e : L ≃+* M) (x : GL (Fin 2) L) :
    ((glEquivOfRingEquiv e x : GL (Fin 2) M) : Matrix (Fin 2) (Fin 2) M) = (x : Matrix (Fin 2) (Fin 2) L).map e := by
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, Matrix.map_apply]

end WeightConjunct

end LanglandsTunnell.Converse.CuspSynthesis

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section TwistTransport

open MeasureTheory AutomorphicForm NumberField.TateGlobal

variable {K : Type} [Field K] [NumberField K]

private def halfDet (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

private theorem halfDet_def (g : AdelicGL2 (𝓞 K) K) :
    halfDet g = (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := rfl

private theorem halfDet_ne_zero (g : AdelicGL2 (𝓞 K) K) : halfDet g ≠ 0 := by
  rw [halfDet_def]
  exact_mod_cast (Real.rpow_pos_of_pos (ideleNorm_pos _) _).ne'

private theorem halfDet_mul (g h : AdelicGL2 (𝓞 K) K) : halfDet (g * h) = halfDet g * halfDet h := by
  simp only [halfDet_def, map_mul, ideleNorm_mul]
  rw [Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, Complex.ofReal_mul]

end TwistTransport

end LanglandsTunnell.Converse.CuspSynthesis

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section HolomorphyFurniture

open AutomorphicForm.SmoothCusp FiniteWhittaker NumberField.TateGlobal NumberField.AdelicVolume
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private theorem glArch_adelicArchGLInclAt' (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    glArch (𝓞 K) K (adelicArchGLInclAt K w k) = archGLIncl K w k := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]

private theorem glFin_adelicArchGLInclAt' (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (adelicArchGLInclAt K w k) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

private theorem archDetNorm_adelicArchGLInclAt_self (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    archDetNorm w (adelicArchGLInclAt K w k)
      = ‖((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ := by
  unfold archDetNorm
  rw [glArch_adelicArchGLInclAt', AutomorphicForm.archComponent_archGLIncl_self]

private theorem archDetNorm_adelicArchGLInclAt_of_ne {w' w : InfinitePlace K} (hne : w' ≠ w)
    (k : GL (Fin 2) w.Completion) : archDetNorm w' (adelicArchGLInclAt K w k) = 1 := by
  unfold archDetNorm
  rw [glArch_adelicArchGLInclAt', AutomorphicForm.archComponent_archGLIncl_of_ne K hne, Units.val_one,
    Matrix.det_one, norm_one]

private theorem ideleNorm_det_adelicArchGLInclAt (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (adelicArchGLInclAt K w k))
      = ‖((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ w.mult := by
  rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult K _ (by rw [glFin_adelicArchGLInclAt']; exact one_mem _),
    Fintype.prod_eq_single w fun w' hne => by rw [archDetNorm_adelicArchGLInclAt_of_ne hne, one_pow],
    archDetNorm_adelicArchGLInclAt_self]

private noncomputable def realImage {w : InfinitePlace K} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map (ringEquivRealOfIsReal hw)

omit [NumberField K] in
private theorem realImage_def {w : InfinitePlace K} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    realImage hw k
      = ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).map (ringEquivRealOfIsReal hw) :=
  rfl

private theorem realComponent_mul_adelicArchGLInclAt' {w : InfinitePlace K} (hw : w.IsReal)
    (g : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    realComponent w hw (g * adelicArchGLInclAt K w k) = realComponent w hw g * realImage hw k :=
  realComponent_mul_adelicArchGLInclAt w hw g k

private theorem det_realImage {w : InfinitePlace K} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    (realImage hw k).det
      = ringEquivRealOfIsReal hw ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [realImage_def, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply]
  rw [← map_mul, ← map_mul, ← map_sub]

private theorem abs_det_realImage {w : InfinitePlace K} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    |(realImage hw k).det| = ‖((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det‖ := by
  rw [det_realImage, ← Real.norm_eq_abs, norm_ringEquivRealOfIsReal]

private theorem det_realImage_ne_zero {w : InfinitePlace K} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    (realImage hw k).det ≠ 0 := by
  rw [det_realImage]
  exact (map_ne_zero _).mpr (Matrix.GeneralLinearGroup.det_ne_zero k)

private theorem abs_det_realImage_pos {w : InfinitePlace K} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    0 < |(realImage hw k).det| :=
  abs_pos.mpr (det_realImage_ne_zero hw k)

private theorem ideleNorm_det_adelicArchGLInclAt_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (k : GL (Fin 2) w.Completion) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (adelicArchGLInclAt K w k)) = |(realImage hw k).det| := by
  rw [ideleNorm_det_adelicArchGLInclAt, abs_det_realImage, InfinitePlace.mult, if_pos hw, pow_one]

private theorem halfDet_adelicArchGLInclAt_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (k : GL (Fin 2) w.Completion) :
    halfDet (adelicArchGLInclAt K w k) = ((Real.sqrt |(realImage hw k).det| : ℝ) : ℂ) := by
  rw [halfDet_def, ideleNorm_det_adelicArchGLInclAt_of_isReal hw, Real.sqrt_eq_rpow]

private theorem halfDet_mul_adelicArchGLInclAt_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (g : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    halfDet (g * adelicArchGLInclAt K w k) = halfDet g * ((Real.sqrt |(realImage hw k).det| : ℝ) : ℂ) := by
  rw [halfDet_mul, halfDet_adelicArchGLInclAt_of_isReal hw]

private theorem archNormFactor_mul_adelicArchGLInclAt_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (q : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    archNormFactor (q * adelicArchGLInclAt K w k)
      = archNormFactor q * (((Real.sqrt |(realImage hw k).det| : ℝ) : ℂ))⁻¹ := by
  unfold archNormFactor
  have h : (∏ w' : InfinitePlace K, if w' = w then (((Real.sqrt |(realImage hw k).det| : ℝ) : ℂ))⁻¹ else 1)
      = (((Real.sqrt |(realImage hw k).det| : ℝ) : ℂ))⁻¹ :=
    Fintype.prod_ite_eq' w fun _ => (((Real.sqrt |(realImage hw k).det| : ℝ) : ℂ))⁻¹
  rw [← h, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w' _ => ?_
  rcases eq_or_ne w' w with rfl | hne
  · simp only [dif_pos hw, if_pos trivial]
    rw [realComponent_mul_adelicArchGLInclAt' hw, Matrix.det_mul, abs_mul,
      Real.sqrt_mul (abs_nonneg _), Complex.ofReal_mul, mul_inv]
  · by_cases hw' : w'.IsReal
    · simp only [dif_pos hw', if_neg hne, realComponent_mul_adelicArchGLInclAt_of_ne hne, mul_one]
    · simp only [dif_neg hw', if_neg hne, complexComponent_mul_adelicArchGLInclAt_of_ne hne, mul_one]

private noncomputable def archWAway
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (w : InfinitePlace K) (q : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∏ w' ∈ Finset.univ.erase w,
    if hw' : w'.IsReal then (dR w' hw').W (realComponent w' hw' q)
    else (dC w' (InfinitePlace.not_isReal_iff_isComplex.mp hw')).W
      (complexComponent w' (InfinitePlace.not_isReal_iff_isComplex.mp hw') q)

private theorem archW_eq_mul_archWAway
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    {w : InfinitePlace K} (hw : w.IsReal) (q : AdelicGL2 (𝓞 K) K) :
    archW archR archC dR dC q = (dR w hw).W (realComponent w hw q) * archWAway archR archC dR dC w q := by
  unfold archW archWAway
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), dif_pos hw]

private theorem archW_mul_adelicArchGLInclAt_of_isReal
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    {w : InfinitePlace K} (hw : w.IsReal) (q : AdelicGL2 (𝓞 K) K) (k : GL (Fin 2) w.Completion) :
    archW archR archC dR dC (q * adelicArchGLInclAt K w k)
      = (dR w hw).W (realComponent w hw q * realImage hw k) * archWAway archR archC dR dC w q := by
  rw [archW_eq_mul_archWAway archR archC dR dC hw, realComponent_mul_adelicArchGLInclAt' hw]
  congr 1
  unfold archWAway
  refine Finset.prod_congr rfl fun w' hw'mem => ?_
  have hne : w' ≠ w := Finset.ne_of_mem_erase hw'mem
  by_cases hw' : w'.IsReal
  · simp only [dif_pos hw', realComponent_mul_adelicArchGLInclAt_of_ne hne]
  · simp only [dif_neg hw', complexComponent_mul_adelicArchGLInclAt_of_ne hne]

private theorem exists_halfDet_mul_seriesTerm_mul_adelicArchGLInclAt_eq (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) {w : InfinitePlace K} (hw : w.IsReal) (q : AdelicGL2 (𝓞 K) K) (α : Kˣ) :
    ∃ C : ℂ, ∀ k : GL (Fin 2) w.Completion,
      halfDet (q * adelicArchGLInclAt K w k) * seriesTerm d archR archC dR dC dF (q * adelicArchGLInclAt K w k) α
        = C * (dR w hw).W (realComponent w hw (globalPoints (𝓞 K) K (diagOne α) * q) * realImage hw k) := by
  refine ⟨halfDet q * (d.a α * d.epsChar q * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * q))
    * (archWAway archR archC dR dC w (globalPoints (𝓞 K) K (diagOne α) * q)
      * archNormFactor (globalPoints (𝓞 K) K (diagOne α) * q)), fun k => ?_⟩
  have hs : ((Real.sqrt |(realImage hw k).det| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (abs_det_realImage_pos hw k)).ne'
  unfold seriesTerm archW'
  rw [← mul_assoc (globalPoints (𝓞 K) K (diagOne α)) q, archW_mul_adelicArchGLInclAt_of_isReal archR archC dR dC hw,
    archNormFactor_mul_adelicArchGLInclAt_of_isReal hw, halfDet_mul_adelicArchGLInclAt_of_isReal hw,
    epsChar_mul_of_forall_compAt_eq_one d (fun v _ => compAt_adelicArchGLInclAt v w k) q,
    dF.finite_dependent _ _ (glFin_mul_adelicArchGLInclAt w (globalPoints (𝓞 K) K (diagOne α) * q) k)]
  field_simp

end HolomorphyFurniture

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section SectionContinuity

open AutomorphicForm.SmoothCusp FiniteWhittaker NumberField.TateGlobal NumberField.AdelicVolume
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem adelicArchGLInclAt_coe_apply (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      = ((AutomorphicForm.archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) := by
  refine Prod.ext ?_ ?_
  · calc (((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1
        = (glArch (𝓞 K) K (adelicArchGLInclAt K w k) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j :=
          (AdelicLevel.glArch_apply (𝓞 K) K _ i j).symm
      _ = (archGLIncl K w k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j :=
          by rw [glArch_adelicArchGLInclAt' w k]
      _ = AutomorphicForm.archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
  · calc (((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2
        = (glFin (𝓞 K) K (adelicArchGLInclAt K w k) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j :=
          (AdelicLevel.glFin_apply (𝓞 K) K _ i j).symm
      _ = ((1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j :=
          by rw [glFin_adelicArchGLInclAt' w k]
      _ = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j := rfl

omit [NumberField K] in

private theorem archMatrixUpdate_apply_eq (w : InfinitePlace K) (m : Matrix (Fin 2) (Fin 2) w.Completion)
    (i j : Fin 2) (v : InfinitePlace K) :
    AutomorphicForm.archMatrixUpdate K w m i j v
      = Function.update (1 : ∀ v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w m v i j :=
  (AutomorphicForm.archMatrixPiEquiv_apply K _ v i j).symm.trans
    (congrFun (congrFun (congrFun (AutomorphicForm.archMatrixPiEquiv_archMatrixUpdate K w m) v) i) j)

private theorem continuous_coe_adelicArchGLInclAt (w : InfinitePlace K) :
    Continuous fun k : GL (Fin 2) w.Completion =>
      ((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
  refine continuous_matrix fun i j => ?_
  have hfun : (fun k : GL (Fin 2) w.Completion =>
        ((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)
      = fun k : GL (Fin 2) w.Completion =>
        ((AutomorphicForm.archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) :=
    funext fun k => adelicArchGLInclAt_coe_apply w k i j
  have hupd : (fun k : GL (Fin 2) w.Completion =>
        AutomorphicForm.archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j)
      = fun k : GL (Fin 2) w.Completion => fun v : InfinitePlace K =>
        Function.update (1 : ∀ v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
          (k : Matrix (Fin 2) (Fin 2) w.Completion) v i j :=
    funext fun k => funext fun v => archMatrixUpdate_apply_eq w _ i j v
  show Continuous fun k : GL (Fin 2) w.Completion =>
    ((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  rw [hfun]
  refine Continuous.prodMk ?_ continuous_const
  show Continuous fun k : GL (Fin 2) w.Completion =>
    AutomorphicForm.archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j
  rw [hupd]
  refine continuous_pi fun v => ?_
  have hk : Continuous fun k : GL (Fin 2) w.Completion =>
      Function.update (1 : ∀ v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
        (k : Matrix (Fin 2) (Fin 2) w.Completion) :=
    continuous_const.update w Units.continuous_val
  have hkv : Continuous fun k : GL (Fin 2) w.Completion =>
      Function.update (1 : ∀ v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
        (k : Matrix (Fin 2) (Fin 2) w.Completion) v :=
    (continuous_apply v).comp hk
  exact hkv.matrix_elem i j

private theorem continuous_adelicArchGLInclAt (w : InfinitePlace K) :
    Continuous (adelicArchGLInclAt K w : GL (Fin 2) w.Completion → AdelicGL2 (𝓞 K) K) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_coe_adelicArchGLInclAt w, ?_⟩
  have h : (fun k : GL (Fin 2) w.Completion =>
        (((adelicArchGLInclAt K w k)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
      = fun k : GL (Fin 2) w.Completion =>
        ((adelicArchGLInclAt K w k⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    funext k
    rw [map_inv]
  rw [h]
  exact (continuous_coe_adelicArchGLInclAt w).comp continuous_inv

omit [NumberField K] in

private theorem continuous_ringEquivRealOfIsReal_symm {w : InfinitePlace K} (hw : w.IsReal) :
    Continuous fun r : ℝ => (ringEquivRealOfIsReal hw).symm r := by
  have h : (fun r : ℝ => (ringEquivRealOfIsReal hw).symm r) = (isometryEquivRealOfIsReal hw).symm := rfl
  rw [h]
  exact (isometryEquivRealOfIsReal hw).symm.continuous

private theorem continuous_coe_map_realSymm {w : InfinitePlace K} (hw : w.IsReal) :
    Continuous fun x : GL (Fin 2) ℝ =>
      ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom x : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun x : GL (Fin 2) ℝ =>
    (ringEquivRealOfIsReal hw).symm ((x : Matrix (Fin 2) (Fin 2) ℝ) i j)
  exact (continuous_ringEquivRealOfIsReal_symm hw).comp (Units.continuous_val.matrix_elem i j)

private theorem continuous_map_realSymm {w : InfinitePlace K} (hw : w.IsReal) :
    Continuous (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom :
      GL (Fin 2) ℝ → GL (Fin 2) w.Completion) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_coe_map_realSymm hw, ?_⟩
  have h : (fun x : GL (Fin 2) ℝ =>
        (((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom x)⁻¹ :
          GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion))
      = fun x : GL (Fin 2) ℝ =>
        ((Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom x⁻¹ : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) := by
    funext x
    rw [Matrix.GeneralLinearGroup.map_inv]
  rw [h]
  exact (continuous_coe_map_realSymm hw).comp continuous_inv

private theorem iwasawaSectionGL_coe (z : UpperHalfPlane) :
    ((iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] :=
  rfl

private theorem iwasawaSectionGL_inv_coe (z : UpperHalfPlane) :
    (((iwasawaSectionGL z)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(z.im)⁻¹, -(z.re / z.im); 0, 1] := by
  have hy : z.im ≠ 0 := z.im_ne_zero
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [iwasawaSectionGL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy] <;> field_simp <;> ring

private theorem continuous_iwasawaSectionGL : Continuous iwasawaSectionGL := by
  rw [Units.continuous_iff]
  constructor
  · have h : (fun z : UpperHalfPlane => ((iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
        = fun z : UpperHalfPlane => !![z.im, z.re; 0, 1] :=
      funext iwasawaSectionGL_coe
    show Continuous fun z : UpperHalfPlane => ((iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have h : (fun z : UpperHalfPlane => (((iwasawaSectionGL z)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
        = fun z : UpperHalfPlane => !![(z.im)⁻¹, -(z.re / z.im); 0, 1] :=
      funext iwasawaSectionGL_inv_coe
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop (disch := intros; exact UpperHalfPlane.im_ne_zero _)

private theorem continuous_sectionAt {w : InfinitePlace K} (hw : w.IsReal) (q : AdelicGL2 (𝓞 K) K) :
    Continuous fun z : UpperHalfPlane => q * adelicArchGLInclAt K w
      (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (iwasawaSectionGL z)) :=
  continuous_const.mul ((continuous_adelicArchGLInclAt w).comp
    ((continuous_map_realSymm hw).comp continuous_iwasawaSectionGL))

end SectionContinuity

end LanglandsTunnell.Converse.CuspSynthesis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR ArchDatumC FinWhittakerDatum extendByRationalPoints componentMatrix MemZK0At JLData.epsChar realComponent complexComponent archW jlForm JLData IsJLNice IsAdmissibleTwist"
namespace CuspSynthesis
p2m_export "LanglandsTunnell.Converse.CuspSynthesis" "kZeroSet kZeroSet_meets archNormFactor archW' jlSeries' theForm theForm_eq translateSum exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice"
p2m_open "LanglandsTunnell.Converse.CuspSynthesis LanglandsTunnell.Converse LanglandsTunnell"

section HolomorphyFill

open AutomorphicForm.SmoothCusp FiniteWhittaker NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Classical
open scoped Topology

variable {K : Type} [Field K] [NumberField K]

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
  {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

private noncomputable def sectionAt {w : InfinitePlace K} (hw : w.IsReal) (z : UpperHalfPlane) :
    GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (iwasawaSectionGL z)

omit [NumberField K] in
private theorem sectionAt_def {w : InfinitePlace K} (hw : w.IsReal) (z : UpperHalfPlane) :
    sectionAt hw z = Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom (iwasawaSectionGL z) :=
  rfl

private theorem realImage_sectionAt {w : InfinitePlace K} (hw : w.IsReal) (z : UpperHalfPlane) :
    realImage hw (sectionAt hw z) = ((iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [realImage_def, sectionAt_def]
  ext i j
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Matrix.map_apply, RingEquiv.toRingHom_eq_coe]
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _

private theorem abs_det_realImage_sectionAt {w : InfinitePlace K} (hw : w.IsReal) (z : UpperHalfPlane) :
    |(realImage hw (sectionAt hw z)).det| = z.im := by
  rw [realImage_sectionAt, iwasawaSectionGL_coe, Matrix.det_fin_two_of]
  simp only [mul_one, mul_zero, sub_zero]
  exact abs_of_pos z.im_pos

private noncomputable def realPoint {w : InfinitePlace K} (hw : w.IsReal) (p : AdelicGL2 (𝓞 K) K) : GL (Fin 2) ℝ :=
  glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (AdelicLevel.archComponent K w (glArch (𝓞 K) K p))

private theorem coe_realPoint {w : InfinitePlace K} (hw : w.IsReal) (p : AdelicGL2 (𝓞 K) K) :
    ((realPoint hw p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = realComponent w hw p := by
  rw [realPoint, coe_glEquivOfRingEquiv, realComponent_eq_map]

private theorem realComponent_mul_realImage_sectionAt {w : InfinitePlace K} (hw : w.IsReal) (p : AdelicGL2 (𝓞 K) K)
    (z : UpperHalfPlane) :
    realComponent w hw p * realImage hw (sectionAt hw z)
      = ((realPoint hw p * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Units.val_mul, coe_realPoint, realImage_sectionAt]

private theorem exists_forall_theForm_mul_adelicArchGLInclAt_eq (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (w : InfinitePlace K) (p : AdelicGL2 (𝓞 K) K) :
    ∃ p' : AdelicGL2 (𝓞 K) K, ∀ k : GL (Fin 2) w.Completion,
      theForm d archR archC dR dC dF (p * adelicArchGLInclAt K w k)
        = jlSeries' d archR archC dR dC dF (p' * adelicArchGLInclAt K w k) := by
  obtain ⟨γ, hγ⟩ := kZeroSet_meets S d.m p
  refine ⟨globalPoints (𝓞 K) K γ * p, fun k => ?_⟩
  have hmem : globalPoints (𝓞 K) K γ * p * adelicArchGLInclAt K w k ∈ kZeroSet S d.m :=
    (mul_adelicArchGLInclAt_mem_kZeroSet_iff d.m w k _).mpr hγ
  have hinv' : InvOn (kZeroSet S d.m) (jlSeries' d archR archC dR dC dF) := hinv
  rw [theForm_eq, ← extend_mul_left hinv' γ, ← mul_assoc, extend_apply_of_mem hinv' hmem]

private theorem differentiableOn_descent {P : RealArchParam} (D : ArchDatumR P)
    (hhol : ∀ x : GL (Fin 2) ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      fun z : UpperHalfPlane =>
        ((z.im : ℝ) : ℂ)⁻¹ * D.W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (x : GL (Fin 2) ℝ) :
    DifferentiableOn ℂ
      ((fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ * D.W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
        ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp (hhol x)

private theorem norm_halfDet_mul_adelicArchGLInclAt_sectionAt {w : InfinitePlace K} (hw : w.IsReal)
    (q : AdelicGL2 (𝓞 K) K) (z : UpperHalfPlane) :
    ‖halfDet (q * adelicArchGLInclAt K w (sectionAt hw z))‖ = ‖halfDet q‖ * Real.sqrt z.im := by
  rw [halfDet_mul_adelicArchGLInclAt_of_isReal hw, norm_mul, Complex.norm_real, abs_det_realImage_sectionAt,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem mdifferentiable_halfDet_mul_jlSeries'_sectionAt (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hbridge : ∀ g : AdelicGL2 (𝓞 K) K,
      jlSeries' d archR archC dR dC dF g = ∑' α : Kˣ, seriesTerm d archR archC dR dC dF g α)
    (hmaj : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ V ∈ 𝓝 g₀, ∃ b : Kˣ → ℝ, Summable b ∧ (∀ α, 0 ≤ b α) ∧
      ∀ g ∈ V, ∀ α : Kˣ, ‖seriesTerm d archR archC dR dC dF g α‖ ≤ b α)
    {w : InfinitePlace K} (hw : w.IsReal)
    (hhol : ∀ x : GL (Fin 2) ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      fun z : UpperHalfPlane =>
        ((z.im : ℝ) : ℂ)⁻¹ * (dR w hw).W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (q : AdelicGL2 (𝓞 K) K) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * (halfDet (q * adelicArchGLInclAt K w (sectionAt hw z))
        * jlSeries' d archR archC dR dC dF (q * adelicArchGLInclAt K w (sectionAt hw z))) := by
  choose C hC using fun α => exists_halfDet_mul_seriesTerm_mul_adelicArchGLInclAt_eq d archR archC dR dC dF hw q α

  set G : Kˣ → UpperHalfPlane → ℂ := fun α z => ((z.im : ℝ) : ℂ)⁻¹
    * (dR w hw).W ((realPoint hw (globalPoints (𝓞 K) K (diagOne α) * q) * iwasawaSectionGL z : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) with hG

  have hterm : ∀ (α : Kˣ) (z : UpperHalfPlane), C α * G α z = ((z.im : ℝ) : ℂ)⁻¹
      * (halfDet (q * adelicArchGLInclAt K w (sectionAt hw z))
        * seriesTerm d archR archC dR dC dF (q * adelicArchGLInclAt K w (sectionAt hw z)) α) := by
    intro α z
    rw [hC α (sectionAt hw z), realComponent_mul_realImage_sectionAt, hG]
    ring
  have hfun : (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * (halfDet (q * adelicArchGLInclAt K w (sectionAt hw z))
      * jlSeries' d archR archC dR dC dF (q * adelicArchGLInclAt K w (sectionAt hw z))))
      = fun z => ∑' α : Kˣ, C α * G α z := by
    funext z
    rw [hbridge, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun α => (hterm α z).symm
  rw [hfun]
  intro ζ₀
  rw [UpperHalfPlane.mdifferentiableAt_iff]

  obtain ⟨V, hV, b, hb, -, hle'⟩ := hmaj (q * adelicArchGLInclAt K w (sectionAt hw ζ₀))
  obtain ⟨V', hV'V, hV'o, hζ₀V'⟩ := mem_nhds_iff.mp hV

  set W : Set UpperHalfPlane :=
    {z | q * adelicArchGLInclAt K w (sectionAt hw z) ∈ V'} ∩ {z | ζ₀.im / 2 < z.im} with hW
  have hWo : IsOpen W :=
    ((continuous_sectionAt hw q).isOpen_preimage V' hV'o).inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im)
  have hζ₀W : ζ₀ ∈ W := ⟨hζ₀V', half_lt_self ζ₀.im_pos⟩
  set U : Set ℂ := ((↑) : UpperHalfPlane → ℂ) '' W with hU
  have hUo : IsOpen U := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap W hWo
  have hζ₀U : (ζ₀ : ℂ) ∈ U := ⟨ζ₀, hζ₀W, rfl⟩

  have hy₁ : 0 < ζ₀.im / 2 := half_pos ζ₀.im_pos
  have hsum : Summable fun α : Kˣ => (Real.sqrt (ζ₀.im / 2))⁻¹ * ‖halfDet q‖ * b α := hb.mul_left _
  have hbound : ∀ (α : Kˣ) (x : ℂ), x ∈ U →
      ‖((fun z : UpperHalfPlane => C α * G α z) ∘ UpperHalfPlane.ofComplex) x‖
        ≤ (Real.sqrt (ζ₀.im / 2))⁻¹ * ‖halfDet q‖ * b α := by
    rintro α x ⟨ζ, ⟨hζV', hζim⟩, rfl⟩
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply, hterm, norm_mul, norm_mul,
      norm_halfDet_mul_adelicArchGLInclAt_sectionAt, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ζ.im_pos]
    have hsζ : 0 < Real.sqrt ζ.im := Real.sqrt_pos.mpr ζ.im_pos
    have hkey : (ζ.im)⁻¹ * (Real.sqrt ζ.im) = (Real.sqrt ζ.im)⁻¹ := by
      have h := Real.mul_self_sqrt ζ.im_pos.le
      field_simp
      linarith [h]
    have hmono : (Real.sqrt ζ.im)⁻¹ ≤ (Real.sqrt (ζ₀.im / 2))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hy₁) (Real.sqrt_le_sqrt hζim.le)
    have hb' := hle' _ (hV'V hζV') α
    calc (ζ.im)⁻¹ * (‖halfDet q‖ * Real.sqrt ζ.im * ‖seriesTerm d archR archC dR dC dF
            (q * adelicArchGLInclAt K w (sectionAt hw ζ)) α‖)
        = ((ζ.im)⁻¹ * Real.sqrt ζ.im) * ‖halfDet q‖ * ‖seriesTerm d archR archC dR dC dF
            (q * adelicArchGLInclAt K w (sectionAt hw ζ)) α‖ := by ring
      _ = (Real.sqrt ζ.im)⁻¹ * ‖halfDet q‖ * ‖seriesTerm d archR archC dR dC dF
            (q * adelicArchGLInclAt K w (sectionAt hw ζ)) α‖ := by rw [hkey]
      _ ≤ (Real.sqrt (ζ₀.im / 2))⁻¹ * ‖halfDet q‖ * b α := by
            gcongr

  have hdiff : ∀ α : Kˣ,
      DifferentiableOn ℂ ((fun z : UpperHalfPlane => C α * G α z) ∘ UpperHalfPlane.ofComplex) U := by
    intro α
    have h₁ := (differentiableOn_descent (dR w hw) hhol (realPoint hw (globalPoints (𝓞 K) K (diagOne α) * q))).mono
      (show U ⊆ {x : ℂ | 0 < x.im} by rintro _ ⟨ζ, -, rfl⟩; exact ζ.im_pos)
    exact h₁.const_mul (C α)
  have hU_diff : DifferentiableOn ℂ
      (fun x : ℂ => ∑' α : Kˣ, ((fun z : UpperHalfPlane => C α * G α z) ∘ UpperHalfPlane.ofComplex) x) U :=
    Complex.differentiableOn_tsum_of_summable_norm hsum hdiff hUo hbound
  exact hU_diff.differentiableAt (hUo.mem_nhds hζ₀U)

private theorem isArchHolomorphicAt_translateSum_halfDet_of_isJLNice (Pi : HeckeEigensystem K ℂ)
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
    (hhol : ∀ (w : InfinitePlace K) (hw : w.IsReal) (x : GL (Fin 2) ℝ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            (dR w hw).W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) (hks : ∀ i, ks i ∈ finiteAdelicGL2Subgroup K)
    (cs : Fin n → ℂ)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (w : InfinitePlace K) (hw : w.IsReal) :
    IsArchHolomorphicAt w hw fun g => translateSum d archR archC dR dC dF ks cs g * halfDet g := by
  intro g

  choose p hp using fun i =>
    exists_forall_theForm_mul_adelicArchGLInclAt_eq d archR archC dR dC dF hinv w (g * ks i)
  have hcomm : ∀ (i : Fin n) (k : GL (Fin 2) w.Completion),
      g * adelicArchGLInclAt K w k * ks i = g * ks i * adelicArchGLInclAt K w k := by
    intro i k
    have hi : glArch (𝓞 K) K (ks i) = 1 := (mem_finiteAdelicGL2Subgroup_iff K (ks i)).mp (hks i)
    rw [mul_assoc, adelicArchGLInclAt_mul_of_glArch_eq_one hi, ← mul_assoc]

  have hfun : (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹
        * (translateSum d archR archC dR dC dF ks cs (g * adelicArchGLInclAt K w (sectionAt hw z))
          * halfDet (g * adelicArchGLInclAt K w (sectionAt hw z))))
      = fun z => ∑ i, (cs i * (halfDet g * (halfDet (p i))⁻¹)) * (((z.im : ℝ) : ℂ)⁻¹
          * (halfDet (p i * adelicArchGLInclAt K w (sectionAt hw z))
            * jlSeries' d archR archC dR dC dF (p i * adelicArchGLInclAt K w (sectionAt hw z)))) := by
    funext z
    simp only [translateSum]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomm, hp i, halfDet_mul_adelicArchGLInclAt_of_isReal hw g, halfDet_mul_adelicArchGLInclAt_of_isReal hw (p i)]
    have hpi : halfDet (p i) ≠ 0 := halfDet_ne_zero (p i)
    field_simp
  show MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
    ((z.im : ℝ) : ℂ)⁻¹ * (translateSum d archR archC dR dC dF ks cs (g * adelicArchGLInclAt K w (sectionAt hw z))
      * halfDet (g * adelicArchGLInclAt K w (sectionAt hw z)))
  rw [hfun, UpperHalfPlane.mdifferentiable_iff]

  have R := exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice K Pi S archR archC epsS ω
    hω hωb d dR dC dF hnice
  have hbridge : ∀ g : AdelicGL2 (𝓞 K) K,
      jlSeries' d archR archC dR dC dF g = ∑' α : Kˣ, seriesTerm d archR archC dR dC dF g α := R.1
  have hmaj : ∀ g₀ : AdelicGL2 (𝓞 K) K, ∃ V ∈ 𝓝 g₀, ∃ b : Kˣ → ℝ, Summable b ∧ (∀ α, 0 ≤ b α) ∧
      ∀ g ∈ V, ∀ α : Kˣ, ‖seriesTerm d archR archC dR dC dF g α‖ ≤ b α := fun g₀ =>
    R.2.2.2.1 d.a (d.bounded.imp fun _ h α => (h α).1) (fun α h => (d.floor α h).1) id continuous_id g₀
  have hi : ∀ i : Fin n, DifferentiableOn ℂ ((fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹
      * (halfDet (p i * adelicArchGLInclAt K w (sectionAt hw z))
        * jlSeries' d archR archC dR dC dF (p i * adelicArchGLInclAt K w (sectionAt hw z))))
          ∘ UpperHalfPlane.ofComplex) {x : ℂ | 0 < x.im} := fun i =>
    UpperHalfPlane.mdifferentiable_iff.mp
      (mdifferentiable_halfDet_mul_jlSeries'_sectionAt d archR archC dR dC dF hbridge hmaj hw (hhol w hw) (p i))
  have heq : ((fun z : UpperHalfPlane => ∑ i, (cs i * (halfDet g * (halfDet (p i))⁻¹)) * (((z.im : ℝ) : ℂ)⁻¹
        * (halfDet (p i * adelicArchGLInclAt K w (sectionAt hw z))
          * jlSeries' d archR archC dR dC dF (p i * adelicArchGLInclAt K w (sectionAt hw z)))))
        ∘ UpperHalfPlane.ofComplex)
      = fun x : ℂ => ∑ i, (cs i * (halfDet g * (halfDet (p i))⁻¹)) * (((fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹
          * (halfDet (p i * adelicArchGLInclAt K w (sectionAt hw z))
            * jlSeries' d archR archC dR dC dF (p i * adelicArchGLInclAt K w (sectionAt hw z))))
              ∘ UpperHalfPlane.ofComplex) x) := by
    funext x
    simp only [Function.comp_apply]
  rw [heq]
  exact DifferentiableOn.fun_sum fun i _ => (hi i).const_mul _

end HolomorphyFill

end LanglandsTunnell.Converse.CuspSynthesis

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.TateGlobal
p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse"

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell _root_.LanglandsTunnell.Converse _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse _root_.LanglandsTunnell.Converse.CuspSynthesis _root_.P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.LanglandsTunnell.Converse.CuspSynthesis in

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
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (hhol : ∀ (w : InfinitePlace K) (hw : w.IsReal) (x : GL (Fin 2) ℝ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            (dR w hw).W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) (hks : ∀ i, ks i ∈ finiteAdelicGL2Subgroup K)
    (cs : Fin n → ℂ)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (w : InfinitePlace K) (hw : w.IsReal) :
    IsArchHolomorphicAt w hw fun g =>
      translateSum d archR archC dR dC dF ks cs g *
        (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
  LanglandsTunnell.Converse.CuspSynthesis.isArchHolomorphicAt_translateSum_halfDet_of_isJLNice Pi S archR archC epsS ω hω hωb
    d dR dC dF hnice hhol ks hks cs hinv w hw

end S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet
end P2MW
export P2MW.S_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet (solution)
