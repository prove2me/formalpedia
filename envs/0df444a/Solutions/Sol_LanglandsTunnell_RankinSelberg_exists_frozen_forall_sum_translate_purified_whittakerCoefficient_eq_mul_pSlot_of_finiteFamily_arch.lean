-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/dbca1e27-bc05-5497-97a3-bfbf5018b97b

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import Theorems.Thm_AutomorphicForm_exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_twist_det_package
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_sigmaCentralizer_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply"

section SecCubicSide

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"

namespace Ws23B

structure CubicSide (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))) where
  form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ
  whittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ
  whittakerLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ
  whittakerArch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ
  dualWhittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ
  automorphic : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g
  form_continuous : Continuous form
  whittaker_continuous : Continuous whittaker
  dualWhittaker_continuous : Continuous dualWhittaker
  whittaker_gauge : IsGaugeMajorised3 ℚ whittaker
  dualWhittaker_gauge : IsGaugeMajorised3 ℚ dualWhittaker
  whittaker_law : IsGL3PsiWhittakerFn ψ whittaker
  dualWhittaker_law : IsGL3PsiWhittakerFn ψ⁻¹ dualWhittaker
  expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => whittaker (mirabolicTranslate i * g)) (form g)
  dual_expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => dualWhittaker (mirabolicTranslate i * g)) (dualForm form g)
  whittakerLoc_law : ∀ v, IsGL3PsiWhittakerFn (psiLoc ψ v) (whittakerLoc v)
  factorizable : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
    (∀ v, IsBadPlace K μ v → v ∈ T) →
    (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
    whittaker g = whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
      ∏ v ∈ T, whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v g)
  spherical : ∀ v, ¬ IsBadPlace K μ v →
    IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (whittakerLoc v)
  levelInvariant : ∀ v, v ∉ Sχ → ¬ IsRamifiedIn K v →
    ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, whittakerLoc v (g * k) = whittakerLoc v g
  dualWhittaker_eq : dualWhittaker = dualWhittakerFn3 whittaker
  dual_factorizable : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
    (∀ v, IsBadPlace K μ v → v ∈ T) →
    (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
    dualWhittaker g = dualWhittakerFn3 whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
      ∏ v ∈ T, dualWhittakerFn3 (whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v g)

end Ws23B

end SecCubicSide

section SecJ6Kit

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open scoped nonZeroDivisors

section Ws23ArchFSupply

open IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace Ws23ArchF

end Ws23ArchF

end

end Ws23ArchFSupply

section Ws23BCubicSide

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"

namespace Ws23B

end Ws23B

namespace Ws23B
variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)} {U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)}
  {gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ}
  (F : LanglandsTunnell.CubicInduction.CubicInductionForm K
    (AutomorphicForm.productionPinsOf ℚ D U gen (NumberField.AdelicBox.adelicBox ℚ)) ψ μ)
  (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
  (hFg : LanglandsTunnell.CubicInduction.IsGaugeMajorised3 ℚ F.whittaker)
  (hFdg : LanglandsTunnell.CubicInduction.IsGaugeMajorised3 ℚ F.dualWhittaker)
  (Sχ : Finset (HeightOneSpectrum (𝓞 ℚ)))
end Ws23B

end Ws23BCubicSide

section Ws23FactFSupply

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23FactF

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

section Factors

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))}

variable {K}

end Factors

end Ws23FactF

end

end Ws23FactFSupply

section Ws23DetNormSupply

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel NumberField.AdelicVolume

noncomputable section

namespace Ws23FactF

end Ws23FactF

end

end Ws23DetNormSupply

section Ws23FactFDualSupply

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23FactF

section DualFactors

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))}

variable {K}

end DualFactors

end Ws23FactF

end

end Ws23FactFDualSupply

section Ws23FactFTranslateSupply

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23FactF

section TranslateFactors

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))}

end TranslateFactors

end Ws23FactF

end

end Ws23FactFTranslateSupply

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.InfinitePlace.Completion
open scoped Matrix

noncomputable section

namespace Ws23ArchN

abbrev hR : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _

abbrev A (h : GL (Fin 2) ℝ) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt hR h))

end Ws23ArchN

end

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.InfinitePlace.Completion
open scoped Matrix

noncomputable section

namespace Ws23ArchM

abbrev hR : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _
abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hR

abbrev Φ : GL (Fin 2) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  (archComponent3 (𝓞 ℚ) ℚ).comp ((iota (𝓞 ℚ) ℚ).comp ιR)

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = default := Subsingleton.elim _ _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl := infinitePlace_eq v
  show archMatrixUpdate ℚ default ((glEquivOfRingEquiv (ringEquivRealOfIsReal hR).symm M :
    GL (Fin 2) (default : InfinitePlace ℚ).Completion) : Matrix _ _ _) i j default = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

end Ws23ArchM

end

section Ws23FactPhiDualSupply

p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws23FactPhiDual

open Matrix MeasureTheory NumberField.InfinitePlace.Completion

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev w0 : InfinitePlace ℚ := default
theorem hw0 : (w0).IsReal := IsTotallyReal.isReal _
abbrev eR : (w0).Completion ≃+* ℝ := ringEquivRealOfIsReal hw0
abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hw0

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = w0 := Subsingleton.elim _ _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl := infinitePlace_eq v
  show archMatrixUpdate ℚ w0 ((glEquivOfRingEquiv (eR).symm M : GL (Fin 2) (w0).Completion) : Matrix _ _ _) i j w0 = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem iotaR_snd (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := rfl

abbrev fstM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
abbrev sndM (g : G2) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)

theorem fstM_mul (g h : G2) : fstM (g * h) = fstM g * fstM h := (RingHom.mapMatrix _).map_mul _ _
theorem sndM_mul (g h : G2) : sndM (g * h) = sndM g * sndM h := (RingHom.mapMatrix _).map_mul _ _

theorem eq_of_fstM_sndM {g h : G2} (h1 : fstM g = fstM h) (h2 : sndM g = sndM h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem fstM_eq_one_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : fstM g = 1 := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) hg

theorem sndM_iotaR (M : GL (Fin 2) ℝ) : sndM (ιR M) = 1 := Matrix.ext fun i j => iotaR_snd M i j

theorem iotaR_mul_comm {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) : ιR M * g = g * ιR M := by
  refine eq_of_fstM_sndM ?_ ?_
  · rw [fstM_mul, fstM_mul, fstM_eq_one_of_mem hg, mul_one, one_mul]
  · rw [sndM_mul, sndM_mul, sndM_iotaR, mul_one, one_mul]

theorem ratArchGL2_apply (g : G2) (i j : Fin 2) :
    ((ratArchGL2 g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = eR (((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0) := rfl

theorem ratArchGL2_mul (g h : G2) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_mul, map_mul, map_mul]

theorem ratArchGL2_inv (g : G2) : ratArchGL2 g⁻¹ = (ratArchGL2 g)⁻¹ := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_inv, map_inv, map_inv]

theorem ratArchGL2_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

theorem coe_finFactor (g : G2) : (RSCarrier.finFactor g : G2) = (ιR (ratArchGL2 g))⁻¹ * g := rfl

local notation "T" => transposeInvN (Fin 2)

theorem T_apply (g : G2) (i j : Fin 2) :
    ((T g : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j = ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸) j i := rfl

theorem ratArchGL2_T (g : G2) : ratArchGL2 (T g) = RSCarrier.transposeInv (ratArchGL2 g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [ratArchGL2_apply, T_apply]
  show _ = (((ratArchGL2 g)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) j i
  rw [← ratArchGL2_inv, ratArchGL2_apply]

theorem T_iotaR (M : GL (Fin 2) ℝ) : T (ιR M) = ιR (RSCarrier.transposeInv M) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun v => ?_) ?_)
  · rw [iotaR_fst]
    show ((((ιR M)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸) j i).1 v = _
    rw [← map_inv, iotaR_fst]
    rfl
  · rw [iotaR_snd]
    show ((((ιR M)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸) j i).2 = _
    rw [← map_inv, iotaR_snd, ← Matrix.transpose_apply (1 : Matrix (Fin 2) (Fin 2) _) i j, Matrix.transpose_one]

def w₁ : GL (Fin 2) ℚ := ⟨!![0, -1; 1, 0], !![0, 1; -1, 0],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def w₁inv : GL (Fin 2) ℚ := ⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def dm : GL (Fin 2) ℚ := ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def w₀ : GL (Fin 2) ℚ := dm * w₁

def w₀R : GL (Fin 2) ℝ := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem w₀_val : ((w₀ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0] := by
  show (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, -1; 1, 0] = _
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((globalPoints (𝓞 ℚ) ℚ γ : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j = algebraMap ℚ 𝔸 ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

theorem ratArchGL2_w₀ : ratArchGL2 (globalPoints (𝓞 ℚ) ℚ w₀) = w₀R := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [ratArchGL2_apply, globalPoints_apply, w₀_val]
  fin_cases i <;> fin_cases j
  · show eR ((algebraMap ℚ 𝔸 0).1 w0) = 0
    rw [map_zero]; exact map_zero _
  · show eR ((algebraMap ℚ 𝔸 1).1 w0) = 1
    rw [map_one]; exact map_one _
  · show eR ((algebraMap ℚ 𝔸 1).1 w0) = 1
    rw [map_one]; exact map_one _
  · show eR ((algebraMap ℚ 𝔸 0).1 w0) = 0
    rw [map_zero]; exact map_zero _

theorem T_unipotentGL2 (x : 𝔸) :
    T (unipotentGL2 x) = globalPoints (𝓞 ℚ) ℚ w₁inv * unipotentGL2 x * globalPoints (𝓞 ℚ) ℚ w₁ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [T_apply]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, globalPoints_apply, unipotentGL2]
  fin_cases i <;> fin_cases j <;> simp [w₁, w₁inv]

theorem dm_mul_unipotentGL2 (x : 𝔸) :
    globalPoints (𝓞 ℚ) ℚ dm * unipotentGL2 x = unipotentGL2 (-x) * globalPoints (𝓞 ℚ) ℚ dm := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, globalPoints_apply, unipotentGL2]
  fin_cases i <;> fin_cases j <;> simp [dm]

abbrev pinsQ (D : Set G2) : CarrierPins ℚ :=
  productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

theorem W_apply (D : Set G2) (χ : AddChar 𝔸 ℂ) (f : G2 → ℂ) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ f 1 g = ∫ x, f (unipotentGL2 x * g) * χ (-x)
      ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  show (∫ x, f (unipotentGL2 x * g) * χ (-(algebraMap ℚ 𝔸 1 * x)) ∂(ProbabilityTheory.cond μA (adelicBox ℚ))) = _
  congr 1; funext x; rw [map_one, one_mul]

theorem globalPoints_unipotentGL2 (q : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 q) = unipotentGL2 (algebraMap ℚ 𝔸 q) := by
  refine Units.ext ?_
  change (algebraMap ℚ 𝔸).mapMatrix ((unipotentGL2 q : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
  rw [unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

scoped instance isAddHaarMeasure_adelicAddHaar' : (μA).IsAddHaarMeasure :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

scoped instance regular_adelicAddHaar' : (μA).Regular := by
  show (Measure.addHaarMeasure _).Regular
  exact Measure.regular_addHaarMeasure

scoped instance countable_principalSubgroup' : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  show Countable {x : 𝔸 // x ∈ Set.range (algebraMap ℚ 𝔸)}
  exact (Set.countable_range _).to_subtype

theorem integral_cond_adelicBox_comp_neg (P : 𝔸 → ℂ)
    (hP : ∀ (k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸), P ((k : 𝔸) + x) = P x) :
    ∫ x, P (-x) ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) = ∫ x, P x ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  have hcond : ProbabilityTheory.cond μA (adelicBox ℚ) = ((μA) (adelicBox ℚ))⁻¹ • (μA).restrict (adelicBox ℚ) := rfl
  rw [hcond, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [← (Measure.measurePreserving_neg (μA)).setIntegral_image_emb (MeasurableEquiv.neg 𝔸).measurableEmbedding P
    (adelicBox ℚ)]
  have hbox := isAddFundamentalDomain_adelicBox ℚ (μA)
  have himg : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) ((fun x : 𝔸 => -x) '' adelicBox ℚ) μA := by
    refine hbox.image_of_equiv (ν := μA) (Equiv.neg 𝔸)
      (by simpa using (Measure.measurePreserving_neg (μA)).quasiMeasurePreserving)
      (Equiv.neg (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
    intro k x
    show -((((-k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) : 𝔸) + x) = (k : 𝔸) + -x
    rw [AddSubgroup.coe_neg, neg_add, neg_neg]
  exact MeasureTheory.IsAddFundamentalDomain.setIntegral_eq himg hbox (f := P) (fun k x => hP k x)

theorem transposeInv_one : RSCarrier.transposeInv (1 : GL (Fin 2) ℝ) = 1 :=
  Units.ext (by simp [RSCarrier.transposeInv])

section Main

variable {D : Set G2} {ψ : AddChar 𝔸 ℂ} {φ : G2 → ℂ}

end Main

end Ws23FactPhiDual
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end Ws23FactPhiDualSupply
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section Ws23MiniPlaceKit

p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"

noncomputable section

namespace Ws23HeckeLocalDual

open Matrix Ws23FactPhiDual NumberField.AdelicVolume UnramifiedWhittaker

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

abbrev Kp : Type := p.adicCompletion ℚ

theorem placeEmbed_eq (x : GL (Fin 2) (Kp p)) :
    placeEmbed ℚ p x = AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x) := rfl

theorem placeEmbed_mem_fin (x : GL (Fin 2) (Kp p)) : placeEmbed ℚ p x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff, placeEmbed_eq, AdelicDock.glArch_finEmbed]

abbrev archM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
abbrev finM (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
    ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸))

theorem eq_of_components {g h : G2} (ha : archM g = archM h) (hf : ∀ w, finM w g = finM w h) : g = h :=
  Units.ext (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ha
    (AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ hf))

theorem archM_placeEmbed (x : GL (Fin 2) (Kp p)) : archM (placeEmbed ℚ p x) = 1 := by
  show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix _ = 1
  rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_arch_finMat]

theorem finM_placeEmbed_self (x : GL (Fin 2) (Kp p)) : finM p (placeEmbed ℚ p x) = x := by
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix _) = _
  rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed,
    AdelicDock.mapMatrix_localMat_self]

theorem finM_placeEmbed_of_ne (x : GL (Fin 2) (Kp p)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ p) :
    finM w (placeEmbed ℚ p x) = 1 := by
  show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix _) = _
  rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed,
    AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hw]

end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end Ws23HeckeLocalDual
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end Ws23MiniPlaceKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section Ws23HmuCentral

noncomputable section

namespace Ws23HeckeLocalDual

open Matrix Ws23FactPhiDual UnramifiedWhittaker

end Ws23HeckeLocalDual
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end Ws23HmuCentral
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section prover2_prefactor

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.Converse"
p2m_open "UnramifiedWhittaker AutomorphicForm~globalPoints_apply"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.psiLoc CubicInduction.CubicInductionForm Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt RealArchParam signShift RealArchParam.discrete RealArchParam.principal CubicInduction.IsGaugeMajorised3 ratArchGL2 CubicInduction.CubicInductionForm.twist_det_package CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre inducedE1 inducedE2 inducedE3"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section NormAlgebra
variable {G : Type*} [Group G] (ν : G → ℝ) (hmul : ∀ a b, ν (a * b) = ν a * ν b) (hone : ν 1 = 1) (hpos : ∀ a, 0 < ν a)
end NormAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Fibre
variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

end Fibre
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end prover2_prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section prover2_hmu_localAt

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.Converse"
p2m_open "UnramifiedWhittaker AutomorphicForm~globalPoints_apply"

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.psiLoc CubicInduction.CubicInductionForm Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt RealArchParam signShift RealArchParam.discrete RealArchParam.principal CubicInduction.IsGaugeMajorised3 ratArchGL2 CubicInduction.CubicInductionForm.twist_det_package CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre inducedE1 inducedE2 inducedE3"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

theorem localAt_placeEmbed_self (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    localAt ℚ p (placeEmbed ℚ p x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

section Hmu

open scoped Classical

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
        ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)

end Hmu
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end prover2_hmu_localAt
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section prover2_hlev

open IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.psiLoc CubicInduction.CubicInductionForm Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt RealArchParam signShift RealArchParam.discrete RealArchParam.principal CubicInduction.IsGaugeMajorised3 ratArchGL2 CubicInduction.CubicInductionForm.twist_det_package CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre inducedE1 inducedE2 inducedE3"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end prover2_hlev
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section Ws23TranslateHeckeHelpers

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23TH

private theorem _root_.Ws23TH.ratArchGL2_mul (g k : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * k) = ratArchGL2 g * ratArchGL2 k := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, map_mul, map_mul]

p2m_export "Ws23TH" "ratArchGL2_mul"
end Ws23TH
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end Ws23TranslateHeckeHelpers
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.psiLoc CubicInduction.CubicInductionForm Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt RealArchParam signShift RealArchParam.discrete RealArchParam.principal CubicInduction.IsGaugeMajorised3 ratArchGL2 CubicInduction.CubicInductionForm.twist_det_package CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre inducedE1 inducedE2 inducedE3"
namespace EntirePairAssembly
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

p2m_open "LanglandsTunnell.CubicInduction AutomorphicForm~globalPoints_apply MeasureTheory"

section prover2_psi_bridge

end prover2_psi_bridge
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

noncomputable section prover2_uniformizerNorm

section NormAlgebra

variable {G : Type*} [Group G] (ν : G → ℝ) (hmul : ∀ a b, ν (a * b) = ν a * ν b) (hone : ν 1 = 1) (hpos : ∀ a, 0 < ν a)

end NormAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

variable (v : HeightOneSpectrum (𝓞 ℚ))

end prover2_uniformizerNorm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section orth_tables
open IsDedekindDomain NumberField Filter Topology

section RankinSelbergTables

variable (F : Type*) [Field F] [NumberField F] {K : Type*} [Field K] [Algebra (𝓞 F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

end RankinSelbergTables
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end orth_tables
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section prover2_psi
open IsDedekindDomain NumberField

end prover2_psi
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section prover2_dual
p2m_open "Complex IsDedekindDomain NumberField MeasureTheory AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"
open scoped Matrix

theorem detNorm_pos' (g : AdelicGL2 (𝓞 ℚ) ℚ) : 0 < detNorm g := NumberField.TateGlobal.ideleNorm_pos _

theorem detNorm_globalPoints_mul' (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    detNorm (globalPoints (𝓞 ℚ) ℚ γ * g) = detNorm g := by
  unfold detNorm
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))).matrix_transpose
  · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))).matrix_transpose

theorem continuous_detNorm' : Continuous (detNorm : AdelicGL2 (𝓞 ℚ) ℚ → ℝ) :=
  NumberField.TateGlobal.continuous_ideleNorm_det ℚ

end prover2_dual
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section prover2_meas_ninv
p2m_open "IsDedekindDomain NumberField MeasureTheory AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"
open Matrix
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

scoped instance isAddHaarMeasure_adelicAddHaar'' : (μA).IsAddHaarMeasure :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

scoped instance countable_principalSubgroup' : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  show Countable {x : 𝔸 // x ∈ Set.range (algebraMap ℚ 𝔸)}
  exact (Set.countable_range _).to_subtype

scoped instance vaddInvariantMeasure_principalSubgroup' :
    VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) 𝔸 μA :=
  ⟨fun k s _ => measure_preimage_add _ (k : 𝔸) s⟩

end prover2_meas_ninv
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

section orth_phiBound
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm~globalPoints_apply AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
open AutomorphicForm.CuspidalConstituent

theorem supply_phiBound
    (Φ : HeckeEigensystem ℚ ℂ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p ∉ SQ, ‖Φ.b p‖ = 1)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Ψ : HeckeEigensystem ℚ ℂ)
    (tys : ArchTypeFamily ℚ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar N S Ψ φ)
    (htys : φ ∈ archCutSubmodule ℚ tys) :
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ‖φ g‖ * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-(1 / 2 : ℝ)) ≤ C := by

  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hd : (1 / 2 : ℝ) < 2 := by norm_num
  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1 / 2 : ℝ) 1 (1 / 2) 2) :=
    coversModCentre_productionPinsGeneral_D_rat

  have hξ : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ z ^ (1 : ℝ) := fun z => by
    rw [Real.rpow_one]
    exact SmoothCuspRealizationAt.norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one ℚ _ _ Φ R hRc SQ hb
      ⟨z, Subgroup.mem_top z⟩

  have hmem : φ ∈ isotypicCuspSubmodule ℚ (productionPinsGeneral ℚ) R.centralChar N S Ψ :=
    hiso.mem_isotypicCuspSubmodule
  have hlev : φ ∈ levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N := hiso.level_invariant

  obtain ⟨𝒱, h𝒱, hdom⟩ := exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets ℚ (1 / 2 : ℝ) 1 (1 / 2) 2
    (classRepTranslates ℚ) hd hcov R.centralChar N hN S Ψ
  have hsup : φ ∈ ⨆ W ∈ 𝒱, W := by
    have h1 := isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent ℚ (1 / 2 : ℝ) 1 (1 / 2) 2
      (classRepTranslates ℚ) hd hcov R.centralChar N S tys Ψ (Submodule.mem_inf.mpr ⟨hmem, htys⟩)
    exact (iSup₂_le fun V hV => hdom V hV.1 hV.2.1) h1
  have hcut : φ ∈ ⨆ V ∈ 𝒱,
      (V ⊓ levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓ archCutSubmodule ℚ tys) :=
    iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le ℚ _ R.centralChar N tys 𝒱
      (fun V hV => (h𝒱 V hV).1) (Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hsup, hlev⟩, htys⟩)
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hcut

  have hM : ∀ V ∈ 𝒱, ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ‖(μ V : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) g‖ ≤
        M * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ ((1 : ℝ) / 2) := by
    intro V hV
    exact exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent ℚ (1 / 2 : ℝ) 1 (1 / 2) 2
      (classRepTranslates ℚ) hc hc hd hcov R.centralChar N hN tys V (h𝒱 V hV) (μ V) (μ V).2 1 hξ
  choose! M hM using hM
  refine ⟨∑ V ∈ 𝒱, max (M V) 0, fun g => ?_⟩
  set n : ℝ := TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) with hn
  have hn0 : 0 < n := TateGlobal.ideleNorm_pos _
  have hφg : φ g = ∑ V ∈ 𝒱, (μ V : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) g := by
    rw [← hμ, Finset.sum_apply]
  have h1 : ‖φ g‖ ≤ (∑ V ∈ 𝒱, max (M V) 0) * n ^ ((1 : ℝ) / 2) := by
    rw [hφg, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun V hV => ?_)
    exact (hM V hV g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn0.le _))
  calc ‖φ g‖ * n ^ (-(1 / 2 : ℝ)) ≤ (∑ V ∈ 𝒱, max (M V) 0) * n ^ ((1 : ℝ) / 2) * n ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hn0.le _)
    _ = ∑ V ∈ 𝒱, max (M V) 0 := by
        rw [mul_assoc, ← Real.rpow_add hn0, show (1 : ℝ) / 2 + -(1 / 2 : ℝ) = 0 by norm_num, Real.rpow_zero,
          mul_one]

theorem supply_phiBound_of_hasArchCharacterAt₀
    (Φ : HeckeEigensystem ℚ ℂ) (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ p ∉ SQ, ‖Φ.b p‖ = 1)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Ψ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar N S Ψ φ)
    (k : InfinitePlace ℚ → ℤ)
    (hφarch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) :
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ‖φ g‖ * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-(1 / 2 : ℝ)) ≤ C := by
  refine supply_phiBound Φ SQ hb R hRc N hN S Ψ
    (ArchTypeFamily.ofChar ℚ fun w => archWeightCharAt (IsTotallyReal.isReal w) (k w)) φ hiso ?_
  rw [mem_archCutSubmodule_iff]
  intro w
  refine Submodule.mem_iSup_of_mem (0 : Fin 1) ?_
  exact (mem_archTypeSubmoduleAt_ofChar_iff ℚ w _ φ).mpr (hφarch w (IsTotallyReal.isReal w))

end orth_phiBound
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell"

section Ws23APrimeKit
p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory"

noncomputable section

namespace Ws23APrime

open Matrix NumberField.InfinitePlace.Completion

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev w0 : InfinitePlace ℚ := default
theorem hw0 : (w0).IsReal := IsTotallyReal.isReal _
abbrev eR : (w0).Completion ≃+* ℝ := ringEquivRealOfIsReal hw0
abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hw0

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = w0 := Subsingleton.elim _ _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl := infinitePlace_eq v
  show archMatrixUpdate ℚ w0 ((glEquivOfRingEquiv (eR).symm M : GL (Fin 2) (w0).Completion) : Matrix _ _ _) i j w0 = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem iotaR_snd (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := rfl

abbrev fstM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
abbrev sndM (g : G2) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)

theorem fstM_mul (g h : G2) : fstM (g * h) = fstM g * fstM h := (RingHom.mapMatrix _).map_mul _ _
theorem sndM_mul (g h : G2) : sndM (g * h) = sndM g * sndM h := (RingHom.mapMatrix _).map_mul _ _

theorem eq_of_fstM_sndM {g h : G2} (h1 : fstM g = fstM h) (h2 : sndM g = sndM h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem fstM_eq_one_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : fstM g = 1 := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) hg

theorem sndM_iotaR (M : GL (Fin 2) ℝ) : sndM (ιR M) = 1 := Matrix.ext fun i j => iotaR_snd M i j

theorem iotaR_mul_comm {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) : ιR M * g = g * ιR M := by
  refine eq_of_fstM_sndM ?_ ?_
  · rw [fstM_mul, fstM_mul, fstM_eq_one_of_mem hg, mul_one, one_mul]
  · rw [sndM_mul, sndM_mul, sndM_iotaR, mul_one, one_mul]

theorem ratArchGL2_apply (g : G2) (i j : Fin 2) :
    ((ratArchGL2 g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = eR (((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0) := rfl

private theorem _root_.Ws23APrime.ratArchGL2_mul (g h : G2) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_mul, map_mul, map_mul]

p2m_export "Ws23APrime" "ratArchGL2_mul"
theorem ratArchGL2_inv (g : G2) : ratArchGL2 g⁻¹ = (ratArchGL2 g)⁻¹ := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_inv, map_inv, map_inv]

private theorem _root_.Ws23APrime.ratArchGL2_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

p2m_export "Ws23APrime" "ratArchGL2_of_mem"
theorem coe_finFactor (g : G2) : (RSCarrier.finFactor g : G2) = (ιR (ratArchGL2 g))⁻¹ * g := rfl

end Ws23APrime
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23APrimeKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

namespace Ws23Glue

end Ws23Glue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23ContPrimal
open Complex LanglandsTunnell.RankinSelberg.EntirePairAssembly
namespace Ws23Glue2

end Ws23Glue2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"
end Ws23ContPrimal
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

noncomputable section
namespace Ws23V17
p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse AutomorphicForm~globalPoints_apply M4aHerbrand.GenuineDescent"

section K1
variable (F : Type) [Field F] [NumberField F]

end K1
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section K2
variable {G : Type} [CommGroup G] {M : Type} [MulOneClass M]

end K2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section K4
variable (F : Type) [Field F] [NumberField F]

end K4
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section K5
open NumberField.InfinitePlace

end K5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section K3
p2m_open "AutomorphicForm~globalPoints_apply NumberField.AdelicLevel"

end K3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23V17
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end SecJ6Kit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section SecTwistSide

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open LanglandsTunnell.CubicInduction NumberField.AdelicBox

open scoped nonZeroDivisors

noncomputable section

namespace Ws23B

def CubicSide.twist (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hν : IsAdmissibleTwist K ν)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (F : CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ ν)
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : IsAdmissibleTwist ℚ χA)
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ χA v 0 0)
    (Sχ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSχ : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsUnramifiedCharAt χA v → v ∈ Sχ)
    (hχbad : ∀ v ∈ Sχ, IsBadPlace K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v)
    (hDEQ : (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x) =
      dualWhittakerFn3 (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x))
    (hDFAC : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (∀ v, IsBadPlace K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v → v ∈ T) →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x) g =
        dualWhittakerFn3 F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
          ∏ v ∈ T, dualWhittakerFn3
            (fun y : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) *
              F.whittakerLoc v y) (componentAt3 (𝓞 ℚ) ℚ v g)) :
    CubicSide K ψ (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) Sχ :=
  let P := LanglandsTunnell.CubicInduction.CubicInductionForm.twist_det_package K _ ψ ν F χA hχA hχinf
  have hunr : ∀ v, v ∉ Sχ → IsUnramifiedCharAt χA v := fun v hv => by
    by_contra h; exact hv (hSχ v h)
  have hbadν : ∀ v, IsBadPlace K ν v → IsBadPlace K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v :=
    fun v hv => by
      by_cases h : v ∈ Sχ
      · exact hχbad v h
      · exact (LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K hdeg ν χA hχA
          v (hunr v h)).1.2 hv
  { form := fun x => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x
    whittaker := fun x => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x
    whittakerLoc := fun v y =>
      ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * F.whittakerLoc v y
    whittakerArch := F.whittakerArch
    dualWhittaker := fun x => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x
    automorphic := P.1
    whittaker_law := P.2.1
    dualWhittaker_law := P.2.2.1
    expansion := P.2.2.2.1
    dual_expansion := P.2.2.2.2.1
    form_continuous := P.2.2.2.2.2.1 hFc
    whittaker_continuous := P.2.2.2.2.2.2.1 hFw
    dualWhittaker_continuous := P.2.2.2.2.2.2.2.1 hFdw
    whittaker_gauge := P.2.2.2.2.2.2.2.2.1 hFg
    dualWhittaker_gauge := P.2.2.2.2.2.2.2.2.2.1 hFdg
    whittakerLoc_law := P.2.2.2.2.2.2.2.2.2.2.1
    factorizable := fun g T hT hg =>
      P.2.2.2.2.2.2.2.2.2.2.2 g T (fun v hv => hT v (hbadν v hv)) (fun v hv => hT v (hχbad v (hSχ v hv))) hg
    spherical := fun v hv => by
      have hvS : v ∉ Sχ := fun h => hv (hχbad v h)
      have H := LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K hdeg ν χA hχA
        v (hunr v hvS)
      exact H.2.2 (F.whittakerLoc v) (F.spherical v (fun h => hv (H.1.2 h)))
    levelInvariant := fun v hvS hram k hk g => by
      have H := LanglandsTunnell.CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt K hdeg ν hν χA hχA
        v (hunr v hvS)
      rw [H.2.1] at hk
      exact H.2.2 _ (F.whittakerLoc v) (F.levelInvariant v hram) k hk g
    dualWhittaker_eq := hDEQ
    dual_factorizable := hDFAC }

end Ws23B
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

namespace Ws23B

p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"

end Ws23B
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end SecTwistSide
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section SecTablesBFin

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
p2m_open "NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"

section Ws23TabFSupply

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23TabF

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

section Factors

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))}

variable {K}

end Factors
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabF
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabFSupply
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23TabTTLocal

open IsDedekindDomain NumberField Matrix
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg UnramifiedWhittaker"

namespace Ws23TabTT

section MatrixAlgebra

variable {A : Type*} [Field A]

end MatrixAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Valuations

variable (p : HeightOneSpectrum (𝓞 ℚ))

end Valuations
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

variable (W : LocalGL3 p → ℂ) (ψp : AddChar (p.adicCompletion ℚ) ℂ) (hlaw : IsGL3PsiWhittakerFn ψp W)
  (c : ℕ) (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p c, ∀ g, W (g * k) = W g)

variable (ϖ : p.adicCompletion ℚ) (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
  (hψ1 : ∃ r : HeightOneSpectrum.adicCompletionIntegers ℚ p, ψp ((r : p.adicCompletion ℚ) / ϖ) ≠ 1)

variable {Kf : Type} [Field Kf] [Algebra (𝓞 ℚ) (𝓞 Kf)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 Kf)]
  (cK : HeightOneSpectrum (𝓞 Kf) → ℂ) (hsph : HasSphericalTorusValuesAt cK p W)
  (hH : ℕ → ℂ) (uH : ℕ → ℕ → ℂ) (uZ : ℤ → ℤ → ℂ)
  (hh0 : hH 0 = 1) (hh1 : hH 1 = inducedE1 ℚ cK p) (hh2 : hH 2 = inducedE1 ℚ cK p ^ 2 - inducedE2 ℚ cK p)
  (hh3 : ∀ n, hH (n + 3) =
    inducedE1 ℚ cK p * hH (n + 2) - inducedE2 ℚ cK p * hH (n + 1) + inducedE3 ℚ cK p * hH n)
  (hu0 : ∀ k, uH k 0 = hH k) (hu1 : ∀ k₁ k₂, uH k₁ (k₂ + 1) = hH k₁ * hH (k₂ + 1) - hH (k₁ + 1) * hH k₂)
  (huZoff : ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0)
  (huZcone : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ k₁ k₂ = uH k₁ k₂)

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabTT
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabTTLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23TabTTAdelic

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker Ws23TabF

noncomputable section

namespace Ws23TabTT

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))}

end Ws23TabTT
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabTTAdelic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.psiLoc CubicInduction.CubicInductionForm Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt RealArchParam signShift RealArchParam.discrete RealArchParam.principal CubicInduction.IsGaugeMajorised3 ratArchGL2 CubicInduction.CubicInductionForm.twist_det_package CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre inducedE1 inducedE2 inducedE3"
namespace EntirePairAssembly
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

p2m_open "LanglandsTunnell.CubicInduction AutomorphicForm~globalPoints_apply MeasureTheory"

section prover2_psi
open IsDedekindDomain NumberField

end prover2_psi
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end SecTablesBFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section SecTablesBDual

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23TabD

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

end Ws23TabD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23TabDDualSupply

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23TabD

end Ws23TabD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabDDualSupply
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23DualTorusLocal

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction NumberField.AdelicLevel"

noncomputable section

namespace Ws23TabD

section GL3Algebra

variable {L : Type*} [Field L]

end GL3Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Local

variable (v : HeightOneSpectrum (𝓞 ℚ))

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23DualTorusLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23DualTorusTable

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction NumberField.AdelicLevel"

noncomputable section

namespace Ws23TabD

end Ws23TabD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23DualTorusTable
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23DualPeel

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23TabD

end Ws23TabD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23DualPeel
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23TransPeel

p2m_open "IsDedekindDomain NumberField Matrix AutomorphicForm~globalPoints_apply"
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg"
open NumberField.AdelicLevel NumberField.TateGlobal AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23TabD

section PeelT

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
variable {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))}

end PeelT
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabD
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TransPeel
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section OrthTT1

open IsDedekindDomain NumberField Matrix
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg UnramifiedWhittaker"

namespace Ws23TabTTd

section MatrixAlgebra

variable {A : Type*} [Field A]

end MatrixAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Valuations

variable (p : HeightOneSpectrum (𝓞 ℚ))

end Valuations
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

variable (W : LocalGL3 p → ℂ) (ψp : AddChar (p.adicCompletion ℚ) ℂ) (hlaw : IsGL3PsiWhittakerFn ψp W)
  (c : ℕ) (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p c, ∀ g, W (g * k) = W g)

variable (ϖ : p.adicCompletion ℚ) (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
  (hψ1 : ∃ r : HeightOneSpectrum.adicCompletionIntegers ℚ p, ψp ((r : p.adicCompletion ℚ) / ϖ) ≠ 1)

variable {Kf : Type} [Field Kf] [Algebra (𝓞 ℚ) (𝓞 Kf)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 Kf)]
  (cK : HeightOneSpectrum (𝓞 Kf) → ℂ) (hsph : HasSphericalTorusValuesAt cK p W)
  (hH : ℕ → ℂ) (uH : ℕ → ℕ → ℂ) (uZ : ℤ → ℤ → ℂ)
  (hh0 : hH 0 = 1) (hh1 : hH 1 = inducedE1 ℚ cK p) (hh2 : hH 2 = inducedE1 ℚ cK p ^ 2 - inducedE2 ℚ cK p)
  (hh3 : ∀ n, hH (n + 3) =
    inducedE1 ℚ cK p * hH (n + 2) - inducedE2 ℚ cK p * hH (n + 1) + inducedE3 ℚ cK p * hH n)
  (hu0 : ∀ k, uH k 0 = hH k) (hu1 : ∀ k₁ k₂, uH k₁ (k₂ + 1) = hH k₁ * hH (k₂ + 1) - hH (k₁ + 1) * hH k₂)
  (huZoff : ∀ m₁ m₂ : ℤ, (m₂ < 0 ∨ m₁ < m₂) → uZ m₁ m₂ = 0)
  (huZcone : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → uZ k₁ k₂ = uH k₁ k₂)

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23TabTTd
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end OrthTT1
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section Ws23HTTdTranslate
p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open LanglandsTunnell.TateLocal UnramifiedWhittaker

end Ws23HTTdTranslate
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end SecTablesBDual
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section SecTwistDual

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open LanglandsTunnell.CubicInduction NumberField.AdelicBox Matrix

noncomputable section

namespace Ws23B

namespace TwistDualAux

variable {A B : Type*} [CommRing A] [CommRing B]

end TwistDualAux
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

open TwistDualAux

section
variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  (hdeg : Module.finrank ℚ K = 3)
  (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
  (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
  (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
  (F : CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ ν) (hFc : Continuous F.form)
  (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : IsAdmissibleTwist ℚ χA)
  (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ χA v 0 0)
  (Sχ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSχ : ∀ v, ¬ IsUnramifiedCharAt χA v → v ∈ Sχ)
  (hχbad : ∀ v ∈ Sχ, IsBadPlace K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v)

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end Ws23B
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"
end SecTwistDual
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section SecTwistLoc

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal LanglandsTunnell.Converse
open scoped Topology

noncomputable section

namespace Ws23B

namespace TwistLocAux

variable (v : HeightOneSpectrum (𝓞 ℚ))

end TwistLocAux
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

open TwistLocAux

end Ws23B
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end SecTwistLoc
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

section SecJ6Sol

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~globalPoints_apply LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section GamPT2Sec

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace GamPT2

open Matrix Ws23FactPhiDual UnramifiedWhittaker

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ
local notation "T" => transposeInvN (Fin 2)

theorem integrable_cond_adelicBox {f : 𝔸 → ℂ} (hf : Continuous f) :
    Integrable f (ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset (K := ℚ)
  have h1 : IntegrableOn f (adelicBox ℚ) μA := (hf.continuousOn.integrableOn_compact hC).mono_set hsub
  have hcond : ProbabilityTheory.cond μA (adelicBox ℚ) = ((μA) (adelicBox ℚ))⁻¹ • (μA).restrict (adelicBox ℚ) := rfl
  rw [hcond]
  exact h1.integrable.smul_measure (ENNReal.inv_ne_top.2 (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos (K := ℚ)).ne')

theorem W_finsum (D : Set G2) (χ : AddChar 𝔸 ℂ) (hχ : Continuous χ) {n : ℕ} (c : Fin n → ℂ) (f : Fin n → G2 → ℂ)
    (hf : ∀ i, Continuous (f i)) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ (fun z => ∑ i, c i * f i z) 1 g =
      ∑ i, c i * whittakerCoefficient ℚ (pinsQ D) χ (f i) 1 g := by
  rw [W_apply]
  simp_rw [W_apply, Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  · have hc : Continuous fun y : 𝔸 => c i * f i (unipotentGL2 y * g) * χ (-y) :=
      (continuous_const.mul ((hf i).comp ((AutomorphicForm.continuous_unipotentGL2 (R := 𝔸)).mul continuous_const))).mul
        (hχ.comp continuous_neg)
    exact integrable_cond_adelicBox hc

theorem W_translate (D : Set G2) (χ : AddChar 𝔸 ℂ) (f : G2 → ℂ) (k g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ (fun z => f (z * k)) 1 g = whittakerCoefficient ℚ (pinsQ D) χ f 1 (g * k) := by
  rw [W_apply, W_apply]
  simp only [mul_assoc]

theorem W_dual_eq₀ (D : Set G2) {ψ : AddChar 𝔸 ℂ} (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ) {φ : G2 → ℂ}
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : G2), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) ψ (fun g => φ (T g)) 1 g =
      whittakerCoefficient ℚ (pinsQ D) NumberField.StandardAddChar.psiQ φ 1 (globalPoints (𝓞 ℚ) ℚ w₀ * T g) := by
  have hψ : ∀ x : 𝔸, ψ (-x) = NumberField.StandardAddChar.psiQ x := fun x => by
    rw [← AddChar.inv_apply, hψQ]
  set M : G2 := globalPoints (𝓞 ℚ) ℚ w₀ * T g with hM
  set P : 𝔸 → ℂ := fun y => φ (unipotentGL2 y * M) * NumberField.StandardAddChar.psiQ (-y) with hP
  have hPer : ∀ (q : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸), P ((q : 𝔸) + x) = P x := by
    rintro ⟨_, q, rfl⟩ x
    simp only [hP]
    rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ, neg_add, AddChar.map_add_eq_mul,
      ← map_neg, NumberField.StandardAddChar.psiQ_algebraMap, one_mul]
  have e1 : ∀ x : 𝔸, T (unipotentGL2 x * g) =
      globalPoints (𝓞 ℚ) ℚ w₁inv * (unipotentGL2 x * (globalPoints (𝓞 ℚ) ℚ w₁ * T g)) := fun x => by
    rw [transposeInvN_mul, T_unipotentGL2]; simp only [mul_assoc]
  have e2 : ∀ x : 𝔸, φ (T (unipotentGL2 x * g)) = φ (unipotentGL2 (-x) * M) := fun x => by
    rw [e1, hφ, ← hφ dm, ← mul_assoc, dm_mul_unipotentGL2, hM]
    congr 1
    show _ = unipotentGL2 (-x) * (globalPoints (𝓞 ℚ) ℚ (dm * w₁) * T g)
    rw [map_mul]; simp only [mul_assoc]
  have hpt : ∀ x : 𝔸, φ (T (unipotentGL2 x * g)) * ψ (-x) = P (-x) := fun x => by
    rw [e2, hψ]
    simp only [hP, neg_neg]
  rw [W_apply, W_apply]
  simp_rw [hpt]
  exact integral_cond_adelicBox_comp_neg P hPer

theorem w₀_mul_T_unipotentGL2 (t : 𝔸) :
    globalPoints (𝓞 ℚ) ℚ w₀ * T (unipotentGL2 t) = unipotentGL2 (-t) * globalPoints (𝓞 ℚ) ℚ w₀ := by
  have hw : w₁ * w₁inv = 1 := by
    refine Units.ext ?_
    change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, 1; -1, 0] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [T_unipotentGL2, show w₀ = dm * w₁ from rfl, map_mul]
  calc globalPoints (𝓞 ℚ) ℚ dm * globalPoints (𝓞 ℚ) ℚ w₁ *
        (globalPoints (𝓞 ℚ) ℚ w₁inv * unipotentGL2 t * globalPoints (𝓞 ℚ) ℚ w₁)
      = globalPoints (𝓞 ℚ) ℚ dm * (globalPoints (𝓞 ℚ) ℚ (w₁ * w₁inv)) * unipotentGL2 t * globalPoints (𝓞 ℚ) ℚ w₁ := by
        rw [map_mul]; simp only [mul_assoc]
    _ = unipotentGL2 (-t) * (globalPoints (𝓞 ℚ) ℚ dm * globalPoints (𝓞 ℚ) ℚ w₁) := by
        rw [hw, map_one, mul_one, dm_mul_unipotentGL2]; simp only [mul_assoc]

theorem map_transposeInvN {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (g : GL ι A) :
    Matrix.GeneralLinearGroup.map φ (transposeInvN ι g) = transposeInvN ι (Matrix.GeneralLinearGroup.map φ g) := by
  refine Units.ext ?_
  ext i j
  rfl

theorem localAt_T (p : HeightOneSpectrum (𝓞 ℚ)) (x : G2) : localAt ℚ p (T x) = T (localAt ℚ p x) := by
  change Matrix.GeneralLinearGroup.map (finAdeleEval (𝓞 ℚ) ℚ p)
      (Matrix.GeneralLinearGroup.map (adeleFin (𝓞 ℚ) ℚ) (T x)) =
    T (Matrix.GeneralLinearGroup.map (finAdeleEval (𝓞 ℚ) ℚ p) (Matrix.GeneralLinearGroup.map (adeleFin (𝓞 ℚ) ℚ) x))
  rw [map_transposeInvN, map_transposeInvN]

theorem T_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ)) :
    T (placeEmbed ℚ p y) = placeEmbed ℚ p (T y) := by
  refine Ws23HeckeLocalDual.eq_of_components ?_ fun w => ?_
  · have h1 : Ws23HeckeLocalDual.archM (T (placeEmbed ℚ p y)) =
        (Ws23HeckeLocalDual.archM ((placeEmbed ℚ p y)⁻¹ : G2))ᵀ := by
      show (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (Matrix.transpose _) = _
      rw [RingHom.mapMatrix_apply, Matrix.transpose_map]; rfl
    rw [h1, ← map_inv, Ws23HeckeLocalDual.archM_placeEmbed, Ws23HeckeLocalDual.archM_placeEmbed, Matrix.transpose_one]
  · have h1 : Ws23HeckeLocalDual.finM w (T (placeEmbed ℚ p y)) =
        (Ws23HeckeLocalDual.finM w ((placeEmbed ℚ p y)⁻¹ : G2))ᵀ := by
      show (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (Matrix.transpose _)) = _
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map, Matrix.transpose_map]; rfl
    rw [h1, ← map_inv]
    by_cases hw : w = p
    · subst hw
      rw [Ws23HeckeLocalDual.finM_placeEmbed_self, Ws23HeckeLocalDual.finM_placeEmbed_self]
      rfl
    · rw [Ws23HeckeLocalDual.finM_placeEmbed_of_ne _ _ hw, Ws23HeckeLocalDual.finM_placeEmbed_of_ne _ _ hw,
        Matrix.transpose_one]

theorem finFactor_w₀_T (g : G2) :
    RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T g) =
      RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T (RSCarrier.finFactor g : G2)) := by
  have hA : ratArchGL2 (globalPoints (𝓞 ℚ) ℚ w₀ * T g) = w₀R * RSCarrier.transposeInv (ratArchGL2 g) := by
    rw [ratArchGL2_mul, ratArchGL2_w₀, ratArchGL2_T]
  have hT : T g = ιR (RSCarrier.transposeInv (ratArchGL2 g)) * T (RSCarrier.finFactor g : G2) := by
    conv_lhs => rw [(mul_inv_cancel_left (ιR (ratArchGL2 g)) g).symm]
    rw [transposeInvN_mul, T_iotaR]
    rfl
  apply Subtype.ext
  rw [coe_finFactor, coe_finFactor, hA, ratArchGL2_mul, ratArchGL2_w₀, ratArchGL2_T,
    ratArchGL2_of_mem (RSCarrier.finFactor g).2, transposeInv_one, mul_one, hT, map_mul, _root_.mul_inv_rev]
  have hc : (ιR w₀R)⁻¹ * globalPoints (𝓞 ℚ) ℚ w₀ ∈ finiteAdelicGL2Subgroup ℚ := by
    have := (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀)).2
    rwa [coe_finFactor, ratArchGL2_w₀] at this
  have hcomm := iotaR_mul_comm hc (RSCarrier.transposeInv (ratArchGL2 g))
  calc (ιR (RSCarrier.transposeInv (ratArchGL2 g)))⁻¹ * (ιR w₀R)⁻¹ *
        (globalPoints (𝓞 ℚ) ℚ w₀ * (ιR (RSCarrier.transposeInv (ratArchGL2 g)) * T (RSCarrier.finFactor g : G2)))
      = (ιR (RSCarrier.transposeInv (ratArchGL2 g)))⁻¹ * (((ιR w₀R)⁻¹ * globalPoints (𝓞 ℚ) ℚ w₀) *
          ιR (RSCarrier.transposeInv (ratArchGL2 g))) * T (RSCarrier.finFactor g : G2) := by
        simp only [mul_assoc]
    _ = (ιR w₀R)⁻¹ * (globalPoints (𝓞 ℚ) ℚ w₀ * T (RSCarrier.finFactor g : G2)) := by
        rw [← hcomm, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]; simp only [mul_assoc]

theorem ratArchGL2_w₀_T (g : G2) : ratArchGL2 (globalPoints (𝓞 ℚ) ℚ w₀ * T g) = w₀R * RSCarrier.transposeInv (ratArchGL2 g) := by
  rw [ratArchGL2_mul, ratArchGL2_w₀, ratArchGL2_T]

theorem continuous_finFactor_w₀_T :
    Continuous (fun gf : finiteAdelicGL2Subgroup ℚ => RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T (gf : G2))) := by
  have hval : (fun gf : finiteAdelicGL2Subgroup ℚ => ((RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T (gf : G2))) : G2)) =
      fun gf : finiteAdelicGL2Subgroup ℚ => (ιR w₀R)⁻¹ * (globalPoints (𝓞 ℚ) ℚ w₀ * T (gf : G2)) := by
    funext gf
    rw [coe_finFactor, ratArchGL2_mul, ratArchGL2_w₀, ratArchGL2_T, ratArchGL2_of_mem gf.2, transposeInv_one, mul_one]
  refine continuous_induced_rng.2 ?_
  show Continuous (fun gf : finiteAdelicGL2Subgroup ℚ => ((RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * T (gf : G2))) : G2))
  rw [hval]
  exact continuous_const.mul (continuous_const.mul
    (LanglandsTunnell.RankinSelberg.EntirePairAssembly.continuous_transposeInvN.comp continuous_subtype_val))

theorem globalPoints_eq_w₀ (w : GL (Fin 2) ℚ) (hw : (w : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0]) :
    w = w₀ := Units.ext (by rw [hw, w₀_val])

end GamPT2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

end GamPT2Sec
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

namespace GamPT3
theorem addChar_neg_mul {A : Type*} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ (-a) * ψ a = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
end GamPT3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.Ws23FactPhiDual P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch.LanglandsTunnell.RankinSelberg.EntirePairAssembly"

set_option maxHeartbeats 3200000 in
open MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (P : RealArchParam)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (hP1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hP2 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hRcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wr : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℂ → ℂ)
    (kw : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℤ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (hφarch : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (kw par w)) (φv par))
    (hkw1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w))
    (hkw2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hφW : ∀ par, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) 1 (diagOne a * g)
          = (∏ w : InfinitePlace ℚ, Wr par w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
              * Cfin (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (hWr1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par w ∨ b = par w + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓)
    (hE : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hkχ : ∀ p ∈ SQ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) (kχ p))
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (c₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hν : ∀ p ∈ SQ, ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ p ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w
        (NumberField.TateGlobal.localChar
          (μ * (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹) w) c)
    (bQ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hbQ : ∀ p ∈ SQ, p.asIdeal ^ bQ p ∣ Φ.level ∧ ¬ p.asIdeal ^ (bQ p + 1) ∣ Φ.level)
    (hkfloor : ∀ p ∈ SQ,
      6 * ((bQ p : ℤ) + 3 * (2 * ((∑ᶠ w ∈ primeFibre ℚ K p,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((52 : ℤ) + 3 * (c₀ p : ℤ)) +
                      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  (c₀ p : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((52 : ℤ) + 3 * (c₀ p : ℤ)))) + 3) + 7 ≤ (kχ p : ℤ))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (mP : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)
    (hmPmem : ∀ p : ↥SQ, mP p ∈ gl3CyclicSubspace
      (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g))
    (hmP1 : ∀ p : ↥SQ, mP p 1 = 1)
    (hW₃admM : ∀ p : ↥SQ, ∀ Uv : Subgroup (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))) →
      ∃ B : Finset (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ), ∀ W ∈ gl3CyclicSubspace (mP p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)))
    (hW₃irrM : ∀ p : ↥SQ, ∀ W ∈ gl3CyclicSubspace (mP p), W ≠ 0 → mP p ∈ gl3CyclicSubspace W)
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hWf1 : ∀ par, Wf par 1 ≠ 0)
    (hV : ∀ par, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (par : InfinitePlace ℚ → ZMod 2) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
    (w₂b : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂b : w₂b ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par))
    (h₂ : AdelicGL2 (𝓞 ℚ) ℚ) (hh₂ : localAt ℚ p h₂ = 1)

    (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
    (wA : GL (Fin 2) ℝ → ℂ) (wf : finiteAdelicGL2Subgroup ℚ → ℂ) (wp : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwfp : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = wf (RSCarrier.finFactor g))
    (hwfm : Measurable wf)
    (hwfn : ∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, wf (RSCarrier.finFactor (unipotentGL2 t * g)) =
        (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * wf (RSCarrier.finFactor g))
    (hwpn : ∀ (t : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)),
      wp (unipotent t * y) = NumberField.StandardAddChar.psiLocal ℚ p t * wp y)
    (hwp0 : wp ≠ 0)
    (hwpV : ∃ w₁ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
      ∀ y : GL (Fin 2) (p.adicCompletion ℚ), wp y = ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₁ y)
    (hpure : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
          (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (xP j) * h₂))) 1 g =
        wp (localAt ℚ p g) * (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g))) :
    ∃ (WA' WdA' : GL (Fin 2) ℝ → ℂ) (Wf' Wdf' : finiteAdelicGL2Subgroup ℚ → ℂ),

      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf' (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wf' (RSCarrier.finFactor g)) ∧
      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wdf' (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wdf' (RSCarrier.finFactor g)) ∧
      Measurable Wf' ∧ Measurable Wdf' ∧

      (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wf' (RSCarrier.finFactor (unipotentGL2 t * g)) =
          (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * Wf' (RSCarrier.finFactor g)) ∧
      (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wdf' (RSCarrier.finFactor (unipotentGL2 t * g)) =
          (ψ t * (LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p))⁻¹) * Wdf' (RSCarrier.finFactor g)) ∧

      ∀ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → GL (Fin 2) (p.adicCompletion ℚ)),
        Continuous (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) ∧
        (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) (globalPoints (𝓞 ℚ) ℚ γ * g) = (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) g) ∧
        (∃ C r : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖(fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) g‖ ≤ C * detNorm g ^ r) ∧

        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) 1 g =
            (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ i, c i * wp (y * x i)) (localAt ℚ p g) * (WA' (ratArchGL2 g) * Wf' (RSCarrier.finFactor g))) ∧

        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ (fun g => (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) (transposeInvN (Fin 2) g)) 1 g =
            (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ i, c i * wp (y * x i)) ((localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)) * transposeInvN (Fin 2) (localAt ℚ p g)) *
              (WdA' (ratArchGL2 g) * Wdf' (RSCarrier.finFactor g))) := by
  classical

  have hφc : Continuous (φv par) := (hiso par).continuous
  have hφinv : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φv par (globalPoints (𝓞 ℚ) ℚ γ * g) = φv par g :=
    fun γ g => (@AutomorphicForm.LsXiMember.toIsLsXiFunction _ _ _ _ _ _ _ _ _ (_) _ _
      (hiso par).smoothCusp.1.1).left_invariant γ g
  obtain ⟨Cφ, hCφ⟩ : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φv par g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C :=
    LanglandsTunnell.RankinSelberg.EntirePairAssembly.supply_phiBound_of_hasArchCharacterAt₀ Φ SQ hb R hRc Φ.level
      Φ.level_ne_bot S Φ (φv par) (hiso par) (kw par) (hφarch par)
  have hCφ' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φv par g‖ ≤ Cφ * detNorm g ^ (1 / 2 : ℝ) := by
    intro g
    have hd := LanglandsTunnell.RankinSelberg.EntirePairAssembly.detNorm_pos' g
    have h := hCφ g
    have hpos : 0 < detNorm g ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hd _
    have hinv : (detNorm g ^ (-(1 / 2 : ℝ)))⁻¹ = detNorm g ^ (1 / 2 : ℝ) := by rw [Real.rpow_neg hd.le, inv_inv]
    rw [← le_div_iff₀ hpos, div_eq_mul_inv, hinv] at h
    exact h
  have hdetmul : ∀ g h : AdelicGL2 (𝓞 ℚ) ℚ, detNorm (g * h) = detNorm g * detNorm h := fun g h => by
    unfold detNorm; rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  have hw₀eq : w₀ = Ws23FactPhiDual.w₀ := GamPT2.globalPoints_eq_w₀ w₀ hw₀

  have hτc : ∀ k : AdelicGL2 (𝓞 ℚ) ℚ, Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      (((detNorm (g * k)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * k * h₂) := by
    intro k
    refine Continuous.mul ?_ (hφc.comp ((continuous_mul_right k).mul continuous_const))
    refine Continuous.cpow ?_ continuous_const fun g => ?_
    · exact Complex.continuous_ofReal.comp
        (LanglandsTunnell.RankinSelberg.EntirePairAssembly.continuous_detNorm'.comp (continuous_mul_right k))
    · exact Complex.ofReal_mem_slitPlane.2 (LanglandsTunnell.RankinSelberg.EntirePairAssembly.detNorm_pos' _)
  have hτb : ∀ (k g : AdelicGL2 (𝓞 ℚ) ℚ),
      ‖(((detNorm (g * k)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * k * h₂)‖ ≤ Cφ * detNorm h₂ ^ (1 / 2 : ℝ) := by
    intro k g
    have hd := LanglandsTunnell.RankinSelberg.EntirePairAssembly.detNorm_pos' (g * k)
    have hd₂ := LanglandsTunnell.RankinSelberg.EntirePairAssembly.detNorm_pos' h₂
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd]
    have hre : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by simp
    rw [hre]
    calc detNorm (g * k) ^ (-(1 / 2 : ℝ)) * ‖φv par (g * k * h₂)‖
        ≤ detNorm (g * k) ^ (-(1 / 2 : ℝ)) * (Cφ * detNorm (g * k * h₂) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hCφ' _) (Real.rpow_nonneg hd.le _)
      _ = Cφ * detNorm h₂ ^ (1 / 2 : ℝ) := by
          rw [hdetmul (g * k) h₂, Real.mul_rpow hd.le hd₂.le, ← mul_assoc, ← mul_assoc,
            mul_comm (detNorm (g * k) ^ (-(1 / 2 : ℝ))) Cφ, mul_assoc Cφ, ← Real.rpow_add hd,
            show (-(1 / 2 : ℝ)) + 1 / 2 = 0 by norm_num, Real.rpow_zero, mul_one]

  set φP : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (xP j) * h₂))) with hφP
  have hφPc : Continuous φP :=
    continuous_finset_sum _ fun j _ => continuous_const.mul (hτc _)

  refine ⟨wA, fun y => wA (Ws23FactPhiDual.w₀R * RSCarrier.transposeInv y), wf,
    fun gf => wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ Ws23FactPhiDual.w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))),
    hwfp, ?_, hwfm, ?_, hwfn, ?_, ?_⟩
  ·
    intro x g
    show wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ Ws23FactPhiDual.w₀ * transposeInvN (Fin 2)
        ((RSCarrier.finFactor (g * placeEmbed ℚ p x) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) =
      wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ Ws23FactPhiDual.w₀ * transposeInvN (Fin 2)
        ((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)))
    rw [← GamPT2.finFactor_w₀_T, ← GamPT2.finFactor_w₀_T, transposeInvN_mul, GamPT2.T_placeEmbed, ← mul_assoc, hwfp]
  ·
    exact hwfm.comp GamPT2.continuous_finFactor_w₀_T.measurable
  ·
    intro t ht g
    show wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ Ws23FactPhiDual.w₀ * transposeInvN (Fin 2)
        ((RSCarrier.finFactor (unipotentGL2 t * g) : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) =
      (ψ t * (LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p))⁻¹) *
      wf (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ Ws23FactPhiDual.w₀ * transposeInvN (Fin 2)
        ((RSCarrier.finFactor g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)))
    rw [← GamPT2.finFactor_w₀_T, ← GamPT2.finFactor_w₀_T, transposeInvN_mul, ← mul_assoc,
      GamPT2.w₀_mul_T_unipotentGL2, mul_assoc]
    have ht' : (-t).1 = 0 := by change -t.1 = 0; rw [ht, neg_zero]
    rw [hwfn (-t) ht']
    congr 1
    rw [AddChar.inv_apply, neg_neg]
    congr 1
    show LanglandsTunnell.CubicInduction.psiLoc ψ p (-(t.2 p)) = _
    exact (inv_eq_of_mul_eq_one_left (GamPT3.addChar_neg_mul _ _)).symm

  intro n c x

  have hfam : (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j * (((detNorm (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * placeEmbed ℚ p (x i) * placeEmbed ℚ p (xP j) * h₂))) = fun g => ∑ i, c i * φP (g * placeEmbed ℚ p (x i)) := by
    funext g
    simp only [hφP]
  rw [hfam]
  have hcxc : Continuous (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * φP (g * placeEmbed ℚ p (x i))) :=
    continuous_finset_sum _ fun i _ => continuous_const.mul (hφPc.comp (continuous_mul_right _))
  have hcxinv : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * φP (g * placeEmbed ℚ p (x i))) (globalPoints (𝓞 ℚ) ℚ γ * g) =
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * φP (g * placeEmbed ℚ p (x i))) g := by
    intro γ g
    simp only [hφP, mul_assoc, LanglandsTunnell.RankinSelberg.EntirePairAssembly.detNorm_globalPoints_mul', hφinv]

  have hprim : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹ (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * φP (g * placeEmbed ℚ p (x i))) 1 g =
        (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ i, c i * wp (y * x i)) (localAt ℚ p g) *
          (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g)) := by
    intro g
    have hψc : Continuous (ψ⁻¹ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) := by
      have : ((ψ⁻¹ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) : AdeleRing (𝓞 ℚ) ℚ → ℂ) = fun a => ψ (-a) :=
        funext fun a => AddChar.inv_apply ψ a
      rw [this]; exact hψ.continuous.comp continuous_neg
    have h1 := GamPT2.W_finsum (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) ψ⁻¹ hψc c
      (fun i z => φP (z * placeEmbed ℚ p (x i))) (fun i => hφPc.comp (continuous_mul_right _)) g
    rw [h1]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GamPT2.W_translate (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) ψ⁻¹ φP, hpure, map_mul,
      LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor.localAt_placeEmbed_self, Ws23FactPhiDual.ratArchGL2_mul,
      Ws23FactPhiDual.ratArchGL2_of_mem (Ws23HeckeLocalDual.placeEmbed_mem_fin p (x i)), mul_one, hwfp]
    ring
  refine ⟨hcxc, hcxinv, ?_, hprim, ?_⟩
  ·
    refine ⟨∑ i, ‖c i‖ * ∑ j, ‖cP j‖ * (Cφ * detNorm h₂ ^ (1 / 2 : ℝ)), 0, fun g => ?_⟩
    rw [Real.rpow_zero, mul_one]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [hφP]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hτb _ _) (norm_nonneg _)
  ·
    intro g
    rw [GamPT2.W_dual_eq₀ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) hψQ
      (φ := fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * φP (g * placeEmbed ℚ p (x i))) hcxinv g, ← hψQ, hprim, map_mul,
      GamPT2.localAt_T, GamPT2.ratArchGL2_w₀_T, GamPT2.finFactor_w₀_T, hw₀eq]

end SecJ6Sol
end S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch (solution)
