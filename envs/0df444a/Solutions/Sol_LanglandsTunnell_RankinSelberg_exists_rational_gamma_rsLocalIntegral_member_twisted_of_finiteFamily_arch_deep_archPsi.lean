-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ed5d3cee-3e1c-5658-8905-01d2faa92fa3

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
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
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_isAdmissibleTwist_eq_centralChar_mul_ideleNorm_inv
import Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_norm_diagOne_mul_le_of_irreducible_admissible
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_placeEmbed
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_localMaximalCompact3
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.mem_sigmaCentralizer_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField Matrix
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction NumberField.AdelicLevel AdelicDock"

noncomputable section

namespace Ws23PlaceEmbed3

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem matrix3_eq_of_forall_mapMatrix_finAdeleEval_eq {M N : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] using hw

theorem matrix3_eq_of_mapMatrix_arch_fin_eq {M N : Matrix (Fin 3) (Fin 3) (AdeleRing R K)}
    (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) :
    M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

variable (v : HeightOneSpectrum R)

def localMat3 (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K) :=
  Matrix.of fun i j => splice R K v ((1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) i j) (g i j)

theorem localMat3_apply_self (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) (i j : Fin 3) :
    localMat3 R K v g i j v = g i j := by
  simp [localMat3]

theorem localMat3_apply_of_ne (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) (i j : Fin 3)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMat3 R K v g i j w = (1 : Matrix (Fin 3) (Fin 3) (w.adicCompletion K)) i j := by
  simp only [localMat3, Matrix.of_apply, splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mapMatrix_localMat3_self (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMat3 R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat3_apply_self]

theorem mapMatrix_localMat3_of_ne (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMat3 R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMat3_apply_of_ne R K v g i j hw]

theorem localMat3_one : localMat3 R K v 1 = 1 := by
  refine matrix3_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMat3_self, map_one]
  · rw [mapMatrix_localMat3_of_ne R K v _ hw, map_one]

theorem localMat3_mul (g h : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    localMat3 R K v (g * h) = localMat3 R K v g * localMat3 R K v h := by
  refine matrix3_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, mapMatrix_localMat3_self, mapMatrix_localMat3_self, mapMatrix_localMat3_self]
  · rw [map_mul, mapMatrix_localMat3_of_ne R K v _ hw, mapMatrix_localMat3_of_ne R K v _ hw,
      mapMatrix_localMat3_of_ne R K v _ hw, mul_one]

def localEmbed3 : GL (Fin 3) (v.adicCompletion K) →* GL (Fin 3) (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMat3 R K v g
      inv := localMat3 R K v ((g⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMat3_mul, Units.mul_inv, localMat3_one]
      inv_val := by rw [← localMat3_mul, Units.inv_mul, localMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact localMat3_one R K v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact localMat3_mul R K v _ _)

def finMat3 (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) : Matrix (Fin 3) (Fin 3) (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

theorem mapMatrix_arch_finMat3 (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (finMat3 R K g) = 1 := by
  ext i j
  simp [finMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_finMat3 (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (finMat3 R K g) = g := by
  ext i j
  simp [finMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem finMat3_one : finMat3 R K 1 = 1 :=
  matrix3_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_finMat3, map_one])
    (by rw [mapMatrix_fin_finMat3, map_one])

theorem finMat3_mul (g h : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) :
    finMat3 R K (g * h) = finMat3 R K g * finMat3 R K h :=
  matrix3_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_finMat3, mapMatrix_arch_finMat3, mapMatrix_arch_finMat3, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMat3, mapMatrix_fin_finMat3, mapMatrix_fin_finMat3])

def finEmbed3 : GL (Fin 3) (FiniteAdeleRing R K) →* AdelicGL 3 R K where
  toFun g :=
    { val := finMat3 R K g
      inv := finMat3 R K ((g⁻¹ : GL (Fin 3) (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMat3_mul, Units.mul_inv, finMat3_one]
      inv_val := by rw [← finMat3_mul, Units.inv_mul, finMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMat3_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMat3_mul R K _ _)

def placeEmbed3 : GL (Fin 3) (v.adicCompletion K) →* AdelicGL 3 R K :=
  (finEmbed3 R K).comp (localEmbed3 R K v)

theorem componentAt3_placeEmbed3_self (g : GL (Fin 3) (v.adicCompletion K)) :
    componentAt3 R K v (placeEmbed3 R K v g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.finAdeleEval R K v) ((AdelicLevel.adeleFin R K) (finMat3 R K (localMat3 R K v g) i j)) = _
  rw [AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply]
  simp only [finMat3, Matrix.of_apply]
  exact localMat3_apply_self R K v g i j

theorem componentAt3_placeEmbed3_of_ne (g : GL (Fin 3) (v.adicCompletion K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : componentAt3 R K w (placeEmbed3 R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.finAdeleEval R K w) ((AdelicLevel.adeleFin R K) (finMat3 R K (localMat3 R K v g) i j)) = _
  rw [AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply, Units.val_one]
  simp only [finMat3, Matrix.of_apply]
  exact localMat3_apply_of_ne R K v g i j hw

theorem archComponent3_placeEmbed3 (g : GL (Fin 3) (v.adicCompletion K)) :
    archComponent3 R K (placeEmbed3 R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.adeleArch R K) (finMat3 R K (localMat3 R K v g) i j) = _
  rw [AdelicLevel.adeleArch_apply, Units.val_one]
  simp only [finMat3, Matrix.of_apply]

end Generic

section Family

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

variable (m : ↥SQ → ℕ)

variable {SQ m}

end Family

end Ws23PlaceEmbed3

end

namespace Ws23Fam5

theorem psiLoc_eq_psiLocal_inv_of_inv_eq_psiQ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc ψ p = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ := by
  classical
  have hinv : ∀ (χ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ),
      LanglandsTunnell.CubicInduction.psiLoc χ⁻¹ p = (LanglandsTunnell.CubicInduction.psiLoc χ p)⁻¹ := by
    intro χ
    refine DFunLike.ext _ _ fun x => ?_
    rw [AddChar.inv_apply]
    show χ⁻¹ (NumberField.StandardAddChar.adeleSingleAt ℚ p x) = χ (NumberField.StandardAddChar.adeleSingleAt ℚ p (-x))
    rw [map_neg (NumberField.StandardAddChar.adeleSingleAt ℚ p) x, AddChar.inv_apply]
  have hQ : LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ p =
      NumberField.StandardAddChar.psiLocal ℚ p := by
    rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
    refine DFunLike.ext _ _ fun x => ?_
    show NumberField.StandardAddChar.psiQ (NumberField.StandardAddChar.adeleSingleAt ℚ p x) = _
    rw [show NumberField.StandardAddChar.adeleSingleAt ℚ p x =
        ((0 : InfiniteAdeleRing ℚ), NumberField.StandardAddChar.finAdeleSingleAt ℚ p x) from rfl,
      NumberField.StandardAddChar.psiQ_apply]
    simp only
    rw [AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply]
    rw [finprod_eq_single (fun w => NumberField.StandardAddChar.psiV w
      (NumberField.StandardAddChar.finAdeleSingleAt ℚ p x w)) p]
    · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
    · intro w hw
      rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ p x hw]
      exact AddChar.map_zero_eq_one _
  rw [← inv_inv ψ, hinv, hψQ, hQ]

section IotaComponents

open Matrix NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ

theorem eventually_valued_le_one (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∀ᶠ v in Filter.cofinite, Valued.v (a v) ≤ 1 := by
  have h := RestrictedProduct.eventually (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) a
  filter_upwards [h] with v hv
  exact hv

end IotaComponents

section WhittakerUnipotentLaw

open Matrix MeasureTheory
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

scoped instance isAddHaarMeasure_adelicAddHaar_fam5 : (μA).IsAddHaarMeasure :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

scoped instance countable_principalSubgroup_fam5 : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  show Countable {x : 𝔸 // x ∈ Set.range (algebraMap ℚ 𝔸)}
  exact (Set.countable_range _).to_subtype

scoped instance vaddInvariantMeasure_principalSubgroup_fam5 :
    VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) 𝔸 μA :=
  ⟨fun k s _ => measure_preimage_add _ (k : 𝔸) s⟩

end WhittakerUnipotentLaw

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

noncomputable section

namespace Ws23Fam5Holes

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem isClosed_setOf_isLocalLevelOne (N : Ideal (𝓞 ℚ)) :
    IsClosed {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} := by
  have h : {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} =
      (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
        ((fun m => m 1 0) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p} ∩
          (fun m => m 1 1 - 1) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p}) := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hm => ⟨hm.integral, hm.lowerLeft, hm.lowerRight⟩, fun hm => ⟨hm.1, hm.2.1, hm.2.2⟩⟩
  rw [h]
  exact (isClosed_iInter fun i => isClosed_iInter fun j =>
      (isClosed_adicCompletionIntegers p).preimage (continuous_id.matrix_elem i j)).inter
    (((isClosed_setOf_valued_le_idealBound p N).preimage (continuous_id.matrix_elem 1 0)).inter
      ((isClosed_setOf_valued_le_idealBound p N).preimage
        ((continuous_id.matrix_elem 1 1).sub continuous_const)))

theorem isOpen_setOf_isLocalLevelOne {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    IsOpen {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} := by
  have h : {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} =
      (⋂ i, ⋂ j, (fun m => m i j) ⁻¹' (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
        ((fun m => m 1 0) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p} ∩
          (fun m => m 1 1 - 1) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 ℚ) N p}) := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hm => ⟨hm.integral, hm.lowerLeft, hm.lowerRight⟩, fun hm => ⟨hm.1, hm.2.1, hm.2.2⟩⟩
  rw [h]
  have hO : IsOpen (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out p
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (continuous_id.matrix_elem i j)).inter
    (((isOpen_setOf_valued_le_idealBound p hN).preimage (continuous_id.matrix_elem 1 0)).inter
      ((isOpen_setOf_valued_le_idealBound p hN).preimage
        ((continuous_id.matrix_elem 1 1).sub continuous_const)))

theorem coe_localLevelOne_eq (N : Ideal (𝓞 ℚ)) :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      Units.val ⁻¹' {m | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} ∩
        (fun u : GL (Fin 2) (p.adicCompletion ℚ) => ((u⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix _ _ _)) ⁻¹'
          {m | AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m} := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff]
  rfl

theorem isClosed_localLevelOne (N : Ideal (𝓞 ℚ)) :
    IsClosed (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [coe_localLevelOne_eq]
  exact ((isClosed_setOf_isLocalLevelOne p N).preimage Units.continuous_val).inter
    ((isClosed_setOf_isLocalLevelOne p N).preimage Units.continuous_coe_inv)

theorem localLevelOne_subset_localIntegralSet (N : Ideal (𝓞 ℚ)) :
    (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) ⊆ localIntegralSet ℚ p := by
  intro k hk
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff] at hk
  exact ⟨hk.1.integral, hk.2.integral⟩

theorem localLevelOne_isCompact_isOpen {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  refine ⟨(isCompact_localIntegralSet ℚ p).of_isClosed_subset (isClosed_localLevelOne p N)
    (localLevelOne_subset_localIntegralSet p N), ?_⟩
  rw [coe_localLevelOne_eq]
  exact ((isOpen_setOf_isLocalLevelOne p hN).preimage Units.continuous_val).inter
    ((isOpen_setOf_isLocalLevelOne p hN).preimage Units.continuous_coe_inv)

end Local
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section Ugrp

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : Ideal (𝓞 ℚ))

theorem localAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    ((localAt ℚ p g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      (((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p := by
  rw [show localAt ℚ p g = finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) from rfl, finComponent_apply, glFin_apply]

theorem det_mem_of_forall_mem {p : HeightOneSpectrum (𝓞 ℚ)} (m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    (h : ∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) : m.det ∈ p.adicCompletionIntegers ℚ := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

end Ugrp
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

noncomputable section

namespace Ws23Fam5Holes

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal

section H45

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end H45
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section PencBatch3
open scoped Matrix

namespace Ws23Fam5Holes

section GL3

variable {A : Type*} [CommRing A]

variable {R : Type*} [CommRing R]

theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace (ψ : AddChar A R) {W W' : GL (Fin 3) A → R}
    (hW : IsGL3PsiWhittakerFn ψ W) (h : W' ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ W' := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace A R ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', rfl⟩
    show IsGL3PsiWhittakerFn ψ (gl3AmbientRightTranslate h' W)
    intro x y z g
    rw [gl3AmbientRightTranslate_apply, gl3AmbientRightTranslate_apply, mul_assoc]
    exact hW x y z (g * h')
  exact hle h

end GL3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end PencBatch3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction NumberField.AdelicLevel"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section PencN12
open scoped Matrix

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section OffPlace

variable (p : HeightOneSpectrum (𝓞 ℚ))

end OffPlace
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section DualLaw

variable {A : Type*} [CommRing A] {R : Type*} [CommRing R]

end DualLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end PencN12
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section PencL13
open scoped Matrix Classical

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section Ext2

end Ext2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section L1

end L1
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section L3

theorem localAt_globalPoints (p : HeightOneSpectrum (𝓞 ℚ)) (γ : GL (Fin 2) ℚ) :
    localAt ℚ p (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (algebraMap ℚ (p.adicCompletion ℚ)) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [localAt_apply]
  rfl

end L3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end PencL13
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section PencL2
open scoped Matrix Classical

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section L2

variable (T : Finset (HeightOneSpectrum (𝓞 ℚ)))

end L2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end PencL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section PencDE
open scoped Matrix Classical

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end PencDE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section Ws23MiniPlaceKit

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg"

noncomputable section

namespace Ws23HeckeLocalDualPort

open Matrix NumberField.AdelicVolume UnramifiedWhittaker

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23HeckeLocalDualPort
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23MiniPlaceKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section prover2_prefactor

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction LanglandsTunnell.Converse"
open UnramifiedWhittaker AutomorphicForm

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.localBorel TateLocal.selfDualHaarAt TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.modulus TateLocal.modulus_ne_zero TateLocal.modulus_mul TateLocal.mulMeasure RealArchParam signShift RealArchParam.discrete RealArchParam.principal RankinSelberg.primeFibre CubicInduction.psiLoc CubicInduction.CubicInductionForm ratArchGL2 TateLocal.modulus_adicCompletion_eq_nnnorm CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.isOpen_localMaximalCompact3 RankinSelberg.exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep RankinSelberg.exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section NormAlgebra
variable {G : Type*} [Group G] (ν : G → ℝ) (hmul : ∀ a b, ν (a * b) = ν a * ν b) (hone : ν 1 = 1) (hpos : ∀ a, 0 < ν a)
end NormAlgebra
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Fibre
variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

end Fibre
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end prover2_prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section prover2_hlev

open IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.localBorel TateLocal.selfDualHaarAt TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.modulus TateLocal.modulus_ne_zero TateLocal.modulus_mul TateLocal.mulMeasure RealArchParam signShift RealArchParam.discrete RealArchParam.principal RankinSelberg.primeFibre CubicInduction.psiLoc CubicInduction.CubicInductionForm ratArchGL2 TateLocal.modulus_adicCompletion_eq_nnnorm CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.isOpen_localMaximalCompact3 RankinSelberg.exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep RankinSelberg.exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing"
namespace EntirePairAssembly
namespace Prefactor
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

end LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end prover2_hlev
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Tw

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

structure TwCubic (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) where

  whittakerLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ

  cenLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletion ℚ)ˣ →* ℂˣ
  whittakerLoc_law : ∀ v, IsGL3PsiWhittakerFn (psiLoc ψ v) (whittakerLoc v)
  spherical : ∀ v, ¬ IsBadPlace K μ v →
    IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (whittakerLoc v)
  levelInvariant : ∀ v, v ∉ S₀ →
    ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, whittakerLoc v (g * k) = whittakerLoc v g
  continuous : ∀ v, Continuous (whittakerLoc v)
  ne_zero : ∀ v, whittakerLoc v ≠ 0
  scalar : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
    whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((cenLoc v t : ℂˣ) : ℂ) * whittakerLoc v h
  gauge : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → whittakerLoc p h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖whittakerLoc p h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)

private noncomputable def _root_.Ws23Tw.twist (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun x => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x

p2m_export "Ws23Tw" "twist"
end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section SupportedOn

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

def IsSupportedOn (h : AdelicGL2 (𝓞 ℚ) ℚ) : Prop :=
  glArch (𝓞 ℚ) ℚ h = 1 ∧ ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → localAt ℚ q h = 1

theorem IsSupportedOn.mul {h h' : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) (hh' : IsSupportedOn SQ h') :
    IsSupportedOn SQ (h * h') :=
  ⟨by rw [map_mul, hh.1, hh'.1, mul_one], fun q hq => by rw [map_mul, hh.2 q hq, hh'.2 q hq, mul_one]⟩

theorem IsSupportedOn.inv {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) : IsSupportedOn SQ h⁻¹ :=
  ⟨by rw [map_inv, hh.1, inv_one], fun q hq => by rw [map_inv, hh.2 q hq, inv_one]⟩

theorem IsSupportedOn.conj {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsSupportedOn SQ h) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    IsSupportedOn SQ (g⁻¹ * h * g) :=
  ⟨by rw [map_mul, map_mul, map_inv, hh.1, mul_one, inv_mul_cancel],
    fun q hq => by rw [map_mul, map_mul, map_inv, hh.2 q hq, mul_one, inv_mul_cancel]⟩

variable {SQ}

variable (SQ)

end SupportedOn
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section Weyl

end Weyl
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section Centrality

end Centrality
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section FinFactor

end FinFactor
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section UnitNorms

theorem det_unipotentGL2_val {A : Type*} [CommRing A] (x : A) :
    Matrix.det ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = 1 := by
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]; ring

end UnitNorms
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section Levels

end Levels
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

section FlipOff

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end FlipOff
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section MixedGL2

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (w₀ : GL (Fin 2) ℚ) (H : AdelicGL2 (𝓞 ℚ) ℚ)

theorem localAt_globalPoints_antidiag (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0]) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((localAt ℚ v (globalPoints (𝓞 ℚ) ℚ w₀) : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![0, 1; 1, 0] := by
  rw [localAt_globalPoints]
  change (algebraMap ℚ (v.adicCompletion ℚ)).mapMatrix (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = _
  rw [hw₀]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {SQ w₀ H}

end MixedGL2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section CubicLaws

open scoped Classical

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (F : Ws23Tw.TwCubic K ψ μ SQ)
  (W' : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ)
  (BTv1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), LocalGL3 v → ℂ)
  (hBTv1 : ∀ v y, BTv1 v y = if hv : v ∈ SQ then W' ⟨v, hv⟩ y else dualWhittakerFn3 (F.whittakerLoc v) y)

include hBTv1

end CubicLaws
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23W2

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5Holes P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section PenbSwapStep
open LanglandsTunnell.TateLocal UnramifiedWhittaker

noncomputable section

namespace Ws23SwapStep

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction RSCarrier NumberField.AdelicLevel AdelicDock"

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction RSCarrier NumberField.AdelicLevel AdelicDock"

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

theorem modulus_det_pos (p : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    0 < modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) :=
  modulus_pos (Units.ne_zero _)

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

theorem exists_local_uniformizer (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ ϖ : p.adicCompletionIntegers ℚ, algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 ∧
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := by
  refine ⟨⟨(NumberField.AdelicLevel.uniformizerUnit ℚ p : p.adicCompletion ℚ), ?_⟩, ?_, ?_⟩
  · show Valued.v (NumberField.AdelicLevel.uniformizerUnit ℚ p : p.adicCompletion ℚ) ≤ 1
    rw [NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by norm_num)
  · exact Units.ne_zero _
  · exact NumberField.AdelicLevel.valued_uniformizerUnit ℚ p

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

open AutomorphicForm in
theorem whittakerCoefficient_mul_right {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (X Y : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (X * Y) = whittakerCoefficient F pins ψ (fun x => φ (x * Y)) α X := by
  unfold whittakerCoefficient
  simp only [mul_assoc]

open AutomorphicForm AutomorphicForm.WhittakerModel in
theorem localFnAt_translate {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : GL (Fin 2) (v.adicCompletion F)) (g : GL (Fin 2) (v.adicCompletion F)) :
    localFnAt F pins ψ v φ (g * h) =
      localFnAt F pins ψ v (fun x => φ (x * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v h))) g := by
  unfold localFnAt
  rw [map_mul, map_mul, whittakerCoefficient_mul_right]

open AutomorphicForm AutomorphicForm.WhittakerModel in

theorem localSpaceAt_translate_mem {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    ∀ W ∈ localSpaceAt F pins ψ v φ, ∀ h : GL (Fin 2) (v.adicCompletion F),
      (fun g => W (g * h)) ∈ localSpaceAt F pins ψ v φ := by
  intro W hW h
  refine Submodule.span_induction (p := fun W _ => (fun g => W (g * h)) ∈ localSpaceAt F pins ψ v φ)
    ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h', rfl⟩
    refine Submodule.subset_span ⟨AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v h) * h', ?_⟩
    funext g
    rw [localFnAt_translate]
    simp only [mul_assoc]
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ a hx

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23SwapStep

section TranslateSpan
variable {G : Type*} [Group G]

theorem translateSpan_stable (w : G → ℂ) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)), ∀ h : G,
      (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := by
  intro W hW h
  refine Submodule.span_induction (p := fun W _ => (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)))
    ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h', rfl⟩
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g
    simp only [mul_assoc]
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ a hx

theorem translateSpan_law {N : Type*} (act : N → G → G) (χ : N → ℂ) (hact : ∀ n g h, act n (g * h) = act n g * h)
    (w : G → ℂ) (hw : ∀ n g, w (act n g) = χ n * w g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)), ∀ n g, W (act n g) = χ n * W g := by
  intro W hW
  refine Submodule.span_induction (p := fun W _ => ∀ n g, W (act n g) = χ n * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ n g
    show w (act n g * h) = χ n * w (g * h)
    rw [← hact, hw]
  · intro n g; simp
  · intro x y _ _ hx hy n g
    simp only [Pi.add_apply, hx, hy]; ring
  · intro a x _ hx n g
    simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

end TranslateSpan
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

theorem diagZ_eq_diagOne {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) (m : ℤ) :
    diagZ π hπ m = diagOne (Units.mk0 π hπ ^ m) := by
  refine Units.ext ?_
  show (!![π ^ m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![((Units.mk0 π hπ ^ m : Kˣ) : K), 1]
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem norm_uniformizer (p : HeightOneSpectrum (𝓞 ℚ)) {ϖ : p.adicCompletionIntegers ℚ}
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ‖algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def (K := ℚ) (v := p), hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have h1 : (WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0)).toAdd = -1 := by
    rw [show WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0) = Multiplicative.ofAdd (-1 : ℤ) from
      WithZero.unzero_coe _, toAdd_ofAdd]
  rw [h1, _root_.zpow_neg, _root_.zpow_one, NNReal.coe_inv]
  norm_cast

theorem det_diagOne {K : Type*} [CommRing K] (y : Kˣ) : Matrix.GeneralLinearGroup.det (diagOne y) = y := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(y : K), 1]) = y
  rw [Matrix.det_diagonal]
  simp

theorem twisted_shell_growth (p : HeightOneSpectrum (𝓞 ℚ)) (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (C : ℝ) (M : ℕ)
    (hb : ∀ (y : (p.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
      ‖W (diagOne y * k)‖ ≤ C * max 1 ((modulus (y : p.adicCompletion ℚ)) ^ M)⁻¹)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1) :
    ∃ (C' A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖(fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (-(1 / 2 : ℂ)) * W g)
        (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C' * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m) := by
  set π : p.adicCompletion ℚ := algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ with hπdef
  set q : ℝ := (Ideal.absNorm p.asIdeal : ℝ) with hqdef
  have hq1 : 1 < q := by rw [hqdef]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hq0 : 0 < q := lt_trans one_pos hq1
  have hnorm : ∀ x : p.adicCompletion ℚ, ((modulus x : NNReal) : ℝ) = ‖x‖ := fun x => by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]
  have hπn : ‖π‖ = q⁻¹ := by rw [hπdef, norm_uniformizer p hϖ, hqdef]
  refine ⟨max C 0, (M : ℝ) + 1 / 2, fun m hm k hk => ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm

  rw [diagZ_eq_diagOne, zpow_natCast]
  set y : (p.adicCompletion ℚ)ˣ := Units.mk0 π hπ ^ n with hydef
  have hy : ‖(y : p.adicCompletion ℚ)‖ = q ^ (-(n : ℝ)) := by
    rw [hydef, Units.val_pow_eq_pow_val, Units.val_mk0, norm_pow, hπn, ← Real.rpow_neg_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hq0.le]
    ring_nf

  have hdet : ((modulus ((Matrix.GeneralLinearGroup.det (diagOne y * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) =
      q ^ (-(n : ℝ)) := by
    rw [map_mul, det_diagOne, Units.val_mul, modulus_mul, NNReal.coe_mul, hK k hk, NNReal.coe_one, mul_one, hnorm, hy]
  have hfac : ‖(((modulus ((Matrix.GeneralLinearGroup.det (diagOne y * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
      (-(1 / 2 : ℂ)))‖ = q ^ ((n : ℝ) / 2) := by
    rw [hdet, Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hq0 _), ← Real.rpow_mul hq0.le]
    congr 1
    simp
    ring

  have hW : ‖W (diagOne y * k)‖ ≤ max C 0 * q ^ ((n : ℝ) * M) := by
    refine (hb y k hk).trans ?_
    have hmax : max 1 (((modulus (y : p.adicCompletion ℚ) : ℝ)) ^ M)⁻¹ = q ^ ((n : ℝ) * M) := by
      rw [hnorm, hy, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_neg hq0.le]
      rw [max_eq_right]
      · congr 1; ring
      · refine Real.one_le_rpow hq1.le ?_
        have : (0 : ℝ) ≤ n * M := by positivity
        linarith [show -( -(n:ℝ) * M) = n * M from by ring]
    have hcast : (((max 1 ((modulus (y : p.adicCompletion ℚ)) ^ M)⁻¹ : NNReal)) : ℝ) =
        max 1 (((modulus (y : p.adicCompletion ℚ) : ℝ)) ^ M)⁻¹ := by
      rw [NNReal.coe_max, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_one]
    rw [hcast, hmax]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hq0.le _)

  rw [norm_mul, hfac]
  calc q ^ ((n : ℝ) / 2) * ‖W (diagOne y * k)‖
      ≤ q ^ ((n : ℝ) / 2) * (max C 0 * q ^ ((n : ℝ) * M)) :=
        mul_le_mul_of_nonneg_left hW (Real.rpow_nonneg hq0.le _)
    _ = max C 0 * q ^ (((M : ℝ) + 1 / 2) * (n : ℤ)) := by
        rw [show (((n : ℕ) : ℤ) : ℝ) = (n : ℝ) from by norm_cast, mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

theorem twisted_shell_growth_of_mem (p : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hVstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V)
    (hVirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h)))
    (hVadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hVsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hVcen : ∀ W ∈ V, ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : w ∈ V)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1) :
    ∃ (C' A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖(fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (-(1 / 2 : ℂ)) * w g)
        (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C' * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m) := by
  set V' : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) := Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)) with hV'
  have hle : V' ≤ V := Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hVstab w hw h)
  have hlaw' : ∀ W ∈ V', ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    translateSpan_law (fun (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)) => unipotent x * g)
      (fun x => NumberField.StandardAddChar.psiLocal ℚ p x) (fun x g h => (mul_assoc _ _ _).symm) w hwlaw
  obtain ⟨C, M, c, -, -, hb⟩ := AutomorphicForm.WhittakerModel.exists_norm_diagOne_mul_le_of_irreducible_admissible p V'
    (translateSpan_stable w) hlaw' (fun W hW => hVsm W (hle hW))
    (fun U hU => by obtain ⟨B, hB⟩ := hVadm U hU; exact ⟨B, fun W hW hinv => hB W (hle hW) hinv⟩)
    (fun W₀ hW₀ h0 W hW => hVirr W₀ (hle hW₀) h0 W (hle hW)) ω (fun W hW => hVcen W (hle hW))
    w (Submodule.subset_span ⟨1, funext fun g => by beta_reduce; rw [mul_one]⟩)
  exact twisted_shell_growth p w C M (fun y k hk => (hb y k hk).1) hπ hϖ hK

end Ws23SwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end PenbSwapStep
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23PencSwap

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

open scoped Pointwise

theorem modulus_det_eq_one_of_mem_localLevelOne (p : HeightOneSpectrum (𝓞 ℚ)) {N : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (p.adicCompletion ℚ)} (hu : u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) :
    LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
  have hu' := (AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p u).1 hu
  have h1 := Ws23Fam5Holes.det_mem_of_forall_mem _ hu'.1.integral
  have h2 := Ws23Fam5Holes.det_mem_of_forall_mem _ hu'.2.integral
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  have hprod : Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
      Matrix.det ((u⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = 1 := by
    refine le_antisymm h1 ?_
    have h := congrArg Valued.v hprod
    rw [map_mul, map_one] at h
    calc (1 : WithZero (Multiplicative ℤ)) = _ * _ := h.symm
      _ ≤ Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  rw [Matrix.GeneralLinearGroup.val_det_apply, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p,
    ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one, NumberField.FinitePlace.norm_def, hv, map_one, NNReal.coe_one]

section Stage

open scoped Classical

end Stage
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23PencSwap
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

section Continuity3

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

end Continuity3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

theorem eventually_componentAt3_mem (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᶠ v in Filter.cofinite, componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hA : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 3,
      Valued.v ((((x : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Ws23Fam5.eventually_valued_le_one _
  have hB : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 3,
      Valued.v ((((x⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Ws23Fam5.eventually_valued_le_one _
  filter_upwards [hA, hB] with v hA hB
  refine ⟨fun i j => hA i j, fun i j => ?_⟩
  rw [← map_inv]
  exact hB i j

theorem exists_whittaker_ne_zero
    {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (F : CubicInductionForm K pins ψ μ) (hF : F.form ≠ 0) : ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, F.whittaker g ≠ 0 := by
  by_contra h
  push_neg at h
  apply hF
  funext g
  have hs := F.expansion g
  simp_rw [h] at hs
  exact hs.unique hasSum_zero

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem smooth_of_mem {W₃ m : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W₃ (g * k) = W₃ g)
    (hm : m ∈ gl3CyclicSubspace W₃) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, m (g * k) = m g := by
  obtain ⟨U, hU, hWU⟩ := hsm
  induction hm using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨h, rfl⟩ := hf

    refine ⟨U.comap (MulAut.conj h⁻¹).toMonoidHom, hU.preimage ?_, fun k hk g => ?_⟩
    · show Continuous fun k : LocalGL3 v => (MulAut.conj h⁻¹) k
      simp only [MulAut.conj_apply, inv_inv]
      exact (continuous_const.mul continuous_id).mul continuous_const
    · have hk' : h⁻¹ * k * h ∈ U := by
        have := hk; rw [Subgroup.mem_comap] at this
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
      show W₃ (g * k * h) = W₃ (g * h)
      calc W₃ (g * k * h) = W₃ (g * h * (h⁻¹ * k * h)) := by group
        _ = W₃ (g * h) := hWU _ hk' _
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := h₁
    obtain ⟨U₂, hU₂, h₂⟩ := h₂
    exact ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => by
      rw [Pi.add_apply, Pi.add_apply, h₁ k hk.1 g, h₂ k hk.2 g]⟩
  | smul a f _ hf =>
    obtain ⟨U₁, hU₁, h₁⟩ := hf
    exact ⟨U₁, hU₁, fun k hk g => by rw [Pi.smul_apply, Pi.smul_apply, h₁ k hk g]⟩

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

theorem scalar_law_of_mem {v : HeightOneSpectrum (𝓞 ℚ)} {W₃ m : LocalGL3 v → ℂ} (c : (v.adicCompletion ℚ)ˣ → ℂ)
    (hlaw : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W₃ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = c t * W₃ h)
    (hm : m ∈ gl3CyclicSubspace W₃) :
    ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v), m (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = c t * m h := by
  induction hm using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    intro t h
    show W₃ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h * g) = c t * W₃ (h * g)
    rw [mul_assoc, hlaw]
  | zero => intro t h; simp
  | add f₁ f₂ _ _ h₁ h₂ => intro t h; rw [Pi.add_apply, Pi.add_apply, h₁, h₂, mul_add]
  | smul a f _ hf => intro t h; rw [Pi.smul_apply, Pi.smul_apply, hf, smul_eq_mul, smul_eq_mul]; ring

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

theorem finRoot₁_congr {g g' : AdelicGL 3 (𝓞 ℚ) ℚ} {v : HeightOneSpectrum (𝓞 ℚ)}
    (h : componentAt3 (𝓞 ℚ) ℚ v g = componentAt3 (𝓞 ℚ) ℚ v g') : finRoot₁ ℚ v g = finRoot₁ ℚ v g' := by
  unfold finRoot₁; rw [h]

theorem finRoot₂_congr {g g' : AdelicGL 3 (𝓞 ℚ) ℚ} {v : HeightOneSpectrum (𝓞 ℚ)}
    (h : componentAt3 (𝓞 ℚ) ℚ v g = componentAt3 (𝓞 ℚ) ℚ v g') : finRoot₂ ℚ v g = finRoot₂ ℚ v g' := by
  unfold finRoot₂; rw [h]

theorem archRoot_congr {g g' : AdelicGL 3 (𝓞 ℚ) ℚ} (h : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ g')
    (w : InfinitePlace ℚ) : archRoot₁ ℚ w g = archRoot₁ ℚ w g' ∧ archRoot₂ ℚ w g = archRoot₂ ℚ w g' := by
  have hc : archPlaceComponent3 ℚ w g = archPlaceComponent3 ℚ w g' := by
    unfold archPlaceComponent3; rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h]
  exact ⟨by unfold archRoot₁; rw [hc], by unfold archRoot₂; rw [hc]⟩

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "Converse.pinnedExp Converse.IsAdmissibleTwist Converse.IsArchCompAt TateLocal.addCharLevel TateLocal.localBorel TateLocal.selfDualHaarAt TateLocal.stdRootNumberAt TateLocal.higherUnitsAt TateLocal.mem_higherUnitsAt_iff TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.modulus TateLocal.modulus_ne_zero TateLocal.modulus_mul TateLocal.mulMeasure RealArchParam signShift RealArchParam.discrete RealArchParam.principal RankinSelberg.primeFibre CubicInduction.psiLoc CubicInduction.CubicInductionForm ratArchGL2 TateLocal.modulus_adicCompletion_eq_nnnorm CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt CubicInduction.isOpen_localMaximalCompact3 RankinSelberg.exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep RankinSelberg.exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3PsiWhittakerFnSpace gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 inducedCoeff psiLoc CubicInductionForm AdelicGL iotaGL iota localMaximalCompact3 componentAt3 archComponent3 LocalGL3 IsInducedSphericalAt IsRamifiedIn IsBadPlace inducedLevelAt archPlaceComponent3 diagUnitGL2 congruenceK1 HasSphericalTorusValuesAt lastRowSup bottomMinor minorSup detSize finRoot₁ finRoot₂ archRoot₁ archRoot₂ rootSizeProd InRootLevel IsGaugeMajorised3 dualWhittakerFn3 weylPrime3 CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul localZeta30 localZetaDual31 IsLocalZeta30ConvergentAbove IsLocalZeta31ConvergentAbove hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt isOpen_localMaximalCompact3 det_upperUnipotent3" namespace CubicInductionForm p2m_export "LanglandsTunnell.CubicInduction.CubicInductionForm" "zero whittakerArch spherical factorizable expansion centralChar central levelInvariant dualWhittaker whittaker whittakerLoc form whittakerLoc_law whittakerLoc_scalar_mul_eq_localChar_centralChar_mul" end LanglandsTunnell.CubicInduction.CubicInductionForm
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.CubicInductionForm" in
open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel _root_.LanglandsTunnell.CubicInduction in

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_gauge
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hbad : {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v}.Finite)
    (F : CubicInductionForm K pins ψ μ) (hF : F.form ≠ 0)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → F.whittakerLoc p h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖F.whittakerLoc p h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
  classical

  obtain ⟨g₀, hg₀⟩ := Ws23Cubic.exists_whittaker_ne_zero F hF
  have hfin := Filter.eventually_cofinite.1 (Ws23Cubic.eventually_componentAt3_mem g₀)
  let T₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) := hbad.toFinset ∪ {p} ∪ hfin.toFinset
  have hT₀ : ∀ w, IsBadPlace K μ w → w ∈ T₀ := fun w hw =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (hbad.mem_toFinset.2 hw))
  have hpT₀ : p ∈ T₀ := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self p))
  have hint : ∀ w, w ∉ T₀ → componentAt3 (𝓞 ℚ) ℚ w g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w := by
    intro w hw
    by_contra h
    exact hw (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))

  let gy : LocalGL3 p → AdelicGL 3 (𝓞 ℚ) ℚ := fun y =>
    g₀ * Ws23PlaceEmbed3.placeEmbed3 (𝓞 ℚ) ℚ p ((componentAt3 (𝓞 ℚ) ℚ p g₀)⁻¹ * y)
  have hgy_p : ∀ y, componentAt3 (𝓞 ℚ) ℚ p (gy y) = y := fun y => by
    simp only [gy, map_mul, Ws23PlaceEmbed3.componentAt3_placeEmbed3_self, mul_inv_cancel_left]
  have hgy_w : ∀ y, ∀ w ≠ p, componentAt3 (𝓞 ℚ) ℚ w (gy y) = componentAt3 (𝓞 ℚ) ℚ w g₀ := fun y w hw => by
    simp only [gy, map_mul, Ws23PlaceEmbed3.componentAt3_placeEmbed3_of_ne (𝓞 ℚ) ℚ p _ hw, mul_one]
  have hgy_arch : ∀ y, archComponent3 (𝓞 ℚ) ℚ (gy y) = archComponent3 (𝓞 ℚ) ℚ g₀ := fun y => by
    simp only [gy, map_mul, Ws23PlaceEmbed3.archComponent3_placeEmbed3, mul_one]

  set A : ℂ := F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g₀) *
    ∏ w ∈ T₀.erase p, F.whittakerLoc w (componentAt3 (𝓞 ℚ) ℚ w g₀) with hA
  have hfacy : ∀ y, F.whittaker (gy y) = A * F.whittakerLoc p y := by
    intro y
    rw [F.factorizable (gy y) T₀ hT₀ (fun w hw => by
      rw [hgy_w y w (fun h => hw (h ▸ hpT₀))]; exact hint w hw), hgy_arch, ← Finset.mul_prod_erase T₀ _ hpT₀, hgy_p,
      Finset.prod_congr rfl fun w hw => by rw [hgy_w y w (Finset.ne_of_mem_erase hw)], hA]
    ring
  have hA0 : A ≠ 0 := by
    intro h0
    apply hg₀
    rw [F.factorizable g₀ T₀ hT₀ hint, ← Finset.mul_prod_erase T₀ _ hpT₀,
      show F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g₀) *
        (F.whittakerLoc p (componentAt3 (𝓞 ℚ) ℚ p g₀) * ∏ w ∈ T₀.erase p, F.whittakerLoc w (componentAt3 (𝓞 ℚ) ℚ w g₀)) =
        A * F.whittakerLoc p (componentAt3 (𝓞 ℚ) ℚ p g₀) from by rw [hA]; ring, h0, zero_mul]
  have hApos : 0 < ‖A‖ := norm_pos_iff.2 hA0

  obtain ⟨t, T, B, hN⟩ := hFg
  obtain ⟨C, hC⟩ := hN 0

  have hlev0 : InRootLevel ℚ T B g₀ := by
    by_contra h
    exact hg₀ ((hC g₀).1 h)

  let Bp : ℝ := if p ∈ T then B else 1
  have hroot_w : ∀ y, ∀ w ≠ p, finRoot₁ ℚ w (gy y) = finRoot₁ ℚ w g₀ ∧ finRoot₂ ℚ w (gy y) = finRoot₂ ℚ w g₀ :=
    fun y w hw => ⟨Ws23Cubic.finRoot₁_congr (hgy_w y w hw), Ws23Cubic.finRoot₂_congr (hgy_w y w hw)⟩
  have hroot_p : ∀ y, finRoot₁ ℚ p (gy y) = detSize y * lastRowSup y / minorSup y ^ 2 ∧
      finRoot₂ ℚ p (gy y) = minorSup y / lastRowSup y ^ 2 := fun y => by
    unfold finRoot₁ finRoot₂; rw [hgy_p]; exact ⟨rfl, rfl⟩
  have hbox_of : ∀ y, InRootLevel ℚ T B (gy y) →
      (detSize y * lastRowSup y / minorSup y ^ 2 ≤ Bp ∧ minorSup y / lastRowSup y ^ 2 ≤ Bp) := by
    intro y hl
    by_cases hp : p ∈ T
    · have h := hl.2 p hp
      rw [(hroot_p y).1, (hroot_p y).2] at h
      simp only [Bp, if_pos hp]; exact h
    · have h := hl.1 p hp
      rw [(hroot_p y).1, (hroot_p y).2] at h
      simp only [Bp, if_neg hp]; exact h
  have hlev_of : ∀ y, (detSize y * lastRowSup y / minorSup y ^ 2 ≤ Bp ∧ minorSup y / lastRowSup y ^ 2 ≤ Bp) →
      InRootLevel ℚ T B (gy y) := by
    intro y hb
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · by_cases hwp : w = p
      · subst hwp
        rw [(hroot_p y).1, (hroot_p y).2]
        simp only [Bp, if_neg hw] at hb; exact hb
      · rw [(hroot_w y w hwp).1, (hroot_w y w hwp).2]; exact hlev0.1 w hw
    · by_cases hwp : w = p
      · subst hwp
        rw [(hroot_p y).1, (hroot_p y).2]
        simp only [Bp, if_pos hw] at hb; exact hb
      · rw [(hroot_w y w hwp).1, (hroot_w y w hwp).2]; exact hlev0.2 w hw

  let f : HeightOneSpectrum (𝓞 ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ → ℝ := fun v g => finRoot₁ ℚ v g * finRoot₂ ℚ v g
  have hf_w : ∀ y, ∀ w ≠ p, f w (gy y) = f w g₀ := fun y w hw => by
    simp only [f, (hroot_w y w hw).1, (hroot_w y w hw).2]
  have hf_p : ∀ y, f p (gy y) = (detSize y * lastRowSup y / minorSup y ^ 2) * (minorSup y / lastRowSup y ^ 2) := fun y => by
    simp only [f, (hroot_p y).1, (hroot_p y).2]
  have harchprod : ∀ y, (∏ w : InfinitePlace ℚ, archRoot₁ ℚ w (gy y) * archRoot₂ ℚ w (gy y)) =
      ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g₀ * archRoot₂ ℚ w g₀ := fun y =>
    Finset.prod_congr rfl fun w _ => by
      rw [(Ws23Cubic.archRoot_congr (hgy_arch y) w).1, (Ws23Cubic.archRoot_congr (hgy_arch y) w).2]
  have hrsp : ∀ y, rootSizeProd ℚ (gy y) = (∏ᶠ v, f v (gy y)) * ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g₀ * archRoot₂ ℚ w g₀ :=
    fun y => by unfold rootSizeProd; rw [harchprod y]

  have hbound : ∀ y, InRootLevel ℚ T B (gy y) → ‖F.whittakerLoc p y‖ ≤ (C / rootSizeProd ℚ (gy y) ^ t) / ‖A‖ := by
    intro y hl
    have h := (hC (gy y)).2 hl
    rw [pow_zero, mul_one, hfacy, norm_mul] at h
    rw [le_div_iff₀ hApos, mul_comm]; exact h
  by_cases hS₀ : (Function.mulSupport fun v => f v g₀).Finite
  ·
    let s : Finset (HeightOneSpectrum (𝓞 ℚ)) := insert p hS₀.toFinset
    set Q₀ : ℝ := (∏ v ∈ s.erase p, f v g₀) * ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g₀ * archRoot₂ ℚ w g₀ with hQ₀
    have hprod : ∀ y, rootSizeProd ℚ (gy y) =
        ((detSize y * lastRowSup y / minorSup y ^ 2) * (minorSup y / lastRowSup y ^ 2)) * Q₀ := by
      intro y
      have hsub : (Function.mulSupport fun v => f v (gy y)) ⊆ ↑s := by
        intro v hv
        by_cases hvp : v = p
        · subst hvp; exact Finset.mem_coe.2 (Finset.mem_insert_self _ _)
        · rw [Function.mem_mulSupport, hf_w y v hvp] at hv
          exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (hS₀.mem_toFinset.2 hv))
      rw [hrsp, finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.mul_prod_erase s _ (Finset.mem_insert_self _ _),
        hf_p, Finset.prod_congr rfl fun v hv => hf_w y v (Finset.ne_of_mem_erase hv), hQ₀]
      ring
    refine ⟨Bp, t, C / (Q₀ ^ t * ‖A‖), fun y => ⟨fun hnb => ?_, fun hb => ?_⟩⟩
    · have h0 := (hC (gy y)).1 (fun hl => hnb (hbox_of y hl))
      rw [hfacy] at h0
      exact (mul_eq_zero.1 h0).resolve_left hA0
    · have h := hbound y (hlev_of y hb)
      rw [hprod y] at h
      calc ‖F.whittakerLoc p y‖ ≤ _ := h
        _ = C / (Q₀ ^ t * ‖A‖) / ((detSize y * lastRowSup y / minorSup y ^ 2) * (minorSup y / lastRowSup y ^ 2)) ^ t := by
            rw [mul_pow]; ring
  ·
    set Q₀ : ℝ := ∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g₀ * archRoot₂ ℚ w g₀ with hQ₀
    have hprod : ∀ y, rootSizeProd ℚ (gy y) = Q₀ := by
      intro y
      have hinf : (Function.mulSupport fun v => f v (gy y)).Infinite := by
        refine Set.Infinite.mono (fun v hv => ?_) ((Set.not_finite.1 hS₀).diff (Set.finite_singleton p))
        obtain ⟨hv1, hv2⟩ := hv
        rw [Function.mem_mulSupport, hf_w y v hv2]
        exact hv1
      rw [hrsp, finprod_of_infinite_mulSupport hinf, one_mul]
    refine ⟨Bp, 0, C / Q₀ ^ t / ‖A‖, fun y => ⟨fun hnb => ?_, fun hb => ?_⟩⟩
    · have h0 := (hC (gy y)).1 (fun hl => hnb (hbox_of y hl))
      rw [hfacy] at h0
      exact (mul_eq_zero.1 h0).resolve_left hA0
    · have h := hbound y (hlev_of y hb)
      rw [hprod y] at h
      rw [pow_zero, div_one]
      exact h

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section W2
open UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel NumberField.TateGlobal AdelicDock

namespace Ws23W2

section Twist

variable {G : Type*} [Group G]

theorem span_translates_mul_eq_map (χ : G → ℂ) (hχ : ∀ g h, χ (g * h) = χ g * χ h)
    (hχ0 : ∀ g, χ g ≠ 0) (f : G → ℂ) :
    Submodule.span ℂ (Set.range fun h : G => fun g : G => χ (g * h) * f (g * h)) =
      (Submodule.span ℂ (Set.range fun h : G => fun g : G => f (g * h))).map
        (LinearMap.mulLeft ℂ χ) := by
  rw [Submodule.map_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    dsimp only
    have hfun : (fun g : G => χ (g * h) * f (g * h)) =
        χ h • (LinearMap.mulLeft ℂ χ (fun g : G => f (g * h))) := by
      funext g
      simp only [Pi.smul_apply, LinearMap.mulLeft_apply, Pi.mul_apply, smul_eq_mul, hχ]
      ring
    rw [hfun]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨h, rfl⟩, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    dsimp only
    have hfun : LinearMap.mulLeft ℂ χ (fun g : G => f (g * h)) =
        (χ h)⁻¹ • (fun g : G => χ (g * h) * f (g * h)) := by
      funext g
      simp only [Pi.smul_apply, LinearMap.mulLeft_apply, Pi.mul_apply, smul_eq_mul, hχ]
      field_simp [hχ0 h]
    rw [hfun]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem twist_irreducible_aux (χ : G → ℂ) (hχ : ∀ g h, χ (g * h) = χ g * χ h) (hχ0 : ∀ g, χ g ≠ 0)
    (V : Submodule ℂ (G → ℂ))
    (hVstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hVirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)))
    (w : G → ℂ) (hw : w ∈ V) (_hw0 : w ≠ 0) :
    ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => (fun g : G => χ g * w g) (g * h)),
      w' ≠ 0 → (fun g : G => χ g * w g) ∈
        Submodule.span ℂ (Set.range fun h : G => fun g : G => w' (g * h)) := by
  intro w' hw' hw'0
  have key := span_translates_mul_eq_map χ hχ hχ0
  beta_reduce at hw'
  rw [key w, Submodule.mem_map] at hw'
  obtain ⟨u, hu, rfl⟩ := hw'
  have hle : Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) ≤ V :=
    Submodule.span_le.mpr (by rintro _ ⟨h, rfl⟩; exact hVstab w hw h)
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hw'0 (map_zero _)
  have hmem : LinearMap.mulLeft ℂ χ w ∈
      (Submodule.span ℂ (Set.range fun h : G => fun g : G => u (g * h))).map (LinearMap.mulLeft ℂ χ) :=
    Submodule.mem_map_of_mem (hVirr u (hle hu) hu0 w hw)
  rw [← key u] at hmem
  simpa only [LinearMap.mulLeft_apply, Pi.mul_def] using hmem

end Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

variable (p : HeightOneSpectrum (𝓞 ℚ))

noncomputable def twistChar (g : GL (Fin 2) (p.adicCompletion ℚ)) : ℂ :=
  ((LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))

theorem twistChar_mul (g h : GL (Fin 2) (p.adicCompletion ℚ)) :
    twistChar p (g * h) = twistChar p g * twistChar p h := by
  unfold twistChar
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem modulus_cast_ne_zero (z : (p.adicCompletion ℚ)ˣ) :
    ((LanglandsTunnell.TateLocal.modulus (z : p.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast modulus_ne_zero z.ne_zero

theorem twistChar_ne_zero (g : GL (Fin 2) (p.adicCompletion ℚ)) : twistChar p g ≠ 0 := by
  unfold twistChar
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (modulus_cast_ne_zero p _)

theorem twistChar_scalar_mul (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    twistChar p (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
      ((LanglandsTunnell.TateLocal.modulus (z : p.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ * twistChar p g := by
  have hmz := modulus_cast_ne_zero p z
  have hhalf : ((LanglandsTunnell.TateLocal.modulus (z : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
      ((LanglandsTunnell.TateLocal.modulus (z : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((LanglandsTunnell.TateLocal.modulus (z : p.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hmz, ← Complex.cpow_neg_one]
    congr 1
    ring
  unfold twistChar
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_mul, Units.val_pow_eq_pow_val,
    pow_two, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
    modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), hhalf]

theorem det_placeEmbed_diagOne (z : (p.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (placeEmbed ℚ p (diagOne z)) =
      Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ p z) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, placeEmbed, MonoidHom.comp_apply,
    AdelicDock.coe_finEmbed, AdelicDock.coe_localEmbed]
  refine Prod.ext ?_ ?_
  · change adeleArch (𝓞 ℚ) ℚ (Matrix.det (n := Fin 2) _) = _
    rw [RingHom.map_det, AdelicDock.mapMatrix_arch_finMat, Matrix.det_one]
    rfl
  · change adeleFin (𝓞 ℚ) ℚ (Matrix.det (n := Fin 2) _) =
      ((localUnit (𝓞 ℚ) ℚ p z : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [RingHom.map_det, AdelicDock.mapMatrix_fin_finMat]
    apply FiniteAdeleRing.ext
    intro w
    change finAdeleEval (𝓞 ℚ) ℚ w (Matrix.det (n := Fin 2) _) = _
    rw [RingHom.map_det]
    by_cases hw : w = p
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self, localUnit_apply_self, Matrix.det_fin_two]
      simp [diagOne_coe_apply]
    · rw [AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hw, localUnit_apply_of_ne _ _ _ _ hw, Matrix.det_one]

theorem ideleNorm_finIncl_localUnit (z : (p.adicCompletion ℚ)ˣ) :
    ideleNorm ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ p z)) =
      (LanglandsTunnell.TateLocal.modulus (z : p.adicCompletion ℚ) : ℝ) := by
  rw [← det_placeEmbed_diagOne, ideleNorm_det_placeEmbed]
  congr 3
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp [diagOne_coe_apply]

theorem localChar_untwist (ξ η₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hη₀ : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ((η₀ z : ℂˣ) : ℂ) = ((ξ z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm ℚ z : ℝ) : ℂ))⁻¹)
    (z : (p.adicCompletion ℚ)ˣ) :
    ((localChar η₀ p z : ℂˣ) : ℂ) =
      ((localChar ξ p z : ℂˣ) : ℂ) * (((LanglandsTunnell.TateLocal.modulus (z : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ := by
  rw [localChar_apply, localChar_apply, hη₀, ideleNorm_finIncl_localUnit]

theorem twist_irreducible (p : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hVstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V)
    (hVirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h)))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : w ∈ V) (hw0 : w ≠ 0) :
    ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (-(1 / 2 : ℂ)) * w g) (g * h)),
      w' ≠ 0 → (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (-(1 / 2 : ℂ)) * w g) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w' (g * h)) := by
  exact twist_irreducible_aux (twistChar p) (twistChar_mul p) (twistChar_ne_zero p) V hVstab hVirr w hw hw0

theorem twist_central (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (ξ η₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hη₀ : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ((η₀ z : ℂˣ) : ℂ) = ((ξ z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm ℚ z : ℝ) : ℂ))⁻¹)
    (hwcen : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((NumberField.TateGlobal.localChar ξ p z : ℂˣ) : ℂ) * w g) :
    ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (-(1 / 2 : ℂ)) * w g) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
        ((NumberField.TateGlobal.localChar η₀ p z : ℂˣ) : ℂ) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (-(1 / 2 : ℂ)) * w g) g := by
  intro z g
  show twistChar p (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) * w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
    ((localChar η₀ p z : ℂˣ) : ℂ) * (twistChar p g * w g)
  rw [twistChar_scalar_mul, hwcen, localChar_untwist p ξ η₀ hη₀]
  ring

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

theorem Ws23W2.phicen
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ) :
    ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * x) =
        (((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) z : ℂˣ) : ℂ) * φ x := by
  intro z x
  letI := (productionPinsGeneral ℚ).mS
  have ht := (((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z R.centralChar
    (productionPinsGeneral ℚ).D φ).mp hiso.smoothCusp.1.1).1).central_transform (Subgroup.topEquiv.symm z) x
  exact ht

end W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker MeasureTheory"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Nrest

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5Holes"

section CutOff

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

end CutOff
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Nrest
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section Eta0Off
open NumberField.AdelicLevel NumberField.TateGlobal AdelicDock Ws23Fam5Holes

end Eta0Off
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Tw

open LanglandsTunnell.TateLocal in

theorem twist_admissible_gl2 (p : HeightOneSpectrum (𝓞 ℚ))
    (Vp : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hVstab : ∀ W ∈ Vp, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ Vp)
    (hVadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ Vp,
        (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
          W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : w ∈ Vp) :
    ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (-(1 / 2 : ℂ)) * w g) (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
            w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) := by
  classical
  intro U hU

  set δ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) with hδ
  have hδmul : ∀ g h : GL (Fin 2) (p.adicCompletion ℚ), δ (g * h) = δ g * δ h := by
    intro g h
    simp only [hδ]
    rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  have hδne : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), δ g ≠ 0 := by
    intro g
    simp only [hδ]
    exact Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.2
      (Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2 (Ws23SwapStep.modulus_det_pos p g).ne'))
  let M : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    { toFun := fun f g => δ g * f g
      map_add' := fun f f' => by funext g; simp only [Pi.add_apply]; ring
      map_smul' := fun c f => by funext g; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hM : ∀ f g, M f g = δ g * f g := fun _ _ => rfl

  set K₀ := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ with hK₀
  have hK₀o : IsOpen (K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    rw [hK₀]; exact (Ws23Fam5Holes.localLevelOne_isCompact_isOpen p (top_ne_bot : (⊤ : Ideal (𝓞 ℚ)) ≠ ⊥)).2
  have hδK : ∀ k ∈ K₀, δ k = 1 := by
    intro k hk
    simp only [hδ]
    rw [hK₀] at hk
    rw [Ws23PencSwap.modulus_det_eq_one_of_mem_localLevelOne p hk, NNReal.coe_one, Complex.ofReal_one,
      Complex.one_cpow]
  obtain ⟨B, hB⟩ := hVadm (U ⊓ K₀) (hU.inter hK₀o)
  refine ⟨B.image M, fun w' hw' hfix => ?_⟩

  have hsub : Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => δ g * w g) (g * h)) ≤ Vp.map M := by
    rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    refine ⟨(δ h) • fun g => w (g * h), Vp.smul_mem _ (hVstab w hw h), ?_⟩
    funext g
    simp only [hM, Pi.smul_apply, smul_eq_mul, hδmul]
    ring
  have hw'' : w' ∈ Vp.map M := hsub (by simpa only [← hδ] using hw')
  obtain ⟨W, hWV, rfl⟩ := Submodule.mem_map.1 hw''

  have hWfix : ∀ k ∈ U ⊓ K₀, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g := by
    intro k hk g
    obtain ⟨hkU, hkK⟩ := Subgroup.mem_inf.1 hk
    have h := hfix k hkU g
    simp only [hM, hδmul, hδK k hkK, mul_one] at h
    exact mul_left_cancel₀ (hδne g) h
  have hWB := hB W hWV hWfix
  rw [Finset.coe_image, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hWB

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23PencMatch

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg"

end Ws23PencMatch
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5Holes

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction UnramifiedWhittaker"

end Ws23Fam5Holes
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Regroup

end Ws23Regroup
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Away

p2m_open "IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction LanglandsTunnell.Converse LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg UnramifiedWhittaker P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg.EntirePairAssembly.Prefactor"

end Ws23Away
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Cubic

open IsDedekindDomain NumberField MeasureTheory

end Ws23Cubic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

section W2EtaArch
open NumberField.AdelicVolume NumberField.InfinitePlace.Completion LanglandsTunnell.Converse

namespace Ws23W2

end Ws23W2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end W2EtaArch
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23GaugeMem

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction Matrix"

variable {L : Type*} [NormedField L]

def LocalGauge (W : GL (Fin 3) L → ℂ) : Prop :=
  ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : GL (Fin 3) L,
    (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
    (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
      ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)

theorem lastRowSup_nonneg (k : GL (Fin 3) L) : 0 ≤ lastRowSup k :=
  le_max_of_le_right (norm_nonneg _)

theorem minorSup_nonneg (k : GL (Fin 3) L) : 0 ≤ minorSup k :=
  le_max_of_le_right (norm_nonneg _)

theorem norm_entry_le_lastRowSup (k : GL (Fin 3) L) (j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ lastRowSup k := by
  unfold lastRowSup
  fin_cases j
  · exact le_max_of_le_left (le_max_left _ _)
  · exact le_max_of_le_left (le_max_right _ _)
  · exact le_max_right _ _

theorem norm_bottomMinor_le_minorSup (k : GL (Fin 3) L) :
    ‖bottomMinor k 0 1‖ ≤ minorSup k ∧ ‖bottomMinor k 0 2‖ ≤ minorSup k ∧ ‖bottomMinor k 1 2‖ ≤ minorSup k :=
  ⟨le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _), le_max_right _ _⟩

theorem det_ne_zero (k : GL (Fin 3) L) : (k : Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact (Matrix.GeneralLinearGroup.det k).ne_zero

theorem detSize_pos (k : GL (Fin 3) L) : 0 < detSize k :=
  norm_pos_iff.2 (det_ne_zero k)

theorem lastRowSup_pos (k : GL (Fin 3) L) : 0 < lastRowSup k := by
  by_contra hle
  have h0 : lastRowSup k = 0 := le_antisymm (not_lt.1 hle) (lastRowSup_nonneg k)
  apply det_ne_zero k
  refine Matrix.det_eq_zero_of_row_eq_zero 2 fun j => ?_
  have h := norm_entry_le_lastRowSup k j
  rw [h0] at h
  exact norm_le_zero_iff.1 h

theorem det_eq_bottomMinors (k : GL (Fin 3) L) :
    (k : Matrix (Fin 3) (Fin 3) L).det =
      (k : Matrix (Fin 3) (Fin 3) L) 0 0 * bottomMinor k 1 2 - (k : Matrix (Fin 3) (Fin 3) L) 0 1 * bottomMinor k 0 2 +
        (k : Matrix (Fin 3) (Fin 3) L) 0 2 * bottomMinor k 0 1 := by
  rw [Matrix.det_fin_three]
  unfold bottomMinor
  ring

theorem minorSup_pos (k : GL (Fin 3) L) : 0 < minorSup k := by
  by_contra hle
  have h0 : minorSup k = 0 := le_antisymm (not_lt.1 hle) (minorSup_nonneg k)
  obtain ⟨h1, h2, h3⟩ := norm_bottomMinor_le_minorSup k
  rw [h0, norm_le_zero_iff] at h1 h2 h3
  apply det_ne_zero k
  rw [det_eq_bottomMinors, h1, h2, h3]
  ring

theorem root₁_pos (h : GL (Fin 3) L) : 0 < detSize h * lastRowSup h / minorSup h ^ 2 :=
  div_pos (mul_pos (detSize_pos h) (lastRowSup_pos h)) (pow_pos (minorSup_pos h) 2)

theorem root₂_pos (h : GL (Fin 3) L) : 0 < minorSup h / lastRowSup h ^ 2 :=
  div_pos (minorSup_pos h) (pow_pos (lastRowSup_pos h) 2)

def entrySum (k : GL (Fin 3) L) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖

theorem entrySum_nonneg (k : GL (Fin 3) L) : 0 ≤ entrySum k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_entry_le_entrySum (k : GL (Fin 3) L) (i j : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ entrySum k := by
  unfold entrySum
  calc ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖
      ≤ ∑ j' : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem entrySum_pos (k : GL (Fin 3) L) : 0 < entrySum k :=
  lt_of_lt_of_le (lt_of_lt_of_le (lastRowSup_pos k) (by
    unfold lastRowSup
    exact max_le (max_le (norm_entry_le_entrySum k 2 0) (norm_entry_le_entrySum k 2 1)) (norm_entry_le_entrySum k 2 2)))
    le_rfl

theorem detSize_mul (h k : GL (Fin 3) L) : detSize (h * k) = detSize h * detSize k := by
  unfold detSize
  rw [Units.val_mul, Matrix.det_mul, norm_mul]

theorem lastRowSup_mul_le (h k : GL (Fin 3) L) : lastRowSup (h * k) ≤ lastRowSup h * entrySum k := by
  have hrow : ∀ j : Fin 3, ‖((h * k : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 j‖ ≤ lastRowSup h * entrySum k := by
    intro j
    rw [Units.val_mul, Matrix.mul_apply]
    calc ‖∑ i : Fin 3, (h : Matrix (Fin 3) (Fin 3) L) 2 i * (k : Matrix (Fin 3) (Fin 3) L) i j‖
        ≤ ∑ i : Fin 3, ‖(h : Matrix (Fin 3) (Fin 3) L) 2 i * (k : Matrix (Fin 3) (Fin 3) L) i j‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, lastRowSup h * ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_entry_le_lastRowSup h i) (norm_nonneg _)
      _ = lastRowSup h * ∑ i : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ lastRowSup h * entrySum k :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
            Finset.single_le_sum (f := fun j' => ‖(k : Matrix (Fin 3) (Fin 3) L) i j'‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_univ j)) (lastRowSup_nonneg h)
  unfold lastRowSup
  exact max_le (max_le (hrow 0) (hrow 1)) (hrow 2)

theorem bottomMinor_mul (h k : GL (Fin 3) L) (j j' : Fin 3) :
    bottomMinor (h * k) j j' =
      bottomMinor h 0 1 * ((k : Matrix (Fin 3) (Fin 3) L) 0 j * (k : Matrix (Fin 3) (Fin 3) L) 1 j' -
          (k : Matrix (Fin 3) (Fin 3) L) 0 j' * (k : Matrix (Fin 3) (Fin 3) L) 1 j) +
      bottomMinor h 0 2 * ((k : Matrix (Fin 3) (Fin 3) L) 0 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
          (k : Matrix (Fin 3) (Fin 3) L) 0 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j) +
      bottomMinor h 1 2 * ((k : Matrix (Fin 3) (Fin 3) L) 1 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
          (k : Matrix (Fin 3) (Fin 3) L) 1 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j) := by
  unfold bottomMinor
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem norm_kminor_le (k : GL (Fin 3) L) (a b j j' : Fin 3) :
    ‖(k : Matrix (Fin 3) (Fin 3) L) a j * (k : Matrix (Fin 3) (Fin 3) L) b j' -
        (k : Matrix (Fin 3) (Fin 3) L) a j' * (k : Matrix (Fin 3) (Fin 3) L) b j‖ ≤ 2 * entrySum k ^ 2 := by
  have hE := entrySum_nonneg k
  have h1 : ‖(k : Matrix (Fin 3) (Fin 3) L) a j * (k : Matrix (Fin 3) (Fin 3) L) b j'‖ ≤ entrySum k ^ 2 := by
    rw [norm_mul, sq]
    exact mul_le_mul (norm_entry_le_entrySum k a j) (norm_entry_le_entrySum k b j') (norm_nonneg _) hE
  have h2 : ‖(k : Matrix (Fin 3) (Fin 3) L) a j' * (k : Matrix (Fin 3) (Fin 3) L) b j‖ ≤ entrySum k ^ 2 := by
    rw [norm_mul, sq]
    exact mul_le_mul (norm_entry_le_entrySum k a j') (norm_entry_le_entrySum k b j) (norm_nonneg _) hE
  calc _ ≤ ‖(k : Matrix (Fin 3) (Fin 3) L) a j * (k : Matrix (Fin 3) (Fin 3) L) b j'‖ +
        ‖(k : Matrix (Fin 3) (Fin 3) L) a j' * (k : Matrix (Fin 3) (Fin 3) L) b j‖ := norm_sub_le _ _
    _ ≤ entrySum k ^ 2 + entrySum k ^ 2 := add_le_add h1 h2
    _ = 2 * entrySum k ^ 2 := by ring

theorem minorSup_mul_le (h k : GL (Fin 3) L) : minorSup (h * k) ≤ 6 * entrySum k ^ 2 * minorSup h := by
  obtain ⟨m1, m2, m3⟩ := norm_bottomMinor_le_minorSup h
  have hM := minorSup_nonneg h
  have hmin : ∀ j j' : Fin 3, ‖bottomMinor (h * k) j j'‖ ≤ 6 * entrySum k ^ 2 * minorSup h := by
    intro j j'
    rw [bottomMinor_mul]
    have b1 := norm_kminor_le k 0 1 j j'
    have b2 := norm_kminor_le k 0 2 j j'
    have b3 := norm_kminor_le k 1 2 j j'
    calc _ ≤ ‖bottomMinor h 0 1 * ((k : Matrix (Fin 3) (Fin 3) L) 0 j * (k : Matrix (Fin 3) (Fin 3) L) 1 j' -
              (k : Matrix (Fin 3) (Fin 3) L) 0 j' * (k : Matrix (Fin 3) (Fin 3) L) 1 j)‖ +
            ‖bottomMinor h 0 2 * ((k : Matrix (Fin 3) (Fin 3) L) 0 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
              (k : Matrix (Fin 3) (Fin 3) L) 0 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j)‖ +
            ‖bottomMinor h 1 2 * ((k : Matrix (Fin 3) (Fin 3) L) 1 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
              (k : Matrix (Fin 3) (Fin 3) L) 1 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j)‖ := norm_add₃_le
      _ ≤ minorSup h * (2 * entrySum k ^ 2) + minorSup h * (2 * entrySum k ^ 2) + minorSup h * (2 * entrySum k ^ 2) := by
          rw [norm_mul, norm_mul, norm_mul]
          exact add_le_add (add_le_add (mul_le_mul m1 b1 (norm_nonneg _) hM) (mul_le_mul m2 b2 (norm_nonneg _) hM))
            (mul_le_mul m3 b3 (norm_nonneg _) hM)
      _ = 6 * entrySum k ^ 2 * minorSup h := by ring
  unfold minorSup
  exact max_le (max_le (hmin 0 1) (hmin 0 2)) (hmin 1 2)

theorem lastRowSup_le_mul_inv (h k : GL (Fin 3) L) : lastRowSup h ≤ lastRowSup (h * k) * entrySum k⁻¹ := by
  have := lastRowSup_mul_le (h * k) k⁻¹
  rwa [mul_inv_cancel_right] at this

theorem minorSup_le_mul_inv (h k : GL (Fin 3) L) : minorSup h ≤ 6 * entrySum k⁻¹ ^ 2 * minorSup (h * k) := by
  have := minorSup_mul_le (h * k) k⁻¹
  rwa [mul_inv_cancel_right] at this

theorem root₁_mul_ge (h k : GL (Fin 3) L) :
    detSize k / (36 * entrySum k⁻¹ * entrySum k ^ 4) * (detSize h * lastRowSup h / minorSup h ^ 2) ≤
      detSize (h * k) * lastRowSup (h * k) / minorSup (h * k) ^ 2 := by
  have hE := entrySum_pos k
  have hE' := entrySum_pos k⁻¹
  have hD := detSize_pos k
  have hd := detSize_pos h
  have hr := lastRowSup_pos h
  have hm := minorSup_pos h
  have hr' := lastRowSup_pos (h * k)
  have hm' := minorSup_pos (h * k)
  have h1 : lastRowSup h ≤ lastRowSup (h * k) * entrySum k⁻¹ := lastRowSup_le_mul_inv h k
  have h2 : minorSup (h * k) ≤ 6 * entrySum k ^ 2 * minorSup h := minorSup_mul_le h k
  rw [detSize_mul, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]

  have h2' : minorSup (h * k) ^ 2 ≤ (6 * entrySum k ^ 2 * minorSup h) ^ 2 :=
    pow_le_pow_left₀ hm'.le h2 2
  calc detSize k * (detSize h * lastRowSup h) * minorSup (h * k) ^ 2
      ≤ detSize k * (detSize h * (lastRowSup (h * k) * entrySum k⁻¹)) * (6 * entrySum k ^ 2 * minorSup h) ^ 2 := by
        gcongr
    _ = detSize h * detSize k * lastRowSup (h * k) * (36 * entrySum k⁻¹ * entrySum k ^ 4 * minorSup h ^ 2) := by ring

theorem root₂_mul_ge (h k : GL (Fin 3) L) :
    1 / (6 * entrySum k⁻¹ ^ 2 * entrySum k ^ 2) * (minorSup h / lastRowSup h ^ 2) ≤
      minorSup (h * k) / lastRowSup (h * k) ^ 2 := by
  have hE := entrySum_pos k
  have hE' := entrySum_pos k⁻¹
  have hr := lastRowSup_pos h
  have hm := minorSup_pos h
  have hr' := lastRowSup_pos (h * k)
  have hm' := minorSup_pos (h * k)
  have h1 : lastRowSup (h * k) ≤ lastRowSup h * entrySum k := lastRowSup_mul_le h k
  have h2 : minorSup h ≤ 6 * entrySum k⁻¹ ^ 2 * minorSup (h * k) := minorSup_le_mul_inv h k
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1' : lastRowSup (h * k) ^ 2 ≤ (lastRowSup h * entrySum k) ^ 2 := pow_le_pow_left₀ hr'.le h1 2
  calc minorSup h * lastRowSup (h * k) ^ 2
      ≤ (6 * entrySum k⁻¹ ^ 2 * minorSup (h * k)) * (lastRowSup h * entrySum k) ^ 2 := by gcongr
    _ = minorSup (h * k) * (6 * entrySum k⁻¹ ^ 2 * entrySum k ^ 2 * lastRowSup h ^ 2) := by ring

theorem translate (W : GL (Fin 3) L → ℂ) (k : GL (Fin 3) L) (hW : LocalGauge W) :
    LocalGauge (fun h => W (h * k)) := by
  obtain ⟨B, t, C, hW⟩ := hW
  set c₁ : ℝ := detSize k / (36 * entrySum k⁻¹ * entrySum k ^ 4) with hc₁
  set c₂ : ℝ := 1 / (6 * entrySum k⁻¹ ^ 2 * entrySum k ^ 2) with hc₂
  have hE := entrySum_pos k
  have hE' := entrySum_pos k⁻¹
  have hc₁pos : 0 < c₁ := by rw [hc₁]; exact div_pos (detSize_pos k) (by positivity)
  have hc₂pos : 0 < c₂ := by rw [hc₂]; exact div_pos one_pos (by positivity)
  refine ⟨max (B / c₁) (B / c₂), t, max C 0 / (c₁ * c₂) ^ t, fun h => ?_⟩
  have g₁ := root₁_mul_ge h k
  have g₂ := root₂_mul_ge h k
  rw [← hc₁] at g₁
  rw [← hc₂] at g₂
  have x₁ := root₁_pos h
  have x₂ := root₂_pos h
  have y₁ := root₁_pos (h * k)
  have y₂ := root₂_pos (h * k)
  constructor
  ·
    intro hnot
    refine (hW (h * k)).1 fun hbox => hnot ⟨?_, ?_⟩
    · exact le_trans ((le_div_iff₀' hc₁pos).2 (le_trans g₁ hbox.1)) (le_max_left _ _)
    · exact le_trans ((le_div_iff₀' hc₂pos).2 (le_trans g₂ hbox.2)) (le_max_right _ _)
  ·
    intro _
    show ‖W (h * k)‖ ≤ _
    have hprod : (c₁ * c₂) * ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ≤
        (detSize (h * k) * lastRowSup (h * k) / minorSup (h * k) ^ 2) * (minorSup (h * k) / lastRowSup (h * k) ^ 2) := by
      calc (c₁ * c₂) * ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2))
          = (c₁ * (detSize h * lastRowSup h / minorSup h ^ 2)) * (c₂ * (minorSup h / lastRowSup h ^ 2)) := by ring
        _ ≤ _ := mul_le_mul g₁ g₂ (by positivity) y₁.le
    have hpow := pow_le_pow_left₀ (by positivity) hprod t
    rw [mul_pow] at hpow
    by_cases hbox : detSize (h * k) * lastRowSup (h * k) / minorSup (h * k) ^ 2 ≤ B ∧
        minorSup (h * k) / lastRowSup (h * k) ^ 2 ≤ B
    · have hb := (hW (h * k)).2 hbox
      have hC : 0 ≤ C := by
        have := le_trans (norm_nonneg _) hb
        rwa [le_div_iff₀ (pow_pos (mul_pos y₁ y₂) t), zero_mul] at this
      calc ‖W (h * k)‖ ≤ C / ((detSize (h * k) * lastRowSup (h * k) / minorSup (h * k) ^ 2) *
            (minorSup (h * k) / lastRowSup (h * k) ^ 2)) ^ t := hb
        _ ≤ C / ((c₁ * c₂) ^ t * ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) :=
            div_le_div_of_nonneg_left hC (by positivity) hpow
        _ ≤ max C 0 / ((c₁ * c₂) ^ t * ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = max C 0 / (c₁ * c₂) ^ t / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t := by
            rw [div_div]
    · rw [(hW (h * k)).1 hbox, norm_zero]
      positivity

theorem zero : LocalGauge (0 : GL (Fin 3) L → ℂ) :=
  ⟨0, 0, 0, fun h => ⟨fun _ => rfl, fun _ => by simp⟩⟩

theorem smul (c : ℂ) (W : GL (Fin 3) L → ℂ) (hW : LocalGauge W) : LocalGauge (c • W) := by
  obtain ⟨B, t, C, hW⟩ := hW
  refine ⟨B, t, ‖c‖ * C, fun h => ⟨fun hnot => ?_, fun hbox => ?_⟩⟩
  · rw [Pi.smul_apply, (hW h).1 hnot, smul_zero]
  · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((hW h).2 hbox) (norm_nonneg _)

theorem bound_mono (W : GL (Fin 3) L → ℂ) {B B' : ℝ} {t t' : ℕ} {C : ℝ} (hBB : B ≤ B') (htt : t ≤ t')
    (hW : ∀ h : GL (Fin 3) L,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (h : GL (Fin 3) L) :
    ‖W h‖ ≤ max C 0 * max 1 (B' ^ 2) ^ (t' - t) /
      ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t' := by
  have x₁ := root₁_pos h
  have x₂ := root₂_pos h
  set x : ℝ := (detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2) with hx
  have xpos : 0 < x := mul_pos x₁ x₂
  by_cases hbox : detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B
  · have hb := (hW h).2 hbox

    have hxB' : x ≤ B' * B' := by
      rw [hx]
      exact mul_le_mul (le_trans hbox.1 hBB) (le_trans hbox.2 hBB) x₂.le (le_trans x₁.le (le_trans hbox.1 hBB))
    have hxB : x ≤ max 1 (B' ^ 2) := le_trans (by rw [sq]; exact hxB') (le_max_right _ _)
    have hsplit : x ^ t' = x ^ t * x ^ (t' - t) := by rw [← pow_add, Nat.add_sub_cancel' htt]
    calc ‖W h‖ ≤ C / x ^ t := hb
      _ ≤ max C 0 / x ^ t := div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max C 0 * x ^ (t' - t) / x ^ t' := by
          rw [hsplit, mul_div_mul_right _ _ (pow_pos xpos _).ne']
      _ ≤ max C 0 * max 1 (B' ^ 2) ^ (t' - t) / x ^ t' := by
          gcongr
  · rw [(hW h).1 hbox, norm_zero]
    positivity

theorem add (W₁ W₂ : GL (Fin 3) L → ℂ) (h₁ : LocalGauge W₁) (h₂ : LocalGauge W₂) : LocalGauge (W₁ + W₂) := by
  obtain ⟨B₁, t₁, C₁, hW₁⟩ := h₁
  obtain ⟨B₂, t₂, C₂, hW₂⟩ := h₂
  set B := max B₁ B₂ with hB
  set t := max t₁ t₂ with ht
  refine ⟨B, t, max C₁ 0 * max 1 (B ^ 2) ^ (t - t₁) + max C₂ 0 * max 1 (B ^ 2) ^ (t - t₂), fun h => ⟨fun hnot => ?_, fun hbox => ?_⟩⟩
  · have n₁ : ¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B₁ ∧ minorSup h / lastRowSup h ^ 2 ≤ B₁) :=
      fun hb => hnot ⟨le_trans hb.1 (le_max_left _ _), le_trans hb.2 (le_max_left _ _)⟩
    have n₂ : ¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B₂ ∧ minorSup h / lastRowSup h ^ 2 ≤ B₂) :=
      fun hb => hnot ⟨le_trans hb.1 (le_max_right _ _), le_trans hb.2 (le_max_right _ _)⟩
    rw [Pi.add_apply, (hW₁ h).1 n₁, (hW₂ h).1 n₂, add_zero]
  · rw [Pi.add_apply, add_div]
    exact le_trans (norm_add_le _ _) (add_le_add
      (bound_mono W₁ (le_max_left _ _) (le_max_left _ _) hW₁ h)
      (bound_mono W₂ (le_max_right _ _) (le_max_right _ _) hW₂ h))

theorem of_mem_gl3CyclicSubspace (W W' : GL (Fin 3) L → ℂ) (hW : LocalGauge W) (hmem : W' ∈ gl3CyclicSubspace W) :
    LocalGauge W' := by
  refine Submodule.span_induction (p := fun (V : GL (Fin 3) L → ℂ) _ => LocalGauge V) ?_ zero (fun x y _ _ hx hy => add x y hx hy)
    (fun c x _ hx => smul c x hx) hmem
  rintro _ ⟨k, rfl⟩
  exact translate W k hW

end Ws23GaugeMem
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Jpss

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

end Ws23Jpss
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Jpss

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

end Ws23Jpss
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Fam5

namespace Ws23J6e

open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.Converse

end Ws23J6e
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

end Ws23Fam5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23Tw

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction"

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem isGL3PsiWhittakerFn_twist (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    {ψv : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψv W) :
    IsGL3PsiWhittakerFn ψv (twist χA v W) := by
  intro x y z g
  simp only [twist]
  rw [map_mul, det_upperUnipotent3, one_mul, hW x y z g]
  ring

theorem norm_localChar_eq_one (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    ‖((NumberField.TateGlobal.localChar χA v u : ℂˣ) : ℂ)‖ = 1 := by
  rw [NumberField.TateGlobal.localChar_apply]
  exact hχA.2.2 _

theorem twist_scalar (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    {W : LocalGL3 v → ℂ} (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hW : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W h)
    (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v) :
    twist χA v W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
      (((ω * NumberField.TateGlobal.localChar χA v ^ 3) t : ℂˣ) : ℂ) * twist χA v W h := by
  simp only [twist]
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hW t h, MonoidHom.mul_apply,
    MonoidHom.pow_apply, map_mul, map_pow]
  push_cast
  ring

theorem twist_gauge (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (p : HeightOneSpectrum (𝓞 ℚ)) {W : LocalGL3 p → ℂ}
    (hW : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → twist χA p W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖twist χA p W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by
  obtain ⟨B, t, C, hB⟩ := hW
  refine ⟨B, t, C, fun h => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · simp only [twist, (hB h).1 hb, mul_zero]
  · simp only [twist, norm_mul, norm_localChar_eq_one χA hχA, one_mul]
    exact (hB h).2 hb

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Tw

theorem isOpen_ker_localChar_det (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v n, NumberField.TateGlobal.localChar χA v u = 1)
    (z : v.adicCompletion ℚ) (hz0 : Valued.v z ≠ 0) (hz : Valued.v z ≤ WithZero.exp (-(n : ℤ))) :
    IsOpen (((NumberField.TateGlobal.localChar χA v).comp
      (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (v.adicCompletion ℚ)ˣ)).ker : Set (LocalGL3 v)) := by
  set H := ((NumberField.TateGlobal.localChar χA v).comp
      (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (v.adicCompletion ℚ)ˣ)).ker
  apply Subgroup.isOpen_of_mem_nhds H (g := 1)
  have hz0' : z ≠ 0 := fun h => hz0 (by rw [h, map_zero])

  have hball : {y : v.adicCompletion ℚ | Valued.v (y - 1) < Valued.v z} ∈ nhds (1 : v.adicCompletion ℚ) := by
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 (Valued.v.restrict z) ((Valuation.ne_zero_iff _).2 hz0'), fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq, Units.val_mk0] at hy
    exact (Valuation.restrict_lt_iff _).1 hy

  have hcont : Continuous fun k : LocalGL3 v => ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) :=
    Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det
  have h1det : ((Matrix.GeneralLinearGroup.det (1 : LocalGL3 v) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [map_one, Units.val_one]
  have hpre := hcont.continuousAt.preimage_mem_nhds (by rw [h1det]; exact hball)
  refine Filter.mem_of_superset hpre ?_
  intro k hk
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hk
  show k ∈ H
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply hn
  rw [LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff]
  have hle1 : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega)
  have h1 : Valued.v ((1 : v.adicCompletion ℚ)) = 1 := Valuation.map_one _
  have hlt : Valued.v (((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) <
      Valued.v ((1 : v.adicCompletion ℚ)) := by
    rw [h1]; exact lt_of_lt_of_le hk (hz.trans hle1)
  refine ⟨?_, Or.inr (hk.le.trans hz)⟩
  have := Valuation.map_add_eq_of_lt_left Valued.v hlt
  rwa [add_sub_cancel, h1] at this

theorem twist_open_stabiliser (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v n, NumberField.TateGlobal.localChar χA v u = 1)
    (z : v.adicCompletion ℚ) (hz0 : Valued.v z ≠ 0) (hz : Valued.v z ≤ WithZero.exp (-(n : ℤ)))
    {W : LocalGL3 v → ℂ}
    (hW : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, twist χA v W (g * k) = twist χA v W g := by
  obtain ⟨Uv, hUo, hUW⟩ := hW
  refine ⟨Uv ⊓ ((NumberField.TateGlobal.localChar χA v).comp
      (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (v.adicCompletion ℚ)ˣ)).ker,
    hUo.inter (isOpen_ker_localChar_det χA v n hn z hz0 hz), fun k hk g => ?_⟩
  obtain ⟨hkU, hkK⟩ := Subgroup.mem_inf.1 hk
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hkK
  simp only [twist]
  rw [map_mul, map_mul, hkK, mul_one, hUW k hkU g]

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

namespace Ws23Tw

end Ws23Tw
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.LanglandsTunnell.CubicInduction MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace GamGlue

theorem differentiable_const_cpow_comp {q : ℂ} (hq : q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun s => q ^ (f s) := by
  have : (fun s => q ^ (f s)) = fun s => Complex.exp (Complex.log q * f s) := by
    funext s; rw [Complex.cpow_def_of_ne_zero hq]
  rw [this]
  exact Complex.differentiable_exp.comp ((differentiable_const _).mul hf)

theorem differentiable_eval_comp (P : Polynomial ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun s => P.eval (f s) :=
  (Polynomial.differentiable P).comp hf

theorem entire_ext (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → f s = g s) : ∀ s, f s = g s := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz₀ : ((σ + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ < s.re} := by
    show σ < ((σ + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]; linarith
  have hev : f =ᶠ[nhds ((σ + 1 : ℝ) : ℂ)] g :=
    Filter.eventually_of_mem (hopen.mem_nhds hz₀) fun s hs => h s hs
  have := hfa.eqOn_of_preconnected_of_eventuallyEq hga isPreconnected_univ (Set.mem_univ _) hev
  exact fun s => this (Set.mem_univ s)

end GamGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi.Ws23Fam5"

open MeasureTheory LanglandsTunnell.TateLocal in
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

    (hw₂blaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂b (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂b g)
    (hw₂bK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Φ.level, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂b (g * k) = w₂b g)

    (dMp : ℕ)
    (hπ₀levMp : ∃ W' ∈ gl3CyclicSubspace (mP ⟨p, hp⟩), W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)),
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j) ≤ WithZero.exp (-(dMp : ℤ))) →
        ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)),
          ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)
    (hkCMp : 6 * (bQ (p : HeightOneSpectrum (𝓞 ℚ)) + 3 * dMp + 3) + 7 ≤ kχ (p : HeightOneSpectrum (𝓞 ℚ)))

    (lamMp : ℂ)
    (hlamMIdp :
    ∀ b : ℕ,
            (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA (p : HeightOneSpectrum (𝓞 ℚ)) = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)),
              letI := LanglandsTunnell.TateLocal.localBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))
                  (mP ⟨p, hp⟩) η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (mP ⟨p, hp⟩) η s g *
                    Q₂.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))) (dualWhittakerFn3 (mP ⟨p, hp⟩)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))
                    (mP ⟨p, hp⟩) η (1 - s) g * Q₂.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lamMp *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))

    (hβMp : ∀ b : ℕ, ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ b ∣ Φ.level ∧ ¬ (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b + 1) ∣ Φ.level) →
      ∀ (ϖp : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ)
        (hπp : algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp ≠ 0),
        Valued.v (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) = WithZero.exp (-1 : ℤ) →
      ∀ (g₃ : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) (k₀ : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (η : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) η c → c ≤ b →
      letI := LanglandsTunnell.TateLocal.localBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      letI := localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      haveI := borelSpace_localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      ∀ (μ₂ : Measure (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ | Valued.v (u : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
                  (mP ⟨p, hp⟩) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))) = 0 ∧
          (∫ u in {u : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ | Valued.v (u : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => (mP ⟨p, hp⟩) (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))) = 0)

    (hΨA :
      letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
      ∀ (μNA : Measure RSCarrier.realUnipotent) [μNA.IsHaarMeasure],
        ∃ (hA : GL (Fin 2) ℝ) (hA3 : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : ℝ),
          DifferentiableOn ℂ
              (fun s : ℂ => RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
                (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA)))
                (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)))
              {s : ℂ | σ < s.re} ∧
          ∃ s : ℂ, σ < s.re ∧
            RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
                (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA)))
                (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)) ≠ 0) :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) (g * h)),
        ∀ W₃ ∈ gl3CyclicSubspace (mP ⟨p, hp⟩),
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ ((localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)) * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ ((localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)) * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              R₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                (R₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((r : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  classical
  by_cases hw₂b0 : w₂b = 0
  ·
    have hq0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)
    refine ⟨0, 1, 0, one_ne_zero, ?_⟩
    intro μ₂ _ μN₂ _ w₂ hw₂ W₃ hW₃ P Pd Q Qd m md σ₂ σ₃ hQ hQd hI hId hprim hdual s
    have hbot : Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) (g * h)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨h, rfl⟩
      funext g
      simp only [hw₂b0, Pi.zero_apply, mul_zero]
    have hw₂0 : w₂ = 0 := by
      rw [hbot] at hw₂
      exact (Submodule.mem_bot ℂ).1 hw₂
    have hzero : ∀ s : ℂ, σ₃ < s.re →
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) = 0 := by
      intro s hs
      have h := hdual s hs
      simp only [hw₂0, Pi.zero_apply, mul_zero, RSCarrier.rsLocalIntegral, zero_mul, integral_zero] at h
      exact h.symm
    have dlin : Differentiable ℂ fun s : ℂ => (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) :=
      GamGlue.differentiable_const_cpow_comp hq0 ((differentiable_const _).mul differentiable_id)
    have devn : Differentiable ℂ fun s : ℂ => Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) :=
      GamGlue.differentiable_eval_comp Pd (GamGlue.differentiable_const_cpow_comp hq0 differentiable_neg)
    have hdg : Differentiable ℂ fun s : ℂ =>
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := dlin.mul devn
    have hall := GamGlue.entire_ext
      (fun s : ℂ => (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))
      (fun _ : ℂ => (0 : ℂ)) hdg (differentiable_const _) σ₃ hzero
    have hs0 : (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) = 0 := hall s
    rw [hs0, Polynomial.eval_zero]
    ring
  ·
    have hN1 := LanglandsTunnell.RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep
      K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2
      hφW hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ
      hkfloor ν hνadm hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ
      hϖ mP hmPmem hmP1 hW₃admM hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par p hp w₂b hw₂b hw₂b0 hw₂blaw hw₂bK dMp hπ₀levMp hkCMp lamMp hlamMIdp hβMp
    have hN2 := LanglandsTunnell.RankinSelberg.exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing
      K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2
      hφW hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ
      hkfloor ν hνadm hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ
      hϖ mP hmPmem hmP1 hW₃admM hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par p hp w₂b hw₂b hΨA
    subst hμν
    have hbadν : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v → v ∈ S' := by
      intro v hv
      by_contra hvS
      have hvQ : v ∉ SQ := fun hq => hvS (hSS' hq)
      exact hgood v hvS ((LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt K _hdeg ν χA hχA v (hχoff v hvQ)).1.2 hv)
    have hfinν : {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K ν v}.Finite :=
      (Finset.finite_toSet S').subset fun v hv => hbadν v hv
    have LW3LAW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (Ws23Tw.twist χA p (F.whittakerLoc p)) := by
      have h := Ws23Tw.isGL3PsiWhittakerFn_twist χA p (F.whittakerLoc_law p)
      rwa [Ws23Fam5.psiLoc_eq_psiLocal_inv_of_inv_eq_psiQ ψ hψQ p] at h
    have hTsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 p, Ws23Tw.twist χA p (F.whittakerLoc p) (g * k) = Ws23Tw.twist χA p (F.whittakerLoc p) g := by
      obtain ⟨ϖ₀, hπ₀, hϖ₀⟩ := Ws23SwapStep.exists_local_uniformizer p
      have hvz : Valued.v ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ₀) ^ kχ p) =
          WithZero.exp (-(kχ p : ℤ)) := by
        rw [map_pow, hϖ₀, ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul, mul_one]
      refine Ws23Tw.twist_open_stabiliser χA p (kχ p) (hkχ p hp).1 _ (by rw [hvz]; exact WithZero.exp_ne_zero) hvz.le ?_
      by_cases hb : IsBadPlace K ν p
      · exact (hBad {p}).1 p (Finset.mem_singleton_self _) hb
      · exact ⟨localMaximalCompact3 (𝓞 ℚ) ℚ p, LanglandsTunnell.CubicInduction.isOpen_localMaximalCompact3 (𝓞 ℚ) ℚ p,
          fun k hk g => (F.spherical p hb).1 g k hk⟩
    have hTscal : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
        Ws23Tw.twist χA p (F.whittakerLoc p) (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          (((NumberField.TateGlobal.localChar F.centralChar p * NumberField.TateGlobal.localChar χA p ^ 3) t : ℂˣ) : ℂ) *
            Ws23Tw.twist χA p (F.whittakerLoc p) h :=
      fun t h => Ws23Tw.twist_scalar χA p _
        (LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
          K _ ψ ν hfinν F hF0.1 p) t h
    have hTgau := Ws23Tw.twist_gauge χA hχA p
      (LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_gauge K _ ψ ν hfinν F hF0.1 hFg p)
    have hmPmemT : mP ⟨p, hp⟩ ∈ gl3CyclicSubspace (Ws23Tw.twist χA p (F.whittakerLoc p)) := hmPmem ⟨p, hp⟩
    have LW3LAWm : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (mP ⟨p, hp⟩) :=
      Ws23Fam5Holes.isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace _ LW3LAW hmPmemT
    have hmPsm := Ws23Cubic.smooth_of_mem hTsm hmPmemT
    have hω₃m := Ws23Cubic.scalar_law_of_mem
      (fun t => (((NumberField.TateGlobal.localChar F.centralChar p * NumberField.TateGlobal.localChar χA p ^ 3) t : ℂˣ) : ℂ))
      hTscal hmPmemT
    have hm0 : mP ⟨p, hp⟩ ≠ 0 := fun h => by
      have h1 := congrFun h 1
      rw [hmP1] at h1
      exact one_ne_zero h1
    have LGAUGEM := Ws23GaugeMem.of_mem_gl3CyclicSubspace _ _ hTgau hmPmemT
    have LVSTAB := Ws23SwapStep.localSpaceAt_translate_mem (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par)
    obtain ⟨hVirr, hVadm, hVsm⟩ := hV par p hp
    let ξ0 : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom
    have LPHICEN : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
        φv par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * x) = ((ξ0 z : ℂˣ) : ℂ) * φv par x :=
      Ws23W2.phicen Φ S R (φv par) (hiso par)
    have LVCEN := AutomorphicForm.WhittakerModel.forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
        (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) ξ0 LPHICEN p
    have hwScen := LVCEN w₂b hw₂b
    obtain ⟨η₀, hCADM1, hCADM2, hη₀Z⟩ :=
      AutomorphicForm.SmoothCuspRealizationAt.exists_isAdmissibleTwist_eq_centralChar_mul_ideleNorm_inv K Φ R hRc SQ hb
    have hη₀ : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        ((η₀ z : ℂˣ) : ℂ) = ((ξ0 z : ℂˣ) : ℂ) * (((ideleNorm ℚ z : ℝ) : ℂ))⁻¹ :=
      fun z => hη₀Z (Subgroup.topEquiv.symm z)
    have LU1DET : ∀ u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Φ.level,
        LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 :=
      fun u hu => Ws23PencSwap.modulus_det_eq_one_of_mem_localLevelOne p hu
    obtain ⟨ϖp, hπp, hϖp⟩ := Ws23SwapStep.exists_local_uniformizer p
    have hdetn : ∀ x : p.adicCompletion ℚ, Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
      intro x
      rw [show (UnramifiedWhittaker.unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) = unipotentGL2 x from Units.ext rfl]
      exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, Ws23Fam5Holes.det_unipotentGL2_val, Units.val_one])
    have hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g)
          (UnramifiedWhittaker.unipotent x * g) =
        NumberField.StandardAddChar.psiLocal ℚ p x *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) g := by
      intro x g
      beta_reduce
      rw [map_mul Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.unipotent x) g, hdetn, one_mul, hw₂blaw x g]
      ring
    have hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Φ.level, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) (g * k) =
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) g := by
      intro k hk g
      beta_reduce
      rw [map_mul Matrix.GeneralLinearGroup.det g k, Units.val_mul, LanglandsTunnell.TateLocal.modulus_mul, LU1DET k hk, mul_one,
        hw₂bK k hk g]
    have hw₂ne : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) ≠ 0 := by
      obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hw₂b0
      refine Function.ne_iff.2 ⟨g₀, ?_⟩
      show _ * w₂b g₀ ≠ 0
      refine mul_ne_zero ?_ hg₀
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2
        (LanglandsTunnell.TateLocal.modulus_ne_zero (Units.ne_zero _))))
    have hw₂irr := Ws23W2.twist_irreducible p _ LVSTAB hVirr w₂b hw₂b hw₂b0
    have hw₂adm := Ws23Tw.twist_admissible_gl2 p _ LVSTAB hVadm w₂b hw₂b
    have hw₂cen := Ws23W2.twist_central p w₂b ξ0 η₀ hη₀ hwScen
    have hw₂gr := Ws23SwapStep.twisted_shell_growth_of_mem p _ LVSTAB hVirr hVadm hVsm
        (NumberField.TateGlobal.localChar ξ0 p) LVCEN w₂b hw₂b hw₂blaw hπp hϖp
        (fun k hk => Ws23PencSwap.modulus_det_eq_one_of_mem_localLevelOne _ hk)
    have LW0P := Ws23Fam5Holes.localAt_globalPoints_antidiag w₀ hw₀ p

    exact LanglandsTunnell.RankinSelberg.exists_forall_mem_span_rsLocalIntegral_dual_mul_eq_mul_of_rsGlobalIntegral_realisation
      p (mP ⟨p, hp⟩) LW3LAWm hmPsm hm0 _ hω₃m (hW₃irrM ⟨p, hp⟩) (hW₃admM ⟨p, hp⟩) LGAUGEM
      Φ.level Φ.level_ne_bot _ hw₂law hw₂K hw₂ne hw₂irr hw₂adm _ hw₂cen hπp hϖp hw₂gr
      (localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)) LW0P
      (fun μ₂ _ μN₂ _ => by
        obtain ⟨M, Md, D, hFD, hM, hreal⟩ := hN2 μ₂ μN₂
        obtain ⟨w₂, hw₂, W₃, hW₃, ⟨σ, hΨ⟩, P₀, Pd₀, Q₀, Qd₀, m₀, md₀, σ₂, σ₃, hP₀, hQd₀, hprim', hdual'⟩ := hN1 μ₂ μN₂
        obtain ⟨φ, Θ, hdiff, hFE, ⟨σ₁, hunf⟩, hdunf⟩ := hreal w₂ hw₂ W₃ hW₃
        refine ⟨M, Md, D, hFD, ⟨w₂, hw₂, W₃, hW₃, φ, Θ, max σ₁ σ, ?_, ?_, P₀, Pd₀, Q₀, Qd₀, m₀, md₀, σ₂, σ₃, hP₀, hQd₀, hprim', hdual'⟩, hreal⟩
        · intro s hs
          exact hunf s (lt_of_le_of_lt (le_max_left _ _) hs)
        · intro σ'
          obtain ⟨s, hs, hMs⟩ := hM (max σ' (max σ₁ σ))
          have h1 : σ₁ < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
          have h2 : σ < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
          refine ⟨s, lt_of_le_of_lt (le_max_left _ _) hs, ?_⟩
          rw [hunf _ h1]
          exact mul_ne_zero hMs (hΨ _ h2))

end S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi (solution)
