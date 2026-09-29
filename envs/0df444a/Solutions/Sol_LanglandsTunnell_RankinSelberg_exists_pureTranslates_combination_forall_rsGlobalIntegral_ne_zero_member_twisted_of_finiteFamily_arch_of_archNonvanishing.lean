-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5a8be7f1-32de-5d21-9553-f5d52a97ac2d

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
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
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Definitions.Def_AutomorphicForm_ArchType
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_frozen_forall_sum_translate_whittaker_iota_eq_mul_pSlot_of_finiteFamily_arch_explicit
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_reference_eq_mul_rsArchIntegral_mul_rsFinIntegral_indicator_mul_of_finiteFamily_arch
import Theorems.Thm_Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero
import Theorems.Thm_Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero
import Theorems.Thm_LanglandsTunnell_RankinSelberg_differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments
import Theorems.Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
import Theorems.Thm_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.CubicInduction.fnTwist3_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_sigmaCentralizer_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply"
set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section Ws23AwPlace

open IsDedekindDomain NumberField Matrix AutomorphicForm
open LanglandsTunnell LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel

noncomputable section

namespace Ws23Iso

theorem localAt_eq (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    localAt ℚ p g = finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) := rfl

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem localAt_archRealGLAt (p : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) ℝ) :
    localAt ℚ p (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 := by
  rw [localAt_eq, glFin_archRealGLAt, map_one]

end Ws23Iso

end

end Ws23AwPlace

section Ws23AwKit

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell LanglandsTunnell.CubicInduction

noncomputable section

namespace Ws23Iso

theorem matrix3_eq_of_mapMatrix_arch_fin_eq {M N : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix M = (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix M = (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix N) :
    M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

def archMat3 (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j => ((a i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

theorem mapMatrix_arch_archMat3 (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 a) = a := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat3 (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 a) = 1 := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem archMat3_one : archMat3 1 = 1 :=
  matrix3_eq_of_mapMatrix_arch_fin_eq (by rw [mapMatrix_arch_archMat3, map_one]) (by rw [mapMatrix_fin_archMat3, map_one])

theorem archMat3_mul (a b : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : archMat3 (a * b) = archMat3 a * archMat3 b :=
  matrix3_eq_of_mapMatrix_arch_fin_eq
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

def archEmbed3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun a :=
    { val := archMat3 a
      inv := archMat3 ((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix _ _ _)
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' a b := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

theorem archComponent3_archEmbed3 (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (archEmbed3 a) = a := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (archMat3 a i j) = _
  rw [AdelicLevel.adeleArch_apply]
  simp only [archMat3, Matrix.of_apply]

theorem componentAt3_archEmbed3 (v : HeightOneSpectrum (𝓞 ℚ)) (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (archEmbed3 a) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v) ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (archMat3 a i j)) = _
  rw [AdelicLevel.adeleFin_apply, Units.val_one]
  simp only [archMat3, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem rsLocalIntegral_const_mul_right (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ) (s : ℂ)
    (c : ℂ) (W F : G → ℂ) :
    RSCarrier.rsLocalIntegral μ H μH δ s W (fun g => c * F g) = c * RSCarrier.rsLocalIntegral μ H μH δ s W F := by
  unfold RSCarrier.rsLocalIntegral
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

theorem rsLocalIntegral_const_mul_left (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ) (s : ℂ)
    (c : ℂ) (W F : G → ℂ) :
    RSCarrier.rsLocalIntegral μ H μH δ s (fun g => c * W g) F = c * RSCarrier.rsLocalIntegral μ H μH δ s W F := by
  unfold RSCarrier.rsLocalIntegral
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

theorem away_assembly (Z ΨA ΨF : ℂ → ℂ) (c : ℂ) (hc : c ≠ 0) (σZ σA : ℝ)
    (hZfac : ∀ s : ℂ, σZ < s.re → Z s = c * ΨA s * ΨF s)
    (hent : Differentiable ℂ Z)
    (hAholo : DifferentiableOn ℂ ΨA {s : ℂ | σA < s.re}) (hAne : ∃ s : ℂ, σA < s.re ∧ ΨA s ≠ 0)
    (hFIN : ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ ΨF s ≠ 0}) (σ' : ℝ) :
    ∃ s : ℂ, σ' < s.re ∧ Z s ≠ 0 := by
  have hcnt := Complex.countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero ΨA σA hAholo hAne
  have hns : ¬ ({s : ℂ | max σZ σA < s.re ∧ ΨF s ≠ 0} ⊆ {s : ℂ | σA < s.re ∧ ΨA s = 0}) :=
    fun hsub => hFIN (max σZ σA) (hcnt.mono hsub)
  obtain ⟨s₀, hs₀, hs₀'⟩ := Set.not_subset.1 hns
  have hA0 : ΨA s₀ ≠ 0 := fun h0 => hs₀' ⟨lt_of_le_of_lt (le_max_right _ _) hs₀.1, h0⟩
  have hσ0 : σZ < s₀.re := lt_of_le_of_lt (le_max_left _ _) hs₀.1
  have hZ0 : Z s₀ ≠ 0 := by
    rw [hZfac s₀ hσ0]
    exact mul_ne_zero (mul_ne_zero hc hA0) hs₀.2
  obtain ⟨s, hs, -, hsne⟩ :=
    Complex.exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero (Finset.univ : Finset Unit)
      (fun _ => Z) σZ (fun _ _ => hent.differentiableOn) (fun _ _ => ⟨s₀, hσ0, hZ0⟩) σ'
  exact ⟨s, hs, hsne () (Finset.mem_univ _)⟩

end Ws23Iso

end

end Ws23AwKit

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
    ∃ (h₂ : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p h₂ = 1 ∧
    ∃ (h₃ : AdelicGL 3 (𝓞 ℚ) ℚ), componentAt3 (𝓞 ℚ) ℚ p h₃ = 1 ∧
    ∃ (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
      (wA : GL (Fin 2) ℝ → ℂ) (wf : finiteAdelicGL2Subgroup ℚ → ℂ) (wp : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        wf (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = wf (RSCarrier.finFactor g)) ∧
      Measurable wf ∧
      (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, wf (RSCarrier.finFactor (unipotentGL2 t * g)) =
          (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * wf (RSCarrier.finFactor g)) ∧
      (∀ (t : (p.adicCompletion ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ)),
        wp (UnramifiedWhittaker.unipotent t * y) = NumberField.StandardAddChar.psiLocal ℚ p t * wp y) ∧
      wp ≠ 0 ∧
      (∃ w₁ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
        ∀ y : GL (Fin 2) (p.adicCompletion ℚ), wp y = ((modulus ((Matrix.GeneralLinearGroup.det y : ((p.adicCompletion ℚ))ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₁ y) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
            (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * UnramifiedWhittaker.placeEmbed ℚ p (xP j) * h₂))) 1 g =
          wp (localAt ℚ p g) * (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g))) ∧
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → GL (Fin 2) (p.adicCompletion ℚ))
      (m : ℕ) (d : Fin m → ℂ) (k : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) ∧
      ∀ D : Set (AdelicGL2 (𝓞 ℚ) ℚ),
        IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
            (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
        ∀ σ' : ℝ, ∃ s : ℂ, σ' < s.re ∧
          rsGlobalIntegral D s
              (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j *
                (((detNorm (g * UnramifiedWhittaker.placeEmbed ℚ p (x i) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
                  φv par (g * UnramifiedWhittaker.placeEmbed ℚ p (x i) * UnramifiedWhittaker.placeEmbed ℚ p (xP j) * h₂)))
              (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ j, d j *
                (((χA (Matrix.GeneralLinearGroup.det (x * k j)) : ℂˣ) : ℂ) * F.form (x * k j * h₃))) ≠ 0  := by
  classical
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _

  obtain ⟨μfH, hμfH, hμfR, hsplit⟩ := LanglandsTunnell.Converse.exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
  obtain ⟨μNA, μNF, hμNA, hμNF, hNsplit⟩ := LanglandsTunnell.Converse.exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
  haveI := hμfH
  haveI := hμNF
  haveI := hμNA
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo ℚ

  obtain ⟨hA, hA3, σA, hAholo, sA, hsA, hAne⟩ := hΨA μNA

  obtain ⟨h₂, hh₂def⟩ : ∃ h₂ : AdelicGL2 (𝓞 ℚ) ℚ, h₂ = archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) hA := ⟨_, rfl⟩
  have hh₂ : localAt ℚ p h₂ = 1 := by rw [hh₂def]; exact Ws23Iso.localAt_archRealGLAt p hA

  obtain ⟨nP, cP, xP, wA, wf, wp, hwfp, hwfm, hwfn, hwpn, hwp0, hwpV, hpure, hnondeg⟩ :=
    LanglandsTunnell.RankinSelberg.exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
      K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2 hφW
      hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ hkfloor ν hνadm
      hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ hϖ mP hmPmem hmP1 hW₃admM
      hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par p hp w₂b hw₂b h₂ hh₂

  obtain ⟨hT2, hREF⟩ :=
    LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_reference_eq_mul_rsArchIntegral_mul_rsFinIntegral_indicator_mul_of_finiteFamily_arch
      K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2 hφW
      hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ hkfloor ν hνadm
      hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ hϖ mP hmPmem hmP1 hW₃admM
      hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par p hp w₂b hw₂b hA hA3 h₂ hh₂def nP cP xP wA wf wp ⟨hwfp, hwfm, hwfn, hwpn, hwp0, hwpV, hpure⟩ μfH μNA μNF hsplit hNsplit

  have hnd : ∃ gf : finiteAdelicGL2Subgroup ℚ, (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) gf ≠ 0 := by
    obtain ⟨g, hg⟩ := hnondeg
    rw [hT2 g] at hg
    exact ⟨RSCarrier.finFactor g, right_ne_zero_of_mul hg⟩

  obtain ⟨h₃f, hh₃fA, hh₃fp, hh₃fS, m, d, k, hk, hFIN⟩ :=
    LanglandsTunnell.RankinSelberg.exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
      K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2 hφW
      hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ hkfloor ν hνadm
      hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ hϖ mP hmPmem hmP1 hW₃admM
      hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par p hp w₂b hw₂b nP cP xP hnd μfH μNF

  obtain ⟨h₃, hh₃def⟩ : ∃ h₃ : AdelicGL 3 (𝓞 ℚ) ℚ, h₃ = Ws23Iso.archEmbed3 hA3 * h₃f := ⟨_, rfl⟩
  have hh₃A : archComponent3 (𝓞 ℚ) ℚ h₃ = hA3 := by
    rw [hh₃def, map_mul, Ws23Iso.archComponent3_archEmbed3, hh₃fA, mul_one]
  have hh₃fin : ∀ v : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ v h₃ = componentAt3 (𝓞 ℚ) ℚ v h₃f := fun v => by
    rw [hh₃def, map_mul, Ws23Iso.componentAt3_archEmbed3, one_mul]
  have hh₃ : componentAt3 (𝓞 ℚ) ℚ p h₃ = 1 := by rw [hh₃fin, hh₃fp]
  obtain ⟨c, E, σE, hc0, hEne, hZD⟩ := hREF h₃f ⟨hh₃fA, hh₃fp, hh₃fS⟩ h₃ ⟨hh₃A, hh₃fin⟩ m d k hk

  obtain ⟨WA', WdA', Wf', Wdf', -, -, -, -, -, -, PT2⟩ :=
    LanglandsTunnell.RankinSelberg.exists_frozen_forall_sum_translate_purified_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
      K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2 hφW
      hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ hkfloor ν hνadm
      hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ hϖ mP hmPmem hmP1 hW₃admM
      hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par p hp w₂b hw₂b h₂ hh₂ nP cP xP wA wf wp hwfp hwfm hwfn hwpn hwp0 hwpV hpure
  obtain ⟨FA', FdA', Ff', Fdf', -, -, -, -, -, -, -, -, -, -, PT3⟩ :=
    LanglandsTunnell.RankinSelberg.exists_frozen_forall_sum_translate_whittaker_iota_eq_mul_pSlot_of_finiteFamily_arch_explicit
      K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2 hφW
      hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ hkfloor ν hνadm
      hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ hϖ mP hmPmem hmP1 hW₃admM
      hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par p hp w₂b hw₂b h₃ hh₃
  obtain ⟨hφc, -, ⟨Cφ, rφ, hφb⟩, -, -⟩ := PT2 1 (fun _ => 1) (fun _ => 1)
  obtain ⟨W, Wd, hΘc, hΘmom, -⟩ := PT3 m d k hk

  refine ⟨h₂, hh₂, h₃, hh₃, nP, cP, xP, wA, wf, wp, hwfp, hwfm, hwfn, hwpn, hwp0, hwpV, hpure,
    1, fun _ => 1, fun _ => 1, m, d, k, hk, ?_⟩
  intro D hD σ'
  obtain ⟨σZ, hZfac⟩ := hZD D hD

  have hFIN' : ∀ σ'' : ℝ, ¬ Set.Countable {s : ℂ | σ'' < s.re ∧ (fun s : ℂ => RSCarrier.rsFinIntegral μfH μNF s
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))) s * E s ≠ 0} := by
    intro σ'' hcnt
    refine hFIN (max σ'' σE) (hcnt.mono ?_)
    rintro s ⟨hs, hne⟩
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hs, mul_ne_zero hne (hEne s (lt_of_le_of_lt (le_max_right _ _) hs))⟩
  exact Ws23Iso.away_assembly (fun s => rsGlobalIntegral D s _ _)
    (fun s : ℂ => RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA))) (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)))
    (fun s : ℂ => (fun s : ℂ => RSCarrier.rsFinIntegral μfH μNF s
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))) s * E s)
    c hc0 σZ σA (fun s hs => by beta_reduce; rw [hZfac s hs]; ring)
    (LanglandsTunnell.RankinSelberg.differentiable_and_boundedOnStrips_rsGlobalIntegral_of_hasIotaMoments
        _ hΘc hΘmom D hD _ hφc Cφ rφ hφb).1
    hAholo ⟨sA, hsA, hAne⟩ hFIN' σ'

end S_LanglandsTunnell_RankinSelberg_exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing (solution)
