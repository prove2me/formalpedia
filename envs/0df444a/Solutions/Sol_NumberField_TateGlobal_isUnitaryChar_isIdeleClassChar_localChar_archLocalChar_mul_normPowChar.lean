-- Prove2me | solution 1 for NumberField.TateGlobal.isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/23a86cd0-173f-5818-88b4-0fd8a7989cb1

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

namespace L1Aux

open Complex NumberField.AdelicLevel NumberField.AdeleRing

variable (K : Type) [Field K] [NumberField K]

theorem ideleNorm_principal (u : Kˣ) :
    ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 1 := by
  have h := @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _
    (NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) u
  unfold ideleNorm
  rw [NNReal.coe_eq_one]
  exact h

theorem ideleNorm_localUnit (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (h1 : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (h2 : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ideleNorm K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u)) = 1 := by
  classical
  refine NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K _ rfl ?_
  rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
  have hval : ∀ w : HeightOneSpectrum (𝓞 K),
      ((finitePartUnits (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u)) :
        (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
        Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) v (u : v.adicCompletion K) w := by
    intro w; rfl
  have hinv : ∀ w : HeightOneSpectrum (𝓞 K),
      (((finitePartUnits (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v u)))⁻¹ :
        (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
        Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) v
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) w := by
    intro w; rw [← map_inv, ← map_inv, ← map_inv]; rfl
  refine ⟨fun w => ?_, fun w => ?_⟩
  · rw [hval]
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact h1
    · rw [Function.update_of_ne hw]; exact one_mem _
  · rw [hinv]
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact h2
    · rw [Function.update_of_ne hw]; exact one_mem _

theorem localChar_mul (χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    localChar (χ * ψ) v t = localChar χ v t * localChar ψ v t := rfl

theorem archLocalChar_mul (χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    archLocalChar (χ * ψ) w x = archLocalChar χ w x * archLocalChar ψ w x := rfl

theorem localChar_normPowChar_of_unit (t₀ : ℝ) (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (h1 : (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (h2 : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    localChar (normPowChar K t₀) v u = 1 := by
  rw [localChar_apply]
  exact normPowChar_eq_one_of_ideleNorm_eq_one t₀ (ideleNorm_localUnit K v u h1 h2)

end L1Aux

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ)
    (t₀ : ℝ) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (χ * normPowChar K t₀) ∧
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K (χ * normPowChar K t₀) ∧
    (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ * normPowChar K t₀) z : ℂˣ) : ℂ)) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ),
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      localChar (χ * normPowChar K t₀) v u = localChar χ v u) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt (χ * normPowChar K t₀) v ↔ IsUnramifiedCharAt χ v) ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      (if IsUnramifiedCharAt (χ * normPowChar K t₀) v
        then (((χ * normPowChar K t₀) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) =
      (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t₀))) ∧
    (∀ τ : InfinitePlace K → ℝ,
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I)) →
      ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (χ * normPowChar K t₀) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v + t₀ : ℝ) : ℂ) * Complex.I)) ∧
    (∀ m : InfinitePlace K → ℤ,
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) →
      ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (χ * normPowChar K t₀) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) := by
  have hprod : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      (((χ * normPowChar K t₀) z : ℂˣ) : ℂ) = ((χ z : ℂˣ) : ℂ) * ((normPowChar K t₀ z : ℂˣ) : ℂ) := by
    intro z; rw [MonoidHom.mul_apply, Units.val_mul]

  have h4 : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ),
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      localChar (χ * normPowChar K t₀) v u = localChar χ v u := by
    intro v u h1 h2
    rw [L1Aux.localChar_mul, L1Aux.localChar_normPowChar_of_unit K t₀ v u h1 h2, mul_one]
  have h5 : ∀ v : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt (χ * normPowChar K t₀) v ↔ IsUnramifiedCharAt χ v := by
    intro v
    unfold IsUnramifiedCharAt
    exact forall_congr' fun t => forall_congr' fun h1 => forall_congr' fun h2 => by rw [h4 v t h1 h2]
  refine ⟨?_, ?_, ?_, h4, h5, ?_, ?_, ?_⟩
  ·
    intro z
    rw [hprod, norm_mul, hχu z, norm_coe_normPowChar_apply, mul_one]
  ·
    intro u
    rw [MonoidHom.mul_apply, hχF u, one_mul]
    exact normPowChar_eq_one_of_ideleNorm_eq_one t₀ (L1Aux.ideleNorm_principal K u)
  ·
    have hc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((normPowChar K t₀ z : ℂˣ) : ℂ) := by
      have h1 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ideleNorm K z : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm K)
      have h2 : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ideleNorm K z : ℝ) : ℂ) ^ (Complex.I * t₀) :=
        h1.cpow continuous_const fun z => Or.inl (by
          rw [Complex.ofReal_re]; exact ideleNorm_pos z)
      exact h2
    have h__af := hχc.mul hc
    simp only [hprod] at h__af ⊢
    exact h__af
  ·
    intro v
    have hnp := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t₀ v
    have hN0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t₀)) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      left
      have : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
      exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
    have hunr : IsUnramifiedCharAt (normPowChar K t₀) v := by
      by_contra h; rw [if_neg h] at hnp; exact hN0 hnp.symm
    rw [if_pos hunr] at hnp
    by_cases h : IsUnramifiedCharAt χ v
    · rw [if_pos ((h5 v).mpr h), if_pos h, hprod, hnp]
    · rw [if_neg (fun h' => h ((h5 v).mp h')), if_neg h, zero_mul]
  ·
    intro τ hτ v x hre him
    rw [L1Aux.archLocalChar_mul, Units.val_mul, hτ v x hre him, archLocalChar_apply, ← archUnitHom_apply,
      coe_normPowChar_apply]
    have hr : ((ideleNorm K (archUnitHom v x) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ideleNorm_pos _).ne'
    rw [← Complex.cpow_add _ _ hr]
    congr 1
    push_cast
    ring
  ·
    intro m hm v x hx
    rw [L1Aux.archLocalChar_mul, Units.val_mul, hm v x hx, archLocalChar_apply, ← archUnitHom_apply,
      normPowChar_eq_one_of_ideleNorm_eq_one t₀
        (NumberField.TateGlobal.ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one K v x hx),
      Units.val_one, mul_one]

end S_NumberField_TateGlobal_isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar
end P2MW
export P2MW.S_NumberField_TateGlobal_isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar (solution)
