-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0ce3542a-6cd6-56e6-83f5-6cf3bb81993d

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

open scoped NumberField.PlaceTransport

namespace PBCut

variable (q : ℕ) [Fact q.Prime] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
  (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
  (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
  (hcont : Continuous Φ)

theorem norm_le_one (x : 𝓞 ↥F) : ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ ≤ 1 := by
  have hint : IsIntegral ℤ (σ ((x : ↥F) : AlgebraicClosure ℚ)) :=
    map_isIntegral_int σ (map_isIntegral_int (algebraMap ↥F (AlgebraicClosure ℚ)) x.isIntegral_coe)
  let A : ValuationSubring (AlgebraicClosure ℚ) := padicPlace q
  have hO : IsIntegral ↥(A.valuation.integer) (σ ((x : ↥F) : AlgebraicClosure ℚ)) := by
    obtain ⟨p, hp, hpx⟩ := hint
    refine ⟨p.map (algebraMap ℤ ↥(A.valuation.integer)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim ((algebraMap ↥(A.valuation.integer) (AlgebraicClosure ℚ)).comp (algebraMap ℤ ↥(A.valuation.integer))) (algebraMap ℤ (AlgebraicClosure ℚ))]
    exact hpx
  have hmemI : σ ((x : ↥F) : AlgebraicClosure ℚ) ∈ A.valuation.integer :=
    Valuation.Integers.mem_of_integral (Valuation.integer.integers A.valuation) hO
  have hmem : σ ((x : ↥F) : AlgebraicClosure ℚ) ∈ A := (A.valuation_le_one_iff _).1 ((Valuation.mem_integer_iff _ _).1 hmemI)
  have h := (mem_padicPlace_iff q).1 hmem
  exact_mod_cast h

include hΦF hcont

theorem norm_lt_one_of_mem (x : 𝓞 ↥F) (hx : x ∈ w.asIdeal) :
    ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 := by
  have hv : Valued.v ((((WithVal.equiv (w.valuation ↥F)).symm (x : ↥F)) : w.adicCompletion ↥F)) < 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem w x).2 hx
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
  have ht' : Filter.Tendsto (fun n : ℕ => (padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))) ^ n) Filter.atTop (nhds 0) := by
    have h2 := (hcont.tendsto 0).comp ht
    rw [map_zero] at h2
    refine h2.congr (fun n => ?_)
    change Φ ((algebraMap ↥F (w.adicCompletion ↥F) (x : ↥F)) ^ n) = _
    rw [map_pow, hΦF]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht'

theorem mem_asIdeal_iff (x : 𝓞 ↥F) : x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 := by
  refine ⟨norm_lt_one_of_mem q F w σ Φ hΦF hcont x, fun h => ?_⟩
  by_contra hx
  obtain ⟨y, i, hi, hyxi⟩ := w.isMaximal.exists_inv hx
  let f : 𝓞 ↥F → PadicAlgCl q := fun z => padicEmbedding q (σ ((z : ↥F) : AlgebraicClosure ℚ))
  have hf1 : f y * f x + f i = 1 := by
    have := congrArg f hyxi
    simp only [f] at this ⊢
    push_cast at this
    rw [map_add, map_mul, map_add, map_mul] at this
    simpa using this
  have hlt : ‖f y * f x + f i‖ < 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ (norm_lt_one_of_mem q F w σ Φ hΦF hcont i hi))
    rw [norm_mul]
    calc ‖f y‖ * ‖f x‖ ≤ 1 * ‖f x‖ := by gcongr; exact norm_le_one q F σ y
      _ < 1 := by rw [one_mul]; exact h
  rw [hf1, norm_one] at hlt
  exact lt_irrefl _ hlt

end PBCut

namespace PBSigma

theorem norm_algEquiv (q : ℕ) [Fact q.Prime] (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (y : PadicAlgCl q) : ‖τ y‖ = ‖y‖ :=
  congrArg NNReal.toReal (nnnorm_padicAlgCl_algEquiv _ τ y)

theorem continuous_algEquiv (q : ℕ) [Fact q.Prime] (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) : Continuous τ :=
  (AddMonoidHomClass.isometry_of_norm τ (norm_algEquiv q τ)).continuous

theorem conj_apply (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥F] (σ₀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k : ↥F) :
    σ₀ (((AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * γ * σ₀)) k : ↥F) : AlgebraicClosure ℚ) = γ (σ₀ (k : AlgebraicClosure ℚ)) := by
  have h : algebraMap ↥F (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * γ * σ₀) k) =
      (σ₀⁻¹ * γ * σ₀) (k : AlgebraicClosure ℚ) := AlgEquiv.restrictNormal_commutes (σ₀⁻¹ * γ * σ₀) ↥F k
  change σ₀ (algebraMap ↥F (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * γ * σ₀) k)) = γ (σ₀ (k : AlgebraicClosure ℚ))
  rw [h, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply σ₀ σ₀⁻¹, mul_inv_cancel, AlgEquiv.one_apply]

theorem restrictNormalHom_eq_of_forall (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥F] (α β : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : ∀ k : ↥F, α (k : AlgebraicClosure ℚ) = β (k : AlgebraicClosure ℚ)) :
    AlgEquiv.restrictNormalHom ↥F α = AlgEquiv.restrictNormalHom ↥F β := by
  apply AlgEquiv.ext
  intro k
  apply Subtype.ext
  change algebraMap ↥F (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom ↥F α k) = algebraMap ↥F (AlgebraicClosure ℚ) (AlgEquiv.restrictNormalHom ↥F β k)
  exact (AlgEquiv.restrictNormal_commutes α ↥F k).trans ((h k).trans (AlgEquiv.restrictNormal_commutes β ↥F k).symm)

end PBSigma

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : 𝓞 ↥F, x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1) :
    ∃ Φ : w.adicCompletion ↥F →+* PadicAlgCl q,
      (∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ))) ∧
      (∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w) ∧
      (∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
        (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ)) ∧
      (∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
        (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
        ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x)) ∧
      Continuous Φ := by

  have hw : ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := (hσ _).2 (by
    push_cast
    rw [map_natCast, map_natCast, show ((q : ℕ) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) by rw [map_natCast],
      norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt))

  obtain ⟨σ₀, Φ₀, hΦ₀F, hmem₀, hsurj₀, heqv₀, hcont₀⟩ :=
    NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding q F w hw

  have hcut₀ : ∀ x : 𝓞 ↥F, x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ₀ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 :=
    PBCut.mem_asIdeal_iff q F w σ₀ Φ₀ hΦ₀F hcont₀

  have hgσ : ∀ k : ↥F, σ₀ (((AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * σ)) k : ↥F) : AlgebraicClosure ℚ) = σ (k : AlgebraicClosure ℚ) := fun k => by
    have h1 := PBSigma.conj_apply F σ₀ (σ * σ₀⁻¹) k
    have h2 : σ₀⁻¹ * (σ * σ₀⁻¹) * σ₀ = σ₀⁻¹ * σ := by group
    rw [h2] at h1
    rw [h1, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply σ₀⁻¹ σ₀, inv_mul_cancel, AlgEquiv.one_apply]

  have hg : AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w := by
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp ℚ ↥F w, MulAction.mem_stabilizer_iff]
    have key : ∀ x : 𝓞 ↥F, (AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * σ)) • x ∈ w.asIdeal ↔ x ∈ w.asIdeal := fun x => by
      rw [hcut₀, hσ]
      change ‖padicEmbedding q (σ₀ (((AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * σ)) (x : ↥F) : ↥F) : AlgebraicClosure ℚ))‖ < 1 ↔ _
      rw [hgσ]
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext x
    rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, ← key ((AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * σ))⁻¹ • x), smul_inv_smul]

  obtain ⟨τ, hτ⟩ := hsurj₀ ⟨_, hg⟩
  have hστ : ∀ k : ↥F, σ (k : AlgebraicClosure ℚ) = localGaloisToGlobal q τ (σ₀ (k : AlgebraicClosure ℚ)) := fun k => by
    rw [← hgσ k, ← PBSigma.conj_apply F σ₀ (localGaloisToGlobal q τ) k]
    exact congrArg (fun e : ↥F ≃ₐ[ℚ] ↥F => σ₀ ((e k : ↥F) : AlgebraicClosure ℚ)) hτ
  have hrNH : AlgEquiv.restrictNormalHom ↥F σ = AlgEquiv.restrictNormalHom ↥F (localGaloisToGlobal q τ * σ₀) :=
    PBSigma.restrictNormalHom_eq_of_forall F σ (localGaloisToGlobal q τ * σ₀) (fun k => by rw [hστ k, AlgEquiv.mul_apply])

  have hconj : ∀ τ' : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ' * σ) =
        AlgEquiv.restrictNormalHom ↥F (σ₀⁻¹ * localGaloisToGlobal q (τ⁻¹ * τ' * τ) * σ₀) := fun τ' => by
    rw [map_mul, map_mul, map_inv, hrNH, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]

  refine ⟨(τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q).toAlgHom.toRingHom.comp Φ₀, fun x => ?_, fun τ' => ?_, fun d => ?_, fun d τ' hd x => ?_, ?_⟩
  ·
    change τ (Φ₀ (algebraMap ↥F (w.adicCompletion ↥F) x)) = _
    rw [hΦ₀F, ← padicEmbedding_localGaloisToGlobal, ← hστ]
  ·
    rw [hconj]
    exact hmem₀ _
  ·
    obtain ⟨τ₁, hτ₁⟩ := hsurj₀ d
    refine ⟨τ * τ₁ * τ⁻¹, ?_⟩
    rw [hτ₁, hconj]
    congr 2
    group
  ·
    rw [hconj] at hd
    change τ (Φ₀ (d • x)) = τ' (τ (Φ₀ x))
    rw [heqv₀ d (τ⁻¹ * τ' * τ) hd x, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel,
      AlgEquiv.one_apply]
  ·
    exact (PBSigma.continuous_algEquiv q τ).comp hcont₀

end S_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_of_forall_mem_asIdeal_iff (solution)
