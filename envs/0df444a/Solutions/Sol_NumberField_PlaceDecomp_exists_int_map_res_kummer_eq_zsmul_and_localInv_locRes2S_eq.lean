-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fb7bc25b-1590-56de-8f9d-4e81186d7990

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_localInv_eq_of_inflate_eq_kummer
import Theorems.Thm_NumberField_PlaceDecomp_exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply"
p2m_attr_erase "simp" "IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp"

namespace F3Seam

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

def conjCochain₂ (σ : G) (f : G × G → A) : G × G → A :=
  fun x => A.ρ σ (f (σ⁻¹ * x.1 * σ, σ⁻¹ * x.2 * σ))

def conjHomotopy (σ : G) (f : G × G → A) : G → A :=
  fun g => f (σ, σ⁻¹ * g * σ) - f (g, σ)

@[scoped simp] lemma conjCochain₂_apply (σ : G) (f : G × G → A) (a b : G) :
    conjCochain₂ A σ f (a, b) = A.ρ σ (f (σ⁻¹ * a * σ, σ⁻¹ * b * σ)) := rfl

@[scoped simp] lemma conjHomotopy_apply (σ : G) (f : G × G → A) (g : G) :
    conjHomotopy A σ f g = f (σ, σ⁻¹ * g * σ) - f (g, σ) := rfl

theorem conjCochain₂_sub_eq_d₁₂ (σ : G) {f : G × G → A} (hf : f ∈ cocycles₂ A) :
    conjCochain₂ A σ f - f = (d₁₂ A).hom (conjHomotopy A σ f) := by
  funext x
  obtain ⟨a, b⟩ := x
  have hc := (mem_cocycles₂_iff f).1 hf

  have h1 := hc σ (σ⁻¹ * a * σ) (σ⁻¹ * b * σ)
  have h2 := hc a σ (σ⁻¹ * b * σ)
  have h3 := hc a b σ
  have e1 : σ * (σ⁻¹ * a * σ) = a * σ := by group
  have e2 : σ⁻¹ * a * σ * (σ⁻¹ * b * σ) = σ⁻¹ * (a * b) * σ := by group
  have e4 : σ * (σ⁻¹ * b * σ) = b * σ := by group
  rw [e1, e2] at h1
  rw [e4] at h2
  have r1 := eq_sub_of_add_eq h1.symm
  have r2 := eq_sub_of_add_eq h2.symm
  have r3 := eq_sub_of_add_eq h3.symm
  simp only [Pi.sub_apply, conjCochain₂_apply, conjHomotopy_apply, d₁₂_hom_apply, map_sub]
  rw [r1, r2, r3]
  abel

theorem conjCochain₂_sub_apply (σ : G) {f : G × G → A} (hf : f ∈ cocycles₂ A) (a b : G) :
    A.ρ σ (f (σ⁻¹ * a * σ, σ⁻¹ * b * σ)) - f (a, b) =
      A.ρ a (conjHomotopy A σ f b) - conjHomotopy A σ f (a * b) + conjHomotopy A σ f a := by
  have := congrFun (conjCochain₂_sub_eq_d₁₂ A σ hf) (a, b)
  simpa [d₁₂_hom_apply] using this

theorem conjCochain₂_mem_cocycles₂ (σ : G) {f : G × G → A} (hf : f ∈ cocycles₂ A) :
    conjCochain₂ A σ f ∈ cocycles₂ A := by
  have h : conjCochain₂ A σ f = f + (d₁₂ A).hom (conjHomotopy A σ f) := by
    rw [← conjCochain₂_sub_eq_d₁₂ A σ hf]; abel
  rw [h]
  exact add_mem hf (coboundaries₂_le_cocycles₂ A (LinearMap.mem_range_self _ _))

end Generic

section Level

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

theorem mem_fixingSubgroup_map_iff (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (φ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    τ ∈ (F.map (φ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).fixingSubgroup ↔
      φ⁻¹ * τ * φ ∈ F.fixingSubgroup := by
  simp only [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_map]
  constructor
  · rintro h y hy
    have hy' := h (φ y) ⟨y, hy, rfl⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv]
    show φ.symm (τ (φ y)) = y
    rw [show τ (φ y) = φ y from hy', AlgEquiv.symm_apply_apply]
  · rintro h x ⟨y, hy, rfl⟩
    have hy' := h y hy
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv] at hy'
    have := congrArg φ hy'
    simpa using this

theorem conjHomotopy_mul_eq (σ : G) (f : G × G → A) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hconst : ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g'))
    (g s : G) (hs : r s ∈ F.fixingSubgroup) (hs' : r (σ⁻¹ * s * σ) ∈ F.fixingSubgroup) :
    conjHomotopy A σ f (g * s) = conjHomotopy A σ f g := by
  have h1 : r 1 ∈ F.fixingSubgroup := by rw [map_one]; exact one_mem _
  have e : σ⁻¹ * (g * s) * σ = σ⁻¹ * g * σ * (σ⁻¹ * s * σ) := by group
  have k1 := hconst σ (σ⁻¹ * g * σ) 1 (σ⁻¹ * s * σ) h1 hs'
  have k2 := hconst g σ s 1 hs h1
  rw [mul_one] at k1 k2
  simp only [conjHomotopy_apply]
  rw [e, k1, k2]

theorem conjHomotopy_mul_eq_of_mem_sup (σ : G) (f : G × G → A) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hconst : ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g'))
    (g s : G)
    (hs : r s ∈ (F ⊔ F.map ((r σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).fixingSubgroup) :
    conjHomotopy A σ f (g * s) = conjHomotopy A σ f g := by
  rw [IntermediateField.fixingSubgroup_sup] at hs
  refine conjHomotopy_mul_eq A r σ f F hconst g s hs.1 ?_
  have := (mem_fixingSubgroup_map_iff F (r σ) (r s)).1 hs.2
  simpa [map_mul, map_inv] using this

theorem conjHomotopy_mul_eq_of_normal (σ : G) (f : G × G → A) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    [hN : Normal ℚ ↥F]
    (hconst : ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g'))
    (g s : G) (hs : r s ∈ F.fixingSubgroup) :
    conjHomotopy A σ f (g * s) = conjHomotopy A σ f g := by
  refine conjHomotopy_mul_eq A r σ f F hconst g s hs ?_
  rw [map_mul, map_mul, map_inv]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro y hy
  have hmem : (r σ) y ∈ F := by
    have e : (r σ) y = ((AlgHom.restrictNormal (r σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) F ⟨y, hy⟩ : F) :
        AlgebraicClosure ℚ) :=
      (AlgHom.restrictNormal_commutes (r σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) F ⟨y, hy⟩).symm
    rw [e]
    exact SetLike.coe_mem _
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, hs _ hmem, AlgEquiv.symm_apply_apply]

theorem isLevelConstant₁_conjHomotopy (σ : G) {f : G × G → A} (hf : IsLevelConstant₂ r f) :
    IsLevelConstant₁ r (conjHomotopy A σ f) := by
  obtain ⟨F, hF, h⟩ := hf
  haveI := hF
  refine ⟨F ⊔ F.map ((r σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ), inferInstance, fun g s hs => ?_⟩
  exact conjHomotopy_mul_eq_of_mem_sup A r σ f F h g s hs

theorem isLevelConstant₂_conjCochain₂ (σ : G) {f : G × G → A} (hf : IsLevelConstant₂ r f) :
    IsLevelConstant₂ r (conjCochain₂ A σ f) := by
  obtain ⟨F, hF, h⟩ := hf
  haveI := hF
  refine ⟨F.map ((r σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ), inferInstance, fun g g' s s' hs hs' => ?_⟩
  have ks := (mem_fixingSubgroup_map_iff F (r σ) (r s)).1 hs
  have ks' := (mem_fixingSubgroup_map_iff F (r σ) (r s')).1 hs'
  simp only [conjCochain₂_apply]
  have e : σ⁻¹ * (g * s) * σ = σ⁻¹ * g * σ * (σ⁻¹ * s * σ) := by group
  have e' : σ⁻¹ * (g' * s') * σ = σ⁻¹ * g' * σ * (σ⁻¹ * s' * σ) := by group
  rw [e, e', h _ _ _ _ (by simpa [map_mul, map_inv] using ks) (by simpa [map_mul, map_inv] using ks')]

theorem conjCochain₂_sub_mem_levelCoboundaries₂ (σ : G) {f : G × G → A} (hf : f ∈ levelCocycles₂ r A) :
    conjCochain₂ A σ f - f ∈ levelCoboundaries₂ r A :=
  (mem_levelCoboundaries₂_iff r A _).2
    ⟨conjHomotopy A σ f, isLevelConstant₁_conjHomotopy A r σ hf.2, (conjCochain₂_sub_eq_d₁₂ A σ hf.1).symm⟩

end Level

end F3Seam
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.faithfulSMul_decomp PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass PlaceDecomp.localInv_eq_of_inflate_eq_kummer PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units faithfulSMul_decomp exists_eq_zsmul_map_of_isLocalFundamentalClass zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass localInv_eq_of_inflate_eq_kummer exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace KummerPush
p2m_open "NumberField.PlaceDecomp NumberField"

section cyclo
variable (p : ℕ) [Fact p.Prime]

theorem apply_eq_pow_val_cycloChar (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ζ = ζ ^ ((cycloChar p σ : ZMod p)).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have ht : ((rootsOfUnity.mkOfPowEq ζ hζ : (AlgebraicClosure ℚ)ˣ) : (AlgebraicClosure ℚ)ˣ) ∈ rootsOfUnity p (AlgebraicClosure ℚ) :=
    (rootsOfUnity.mkOfPowEq ζ hζ).2
  have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ht
  (first | exact this | simpa using this | (have h__ := this; simp at h__; exact h__))

theorem apply_padicEmbedding_eq_pow (q : ℕ) [Fact q.Prime] (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1)
    (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    τ (padicEmbedding q ζ) = padicEmbedding q ζ ^ ((cycloChar p (localGaloisToGlobal q τ) : ZMod p)).val := by
  rw [← padicEmbedding_localGaloisToGlobal, apply_eq_pow_val_cycloChar p ζ hζ, map_pow]

end cyclo
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"

variable {p : ℕ} [Fact p.Prime] {q : Nat.Primes} [Fact ((q : ℕ)).Prime]

omit [Fact p.Prime] in

theorem units_pow_eq_one (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) : u ^ p = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, hu, ← map_pow, hζ, map_one, Units.val_one])

noncomputable def kummerHom (u : (PadicAlgCl q)ˣ) (hu : u ^ p = 1) :
    (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →+
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) where
  toFun a := Additive.ofMul (u ^ (a : ZMod p).val)
  map_zero' := by
    change Additive.ofMul (u ^ (0 : ZMod p).val) = 0
    simp
  map_add' a b := by
    change Additive.ofMul (u ^ ((a : ZMod p) + (b : ZMod p)).val) = Additive.ofMul (u ^ (a : ZMod p).val) + Additive.ofMul (u ^ (b : ZMod p).val)
    rw [← ofMul_mul, ← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hu]

theorem kummerHom_apply (u : (PadicAlgCl q)ˣ) (hu : u ^ p = 1) (a : ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) :
    kummerHom u hu a = Additive.ofMul (u ^ (a : ZMod p).val) := rfl

theorem coe_toMul_kummerHom (u : (PadicAlgCl q)ˣ) (hu : u ^ p = 1) (a : ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) :
    ((Additive.toMul (kummerHom u hu a) : (PadicAlgCl q)ˣ) : PadicAlgCl q) = (u : PadicAlgCl q) ^ (a : ZMod p).val := by
  rw [kummerHom_apply, toMul_ofMul, Units.val_pow_eq_pow_val]

theorem coe_toMul_kummerHom_eq (ζ : AlgebraicClosure ℚ) (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ)
    (hup : u ^ p = 1) (a : ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) :
    ((Additive.toMul (kummerHom u hup a) : (PadicAlgCl q)ˣ) : PadicAlgCl q) = padicEmbedding q ζ ^ (a : ZMod p).val := by
  rw [coe_toMul_kummerHom, hu]

theorem kummerHom_rho (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (τ : primeLocalGaloisGroup q) (a : ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) :
    kummerHom u hup ((ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))).ρ τ a) =
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (kummerHom u hup a) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  change Additive.ofMul (u ^ ((cycloChar p (localGaloisToGlobal q (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ)) : ZMod p) * (a : ZMod p)).val) =
    Additive.ofMul ((show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) • (u ^ (a : ZMod p).val))
  refine congrArg Additive.ofMul (Units.ext ?_)
  simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, map_pow]
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ (by rw [← Units.val_pow_eq_pow_val, hup, Units.val_one]), hu,
    apply_padicEmbedding_eq_pow p q ζ hζ, ← pow_mul]

theorem comp_mem_cocycles₂ (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (f : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
    (hf : f ∈ cocycles₂ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) :
    (fun g => kummerHom u hup (f g)) ∈ cocycles₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by
  rw [mem_cocycles₂_iff] at hf ⊢
  intro g h j
  rw [← kummerHom_rho ζ hζ u hu hup, ← map_add, ← map_add, hf]

theorem comp_d₁₂ (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (x : primeLocalGaloisGroup q → ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) :
    (fun g => kummerHom u hup ((d₁₂ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))).hom x g)) =
      (d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom
        (fun g => kummerHom u hup (x g)) := by
  funext g
  rw [d₁₂_hom_apply, d₁₂_hom_apply, map_add, map_sub, kummerHom_rho ζ hζ u hu hup]

theorem comp_mem_levelCocycles₂ (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (f : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
    (hf : f ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) :
    (fun g => kummerHom u hup (f g)) ∈
      levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by
  rw [mem_levelCocycles₂_iff] at hf ⊢
  exact ⟨comp_mem_cocycles₂ ζ hζ u hu hup f hf.1, hf.2.comp _⟩

theorem comp_mem_levelCoboundaries₂ (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (f : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
    (hf : f ∈ levelCoboundaries₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) :
    (fun g => kummerHom u hup (f g)) ∈
      levelCoboundaries₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by
  rw [mem_levelCoboundaries₂_iff] at hf ⊢
  obtain ⟨x, hx, rfl⟩ := hf
  exact ⟨fun g => kummerHom u hup (x g), hx.comp _, (comp_d₁₂ ζ hζ u hu hup x).symm⟩

noncomputable def pushLevelCocycle (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (et : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) :
    levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
  ⟨fun g => kummerHom u hup ((et : primeLocalGaloisGroup q × primeLocalGaloisGroup q → _) g),
    comp_mem_levelCocycles₂ ζ hζ u hu hup _ et.2⟩

theorem coe_toMul_pushLevelCocycle (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (et : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (g h : primeLocalGaloisGroup q) :
    ((Additive.toMul ((pushLevelCocycle ζ hζ u hu hup et : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ (((et : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
        (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h) : ZMod p).val) :=
  coe_toMul_kummerHom_eq ζ u hu hup _

theorem continuousH2π_push_eq (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) (u : (PadicAlgCl q)ˣ)
    (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (et et' : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (h : continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) et =
      continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) et') :
    continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))
        (pushLevelCocycle ζ hζ u hu hup et) =
      continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))
        (pushLevelCocycle ζ hζ u hu hup et') := by
  rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff] at h ⊢
  have := comp_mem_levelCoboundaries₂ ζ hζ u hu hup _ h
  convert this using 1
  funext g
  exact (map_sub (kummerHom u hup)
    ((et : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) g)
    ((et' : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) g)).symm

end NumberField.PlaceDecomp.KummerPush
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.faithfulSMul_decomp PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass PlaceDecomp.localInv_eq_of_inflate_eq_kummer PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units faithfulSMul_decomp exists_eq_zsmul_map_of_isLocalFundamentalClass zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass localInv_eq_of_inflate_eq_kummer exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace Coord
p2m_open "NumberField.PlaceDecomp NumberField"

variable {q : Nat.Primes} [Fact ((q : ℕ)).Prime]
variable {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥F] [IsGalois ℚ ↥F]
variable {w : HeightOneSpectrum (𝓞 ↥F)}

noncomputable def coordHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w) :
    primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) where
  toFun τ := ⟨AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ), hmem τ⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q (a * b) * σ) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q a * σ) *
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q b * σ)
    rw [← map_mul (AlgEquiv.restrictNormalHom ↥F), map_mul (primeLocalToGlobal q)]
    congr 1
    group)

theorem coe_coordHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w) :
    ∀ τ : primeLocalGaloisGroup q, ((coordHom σ hmem τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ) :=
  fun _ => rfl

theorem coordHom_surjective (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w)
    (hsurj : ∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ)) :
    Function.Surjective (coordHom σ hmem) := by
  intro d
  obtain ⟨τ, hτ⟩ := hsurj d
  exact ⟨τ, Subtype.ext hτ.symm⟩

theorem apply_coordHom_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w)
    (heqv : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
      ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x)) :
    ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (coordHom σ hmem τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x) :=
  fun τ x => heqv (coordHom σ hmem τ) τ rfl x

theorem exists_coordHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hmem : ∀ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) ∈ NumberField.PlaceDecomp.decomp ℚ ↥F w)
    (hsurj : ∀ d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w), ∃ τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ))
    (heqv : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (τ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q),
      (d : ↥F ≃ₐ[ℚ] ↥F) = AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * localGaloisToGlobal q τ * σ) →
      ∀ x : w.adicCompletion ↥F, Φ (d • x) = τ (Φ x)) :
    ∃ π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w),
      (∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ)) ∧
      Function.Surjective π ∧
      (∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
        Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x)) :=
  ⟨coordHom σ hmem, coe_coordHom σ hmem, coordHom_surjective σ hmem hsurj, apply_coordHom_smul σ Φ hmem heqv⟩

end NumberField.PlaceDecomp.Coord
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.faithfulSMul_decomp PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass PlaceDecomp.localInv_eq_of_inflate_eq_kummer PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units faithfulSMul_decomp exists_eq_zsmul_map_of_isLocalFundamentalClass zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass localInv_eq_of_inflate_eq_kummer exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace XRep
p2m_open "NumberField.PlaceDecomp NumberField"

variable {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥F] [IsGalois ℚ ↥F]
variable {w : HeightOneSpectrum (𝓞 ↥F)}

noncomputable def coordCocycle
    (b : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)
    (hbc : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) :
    ↥(cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) :=
  (mapCocycles₂ (MonoidHom.id _) ρ) ((mapCocycles₂ (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype
    (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)))) ⟨b, hbc⟩)

theorem coordCocycle_apply
    (b : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)
    (hbc : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (d₁ d₂ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) :
    (coordCocycle b hbc ρ : _ → Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (d₁, d₂) =
      ρ.hom (b ((d₁ : ↥F ≃ₐ[ℚ] ↥F), (d₂ : ↥F ≃ₐ[ℚ] ↥F))) := rfl

theorem H2π_coordCocycle
    (b : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)
    (hbc : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) :
    (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom (coordCocycle b hbc ρ) =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ρ 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))) 2).hom
              ((H2π (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)).hom ⟨b, hbc⟩)) := by
  simp only [coordCocycle, H2π_comp_map_apply]

end NumberField.PlaceDecomp.XRep
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.faithfulSMul_decomp PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass PlaceDecomp.localInv_eq_of_inflate_eq_kummer PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units faithfulSMul_decomp exists_eq_zsmul_map_of_isLocalFundamentalClass zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass localInv_eq_of_inflate_eq_kummer exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace F3X
p2m_open "NumberField.PlaceDecomp NumberField"

theorem restrictNormalHom_eq_one_of_mem_fixingSubgroup
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ F.fixingSubgroup) :
    AlgEquiv.restrictNormalHom ↥F τ = 1 := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
  rw [AlgEquiv.one_apply]
  exact (AlgEquiv.restrictNormal_commutes τ ↥F x).trans
    ((IntermediateField.mem_fixingSubgroup_iff F τ).mp hτ (x : AlgebraicClosure ℚ) x.2)

theorem conj_mem_fixingSubgroup
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ F.fixingSubgroup) :
    σ⁻¹ * τ * σ ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  intro y hy
  have hmem : σ y ∈ F := by
    have e : σ y = ((AlgHom.restrictNormal (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) ↥F ⟨y, hy⟩ : ↥F) :
        AlgebraicClosure ℚ) :=
      (AlgHom.restrictNormal_commutes (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) ↥F ⟨y, hy⟩).symm
    rw [e]
    exact SetLike.coe_mem _
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, hτ _ hmem, AlgEquiv.symm_apply_apply]

section Frame

variable (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (w : HeightOneSpectrum (𝓞 ↥F))
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
  (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))

omit [Fact ((q : ℕ)).Prime] in

theorem pi_eq_one
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (s : primeLocalGaloisGroup q) (hs : primeLocalToGlobal q s ∈ F.fixingSubgroup) : π s = 1 := by
  apply Subtype.ext
  rw [hπ s, OneMemClass.coe_one]
  exact restrictNormalHom_eq_one_of_mem_fixingSubgroup F _ (conj_mem_fixingSubgroup F σ _ hs)

noncomputable def inflateCochain
    (x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) :
    primeLocalGaloisGroup q × primeLocalGaloisGroup q →
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
  fun gh => Additive.ofMul (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul (x (π gh.1, π gh.2))))

omit [IsGalois ℚ ↥F] in

theorem toMul_inflateCochain
    (x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (g h : primeLocalGaloisGroup q) :
    Additive.toMul ((inflateCochain q F w Φ π x : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)
        (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h))) :=
  rfl

noncomputable def unitsMapLinear :
    Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ →ₗ[ℤ]
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
  (MonoidHom.toAdditive (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q))).toIntLinearMap

omit [IsGalois ℚ ↥F] in
theorem unitsMapLinear_apply (a : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) :
    unitsMapLinear q F w Φ a = Additive.ofMul (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul a)) :=
  rfl

omit [IsGalois ℚ ↥F] in

theorem inflateCochain_eq_cochainsPullPush₂
    (x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) :
    inflateCochain q F w Φ π x = groupCohomology.cochainsPullPush₂ π (unitsMapLinear q F w Φ) x := by
  funext gh
  rfl

omit [IsGalois ℚ ↥F] in

theorem unitsMapLinear_equivariant
    (hπΦ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    (g : primeLocalGaloisGroup q)
    (a : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) :
    unitsMapLinear q F w Φ ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ).ρ (π g) a) =
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ g (unitsMapLinear q F w Φ a) := by
  have key : ∀ u : (w.adicCompletion ↥F)ˣ,
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (π g • u) =
        (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from g) • Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) u := fun u => by
    apply Units.ext
    rw [AlgEquiv.smul_units_def]
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [NumberField.PlaceDecomp.coe_smul_units]
    exact hπΦ g u
  exact congrArg Additive.ofMul (key (Additive.toMul a))

omit [IsGalois ℚ ↥F] in

theorem inflateCochain_mem_cocycles₂
    (hπΦ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ}
    (hx : x ∈ cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) :
    inflateCochain q F w Φ π x ∈
      cocycles₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by
  rw [inflateCochain_eq_cochainsPullPush₂]
  exact groupCohomology.cochainsPullPush₂_mem_cocycles₂ π (unitsMapLinear q F w Φ)
    (unitsMapLinear_equivariant q F w Φ π hπΦ) hx

theorem isLevelConstant₂_inflateCochain
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) :
    groupCohomology.IsLevelConstant₂ (primeLocalToGlobal q) (inflateCochain q F w Φ π x) := by
  refine ⟨F, inferInstance, fun g g' s s' hs hs' => ?_⟩
  simp only [inflateCochain, map_mul, pi_eq_one q F w σ π hπ s hs, pi_eq_one q F w σ π hπ s' hs', mul_one]

theorem inflateCochain_mem_levelCocycles₂
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπΦ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ}
    (hx : x ∈ cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) :
    inflateCochain q F w Φ π x ∈
      levelCocycles₂ (primeLocalToGlobal q)
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
  ⟨inflateCochain_mem_cocycles₂ q F w Φ π hπΦ hx, isLevelConstant₂_inflateCochain q F w σ Φ π hπ x⟩

noncomputable def inflateLevelCocycle
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπΦ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ}
    (hx : x ∈ cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) :
    ↥(levelCocycles₂ (primeLocalToGlobal q)
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) :=
  ⟨inflateCochain q F w Φ π x, inflateCochain_mem_levelCocycles₂ q F w σ Φ π hπ hπΦ hx⟩

@[scoped simp] theorem coe_inflateLevelCocycle
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπΦ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ}
    (hx : x ∈ cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) :
    ((inflateLevelCocycle q F w σ Φ π hπ hπΦ hx :
        ↥(levelCocycles₂ (primeLocalToGlobal q)
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))) :
      primeLocalGaloisGroup q × primeLocalGaloisGroup q →
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) =
      inflateCochain q F w Φ π x :=
  rfl

theorem toMul_inflateLevelCocycle
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπΦ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ}
    (hx : x ∈ cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ))
    (g h : primeLocalGaloisGroup q) :
    Additive.toMul ((inflateLevelCocycle q F w σ Φ π hπ hπΦ hx :
        primeLocalGaloisGroup q × primeLocalGaloisGroup q →
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)
        (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h))) :=
  rfl

end Frame
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam"

end NumberField.PlaceDecomp.F3X
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp.F3X"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField"

set_option maxHeartbeats 6400000 in

theorem clauseOne
    {p : ℕ} [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (ζF : (↥F)ˣ) (hζF : ((ζF : ↥F) : AlgebraicClosure ℚ) = ζ)
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p)))
    (b : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)
    (hb : ∀ (g h : ↥F ≃ₐ[ℚ] ↥F) (ĝ ĥ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ y : ↥F, ĝ (y : AlgebraicClosure ℚ) = ((g y : ↥F) : AlgebraicClosure ℚ)) →
      (∀ y : ↥F, ĥ (y : AlgebraicClosure ℚ) = ((h y : ↥F) : AlgebraicClosure ℚ)) →
        b (g, h) = Additive.ofMul (ζF ^ ((f (ĝ, ĥ) : ZMod p).val)))
    (hbc : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))
    (w : HeightOneSpectrum (𝓞 ↥F))
    (hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) L'] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (↥L')ˣ]
    (Φ' : w.adicCompletion ↥F ≃+* L')
    (h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ' (g • x) = g • Φ' x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hK₀ : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) K₀)
    (θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (hθ' : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ'.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (↥L')ˣ))
    (hu' : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) K₀ u') :
    ∃ m : ℤ,
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ρ 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))) 2).hom
              ((H2π (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)).hom ⟨b, hbc⟩)) =
        m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u') := by
  have hp : p.Prime := Fact.out

  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F) := NumberField.PlaceDecomp.faithfulSMul_decomp ℚ ↥F w
  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) ↥L' := ⟨fun {g₁ g₂} h => by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion ↥F)
    intro x
    apply Φ'.injective
    rw [h3, h3]
    exact h (Φ' x)⟩
  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic q L' ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) h1

  set z := (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ρ 2).hom
    ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))) 2).hom
      ((H2π (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)).hom ⟨b, hbc⟩)) with hz
  obtain ⟨k, hk⟩ := NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass ℚ F w hsolv q L' Φ' h1 h2 h3
    K₀ hK₀ θ' hθ' u' hu' z

  have hζFp : ζF ^ p = 1 := by
    apply Units.ext
    apply Subtype.ext
    show (((ζF ^ p : (↥F)ˣ) : ↥F) : AlgebraicClosure ℚ) = (((1 : (↥F)ˣ) : ↥F) : AlgebraicClosure ℚ)
    rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, hζF, hζ.pow_eq_one, Units.val_one, OneMemClass.coe_one]

  have hlift : ∀ g : ↥F ≃ₐ[ℚ] ↥F, ∃ ĝ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ y : ↥F, ĝ (y : AlgebraicClosure ℚ) = ((g y : ↥F) : AlgebraicClosure ℚ) := by
    intro g
    haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
    haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
    exact ⟨g.liftNormal (AlgebraicClosure ℚ), fun y => g.liftNormal_commutes (AlgebraicClosure ℚ) y⟩

  have hpcoc : (p : ℤ) • (⟨b, hbc⟩ : cocycles₂ (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)) = 0 := by
    apply Subtype.ext
    funext gh
    obtain ⟨g, h⟩ := gh
    obtain ⟨ĝ, hĝ⟩ := hlift g
    obtain ⟨ĥ, hĥ⟩ := hlift h
    show (p : ℤ) • b (g, h) = 0
    rw [hb g h ĝ ĥ hĝ hĥ]
    have h1 : ((ζF ^ (f (ĝ, ĥ) : ZMod p).val) ^ (p : ℤ) : (↥F)ˣ) = 1 := by
      rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, hζFp, one_pow]
    calc (p : ℤ) • Additive.ofMul (ζF ^ (f (ĝ, ĥ) : ZMod p).val)
        = Additive.ofMul ((ζF ^ (f (ĝ, ĥ) : ZMod p).val) ^ (p : ℤ)) := (ofMul_zpow _ _).symm
      _ = 0 := by rw [h1, ofMul_one]
  have hpz : (p : ℤ) • z = 0 := by
    simp only [hz, ← map_zsmul, hpcoc, map_zero]
  rw [hk, smul_smul] at hpz
  have hdvd : (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℤ) ∣ (p : ℤ) * k :=
    (NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass ℚ F w hsolv q L' Φ' h1 h2 h3
      K₀ hK₀ θ' hθ' u' hu' _).mp hpz
  obtain ⟨d, hd⟩ := hpD
  have hdk : (d : ℤ) ∣ k := by
    rw [hd, Nat.cast_mul] at hdvd
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero)).mp hdvd
  obtain ⟨m, rfl⟩ := hdk
  refine ⟨m, ?_⟩
  show z = _
  rw [hk, hd, Nat.mul_div_cancel_left d hp.pos, mul_comm, ← smul_smul, natCast_zsmul]

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.faithfulSMul_decomp PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass PlaceDecomp.localInv_eq_of_inflate_eq_kummer PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units faithfulSMul_decomp exists_eq_zsmul_map_of_isLocalFundamentalClass zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass localInv_eq_of_inflate_eq_kummer exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding"
namespace F3Heart
p2m_open "NumberField.PlaceDecomp NumberField"

open NumberField.PlaceDecomp.KummerPush

variable {p : ℕ} [Fact p.Prime] {q : Nat.Primes} [Fact ((q : ℕ)).Prime]
variable {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥F] [IsGalois ℚ ↥F]
variable {w : HeightOneSpectrum (𝓞 ↥F)}

theorem padicEmbedding_pow_eq_one (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) : padicEmbedding q ζ ^ p = 1 := by
  rw [← map_pow, hζ, map_one]

theorem coe_map_toMul_rho_b
    (ζ : AlgebraicClosure ℚ) (hζp : ζ ^ p = 1)
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p)))
    (ζF : (↥F)ˣ) (hζF : ((ζF : ↥F) : AlgebraicClosure ℚ) = ζ)
    (b : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)
    (hb : ∀ (g h : ↥F ≃ₐ[ℚ] ↥F) (ĝ ĥ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ y : ↥F, ĝ (y : AlgebraicClosure ℚ) = ((g y : ↥F) : AlgebraicClosure ℚ)) →
      (∀ y : ↥F, ĥ (y : AlgebraicClosure ℚ) = ((h y : ↥F) : AlgebraicClosure ℚ)) →
        b (g, h) = Additive.ofMul (ζF ^ ((f (ĝ, ĥ) : ZMod p).val)))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (hρ : ∀ u : (↥F)ˣ, ρ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap ↥F (w.adicCompletion ↥F)).toMonoidHom u))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦ : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (g h : primeLocalGaloisGroup q) :
    ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)
        (Additive.toMul (ρ.hom (b (((π g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F),
          ((π h : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F))))) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ (((cycloChar p σ : ZMod p) *
        (f (σ⁻¹ * primeLocalToGlobal q g * σ, σ⁻¹ * primeLocalToGlobal q h * σ) : ZMod p)).val) := by
  have hlift : ∀ τ : primeLocalGaloisGroup q, ∀ y : ↥F,
      (σ⁻¹ * primeLocalToGlobal q τ * σ) (y : AlgebraicClosure ℚ) =
        ((((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) y : ↥F) : AlgebraicClosure ℚ) := by
    intro τ y
    rw [hπ τ]
    change _ = algebraMap ↥F (AlgebraicClosure ℚ) (((σ⁻¹ * primeLocalToGlobal q τ * σ).restrictNormal ↥F) y)
    rw [AlgEquiv.restrictNormal_commutes]
    rfl
  have e1 : Additive.toMul (ρ.hom (b (((π g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F),
          ((π h : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F)))) =
      Units.map (algebraMap ↥F (w.adicCompletion ↥F)).toMonoidHom
        (ζF ^ ((f (σ⁻¹ * primeLocalToGlobal q g * σ, σ⁻¹ * primeLocalToGlobal q h * σ) : ZMod p).val)) := by
    rw [hb _ _ (σ⁻¹ * primeLocalToGlobal q g * σ) (σ⁻¹ * primeLocalToGlobal q h * σ) (hlift g) (hlift h)]
    erw [hρ]
    rfl
  have e2 := congrArg (fun v => ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) v : (PadicAlgCl q)ˣ) : PadicAlgCl q)) e1
  refine e2.trans ?_
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_pow_eq_pow_val, map_pow]
  rw [hΦ, hζF, apply_eq_pow_val_cycloChar p ζ hζp σ, map_pow, ← pow_mul, ZMod.val_mul,
    ← pow_eq_pow_mod _ (padicEmbedding_pow_eq_one ζ hζp)]

theorem coe_toMul_kummerHom_conjCochain₂
    (ζ : AlgebraicClosure ℚ) (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ) (hup : u ^ p = 1)
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g h : primeLocalGaloisGroup q) :
    ((Additive.toMul (kummerHom u hup
        (F3Seam.conjCochain₂ (ofChar (k := ZMod p) (cycloChar p)) σ f (primeLocalToGlobal q g, primeLocalToGlobal q h))) :
          (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ (((cycloChar p σ : ZMod p) *
        (f (σ⁻¹ * primeLocalToGlobal q g * σ, σ⁻¹ * primeLocalToGlobal q h * σ) : ZMod p)).val) := by
  rw [coe_toMul_kummerHom_eq ζ u hu hup, F3Seam.conjCochain₂_apply]
  congr 2

end NumberField.PlaceDecomp.F3Heart
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp.F3X"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp.F3X"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.F3Seam P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq.NumberField.PlaceDecomp.F3X"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (c : continuousH2S S (ofChar (k := ZMod p) (cycloChar p)))

    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p)))
    (hf : f ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)))
    (hfc : continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨f, hf⟩ = c)

    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (ζF : (↥F)ˣ) (hζF : ((ζF : ↥F) : AlgebraicClosure ℚ) = ζ)
    (hconst : ∀ g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g'))

    (b : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)
    (hb : ∀ (g h : ↥F ≃ₐ[ℚ] ↥F) (ĝ ĥ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ y : ↥F, ĝ (y : AlgebraicClosure ℚ) = ((g y : ↥F) : AlgebraicClosure ℚ)) →
      (∀ y : ↥F, ĥ (y : AlgebraicClosure ℚ) = ((h y : ↥F) : AlgebraicClosure ℚ)) →
        b (g, h) = Additive.ofMul (ζF ^ ((f (ĝ, ĥ) : ZMod p).val)))
    (hbc : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))

    (w : HeightOneSpectrum (𝓞 ↥F)) (hw : (((q : Nat.Primes) : ℕ) : 𝓞 ↥F) ∈ w.asIdeal)
    (hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (hρ : ∀ u : (↥F)ˣ, ρ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap ↥F (w.adicCompletion ↥F)).toMonoidHom u))

    (L' : IntermediateField ℚ_[(q : Nat.Primes)] (PadicAlgCl (q : Nat.Primes))) [FiniteDimensional ℚ_[(q : Nat.Primes)] L']
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) L'] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (↥L')ˣ]
    (Φ' : w.adicCompletion ↥F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[(q : Nat.Primes)]), g • algebraMap ℚ_[(q : Nat.Primes)] L' x = algebraMap ℚ_[(q : Nat.Primes)] L' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ' (g • x) = g • Φ' x)
    (K₀ : IntermediateField ℚ_[(q : Nat.Primes)] (PadicAlgCl (q : Nat.Primes))) [FiniteDimensional ℚ_[(q : Nat.Primes)] K₀]
    (_ : ExtCitation.LocalLevel.IsBase (q : Nat.Primes) L' ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) K₀)
    (θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ'.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass (q : Nat.Primes) L' ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) K₀ u') :
    ∃ m : ℤ,
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) ρ 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ))) 2).hom
              ((H2π (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (↥F)ˣ)).hom ⟨b, hbc⟩)) =
        m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u') ∧
      localInv p ζ (q : Nat.Primes)
        (locRes₂S S (ofChar (k := ZMod p) (cycloChar p)) (extArithLoc S (Sum.inr q)) c) = (m : ZMod p) := by
  classical
  rename_i _i1 _i2 _i3 _i4 _i5 _i6 _i7 h1 h2 h3 _i8 hK₀ hθ' hu'
  have hp : p.Prime := Fact.out

  obtain ⟨m, hm⟩ := clauseOne ((q : Nat.Primes) : ℕ) ζ hζ F ζF hζF f b hb hbc w hpD ρ L' Φ' h1 h2 h3 K₀ hK₀ θ' hθ' u' hu'
  refine ⟨m, hm, ?_⟩

  obtain ⟨σ, Φ, hΦ, hmem, hsurj, heqv, hcont⟩ :=
    NumberField.PlaceDecomp.exists_ringHom_adicCompletion_padicAlgCl_extends_padicEmbedding ((q : Nat.Primes) : ℕ) F w hw
  obtain ⟨π, hπ, hπs, hπΦ⟩ := NumberField.PlaceDecomp.Coord.exists_coordHom (q := (q : Nat.Primes)) σ Φ hmem hsurj heqv

  let x := NumberField.PlaceDecomp.XRep.coordCocycle (w := w) b hbc ρ
  have hx := NumberField.PlaceDecomp.XRep.H2π_coordCocycle (w := w) b hbc ρ
  let X := NumberField.PlaceDecomp.F3X.inflateLevelCocycle (q : Nat.Primes) F w σ Φ π hπ hπΦ x.2

  let et : ↥(levelCocycles₂ (primeLocalToGlobal (q : Nat.Primes))
      (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal (q : Nat.Primes))))) :=
    levelCocycles₂Map (rH := MonoidHom.id _) (rG := primeLocalToGlobal (q : Nat.Primes))
      (A := ofChar (k := ZMod p) (cycloChar p)) (B := ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal (q : Nat.Primes))))
      (primeLocalToGlobal (q : Nat.Primes)) (fun _ => rfl) LinearMap.id (fun _ _ => rfl)
      (levelCocyclesS₂ToLevelCocycles₂ S _ ⟨f, hf⟩)
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  let u : (PadicAlgCl (q : Nat.Primes))ˣ :=
    Units.map (padicEmbedding ((q : Nat.Primes) : ℕ) : AlgebraicClosure ℚ →* PadicAlgCl (q : Nat.Primes)) (hζ.isUnit hp.ne_zero).unit
  have hu : (u : PadicAlgCl (q : Nat.Primes)) = padicEmbedding (q : Nat.Primes) ζ := by simp [u]
  have hup : u ^ p = 1 := NumberField.PlaceDecomp.KummerPush.units_pow_eq_one ζ hζp u hu
  let E := NumberField.PlaceDecomp.KummerPush.pushLevelCocycle ζ hζp u hu hup et

  have hXE : continuousH2π (primeLocalToGlobal (q : Nat.Primes))
        (show Rep ℤ (primeLocalGaloisGroup (q : Nat.Primes)) from Rep.ofAlgebraAutOnUnits ℚ_[(q : Nat.Primes)] (PadicAlgCl (q : Nat.Primes))) X =
      continuousH2π (primeLocalToGlobal (q : Nat.Primes))
        (show Rep ℤ (primeLocalGaloisGroup (q : Nat.Primes)) from Rep.ofAlgebraAutOnUnits ℚ_[(q : Nat.Primes)] (PadicAlgCl (q : Nat.Primes))) E := by

    have hglob := F3Seam.conjCochain₂_sub_mem_levelCoboundaries₂ (ofChar (k := ZMod p) (cycloChar p)) (MonoidHom.id _) σ
      (levelCocyclesS₂_le_levelCocycles₂ S _ hf)

    have hloc := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := MonoidHom.id _) (rG := primeLocalToGlobal (q : Nat.Primes))
      (A := ofChar (k := ZMod p) (cycloChar p)) (B := ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal (q : Nat.Primes))))
      (primeLocalToGlobal (q : Nat.Primes)) (fun _ => rfl) LinearMap.id (fun _ _ => rfl) hglob

    have hunits := NumberField.PlaceDecomp.KummerPush.comp_mem_levelCoboundaries₂ ζ hζp u hu hup _ hloc
    rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff, Submodule.coe_sub]
    convert hunits using 1
    funext gh
    obtain ⟨g, h⟩ := gh
    simp only [Pi.sub_apply, cochainsPullPush₂_apply, LinearMap.id_apply, map_sub]
    congr 1
    all_goals first
      | rfl
      | (apply Additive.toMul.injective
         apply Units.ext

         exact (NumberField.PlaceDecomp.F3Heart.coe_map_toMul_rho_b ζ hζp f ζF hζF b hb ρ hρ σ Φ hΦ π hπ g h).trans
           (NumberField.PlaceDecomp.F3Heart.coe_toMul_kummerHom_conjCochain₂ ζ u hu hup f σ g h).symm)

  have key := NumberField.PlaceDecomp.localInv_eq_of_inflate_eq_kummer (q : Nat.Primes) ζ hζ F w hpD σ Φ hΦ hcont π hπ hπs hπΦ
    L' Φ' h1 h2 h3 K₀ hK₀ θ' hθ' u' hu' m _ hm x hx X
    (NumberField.PlaceDecomp.F3X.toMul_inflateLevelCocycle (q : Nat.Primes) F w σ Φ π hπ hπΦ x.2) et E
    (NumberField.PlaceDecomp.KummerPush.coe_toMul_pushLevelCocycle ζ hζp u hu hup et) hXE
  subst hfc
  exact key

end S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_int_map_res_kummer_eq_zsmul_and_localInv_locRes2S_eq (solution)
