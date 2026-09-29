-- Prove2me | solution 1 for NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0f9978ee-a18d-5837-b3e3-64bd600afa3e

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation
import Theorems.Thm_NumberField_LevelArith_exists_hasBrauerLocalInvAt
import Theorems.Thm_NumberField_LevelArith_exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq
import Theorems.Thm_NumberField_IdeleLocalInv_exists_transport_data_of_algEquiv
import Theorems.Thm_NumberField_IdeleLocalInv_hasLocalInv_map_of_ringEquiv
import Theorems.Thm_NumberField_LevelArith_map_prG_conj_transport_eq_map_prG_map_psi
import Theorems.Thm_NumberField_IdeleLocalInv_hasLocalInv_iff_of_forall_map_prG_eq
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv.NumberField.LevelArith TensorProduct Pointwise"
p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv.NumberField NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "place AdeleRing PlaceDecomp.decomp IdeleLocalInv.HasLocalInv placesOverPrimes LevelArith.exists_hasBrauerLocalInvAt LevelArith.exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq IdeleLocalInv.exists_transport_data_of_algEquiv IdeleLocalInv.hasLocalInv_map_of_ringEquiv LevelArith.map_prG_conj_transport_eq_map_prG_map_psi IdeleLocalInv.hasLocalInv_iff_of_forall_map_prG_eq"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelFieldEquiv coe_levelFieldEquiv placesOverPrimes sUnitsMaxRep sUnitsMaxRep.val IsBrauerLocalInv exists_hasBrauerLocalInvAt exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq map_prG_conj_transport_eq_map_prG_map_psi"
namespace NatAssembly
p2m_open "NumberField.LevelArith NumberField"

section LevelInstances
variable (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)

noncomputable def levelFieldAlgEquiv : ↥F ≃ₐ[ℚ] ↥(levelField L F hLF) :=
  AlgEquiv.ofRingEquiv (f := levelFieldEquiv L F hLF) (fun r => by
    apply Subtype.ext
    rw [coe_levelFieldEquiv]
    rfl)

theorem normal_levelField [Normal ℚ ↥F] : Normal ℚ ↥(levelField L F hLF) :=
  Normal.of_algEquiv (levelFieldAlgEquiv L F hLF)

end LevelInstances

theorem coord_transfer (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K) [MulDistribMulAction (K ≃ₐ[E] K) (NumberField.AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (NumberField.AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z)
    (prG₀ : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (NumberField.AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG₀ : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (z : (NumberField.AdeleRing (𝓞 K) K)ˣ), (prG₀ w).hom (Additive.ofMul z) = Additive.ofMul (M4aHerbrand.finPart w z))
    (x₁ x₂ : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (NumberField.AdeleRing (𝓞 K) K)ˣ) 2)
    (hseam : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG₀ w) 2).hom x₁ =
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG₀ w) 2).hom x₂)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)) (h : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₂ v t) :
    NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₁ v t := by
  refine (NumberField.IdeleLocalInv.hasLocalInv_iff_of_forall_map_prG_eq E K D hactI x₁ x₂ (fun w₀ prG hpin => ?_) v t).mpr h
  have hpr : prG₀ w₀ = prG := by
    refine Rep.hom_ext ?_
    ext z
    exact ((hprG₀ w₀ (Additive.toMul z)).trans (hpin (Additive.toMul z)).symm :)
  subst hpr
  exact hseam w₀

end NumberField.LevelArith.NatAssembly

open NumberField.LevelArith.NatAssembly in
set_option maxHeartbeats 6400000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)))
    (hinv : IsBrauerLocalInv p S L inv) :
    ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →
        ∀ (a a' : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ))))
          (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
          (a : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w →
          (a' : (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) = continuousH2Srπ L.fixingSubgroup.subtype S _ w' →
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            sUnitsMaxRep.val S L ((w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s, t)) =
              σ • sUnitsMaxRep.val S L ((w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → (sUnitsMaxRep S L)) (s', t'))) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            inv a' v' = inv a v := by
  intro σ τ hστ a a' w w' ha ha' hww' v v' hvv'

  obtain ⟨t, ht⟩ := NumberField.LevelArith.exists_hasBrauerLocalInvAt S hpS L hL h4 a v
  obtain ⟨F, hLF, fdF, nrmF, galF, hF, ι, hι, φ, hbij, hval, D, instI, hactI, j, hj, f, haf, read⟩ := ht
  have hinvF := hinv F hLF hF ι hι φ hbij hval D hactI j hj
  have h1 : inv a v = t := hinvF f a haf v t read

  obtain ⟨fσ, hffσ, ha'f⟩ :=
    NumberField.LevelArith.exists_cocyclesTwo_conj_transport_continuousH2SrInflation_eq S L hL F hLF hF σ τ hστ a a' w w' ha ha' hww' f haf

  haveI : Normal ℚ ↥(levelField L F hLF) := normal_levelField L F hLF
  let σK : ↥(levelField L F hLF) ≃ₐ[ℚ] ↥(levelField L F hLF) := σ.restrictNormal ↥(levelField L F hLF)
  have hσK : ∀ y : ↥(levelField L F hLF), ((σK y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = σ ((y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) :=
    fun y => AlgEquiv.restrictNormal_commutes σ ↥(levelField L F hLF) y
  have hσK' : ∀ y : ↥(levelField L F hLF), ((σK.toRingEquiv y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = σ ((y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) := hσK
  have hστ' : ∀ x : ↥L, σK (algebraMap ↥L ↥(levelField L F hLF) x) = algebraMap ↥L ↥(levelField L F hLF) (τ.toRingEquiv x) := by
    intro x
    apply Subtype.ext
    rw [hσK]
    exact hστ x

  have hstd := NumberField.IdeleLocalInv.exists_transport_data_of_algEquiv ↥L ↥(levelField L F hLF) σK τ.toRingEquiv hστ' D hactI
  obtain ⟨c, pl, hcd, Tc, ψ, hrest⟩ := hstd
  have hc := hrest.1
  have hpl := hrest.2.1
  have hplb := hrest.2.2.1
  have hTc := hrest.2.2.2.1
  have hTcs := hrest.2.2.2.2.1
  have hψ := hrest.2.2.2.2.2
  have he' : ∀ x : ↥L, σK.toRingEquiv (algebraMap ↥L ↥(levelField L F hLF) x) = algebraMap ↥L ↥(levelField L F hLF) (τ.toRingEquiv x) :=
    fun x => hστ' x
  have hc' : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (y : ↥(levelField L F hLF)), c g (σK.toRingEquiv y) = σK.toRingEquiv (g y) :=
    fun g y => hc g y
  have hv' : ∀ x : ↥L, (v'.1).valuation ↥L (τ.toRingEquiv x) = (v.1).valuation ↥L x := fun x => hvv' x
  have hTc' : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : ↥(levelField L F hLF)),
      Tc w (y : w.adicCompletion ↥(levelField L F hLF)) = ((σK.toRingEquiv y : ↥(levelField L F hLF)) : (pl w).adicCompletion ↥(levelField L F hLF)) :=
    fun w y => hTc w y
  have readσ := NumberField.IdeleLocalInv.hasLocalInv_map_of_ringEquiv ↥L ↥(levelField L F hLF) ↥L ↥(levelField L F hLF)
    τ.toRingEquiv σK.toRingEquiv he' c hc' v.1 v'.1 hv' pl hpl hcd Tc hTc' hTcs D hactI D hactI ψ hψ
    ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) t read

  have hpr0 := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply ↥L ↥(levelField L F hLF) D hactI
  refine hpr0.elim fun prG₀ hprG₀ => ?_
  have hseam := NumberField.LevelArith.map_prG_conj_transport_eq_map_prG_map_psi S L F hLF σ τ hστ σK.toRingEquiv hσK' c hc' pl hplb.2 hpl
    Tc hTc' ψ hψ ι hι φ hval j hj prG₀ hprG₀ f fσ hffσ
  have h2 : inv a' v' = t :=
    hinvF fσ a' ha'f v' t (coord_transfer ↥L ↥(levelField L F hLF) D hactI prG₀ hprG₀ _ _ hseam v'.1 t readσ)
  exact h2.trans h1.symm

end S_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv
end P2MW
export P2MW.S_NumberField_LevelArith_apply_eq_apply_of_isBrauerLocalInv_of_algEquiv (solution)
