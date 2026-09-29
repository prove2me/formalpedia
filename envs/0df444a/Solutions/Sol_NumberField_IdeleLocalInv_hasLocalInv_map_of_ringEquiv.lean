-- Prove2me | solution 1 for NumberField.IdeleLocalInv.hasLocalInv_map_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a4d64462-eb2c-53a1-8b7f-cb538d677aa1

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_map_of_ringEquiv
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_map_of_ringEquiv.NumberField IsDedekindDomain M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass"
namespace Pullback
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    (G H : Type) [Group G] [Group H] [MulSemiringAction H L] [MulDistribMulAction H (↥L)ˣ]
    [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
    (e : G ≃* H) (hGe : ∀ (g : G) (x : L), g • x = e g • x) (hGeu : ∀ (g : G) (v : (↥L)ˣ), g • v = e g • v)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥L)ˣ)) (hu : IsLocalFundamentalClass q L H K u)
    (φ : Rep.res e.toMonoidHom (Rep.ofMulDistribMulAction H (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction G (↥L)ˣ)
    (hφ : ∀ m, φ.hom m = m)

include hGe hGeu hu hφ in
theorem isLocalFundamentalClass_map :
    IsLocalFundamentalClass q L G K ((groupCohomology.map e.toMonoidHom φ 2).hom u) := by
  intro M _ hLM H' _ _ _ _ _ NL Nn _ _ e' φF π d ι hι hfin hc

  let e'' : H ≃* H' ⧸ NL :=
    { toFun := fun h => e' (e.symm h)
      invFun := fun z => e (e'.symm z)
      left_inv := fun h => by simp
      right_inv := fun z => by simp
      map_mul' := fun a b => by simp [map_mul] }

  have d'' : IsUnramOverlayerDatum q L H K M hLM H' NL Nn e'' φF π :=
    { smul_algebraMap := d.smul_algebraMap
      coe_smul_units := d.coe_smul_units
      mem_base_iff := d.mem_base_iff
      mem_layer_iff := d.mem_layer_iff
      coe_smul_eq := fun h₀ h hh x => by
        have hh' : (QuotientGroup.mk h : H' ⧸ NL) = e' (e.symm h₀) := hh
        have := d.coe_smul_eq (e.symm h₀) h hh' x
        rw [hGe, MulEquiv.apply_symm_apply] at this
        exact this
      card_quotient := d.card_quotient.trans (Nat.card_congr e.toEquiv)
      mem_zpowers := d.mem_zpowers
      frobenius := d.frobenius
      smul_pi := d.smul_pi
      pi_mem := d.pi_mem
      norm_pi_lt := d.norm_pi_lt
      norm_le_norm_pi := d.norm_le_norm_pi }

  let ι'' : Rep.res (e''.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction H (↥L)ˣ) ⟶
      Rep.ofMulDistribMulAction H' (↥M)ˣ :=
    (Rep.resFunctor (e'.symm.toMonoidHom.comp (QuotientGroup.mk' NL))).map φ ≫ ι
  have hι'' : ∀ v : (↥L)ˣ, (((Additive.toMul (ι''.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := by
    intro v
    show (((Additive.toMul (ι.hom (φ.hom (Additive.ofMul v))) : (↥M)ˣ) : M) : PadicAlgCl q) = _
    rw [hφ]
    exact hι v
  have key := hu M hLM H' NL Nn e'' φF π d'' ι'' hι'' hfin hc

  have hcomp := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction H (↥L)ˣ) e.toMonoidHom
    (e'.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) φ ι 2
  have happ := congrArg (fun T => (ModuleCat.Hom.hom T) u) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  rw [← happ]
  exact key

end ExtCitation.LocalLevel.Pullback

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing PlaceDecomp.decomp PlaceDecomp.coe_smul_units IdeleLocalInv.HasLocalInv PlaceTransport.mem_smul_asIdeal_iff PlaceTransport.valuation_apply_of_smul_eq PlaceTransport.stabilizer_eq_decomp"
namespace IdeleLocalInv
p2m_export "NumberField.IdeleLocalInv" "HasLocalInv"
namespace FieldIsoTransport
p2m_open "NumberField.IdeleLocalInv NumberField"

section perPlace
variable {E K E' K' : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    [Field E'] [NumberField E'] [Field K'] [NumberField K'] [Algebra E' K'] [IsGalois E' K']
    (c : (K ≃ₐ[E] K) ≃* (K' ≃ₐ[E'] K'))
    (w : HeightOneSpectrum (𝓞 K)) (w' : HeightOneSpectrum (𝓞 K'))
    (hcd : ∀ g : K ≃ₐ[E] K, g ∈ NumberField.PlaceDecomp.decomp E K w → c g ∈ NumberField.PlaceDecomp.decomp E' K' w')
    (hcd' : ∀ g' : K' ≃ₐ[E'] K', g' ∈ NumberField.PlaceDecomp.decomp E' K' w' → c.symm g' ∈ NumberField.PlaceDecomp.decomp E K w)

def decompEquiv : ↥(NumberField.PlaceDecomp.decomp E' K' w') ≃* ↥(NumberField.PlaceDecomp.decomp E K w) where
  toFun g' := ⟨c.symm g', hcd' g' g'.2⟩
  invFun g := ⟨c g, hcd g g.2⟩
  left_inv g' := Subtype.ext (c.apply_symm_apply _)
  right_inv g := Subtype.ext (c.symm_apply_apply _)
  map_mul' a b := Subtype.ext (map_mul c.symm _ _)

theorem coe_decompEquiv (g' : ↥(NumberField.PlaceDecomp.decomp E' K' w')) :
    ((decompEquiv c w w' hcd hcd' g' : ↥(NumberField.PlaceDecomp.decomp E K w)) : K ≃ₐ[E] K) = c.symm g' := rfl

theorem subtype_comp_decompEquiv :
    (NumberField.PlaceDecomp.decomp E K w).subtype.comp (decompEquiv c w w' hcd hcd').toMonoidHom =
      c.symm.toMonoidHom.comp (NumberField.PlaceDecomp.decomp E' K' w').subtype := rfl

end perPlace

end NumberField.IdeleLocalInv.FieldIsoTransport

open NumberField.IdeleLocalInv.FieldIsoTransport in
set_option maxHeartbeats 6400000 in

theorem solution
    (E K E' K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    [Field E'] [NumberField E'] [Field K'] [NumberField K'] [Algebra E' K'] [IsGalois E' K']

    (e₀ : E ≃+* E') (e : K ≃+* K') (he : ∀ x : E, e (algebraMap E K x) = algebraMap E' K' (e₀ x))
    (c : (K ≃ₐ[E] K) ≃* (K' ≃ₐ[E'] K')) (hc : ∀ (g : K ≃ₐ[E] K) (y : K), c g (e y) = e (g y))

    (v : HeightOneSpectrum (𝓞 E)) (v' : HeightOneSpectrum (𝓞 E')) (hv : ∀ x : E, v'.valuation E' (e₀ x) = v.valuation E x)
    (pl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K'))
    (hpl : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), (pl w).valuation K' (e y) = w.valuation K y)
    (hcd : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : K ≃ₐ[E] K), g ∈ NumberField.PlaceDecomp.decomp E K w → c g ∈ NumberField.PlaceDecomp.decomp E' K' (pl w))

    (Tc : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K ≃+* (pl w).adicCompletion K')
    (hTc : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), Tc w (y : w.adicCompletion K) = ((e y : K') : (pl w).adicCompletion K'))
    (hTcs : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K),
      Tc w (g • y) = (⟨c g, hcd w g g.2⟩ : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) • Tc w y)

    (D : IdeleGaloisDescent (𝓞 K) E K) [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z)
    (D' : IdeleGaloisDescent (𝓞 K') E' K') [MulDistribMulAction (K' ≃ₐ[E'] K') (AdeleRing (𝓞 K') K')ˣ]
    (hactI' : ∀ (g : K' ≃ₐ[E'] K') (z : (AdeleRing (𝓞 K') K')ˣ), g • z = D'.unitsAct g z)
    (ψ : Rep.res c.symm.toMonoidHom (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
      Rep.ofMulDistribMulAction (K' ≃ₐ[E'] K') (AdeleRing (𝓞 K') K')ˣ)
    (hψ : ∀ (w : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ),
      finPart (pl w) (Additive.toMul (ψ.hom (Additive.ofMul z))) = Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K') (finPart w z))

    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2) (t : AddCircle (1 : ℚ))
    (h : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t) :
    NumberField.IdeleLocalInv.HasLocalInv E' K' D' hactI' ((groupCohomology.map c.symm.toMonoidHom ψ 2).hom x) v' t := by
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  haveI : FiniteDimensional E' K' := Module.Finite.of_restrictScalars_finite ℚ E' K'
  haveI : Finite (K' ≃ₐ[E'] K') := inferInstance

  have hcd' : ∀ (w : HeightOneSpectrum (𝓞 K)) (g' : K' ≃ₐ[E'] K'), g' ∈ NumberField.PlaceDecomp.decomp E' K' (pl w) →
      c.symm g' ∈ NumberField.PlaceDecomp.decomp E K w := by
    intro w g' hg'
    have hg's : g'⁻¹ • pl w = pl w := by
      have : g'⁻¹ ∈ MulAction.stabilizer (K' ≃ₐ[E'] K') (pl w) := by
        rw [NumberField.PlaceTransport.stabilizer_eq_decomp]; exact inv_mem hg'
      exact this
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp, MulAction.mem_stabilizer_iff]
    apply HeightOneSpectrum.ext
    ext r
    have key : w.valuation K (algebraMap (𝓞 K) K ((c.symm g')⁻¹ • r)) = w.valuation K (algebraMap (𝓞 K) K r) := by
      show w.valuation K ((c.symm g')⁻¹ (r : K)) = w.valuation K (r : K)
      rw [← hpl w ((c.symm g')⁻¹ (r : K)), ← hc, map_inv, MulEquiv.apply_symm_apply,
        NumberField.PlaceTransport.valuation_apply_of_smul_eq hg's, hpl]
    rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), key]
  obtain ⟨prG, hprG, w, hw, q, hq, hqw, L₁, fd, act, faith, actU, Φ, h1, h2, h3, K₀, fd₀, base, θ, hθ, u, hu, n, hn, ht⟩ := h

  obtain ⟨prG', hprG'⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E' K' D' hactI'

  have hmemK : ∀ (y : 𝓞 K), (⟨e y, map_isIntegral_int e.toRingHom y.2⟩ : 𝓞 K') ∈ (pl w).asIdeal ↔ y ∈ w.asIdeal := by
    intro y
    refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K') (pl w) _).symm.trans (Iff.trans ?_ (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w y))
    show (pl w).valuation K' (e (y : K)) < 1 ↔ w.valuation K (y : K) < 1
    rw [hpl]
  have hmemE : ∀ (y : 𝓞 E), (⟨e₀ y, map_isIntegral_int e₀.toRingHom y.2⟩ : 𝓞 E') ∈ v'.asIdeal ↔ y ∈ v.asIdeal := by
    intro y
    refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') v' _).symm.trans (Iff.trans ?_ (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v y))
    show v'.valuation E' (e₀ (y : E)) < 1 ↔ v.valuation E (y : E) < 1
    rw [hv]
  have hw' : (pl w).asIdeal.comap (algebraMap (𝓞 E') (𝓞 K')) = v'.asIdeal := by
    ext y'
    obtain ⟨y, rfl⟩ : ∃ y : 𝓞 E, (⟨e₀ y, map_isIntegral_int e₀.toRingHom y.2⟩ : 𝓞 E') = y' :=
      ⟨⟨e₀.symm y', map_isIntegral_int e₀.symm.toRingHom y'.2⟩, Subtype.ext (e₀.apply_symm_apply _)⟩
    rw [Ideal.mem_comap]
    refine Iff.trans ?_ (hmemE y).symm
    rw [← hw, Ideal.mem_comap]
    refine Iff.trans ?_ (hmemK (algebraMap (𝓞 E) (𝓞 K) y))
    refine iff_of_eq (congrArg (fun r : 𝓞 K' => r ∈ (pl w).asIdeal) (Subtype.ext ?_))
    show algebraMap E' K' (e₀ (y : E)) = e (algebraMap E K (y : E))
    rw [he]

  have hqw' : ((q : ℕ) : 𝓞 K') ∈ (pl w).asIdeal := by
    have := (hmemK ((q : ℕ) : 𝓞 K)).mpr hqw
    obtain ⟨y, hy, hyq⟩ : ∃ y : 𝓞 K', y ∈ (pl w).asIdeal ∧ (y : K') = e ((q : ℕ) : K) := ⟨_, this, rfl⟩
    have hyq' : y = ((q : ℕ) : 𝓞 K') := by
      first
        | exact NumberField.RingOfIntegers.ext (by rw [hyq, map_natCast]; simp)
        | exact NumberField.RingOfIntegers.coe_injective (by simp [hyq, map_natCast])
    exact hyq' ▸ hy

  let c' := decompEquiv c w (pl w) (hcd w) (hcd' w)
  have hc'c : ∀ g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)),
      (⟨c ((c' g' : ↥(NumberField.PlaceDecomp.decomp E K w)) : K ≃ₐ[E] K), hcd w _ (c' g').2⟩ : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) = g' :=
    fun g' => Subtype.ext (c.apply_symm_apply _)
  have hcard : Nat.card ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)) = Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) := Nat.card_congr c'.toEquiv

  letI act' : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)) L₁ := MulSemiringAction.compHom L₁ c'.toMonoidHom
  letI actU' : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)) (↥L₁)ˣ := MulDistribMulAction.compHom (↥L₁)ˣ c'.toMonoidHom
  have hsmul : ∀ (g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) (z : L₁), g' • z = c' g' • z := fun _ _ => rfl
  have hsmulU : ∀ (g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) (z : (↥L₁)ˣ), g' • z = c' g' • z := fun _ _ => rfl
  have faith' : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)) L₁ :=
    ⟨fun {a b} hab => c'.injective (FaithfulSMul.eq_of_smul_eq_smul (α := L₁) fun z => by rw [← hsmul, ← hsmul]; exact hab z)⟩
  have h1' : ∀ (g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) (y : ℚ_[q]), g' • algebraMap ℚ_[q] L₁ y = algebraMap ℚ_[q] L₁ y :=
    fun g' y => by rw [hsmul]; exact h1 _ y
  have h2' : ∀ (g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) (y : (↥L₁)ˣ), ((g' • y : (↥L₁)ˣ) : L₁) = g' • (y : L₁) :=
    fun g' y => by rw [hsmulU, hsmul]; exact h2 _ y

  let Φ' : (pl w).adicCompletion K' ≃+* L₁ := (Tc w).symm.trans Φ
  have hTcs' : ∀ (g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) (y' : (pl w).adicCompletion K'),
      (Tc w).symm (g' • y') = c' g' • (Tc w).symm y' := by
    intro g' y'
    apply (Tc w).injective
    rw [RingEquiv.apply_symm_apply, hTcs w (c' g') ((Tc w).symm y'), RingEquiv.apply_symm_apply, hc'c]
  have h3' : ∀ (g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) (y' : (pl w).adicCompletion K'), Φ' (g' • y') = g' • Φ' y' := by
    intro g' y'
    show Φ ((Tc w).symm (g' • y')) = g' • Φ ((Tc w).symm y')
    rw [hTcs', h3, hsmul]
  have base' : ExtCitation.LocalLevel.IsBase q L₁ ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)) K₀ := by
    refine ⟨base.le, fun z => ?_⟩
    rw [base.mem_iff]
    constructor
    · intro hz g'
      rw [hsmul]
      exact hz _
    · intro hz g
      have := hz (c'.symm g)
      rwa [hsmul, MulEquiv.apply_symm_apply] at this

  let ΦM' : (↥L₁)ˣ →* ((pl w).adicCompletion K')ˣ := Units.map Φ'.symm.toRingHom.toMonoidHom
  have hΦM' : ∀ (g' : ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) (y : (↥L₁)ˣ), ΦM' (g' • y) = g' • ΦM' y := by
    intro g' y
    apply Units.ext
    show Φ'.symm ((g' • y : (↥L₁)ˣ) : ↥L₁) = ((g' • ΦM' y : ((pl w).adicCompletion K')ˣ) : (pl w).adicCompletion K')
    rw [h2' g' y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ'.injective
    rw [h3' g', RingEquiv.apply_symm_apply]
    congr 1
    show (y : ↥L₁) = Φ' (Φ'.symm (y : ↥L₁))
    exact (Φ'.apply_symm_apply _).symm
  let θ' := M4aHerbrand.repHomOfMulEquivariant ΦM' hΦM'
  have hθ' : ∀ y : (↥L₁)ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul y)) : ((pl w).adicCompletion K')ˣ) : (pl w).adicCompletion K') = Φ'.symm (y : ↥L₁) :=
    fun y => rfl

  let φ : Rep.res c'.toMonoidHom (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L₁)ˣ) ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)) (↥L₁)ˣ :=
    Rep.ofHom ⟨(AddMonoidHom.id (Additive (↥L₁)ˣ)).toIntLinearMap, fun g' => LinearMap.ext fun z => by
      change Additive.ofMul ((c' g') • (Additive.toMul z : (↥L₁)ˣ)) = Additive.ofMul (g' • (Additive.toMul z : (↥L₁)ˣ))
      rfl⟩
  have hφ : ∀ m, φ.hom m = m := fun _ => rfl
  have hu' := ExtCitation.LocalLevel.Pullback.isLocalFundamentalClass_map q L₁ ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))
    ↥(NumberField.PlaceDecomp.decomp E K w) c' hsmul hsmulU K₀ u hu φ hφ

  let T : Rep.res c'.toMonoidHom (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ) ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)) ((pl w).adicCompletion K')ˣ :=
    Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K'))).toIntLinearMap,
      fun g' => LinearMap.ext fun z => by
        change Additive.ofMul (Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K') ((c' g') • (Additive.toMul z : (w.adicCompletion K)ˣ))) =
          Additive.ofMul (g' • Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K') (Additive.toMul z : (w.adicCompletion K)ˣ))
        congr 1
        apply Units.ext
        show Tc w (((c' g') • (Additive.toMul z : (w.adicCompletion K)ˣ) : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
          ((g' • Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K') (Additive.toMul z) : ((pl w).adicCompletion K')ˣ) : (pl w).adicCompletion K')
        rw [NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.coe_smul_units, hTcs, hc'c]
        rfl⟩

  have key : (Rep.resFunctor (NumberField.PlaceDecomp.decomp E' K' (pl w)).subtype).map ψ ≫ prG' (pl w) =
      (Rep.resFunctor c'.toMonoidHom).map (prG w) ≫ T := by
    refine Rep.hom_ext ?_
    ext z
    obtain ⟨zu, rfl⟩ : ∃ zu, Additive.ofMul zu = z := ⟨Additive.toMul z, rfl⟩
    show (prG' (pl w)).hom (ψ.hom (Additive.ofMul zu)) = T.hom ((prG w).hom (Additive.ofMul zu))
    rw [hprG, show ψ.hom (Additive.ofMul zu) = Additive.ofMul (Additive.toMul (ψ.hom (Additive.ofMul zu))) from rfl, hprG']
    exact (congrArg Additive.ofMul (hψ w zu)).trans rfl
  have hsq : (groupCohomology.map (NumberField.PlaceDecomp.decomp E' K' (pl w)).subtype (prG' (pl w)) 2).hom
        ((groupCohomology.map c.symm.toMonoidHom ψ 2).hom x) =
      (groupCohomology.map c'.toMonoidHom T 2).hom ((groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x) := by
    have e1 := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
      c.symm.toMonoidHom (NumberField.PlaceDecomp.decomp E' K' (pl w)).subtype ψ (prG' (pl w)) 2
    have e2 := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
      (NumberField.PlaceDecomp.decomp E K w).subtype c'.toMonoidHom (prG w) T 2
    rw [key] at e1
    have hx1 := congrArg (fun T' => (ModuleCat.Hom.hom T') x) e1
    have hx2 := congrArg (fun T' => (ModuleCat.Hom.hom T') x) e2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx1 hx2
    exact hx1.symm.trans hx2

  have key2 : (Rep.resFunctor c'.toMonoidHom).map θ ≫ T = (Rep.resFunctor (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E' K' (pl w)))).map φ ≫ θ' := by
    refine Rep.hom_ext ?_
    ext z
    obtain ⟨y, rfl⟩ : ∃ y : (↥L₁)ˣ, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
    show T.hom (θ.hom (Additive.ofMul y)) = θ'.hom (φ.hom (Additive.ofMul y))
    rw [hφ, M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    change Additive.ofMul (Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K') (Additive.toMul (θ.hom (Additive.ofMul y)))) =
      Additive.ofMul (ΦM' y)
    congr 1
    apply Units.ext
    show Tc w ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ'.symm (y : ↥L₁)
    rw [hθ]
    rfl
  have hθu : (groupCohomology.map c'.toMonoidHom T 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u) =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) θ' 2).hom
        ((groupCohomology.map c'.toMonoidHom φ 2).hom u) := by
    have e3 := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L₁)ˣ)
      (MonoidHom.id _) c'.toMonoidHom θ T 2
    have e4 := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L₁)ˣ)
      c'.toMonoidHom (MonoidHom.id _) φ θ' 2
    rw [key2] at e3
    have hx3 := congrArg (fun T' => (ModuleCat.Hom.hom T') u) e3
    have hx4 := congrArg (fun T' => (ModuleCat.Hom.hom T') u) e4
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx3 hx4
    exact hx3.symm.trans hx4
  have hcoord : (groupCohomology.map (NumberField.PlaceDecomp.decomp E' K' (pl w)).subtype (prG' (pl w)) 2).hom
        ((groupCohomology.map c.symm.toMonoidHom ψ 2).hom x) =
      n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E' K' (pl w))) θ' 2).hom
        ((groupCohomology.map c'.toMonoidHom φ 2).hom u) := by
    rw [hsq, hn, map_zsmul, hθu]
  exact ⟨prG', hprG', pl w, hw', q, hq, hqw', L₁, fd, act', faith', actU', Φ', h1', h2', h3', K₀, fd₀, base', θ', hθ', _, hu', n, hcoord,
    by rw [ht, hcard]⟩

end S_NumberField_IdeleLocalInv_hasLocalInv_map_of_ringEquiv
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_map_of_ringEquiv (solution)
