-- Prove2me | solution 1 for M4aHerbrand.exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2fb945d9-fa41-526c-95d2-79227b77bff8

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup
import Theorems.Thm_M4aHerbrand_exists_hom_adicCompletion_res_decomp_ideles_apply
import Theorems.Thm_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "instance" "instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup.M4aHerbrand"
open scoped NumberField.PlaceDecomp

set_option linter.unusedSectionVars false

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart repHomOfMulEquivariant IdeleClassGroup IdeleGaloisDescent exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup exists_hom_adicCompletion_res_decomp_ideles_apply exists_hom_ideles_ideleClassGroup_apply exists_hom_res_decomp_ideles_adicCompletion_apply"
namespace SingletP
p2m_open "M4aHerbrand"

theorem exists_isBase (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), ExtCitation.LocalLevel.IsBase q L G K := by
  haveI : SMulCommClass G ℚ_[q] L := ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG]⟩
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toLinearMap
      (fun a b h => (IntermediateField.inclusion
        (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toRingHom.injective h)
  · refine ⟨IntermediateField.lift_le _, fun x => ?_⟩
    rw [IntermediateField.mem_lift]
    exact Iff.rfl

structure BridgeFC (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) where
  q : ℕ
  [hq : Fact q.Prime]
  L : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd : FiniteDimensional ℚ_[q] L]
  [act : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [faith : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [actU : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ]
  Φ : w.adicCompletion F ≃+* L
  h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x
  h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)
  h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x
  hqw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal
  K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd₀ : FiniteDimensional ℚ_[q] K₀]
  base : ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀
  θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ
  hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L)
  u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ)
  hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u

theorem nonempty_bridgeFC (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F)) : Nonempty (BridgeFC E F w) := by
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  obtain ⟨q, hq, L, fd, act, faith, actU, Φ, h1, h2, h3, hqw⟩ := NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion E F w
  obtain ⟨K₀, fd₀, base⟩ := exists_isBase q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1

  let ΦM : (↥L)ˣ →* (w.adicCompletion F)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ΦM (g • y) = g • ΦM y := by
    intro g y
    apply Units.ext
    show Φ.symm ((g • y : (↥L)ˣ) : ↥L) = ((g • ΦM y : (w.adicCompletion F)ˣ) : w.adicCompletion F)
    rw [h2 g y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ.injective
    rw [h3 g, RingEquiv.apply_symm_apply]
    congr 1
    show (y : ↥L) = Φ (Φ.symm (y : ↥L))
    exact (Φ.apply_symm_apply _).symm
  let θ := M4aHerbrand.repHomOfMulEquivariant ΦM hΦM
  have hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : ↥L) :=
    fun y => rfl

  have hsolv : Group.IsSolvable (↥(NumberField.PlaceDecomp.decomp E F w)) := by
    haveI := (hG.to_subgroup (NumberField.PlaceDecomp.decomp E F w)).isNilpotent
    infer_instance
  obtain ⟨u, hu⟩ := (ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1 h2 hsolv K₀ base).exists
  exact ⟨{ q := q, L := L, Φ := Φ, h1 := h1, h2 := h2, h3 := h3, hqw := hqw, K₀ := K₀, base := base, θ := θ, hθ := hθ, u := u, hu := hu }⟩

noncomputable def chosen (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F)) : BridgeFC E F w :=
  Classical.choice (nonempty_bridgeFC E F p hG w)

open scoped Pointwise NumberField.PlaceTransport in

theorem exists_above_fixedField_decomp_eq (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    ∃ v₀ : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w))),
      NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w)) F v₀ = w ∧
      ∀ v, NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w)) F v = w → v = v₀ := by
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  refine ⟨w.under (𝓞 ↥(IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w))), ?_, fun v hv => ?_⟩
  ·
    set Z : IntermediateField E F := IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w) with hZ
    set w₁ : HeightOneSpectrum (𝓞 F) := NumberField.PlaceAbove.above ↥Z F (w.under (𝓞 ↥Z)) with hw₁
    have h₁ : w₁.asIdeal.comap (algebraMap (𝓞 ↥Z) (𝓞 F)) = (w.under (𝓞 ↥Z)).asIdeal := NumberField.PlaceAbove.comap_above ↥Z F _
    haveI : w₁.asIdeal.LiesOver (w.under (𝓞 ↥Z)).asIdeal := ⟨h₁.symm⟩
    haveI : w.asIdeal.LiesOver (w.under (𝓞 ↥Z)).asIdeal := ⟨rfl⟩
    haveI : w₁.asIdeal.IsPrime := w₁.isPrime
    haveI : w.asIdeal.IsPrime := w.isPrime
    haveI : FiniteDimensional (↥Z) F := inferInstance
    haveI : Finite (F ≃ₐ[↥Z] F) := inferInstance
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 ↥Z)).asIdeal w₁.asIdeal w.asIdeal (F ≃ₐ[↥Z] F)
    have hτ : σ.restrictScalars E ∈ NumberField.PlaceDecomp.decomp E F w := by
      have : σ.restrictScalars E ∈ IntermediateField.fixingSubgroup Z := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact σ.commutes ⟨x, hx⟩
      rwa [IntermediateField.fixingSubgroup_fixedField] at this

    have hfix : ∀ τ : F ≃ₐ[E] F, τ ∈ NumberField.PlaceDecomp.decomp E F w → τ • w.asIdeal = w.asIdeal := by
      intro τ hτ'
      rw [← NumberField.PlaceTransport.stabilizer_eq_decomp, MulAction.mem_stabilizer_iff] at hτ'
      have h2 := congrArg HeightOneSpectrum.asIdeal hτ'
      rw [NumberField.PlaceTransport.smul_asIdeal_eq_map] at h2
      rw [Ideal.pointwise_smul_def]
      exact h2
    have hact : σ • w₁.asIdeal = (σ.restrictScalars E) • w₁.asIdeal := by
      rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
      congr 1
    have hw₁w : w₁.asIdeal = w.asIdeal := by
      rw [hact] at hσ
      rw [← hfix _ (inv_mem hτ), ← hσ, inv_smul_smul]
    exact HeightOneSpectrum.ext hw₁w
  · apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under]
    have h := NumberField.PlaceAbove.comap_above (↥(IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w))) F v
    rw [hv] at h
    exact h.symm

section coord
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
  (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
  (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
    finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
  (ιD : ∀ w : HeightOneSpectrum (𝓞 F),
    Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
  (hιD : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ), (ιD w).hom (Additive.ofMul x) = Additive.ofMul (ι w x))

include hι hιD

theorem coord_off (w w' : HeightOneSpectrum (𝓞 F)) (hne : w' ≠ w)
    (P : Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
      Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w')))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w')) (w'.adicCompletion F)ˣ))
    (hP : ∀ x : (AdeleRing (𝓞 F) F)ˣ, P.hom (Additive.ofMul x) = Additive.ofMul (finPart w' x))
    (y : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) 2) :
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w))) P 2).hom
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (ιD w) 2).hom y) = 0 := by
  have hψ0 : (Rep.resFunctor (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w)))).map (ιD w) ≫ P = 0 := by
    refine Rep.hom_ext ?_
    ext z
    obtain ⟨t, rfl⟩ : ∃ t, Additive.ofMul t = z := ⟨Additive.toMul z, rfl⟩
    show P.hom ((ιD w).hom (Additive.ofMul t)) = 0
    rw [hιD]
    erw [hP]
    rw [(hι w t).2.1 w' hne]
    rfl
  have hc := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w))
    (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w)))
    (ιD w) P 2
  rw [hψ0] at hc
  simp only [groupCohomology.map, groupCohomology.cochainsMap_zero, HomologicalComplex.homologyMap_zero] at hc
  have happ := congrArg (fun T => (ModuleCat.Hom.hom T) y) hc
  exact happ.symm

theorem coord_at (w : HeightOneSpectrum (𝓞 F))
    (P : Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
      Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
    (hP : ∀ x : (AdeleRing (𝓞 F) F)ˣ, P.hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (y : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) 2) :
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w))) P 2).hom
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (ιD w) 2).hom y) =
    (groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))) 2).hom y := by

  let Q : Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶
      Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) :=
    𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
  have hψ : (Rep.resFunctor (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))).map (ιD w) ≫ P =
      (Rep.resFunctor (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))).map
        (𝟙 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) ≫ Q := by
    refine Rep.hom_ext ?_
    ext z
    obtain ⟨t, rfl⟩ : ∃ t, Additive.ofMul t = z := ⟨Additive.toMul z, rfl⟩
    show P.hom ((ιD w).hom (Additive.ofMul t)) = Additive.ofMul t
    rw [hιD]
    erw [hP]
    rw [(hι w t).1]
    rfl
  have hc1 := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w))
    (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
    (ιD w) P 2
  have hc2 := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w))
    (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
    (𝟙 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) Q 2
  rw [hψ] at hc1
  have hc := hc1.symm.trans hc2
  rw [groupCohomology.map_id, Category.id_comp] at hc
  have happ := congrArg (fun T => (ModuleCat.Hom.hom T) y) hc
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  exact happ

end coord

section prH
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]

theorem finPart_smul_of_prG
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (w : HeightOneSpectrum (𝓞 F)) (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (t : (AdeleRing (𝓞 F) F)ˣ) :
    finPart w ((g : F ≃ₐ[E] F) • t) = g • finPart w t := by
  have hh := Rep.hom_comm_apply (prG w) g (Additive.ofMul t)
  rw [Rep.coe_res_obj_ρ', Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply] at hh
  erw [hprG, hprG] at hh
  exact Additive.ofMul.injective hh

noncomputable def prH
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (w w' : HeightOneSpectrum (𝓞 F)) :
    Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
      Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w')))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w')) (w'.adicCompletion F)ˣ) :=
  Rep.ofHom
    { toLinearMap := (MonoidHom.toAdditive (finPart (R := 𝓞 F) (F := F) w')).toIntLinearMap
      isIntertwining' := fun h => by
        apply LinearMap.ext
        intro z
        obtain ⟨t, rfl⟩ : ∃ t, Additive.ofMul t = z := ⟨Additive.toMul z, rfl⟩
        have key := finPart_smul_of_prG E F prG hprG w'
          (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w')) h) t
        simp only [LinearMap.comp_apply]
        exact congrArg Additive.ofMul key }

theorem prH_hom_apply
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (w w' : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (prH E F prG hprG w w').hom (Additive.ofMul x) = Additive.ofMul (finPart w' x) := rfl

end prH

end M4aHerbrand.SingletP

open M4aHerbrand.SingletP in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))

    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F)) :
    ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup (F ≃ₐ[E] F), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ)),

      Function.Injective invG ∧ (∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧
      (∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F)) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • invG x) ∧

      (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
            n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ∧

      (∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance

  obtain ⟨invG, inv, hI₁, hI₂, hI₃, hI₄, hR, hTG, hT⟩ :=
    M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup E F D hactI hact hinf p hG
  refine ⟨invG, inv, hI₁, hI₂, hI₃, hI₄, hR, hTG, ?_⟩

  intro w q _ L' _ _ _ Φ hΦ₁ hΦ₂ hΦ₃ K₀ _ hbase θ hθ u' hu'

  obtain ⟨ιD, hιD⟩ := M4aHerbrand.exists_hom_adicCompletion_res_decomp_ideles_apply E F D hactI ι hι
  obtain ⟨π, hπ⟩ := M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply E F D hactI hact
  obtain ⟨prG, hprG⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E F D hactI
  let πH : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) :=
    (Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map π
  have hπH : ∀ y : (AdeleRing (𝓞 F) F)ˣ, πH.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : IdeleClassGroup (𝓞 F) F) :=
    fun y => hπ y
  have hprH := prH_hom_apply E F prG hprG w

  let x : ↥(groupCohomology (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) 2) :=
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (ιD w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')

  have hlam_eq : lam w = ιD w ≫ πH := by
    refine Rep.hom_ext ?_
    ext z
    obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
    show (lam w).hom (Additive.ofMul y) = (ιD w ≫ πH).hom (Additive.ofMul y)
    rw [hlam, Rep.hom_comp]
    show _ = πH.hom ((ιD w).hom (Additive.ofMul y))
    rw [hιD]
    exact (hπH (ι w y)).symm
  have hLHS : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u') =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) πH 2).hom x := by
    rw [hlam_eq, groupCohomology.map_id_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hLHS]

  let Z : IntermediateField E F := IntermediateField.fixedField (NumberField.PlaceDecomp.decomp E F w)
  let ch : ∀ w' : HeightOneSpectrum (𝓞 F), BridgeFC E F w' := fun w' => chosen E F p hG w'
  let ab : HeightOneSpectrum (𝓞 ↥Z) → HeightOneSpectrum (𝓞 F) := fun v => NumberField.PlaceAbove.above ↥Z F v
  let n : HeightOneSpectrum (𝓞 ↥Z) → ℤ := fun v => if ab v = w then 1 else 0

  have hTR : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u' = (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (ch w).θ 2).hom (ch w).u := by
    haveI : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F) := NumberField.PlaceDecomp.faithfulSMul_decomp E F w
    haveI : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) L' := ⟨fun {g₁ g₂} h =>
      FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion F) fun y => Φ.injective (by rw [hΦ₃ g₁ y, hΦ₃ g₂ y]; exact h _)⟩
    obtain ⟨-, hqw⟩ := NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F w q L' Φ
    letI := (ch w).hq; letI := (ch w).fd; letI := (ch w).act; letI := (ch w).faith; letI := (ch w).actU; letI := (ch w).fd₀
    exact NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E F w
      q hqw L' Φ hΦ₁ hΦ₂ hΦ₃ K₀ hbase θ hθ u' hu'
      (ch w).q (ch w).hqw (ch w).L (ch w).Φ (ch w).h1 (ch w).h2 (ch w).h3 (ch w).K₀ (ch w).base (ch w).θ (ch w).hθ (ch w).u (ch w).hu
  have hcoord_at : ∀ (w' : HeightOneSpectrum (𝓞 F)), w' = w →
      (groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w))) (prH E F prG hprG w w') 2).hom x =
        (1 : ℤ) • (groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w')))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F w') ≤ (NumberField.PlaceDecomp.decomp E F w'))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w')) (w'.adicCompletion F)ˣ))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w')) (ch w').θ 2).hom (ch w').u) := by
    intro w' hw'
    subst hw'
    rw [one_smul, ← hTR]
    exact coord_at E F ι hι ιD hιD _ (prH E F prG hprG _ _) (hprH _) _
  have hcoord : ∀ v : HeightOneSpectrum (𝓞 ↥Z),
      (groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F (ab v)) ≤ (NumberField.PlaceDecomp.decomp E F w))) (prH E F prG hprG w (ab v)) 2).hom x =
        n v • (groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F (ab v)) ≤ (NumberField.PlaceDecomp.decomp E F (ab v))))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F (ab v)) ≤ (NumberField.PlaceDecomp.decomp E F (ab v))))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (ab v))) ((ab v).adicCompletion F)ˣ))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (ab v))) (ch (ab v)).θ 2).hom (ch (ab v)).u) := by
    intro v
    by_cases h : ab v = w
    · rw [show n v = 1 from if_pos h]
      exact hcoord_at (ab v) h
    · rw [show n v = 0 from if_neg h, zero_smul]
      exact coord_off E F ι hι ιD hιD w (ab v) h (prH E F prG hprG w (ab v)) (hprH (ab v)) _

  have hTw := hT (NumberField.PlaceDecomp.decomp E F w) (prH E F prG hprG w) hprH πH hπH x (fun v => (ch (ab v)).q) (fun v => (ch (ab v)).hq) (fun v => (ch (ab v)).L)
    (fun v => (ch (ab v)).fd) (fun v => (ch (ab v)).act) (fun v => (ch (ab v)).actU) (fun v => (ch (ab v)).Φ)
    (fun v => (ch (ab v)).h1) (fun v => (ch (ab v)).h2) (fun v => (ch (ab v)).h3) (fun v => (ch (ab v)).K₀) (fun v => (ch (ab v)).fd₀)
    (fun v => (ch (ab v)).base) (fun v => (ch (ab v)).θ) (fun v => (ch (ab v)).hθ) (fun v => (ch (ab v)).u) (fun v => (ch (ab v)).hu) n hcoord
  rw [hTw]

  obtain ⟨v₀, hv₀w, hv₀u⟩ := exists_above_fixedField_decomp_eq E F w
  have hsingle := finsum_eq_single (fun v : HeightOneSpectrum (𝓞 ↥Z) =>
      ((((n v : ℚ) / (Nat.card ↥((NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F (ab v))) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) v₀
    (fun v hv => by
      have hn : n v = 0 := if_neg (fun h => hv (hv₀u v h))
      simp only [hn, Int.cast_zero, zero_div]
      rfl)
  rw [hsingle]
  have hn₀ : n v₀ = 1 := if_pos hv₀w
  have hinf : (NumberField.PlaceDecomp.decomp E F w) ⊓ (NumberField.PlaceDecomp.decomp E F (ab v₀)) = (NumberField.PlaceDecomp.decomp E F w) := by
    rw [show ab v₀ = w from hv₀w, inf_idem]
  simp only [hn₀, Int.cast_one, hinf]

end S_M4aHerbrand_exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup
end P2MW
export P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup (solution)
