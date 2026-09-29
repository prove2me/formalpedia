-- Prove2me | solution 1 for M4aHerbrand.exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bd5453ec-2aa9-5d9e-a2c5-2bbf3f8d6cda

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_stabilizesUnitIdeles_placesOverPrimes
import Theorems.Thm_M4aHerbrand_GenuineDescent_map_beta_unitIdelesTrivialOn_placesOverPrimes_le
import Theorems.Thm_M4aHerbrand_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_M4aHerbrand_GenuineDescent_unitsMap_beta_mem_principalIdeles_iff
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup"
p2m_attr_erase "instance" "groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr"
p2m_attr_erase "simp" "ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent

theorem solution
    (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset Nat.Primes) (hpS : (⟨p, Fact.out⟩ : Nat.Primes) ∈ S) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra E F) (_ : FiniteDimensional E F) (_ : IsGalois E F)
      (D : IdeleGaloisDescent (𝓞 F) E F) (hD : D.StabilizesUnitIdeles (NumberField.placesOverPrimes F (↑S : Set Nat.Primes))),
      (∀ w : HeightOneSpectrum (𝓞 F), w ∉ NumberField.placesOverPrimes F (↑S : Set Nat.Primes) →
        Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1) ∧
      ∀ c : SIdeleClassGroup (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes)),
        ∃ d : SIdeleClassGroup (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes)),
          (∀ g : F ≃ₐ[E] F, D.sClassAct hD g d = d) ∧
          (∏ᶠ g : F ≃ₐ[E] F, D.sClassAct hD g c) = d ^ p := by
  classical
  obtain ⟨F, _instF, _instNF, _instAlg, _instGal, hcomm, hexp, hunr, hnorm⟩ :=
    M4aHerbrand.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot E p ζ hζ S hpS
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  obtain ⟨D⟩ := M4aHerbrand.nonempty_ideleGaloisDescent E F
  have hD : D.StabilizesUnitIdeles (NumberField.placesOverPrimes F (↑S : Set Nat.Primes)) :=
    M4aHerbrand.IdeleGaloisDescent.stabilizesUnitIdeles_placesOverPrimes E F D (↑S : Set Nat.Primes)
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD, hunr, ?_⟩
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨-, hfixed, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm E F D

  have hNx : (genuineBaseChange E F).idelicNorm x ∈
      principalIdeles (𝓞 E) E ⊔ ((genuineBaseChange E F).idelicNorm).range :=
    Subgroup.mem_sup_right ⟨x, rfl⟩
  rw [hnorm] at hNx
  obtain ⟨ay, hay, u, hu, hNx_eq⟩ := Subgroup.mem_sup.mp hNx
  obtain ⟨a, ha, y', hy', rfl⟩ := Subgroup.mem_sup.mp hay
  obtain ⟨y, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk (Units.map ((genuineBaseChange E F).β : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 F) F).toMonoidHom y), ?_, ?_⟩
  · intro g
    rw [IdeleGaloisDescent.sClassAct_mk]
    exact congrArg _ ((hfixed _).mpr ⟨y, rfl⟩ g)
  · have h1 : (∏ᶠ g : F ≃ₐ[E] F, D.sClassAct hD g
          (QuotientGroup.mk x : SIdeleClassGroup (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes))))
        = QuotientGroup.mk (∏ g : F ≃ₐ[E] F, D.unitsAct g x) := by
      rw [finprod_eq_prod_of_fintype]
      simp only [IdeleGaloisDescent.sClassAct_mk]
      exact (QuotientGroup.mk_prod (sClassKernel (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes))) _).symm
    rw [h1, hprod x, ← hNx_eq]
    set β : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
      Units.map ((genuineBaseChange E F).β : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 F) F).toMonoidHom with hβdef
    have hβa : β a ∈ principalIdeles (𝓞 F) F :=
      (M4aHerbrand.GenuineDescent.unitsMap_beta_mem_principalIdeles_iff E F a).mpr ha
    have hβu : β u ∈ unitIdelesTrivialOn (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes)) :=
      M4aHerbrand.GenuineDescent.map_beta_unitIdelesTrivialOn_placesOverPrimes_le E F (↑S : Set Nat.Primes) ⟨u, hu, rfl⟩
    have key : (β (a * (powMonoidHom p) y * u))⁻¹ * (β y) ^ p
        ∈ sClassKernel (𝓞 F) F (NumberField.placesOverPrimes F (↑S : Set Nat.Primes)) := by
      rw [map_mul, map_mul, powMonoidHom_apply, map_pow, mul_comm (β a) (β y ^ p), mul_assoc, mul_inv_rev,
        inv_mul_cancel_right]
      exact inv_mem (mul_mem (principalIdeles_le_sClassKernel (𝓞 F) F _ hβa)
        (unitIdelesTrivialOn_le_sClassKernel (𝓞 F) F _ hβu))
    rw [QuotientGroup.eq.mpr key, QuotientGroup.mk_pow]

end S_M4aHerbrand_exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot
end P2MW
export P2MW.S_M4aHerbrand_exists_isGalois_forall_prod_sClassAct_eq_pow_of_isPrimitiveRoot (solution)
