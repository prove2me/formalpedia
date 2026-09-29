-- Prove2me | solution 1 for LanglandsTunnell.P2.Artin.exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a45310d9-14e5-5eeb-b5ad-4ab22623cc77

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_M4aHerbrand_inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing"
p2m_attr_erase "instance" "NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (hℓ : (Module.finrank E F).Prime) (v : HeightOneSpectrum (𝓞 E))
    (hv : (LanglandsTunnell.P2.Artin.primeAbove E F v).inertia (F ≃ₐ[E] F) ≠ ⊥) :
    ∃ t : (v.adicCompletion E)ˣ, (t : v.adicCompletion E) ∈ v.adicCompletionIntegers E ∧
      ((t⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ∈ v.adicCompletionIntegers E ∧
      Units.map (NumberField.AdelicLevel.finIncl (𝓞 E) E)
          (NumberField.AdelicLevel.localUnit (𝓞 E) E v t) ∉
        M4aHerbrand.principalIdeles (𝓞 E) E ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange E F).idelicNorm.range := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance

  haveI : Fact (Module.finrank E F).Prime := ⟨hℓ⟩
  have hcard : Nat.card (F ≃ₐ[E] F) = Module.finrank E F := IsGalois.card_aut_eq_finrank E F
  haveI : IsCyclic (F ≃ₐ[E] F) := isCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
  haveI : IsMulCommutative (F ≃ₐ[E] F) := ⟨⟨fun a b => by
    obtain ⟨i, rfl⟩ := hg a
    obtain ⟨j, rfl⟩ := hg b
    exact (Commute.zpow_zpow (Commute.refl g) i j).eq⟩⟩

  obtain ⟨𝔯, h𝔯, hram𝔯⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd E F
  obtain ⟨𝔣, -, -, hadm⟩ :=
    LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E F 𝔯 h𝔯 hram𝔯 (Module.finrank E F)
  obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank E F 𝔣 hadm

  let w : HeightOneSpectrum (𝓞 F) :=
    ⟨primeAbove E F v, (primeAbove_isMaximal E F v).isPrime, ne_bot_of_under_eq E F v (under_primeAbove E F v)⟩
  have hw : w.under (𝓞 E) = v := HeightOneSpectrum.ext (under_primeAbove E F v)

  obtain ⟨σ, hσI, hσ1⟩ : ∃ σ ∈ w.asIdeal.inertia (F ≃ₐ[E] F), σ ≠ 1 := by
    by_contra h
    push_neg at h
    exact hv ((Subgroup.eq_bot_iff_forall _).mpr h)
  obtain ⟨u, hu, hru⟩ :=
    M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw hσI

  obtain ⟨hunit, hinf, hfin⟩ := (mem_unitIdelesTrivialOn_iff _ u).mp hu
  set t : (v.adicCompletion E)ˣ := finPart v u with ht
  have hueq : Units.map (NumberField.AdelicLevel.finIncl (𝓞 E) E) (NumberField.AdelicLevel.localUnit (𝓞 E) E v t) = u := by
    apply Units.ext
    refine Prod.ext ?_ ?_
    ·
      show (1 : InfiniteAdeleRing E) = (u : AdeleRing (𝓞 E) E).1
      exact (congrArg Units.val hinf).symm
    · show ((NumberField.AdelicLevel.localUnit (𝓞 E) E v t : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) = (u : AdeleRing (𝓞 E) E).2
      refine RestrictedProduct.ext _ _ fun w' => ?_
      rcases eq_or_ne w' v with rfl | hne
      · exact NumberField.AdelicLevel.localUnit_apply_self (𝓞 E) E w' t
      · exact (NumberField.AdelicLevel.localUnit_apply_of_ne (𝓞 E) E v t hne).trans
          (congrArg Units.val (hfin w' hne)).symm
  refine ⟨t, (hunit v (by simp)).1, ?_, ?_⟩
  · have h2 := (hunit v (by simp)).2
    rwa [← coe_finPart_apply, map_inv] at h2
  · rw [hueq]
    intro hmem
    apply hσ1
    rw [← hru, ← MonoidHom.mem_ker, hr₂]
    exact hmem

end S_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
end P2MW
export P2MW.S_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot (solution)
