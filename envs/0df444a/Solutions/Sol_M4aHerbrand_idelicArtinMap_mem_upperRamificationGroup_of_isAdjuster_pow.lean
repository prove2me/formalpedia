-- Prove2me | solution 1 for M4aHerbrand.idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c4e650fa-4547-5e4e-9bf3-c7bb75bb4213

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Theorems.Thm_NumberField_PlaceDecomp_exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LocalReciprocity_IsLocalReciprocityMap
import Theorems.Thm_M4aHerbrand_isLocalReciprocityMap_of_idelicArtinMap_single
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
p2m_attr_erase "instance" "FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite"
p2m_attr_erase "instance" "LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne"
p2m_attr_erase "simp" "NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
set_option autoImplicit false
p2m_open "NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart idelesTrivialOn principalIdeles isLocalReciprocityMap_of_idelicArtinMap_single idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
namespace XC
p2m_open "M4aHerbrand"
universe u
variable (E : Type u) [Field E] [NumberField E]

theorem coe_finPart (v : HeightOneSpectrum (𝓞 E)) (x : (AdeleRing (𝓞 E) E)ˣ) :
    ((finPart v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = (((x : AdeleRing (𝓞 E) E)).2 : FiniteAdeleRing (𝓞 E) E) v := rfl

theorem valued_finPart_of_isAdjuster_pow (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (x : (AdeleRing (𝓞 E) E)ˣ) (hxn : IsAdjuster E (v.asIdeal ^ n) x 1) :
    Valued.v ((finPart v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 ∧
      Valued.v (((finPart v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have hdvd : v.asIdeal ∣ v.asIdeal ^ n := dvd_pow_self _ (by omega)
  have hcnt : (Associates.mk v.asIdeal).count (Associates.mk (v.asIdeal ^ n)).factors = n := by
    rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 v.ne_bot) (Associates.irreducible_mk.2 v.irreducible),
      Associates.count_self (Associates.irreducible_mk.2 v.irreducible), mul_one]
  obtain ⟨h1, h2⟩ := hxn.cong v hdvd
  simp only [map_one, inv_one, mul_one] at h1 h2
  rw [hcnt] at h2
  exact ⟨h1, h2⟩

theorem ext_of_infPart_of_finPart (x y : (AdeleRing (𝓞 E) E)ˣ) (h1 : infPart x = infPart y)
    (h2 : ∀ w : HeightOneSpectrum (𝓞 E), finPart w x = finPart w y) : x = y := by
  apply Units.ext
  apply Prod.ext
  · exact congrArg Units.val h1
  · apply RestrictedProduct.ext
    intro w
    exact congrArg Units.val (h2 w)

theorem eq_single_finPart (v : HeightOneSpectrum (𝓞 E))
    (ιv : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ)
    (hιv : ∀ z, ιv z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hιv' : ∀ z, finPart v (ιv z) = z)
    (x : (AdeleRing (𝓞 E) E)ˣ) (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) :
    x = ιv (finPart v x) := by
  refine ext_of_infPart_of_finPart E x _ (by rw [hx.1, (hιv _).1]) fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [hιv']
  · rw [hx.2 w hw, (hιv _).2 w hw]

end M4aHerbrand.XC

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart idelesTrivialOn principalIdeles isLocalReciprocityMap_of_idelicArtinMap_single idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
namespace XC
p2m_open "M4aHerbrand"
universe u'
variable (E : Type u') [Field E] [NumberField E]

section single
variable (v : HeightOneSpectrum (𝓞 E))

noncomputable def fadSingle (a : v.adicCompletion E) : FiniteAdeleRing (𝓞 E) E := by
  classical
  exact RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) v a

theorem fadSingle_apply_self (a : v.adicCompletion E) : fadSingle E v a v = a := by
  classical
  exact RestrictedProduct.mulSingle_eq_same _ _ a

theorem fadSingle_apply_of_ne (a : v.adicCompletion E) {w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v) : fadSingle E v a w = 1 := by
  classical
  exact RestrictedProduct.mulSingle_eq_of_ne _ a h

theorem fadSingle_one : fadSingle E v 1 = 1 := by
  classical
  exact RestrictedProduct.mulSingle_one _ _

theorem fadSingle_mul (a b : v.adicCompletion E) : fadSingle E v (a * b) = fadSingle E v a * fadSingle E v b := by
  classical
  exact RestrictedProduct.mulSingle_mul _ _ a b

noncomputable def singleUnits : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ where
  toFun z :=
    { val := ((1 : InfiniteAdeleRing E), fadSingle E v (z : v.adicCompletion E))
      inv := ((1 : InfiniteAdeleRing E), fadSingle E v ((z⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E))
      val_inv := by
        refine Prod.ext (one_mul _) ?_
        change fadSingle E v _ * fadSingle E v _ = 1
        rw [← fadSingle_mul, Units.mul_inv, fadSingle_one]
      inv_val := by
        refine Prod.ext (one_mul _) ?_
        change fadSingle E v _ * fadSingle E v _ = 1
        rw [← fadSingle_mul, Units.inv_mul, fadSingle_one] }
  map_one' := by
    apply Units.ext
    refine Prod.ext rfl ?_
    change fadSingle E v ((1 : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [Units.val_one, fadSingle_one]
  map_mul' z z' := by
    apply Units.ext
    refine Prod.ext (one_mul _).symm ?_
    change fadSingle E v ((z * z' : (v.adicCompletion E)ˣ) : v.adicCompletion E) = fadSingle E v _ * fadSingle E v _
    rw [Units.val_mul, fadSingle_mul]

theorem singleUnits_fst (z : (v.adicCompletion E)ˣ) : ((singleUnits E v z : AdeleRing (𝓞 E) E)).1 = 1 := rfl

theorem singleUnits_snd_apply (z : (v.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    (((singleUnits E v z : AdeleRing (𝓞 E) E)).2 : FiniteAdeleRing (𝓞 E) E) w = fadSingle E v (z : v.adicCompletion E) w := rfl

theorem infPart_singleUnits (z : (v.adicCompletion E)ˣ) : infPart (singleUnits E v z) = 1 :=
  Units.ext (singleUnits_fst E v z)

theorem finPart_singleUnits_self (z : (v.adicCompletion E)ˣ) : finPart v (singleUnits E v z) = z :=
  Units.ext (by rw [coe_finPart, singleUnits_snd_apply, fadSingle_apply_self])

theorem finPart_singleUnits_of_ne (z : (v.adicCompletion E)ˣ) {w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v) :
    finPart w (singleUnits E v z) = 1 :=
  Units.ext (by rw [coe_finPart, singleUnits_snd_apply, fadSingle_apply_of_ne E v _ h, Units.val_one])

theorem singleUnits_mem_idelesTrivialOn (z : (v.adicCompletion E)ˣ) :
    singleUnits E v z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) :=
  ⟨infPart_singleUnits E v z, fun w hw => finPart_singleUnits_of_ne E v z (by simpa using hw)⟩

end single

end M4aHerbrand.XC

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart idelesTrivialOn principalIdeles isLocalReciprocityMap_of_idelicArtinMap_single idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt"
namespace XC
p2m_open "M4aHerbrand"
open M4aHerbrand.GenuineDescent LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp Pointwise

theorem idelicArtinMap_mem_decomp_of_mem_idelesTrivialOn
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (x : (AdeleRing (𝓞 E) E)ˣ) (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) :
    r x ∈ NumberField.PlaceDecomp.decomp E F w := by

  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  set φ : F ≃ₐ[E] F := arithFrobAt (𝓞 E) (F ≃ₐ[E] F) w.asIdeal with hφ
  have hφF : IsArithFrobAt (𝓞 E) φ w.asIdeal := IsArithFrobAt.arithFrobAt (𝓞 E) (F ≃ₐ[E] F) w.asIdeal
  have h1 := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
    v (finPart v x) x hx rfl w hw φ hφF

  have hstab : MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal = NumberField.PlaceDecomp.decomp E F w :=
    IsDedekindDomain.HeightOneSpectrum.stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring E F w
  have hI : w.asIdeal.inertia (F ≃ₐ[E] F) ≤ NumberField.PlaceDecomp.decomp E F w :=
    hstab ▸ Ideal.inertia_le_stabilizer _
  have hφD : φ ∈ NumberField.PlaceDecomp.decomp E F w := hstab ▸ hφF.mem_stabilizer
  have h2 : φ ^ placeOrd E (projFin E x) v ∈ NumberField.PlaceDecomp.decomp E F w := Subgroup.zpow_mem _ hφD _
  have := Subgroup.mul_mem _ (hI h1) h2
  rwa [inv_mul_cancel_right] at this

noncomputable def theta
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    (v.adicCompletion E)ˣ →* ↥(NumberField.PlaceDecomp.decomp E F w) :=
  (r.comp (singleUnits E v)).codRestrict _ fun z =>
    idelicArtinMap_mem_decomp_of_mem_idelesTrivialOn E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw _ (singleUnits_mem_idelesTrivialOn E v z)

theorem coe_theta
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) (z : (v.adicCompletion E)ˣ) :
    ((theta E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw z : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) =
      r (singleUnits E v z) := rfl

end M4aHerbrand.XC

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (n : ℕ) (hn : 1 ≤ n)
    (x : (AdeleRing (𝓞 E) E)ˣ) (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxn : IsAdjuster E (v.asIdeal ^ n) x 1) :
    r x ∈ (ValuationSubring.upperRamificationGroup E ((w.valuation F).valuationSubring) (n : ℚ)).map
          (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype := by

  obtain ⟨ha, han⟩ := M4aHerbrand.XC.valued_finPart_of_isAdjuster_pow E v n hn x hxn
  have hxeq : x = M4aHerbrand.XC.singleUnits E v (finPart v x) :=
    M4aHerbrand.XC.eq_single_finPart E v (M4aHerbrand.XC.singleUnits E v)
      (M4aHerbrand.XC.singleUnits_mem_idelesTrivialOn E v) (M4aHerbrand.XC.finPart_singleUnits_self E v) x hx

  have hLR := M4aHerbrand.isLocalReciprocityMap_of_idelicArtinMap_single E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw
    (M4aHerbrand.XC.singleUnits E v) (M4aHerbrand.XC.singleUnits_mem_idelesTrivialOn E v)
    (M4aHerbrand.XC.finPart_singleUnits_self E v)
    (M4aHerbrand.XC.theta E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw) (M4aHerbrand.XC.coe_theta E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw)

  obtain ⟨b, hb, hNb⟩ :=
    NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le
      E F v w hw n (finPart v x) ha han

  have hmem := hLR.mem_of_finprod_quotient_smul_eq
    (ValuationSubring.upperRamificationGroup E ((w.valuation F).valuationSubring) (n : ℚ)) (finPart v x) b hb hNb
  rw [hxeq]
  exact ⟨_, hmem, rfl⟩

end S_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
end P2MW
export P2MW.S_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow (solution)
