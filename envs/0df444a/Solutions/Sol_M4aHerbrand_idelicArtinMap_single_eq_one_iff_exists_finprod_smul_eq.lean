-- Prove2me | solution 1 for M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/253f7e5a-225e-5dbd-8493-a4ac7f56ddf6

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
import Theorems.Thm_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
import Theorems.Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet"
p2m_attr_erase "simp" "ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
set_option autoImplicit false
set_option maxSynthPendingDepth 3
p2m_open "NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart idelesTrivialOn principalIdeles idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia"
namespace KernelSol
p2m_open "M4aHerbrand"

theorem finprod_quotient_bot_out_eq {G M : Type*} [Group G] [CommMonoid M] (f : G → M) :
    ∏ᶠ c : G ⧸ (⊥ : Subgroup G), f (Quotient.out c) = ∏ᶠ g : G, f g := by
  symm
  refine finprod_eq_of_bijective (fun g : G => (g : G ⧸ (⊥ : Subgroup G))) ⟨?_, QuotientGroup.mk_surjective⟩ ?_
  · intro a b hab
    have h := QuotientGroup.eq.mp hab
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h
    exact h
  · intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (⊥ : Subgroup G) g
    rw [hh, Subgroup.mem_bot.mp h.2, mul_one]

section norms
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
  (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)

noncomputable def conjProd : (w.adicCompletion F)ˣ →* (w.adicCompletion F)ˣ where
  toFun b := ∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b
  map_one' := by simp only [smul_one, finprod_one]
  map_mul' b₁ b₂ := by
    simp only [smul_mul']
    exact finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)

theorem conjProd_apply (b : (w.adicCompletion F)ˣ) : conjProd E F w b = ∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b := rfl

noncomputable def normSubgroup : Subgroup (v.adicCompletion E)ˣ :=
  (conjProd E F w).range.comap
    (Units.map ((IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))) : (v.adicCompletion E) →* (w.adicCompletion F)))

theorem mem_normSubgroup_iff (a : (v.adicCompletion E)ˣ) :
    a ∈ normSubgroup E F v w hw ↔
      ∃ b : (w.adicCompletion F)ˣ,
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))) (a : (v.adicCompletion E)) := by
  rw [normSubgroup, Subgroup.mem_comap, MonoidHom.mem_range]
  refine exists_congr fun b => ?_
  rw [conjProd_apply, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe]

end norms

end M4aHerbrand.KernelSol

open M4aHerbrand.KernelSol in
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

    (v : HeightOneSpectrum (𝓞 E)) (a : (v.adicCompletion E)ˣ) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) (hxv : finPart v x = a)

    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    r x = 1 ↔
      ∃ b : (w.adicCompletion F)ˣ,
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
            (a : v.adicCompletion E) := by
  classical

  haveI hDcomm : IsMulCommutative ↥(NumberField.PlaceDecomp.decomp E F w) :=
    ⟨⟨fun s t => Subtype.ext (IsMulCommutative.is_comm.comm (s : F ≃ₐ[E] F) (t : F ≃ₐ[E] F))⟩⟩
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _

  have back : ∀ (a' : (v.adicCompletion E)ˣ) (x' : (AdeleRing (𝓞 E) E)ˣ)
      (hx' : x' ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) (hxv' : finPart v x' = a'),
      a' ∈ normSubgroup E F v w hw → r x' = 1 := by
    intro a' x' hx' hxv' ha'
    obtain ⟨b, hb⟩ := (mem_normSubgroup_iff E F v w hw a').mp ha'
    have key := M4aHerbrand.idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      v a' x' hx' hxv' w hw ⊥ b (fun h hh => by rw [Subgroup.mem_bot.mp hh, one_smul]) (by
        rw [← hb, finprod_quotient_bot_out_eq (fun σ : ↥(NumberField.PlaceDecomp.decomp E F w) => σ • b)])
    rwa [Subgroup.map_bot, Subgroup.mem_bot] at key
  constructor
  ·
    intro hrx
    obtain ⟨n, c, hn, hcov⟩ :=
      NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp E F v w hw
    have hθ0 := (M4aHerbrand.map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia E F 𝔣 hadm r
      hr₁ hr₂ hr₃ hr₄ v w hw).1
    set J : Subgroup (AdeleRing (𝓞 E) E)ˣ := idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) with hJ
    set N : Subgroup (v.adicCompletion E)ˣ := normSubgroup E F v w hw with hNdef
    let f : ↥J →* (v.adicCompletion E)ˣ := (finPart v).comp J.subtype
    let NJ : Subgroup ↥J := N.comap f
    let KJ : Subgroup ↥J := (r.comp J.subtype).ker

    have hNK : NJ ≤ KJ := by
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
      exact back (f y) (y : (AdeleRing (𝓞 E) E)ˣ) y.2 rfl (Subgroup.mem_comap.mp hy)

    have hKJ : KJ.index = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
      rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange (r.comp J.subtype)).toEquiv]
      have hrange : (r.comp J.subtype).range = NumberField.PlaceDecomp.decomp E F w := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, hθ0]
      rw [hrange]

    have hsurj : Function.Surjective (fun i : Fin n => (QuotientGroup.mk (c i) : (v.adicCompletion E)ˣ ⧸ N)) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H a' =>
        obtain ⟨i, b, hb⟩ := hcov a'
        refine ⟨i, ?_⟩
        rw [QuotientGroup.eq]
        have hmem : a' * (c i)⁻¹ ∈ N := (mem_normSubgroup_iff E F v w hw _).mpr ⟨b, hb⟩
        rwa [mul_comm] at hmem
    haveI hfinQ : Finite ((v.adicCompletion E)ˣ ⧸ N) := Finite.of_surjective _ hsurj
    have hcardQ : Nat.card ((v.adicCompletion E)ˣ ⧸ N) ≤ n := by
      simpa [Nat.card_eq_fintype_card, Fintype.card_fin] using Nat.card_le_card_of_surjective _ hsurj
    have hinj : Function.Injective (QuotientGroup.map NJ N f le_rfl) := by
      intro q₁ q₂
      induction q₁ using QuotientGroup.induction_on with
      | H y₁ =>
        induction q₂ using QuotientGroup.induction_on with
        | H y₂ =>
          intro hq
          rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.eq] at hq
          rw [QuotientGroup.eq]
          show y₁⁻¹ * y₂ ∈ N.comap f
          rw [Subgroup.mem_comap, map_mul, map_inv]
          exact hq
    haveI : Finite (↥J ⧸ NJ) := Finite.of_injective _ hinj
    have hNJidx : NJ.index ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
      rw [Subgroup.index_eq_card]
      exact ((Nat.card_le_card_of_injective _ hinj).trans hcardQ).trans hn

    have hmul : NJ.relIndex KJ * KJ.index = NJ.index := Subgroup.relIndex_mul_index hNK
    have hD0 : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := Nat.card_pos
    have hNJ0 : NJ.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hrel0 : NJ.relIndex KJ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      exact hNJ0 hmul.symm
    have hrel : NJ.relIndex KJ = 1 := by
      have hle : NJ.relIndex KJ * Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ≤ 1 * Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
        rw [← hKJ, hmul, one_mul, hKJ]
        exact hNJidx
      have := Nat.le_of_mul_le_mul_right hle hD0
      omega
    have hKN : KJ ≤ NJ := Subgroup.relIndex_eq_one.mp hrel

    have hxK : (⟨x, hx⟩ : ↥J) ∈ KJ := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
      exact hrx
    have hxN : f ⟨x, hx⟩ ∈ N := Subgroup.mem_comap.mp (hKN hxK)
    have hfa : f ⟨x, hx⟩ = a := by
      rw [← hxv]
      rfl
    rw [hfa] at hxN
    exact (mem_normSubgroup_iff E F v w hw a).mp hxN
  ·
    rintro ⟨b, hb⟩
    exact back a x hx hxv ((mem_normSubgroup_iff E F v w hw a).mpr ⟨b, hb⟩)

end S_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
end P2MW
export P2MW.S_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq (solution)
