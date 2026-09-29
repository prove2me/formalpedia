-- Prove2me | solution 1 for M4aHerbrand.map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/801996ad-edd0-5e40-a153-ec9d65fc0d0f

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ArithFrobResidue
import Theorems.Thm_M4aHerbrand_inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing"
p2m_attr_erase "instance" "NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
set_option autoImplicit false
set_option maxSynthPendingDepth 3

set_option synthInstance.maxHeartbeats 1600000
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

namespace Ws45
namespace XTheta0
open scoped Pointwise

section single
open scoped Classical

variable (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))

noncomputable def singleFin (a : (v.adicCompletion E)ˣ) : FiniteAdeleRing (𝓞 E) E :=
  RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletionIntegers E) v (a : v.adicCompletion E)

theorem singleFin_mul (a b : (v.adicCompletion E)ˣ) : singleFin E v (a * b) = singleFin E v a * singleFin E v b := by
  simp only [singleFin, Units.val_mul, RestrictedProduct.mulSingle_mul]
  rfl

theorem singleFin_one : singleFin E v 1 = 1 := by
  simp only [singleFin, Units.val_one, RestrictedProduct.mulSingle_one]
  rfl

noncomputable def singleIdele : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ where
  toFun a := ⟨((1 : InfiniteAdeleRing E), singleFin E v a), ((1 : InfiniteAdeleRing E), singleFin E v a⁻¹),
    Prod.ext (mul_one 1) (show singleFin E v a * singleFin E v a⁻¹ = 1 by rw [← singleFin_mul, mul_inv_cancel, singleFin_one]),
    Prod.ext (mul_one 1) (show singleFin E v a⁻¹ * singleFin E v a = 1 by rw [← singleFin_mul, inv_mul_cancel, singleFin_one])⟩
  map_one' := Units.ext (Prod.ext rfl (show singleFin E v 1 = 1 from singleFin_one E v))
  map_mul' a b := Units.ext (Prod.ext (show (1 : InfiniteAdeleRing E) = 1 * 1 from (mul_one 1).symm)
    (show singleFin E v (a * b) = singleFin E v a * singleFin E v b from singleFin_mul E v a b))

variable {E v}

theorem coe_singleIdele (a : (v.adicCompletion E)ˣ) :
    ((singleIdele E v a : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) = ((1 : InfiniteAdeleRing E), singleFin E v a) := rfl

theorem infPart_singleIdele (a : (v.adicCompletion E)ˣ) : infPart (singleIdele E v a) = 1 :=
  Units.ext rfl

theorem finPart_singleIdele_self (a : (v.adicCompletion E)ˣ) : finPart v (singleIdele E v a) = a := by
  apply Units.ext
  rw [coe_finPart_apply, coe_singleIdele]
  show (singleFin E v a) v = (a : v.adicCompletion E)
  exact RestrictedProduct.mulSingle_eq_same _ _ _

theorem finPart_singleIdele_of_ne (a : (v.adicCompletion E)ˣ) {w : HeightOneSpectrum (𝓞 E)} (hw : w ≠ v) :
    finPart w (singleIdele E v a) = 1 := by
  apply Units.ext
  rw [coe_finPart_apply, coe_singleIdele, Units.val_one]
  show (singleFin E v a) w = 1
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ hw

theorem singleIdele_mem_idelesTrivialOn (a : (v.adicCompletion E)ˣ) :
    singleIdele E v a ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) :=
  (mem_idelesTrivialOn_iff _ _).2 ⟨infPart_singleIdele a, fun _ hw => finPart_singleIdele_of_ne a (Set.mem_compl_singleton_iff.1 hw)⟩

theorem idele_ext {x y : (AdeleRing (𝓞 E) E)ˣ} (hinf : infPart x = infPart y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 E), finPart w x = finPart w y) : x = y := by
  apply Units.ext
  apply Prod.ext
  · exact congrArg Units.val hinf
  · apply RestrictedProduct.ext
    intro w
    exact congrArg Units.val (hfin w)

theorem eq_singleIdele_of_pins {x : (AdeleRing (𝓞 E) E)ˣ} {a : (v.adicCompletion E)ˣ}
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) (hxv : finPart v x = a) :
    x = singleIdele E v a := by
  rw [mem_idelesTrivialOn_iff] at hx
  refine idele_ext (hx.1.trans (infPart_singleIdele a).symm) fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [hxv, finPart_singleIdele_self]
  · rw [hx.2 w (Set.mem_compl_singleton_iff.2 hw), finPart_singleIdele_of_ne a hw]

end single

section decomp
variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

theorem smul_valuationSubring_le (σ : F ≃ₐ[E] F) (hσ : σ • w.asIdeal = w.asIdeal) :
    σ • (w.valuation F).valuationSubring ≤ (w.valuation F).valuationSubring := by
  intro x hx
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hx ⊢
  obtain ⟨a, s, hs, h⟩ := hx
  have hs' : σ • s ∈ w.asIdeal.primeCompl := by
    intro (hmem : σ • s ∈ w.asIdeal)
    rw [← hσ, Ideal.smul_mem_pointwise_smul_iff] at hmem
    exact hs hmem
  refine ⟨σ • a, σ • s, hs', ?_⟩
  have hx' : x = σ • (σ⁻¹ • x) := (smul_inv_smul σ x).symm
  rw [hx', h, smul_mul', smul_inv'']
  rfl

theorem mem_decomp_of_smul_asIdeal_eq (σ : F ≃ₐ[E] F) (hσ : σ • w.asIdeal = w.asIdeal) :
    σ ∈ NumberField.PlaceDecomp.decomp E F w := by
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm (smul_valuationSubring_le E F w σ hσ)
  rw [ValuationSubring.subset_pointwise_smul_iff]
  apply smul_valuationSubring_le E F w σ⁻¹
  rw [← hσ, inv_smul_smul]
  exact hσ.symm

theorem stabilizer_le_decomp' :
    MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal ≤ NumberField.PlaceDecomp.decomp E F w :=
  fun σ hσ => mem_decomp_of_smul_asIdeal_eq E F w σ hσ

theorem inertia_le_decomp' :
    w.asIdeal.inertia (F ≃ₐ[E] F) ≤ NumberField.PlaceDecomp.decomp E F w :=
  (Ideal.inertia_le_stabilizer w.asIdeal).trans (stabilizer_le_decomp' E F w)

end decomp

theorem idelicArtinMap_mem_decomp
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
    r x ∈ NumberField.PlaceDecomp.decomp E F w := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (F ≃ₐ[E] F) w.asIdeal
  have h1 := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v a x hx hxv w hw φ hφ
  have h2 : r x * (φ ^ placeOrd E (projFin E x) v)⁻¹ ∈ NumberField.PlaceDecomp.decomp E F w := inertia_le_decomp' E F w h1
  have h3 : φ ∈ NumberField.PlaceDecomp.decomp E F w := stabilizer_le_decomp' E F w hφ.mem_stabilizer
  have h4 : φ ^ placeOrd E (projFin E x) v ∈ NumberField.PlaceDecomp.decomp E F w := Subgroup.zpow_mem _ h3 _
  simpa using Subgroup.mul_mem _ h2 h4

section abelian
open scoped Pointwise

theorem smul_asIdeal_eq_of_mem_decomp
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))
    (σ : F ≃ₐ[E] F) (hσ : σ ∈ NumberField.PlaceDecomp.decomp E F w) :
    σ • w.asIdeal = w.asIdeal := by
  have key : ∀ τ : F ≃ₐ[E] F, τ ∈ NumberField.PlaceDecomp.decomp E F w →
      ∀ x : 𝓞 F, x ∈ w.asIdeal → τ • x ∈ w.asIdeal := by
    intro τ hτ x hx
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)] at hx ⊢
    have hcoe : algebraMap (𝓞 F) F (τ • x) = τ (algebraMap (𝓞 F) F x) := rfl
    show w.valuation F (algebraMap (𝓞 F) F (τ • x)) < 1
    rw [hcoe, NumberField.PlaceDecomp.valuation_apply_of_mem τ hτ]
    exact hx
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro h
    have := key σ hσ _ h
    rwa [smul_inv_smul] at this
  · intro h
    exact key σ⁻¹ (inv_mem hσ) x h

theorem decomp_le_stabilizer
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F)) :
    NumberField.PlaceDecomp.decomp E F w ≤ MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal :=
  fun σ hσ => smul_asIdeal_eq_of_mem_decomp E F w σ hσ

theorem exists_mul_pow_inv_mem_inertia
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) (φ : F ≃ₐ[E] F) (hφ : IsArithFrobAt (𝓞 E) φ w.asIdeal)
    (σ : F ≃ₐ[E] F) (hσ : σ ∈ MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal) :
    ∃ n : ℕ, σ * (φ ^ n)⁻¹ ∈ w.asIdeal.inertia (F ≃ₐ[E] F) := by
  classical
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Finite (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := .of_injective _ Ideal.algebraMap_quotient_injective
  letI : Fintype (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := Fintype.ofFinite _
  let Fr : MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal := ⟨φ, hφ.mem_stabilizer⟩
  let Sg : MulAction.stabilizer (F ≃ₐ[E] F) w.asIdeal := ⟨σ, hσ⟩
  obtain ⟨n, hn⟩ := ArithFrobResidue.exists_pow_stabilizerHom_eq (A := 𝓞 E) (G := F ≃ₐ[E] F) (P := w.asIdeal) Fr hφ
    (Ideal.Quotient.stabilizerHom w.asIdeal (w.asIdeal.under (𝓞 E)) (F ≃ₐ[E] F) Sg)
  refine ⟨n, ?_⟩
  have hker : Sg * (Fr ^ n)⁻¹ ∈ (Ideal.Quotient.stabilizerHom w.asIdeal (w.asIdeal.under (𝓞 E)) (F ≃ₐ[E] F)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hn, mul_inv_cancel]
  rw [Ideal.Quotient.ker_stabilizerHom] at hker
  first | exact hker | exact AddSubgroup.coe_mem_inertia.mpr hker

theorem placeOrd_eq_zero_of_mem_unitIdelesTrivialOn
    (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) :
    placeOrd E (projFin E x) v = 0 := by
  rw [placeOrd_eq_zero_iff]
  rw [mem_unitIdelesTrivialOn_iff] at hx
  obtain ⟨h1, h2⟩ := hx.1 v (fun h => h rfl)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  have hmul : ((x : AdeleRing (𝓞 E) E).2 v) * (((x⁻¹ : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 v) = 1 := by
    have h := congrArg (fun y : AdeleRing (𝓞 E) E => y.2 v) x.mul_inv
    exact h
  have hv := congrArg Valued.v hmul
  rw [map_mul, map_one] at hv
  show Valued.v ((x : AdeleRing (𝓞 E) E).2 v) = 1
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((x : AdeleRing (𝓞 E) E).2 v) *
          Valued.v ((((x⁻¹ : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 v)) := hv.symm
      _ ≤ Valued.v ((x : AdeleRing (𝓞 E) E).2 v) * 1 := by gcongr
      _ = _ := mul_one _)

theorem exists_placeOrd_singleIdele_eq_one
    (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    ∃ a : (v.adicCompletion E)ˣ, placeOrd E (projFin E (singleIdele E v a)) v = 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer E
  have hπv : Valued.v (π : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : (π : v.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact WithZero.coe_ne_zero hπv.symm
  refine ⟨Units.mk0 _ hπ0, ?_⟩
  unfold placeOrd
  have : ((projFin E (singleIdele E v (Units.mk0 _ hπ0)) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) v
      = ((Units.mk0 _ hπ0 : (v.adicCompletion E)ˣ) : v.adicCompletion E) :=
    congrArg Units.val (finPart_singleIdele_self (E := E) (v := v) (Units.mk0 _ hπ0))
  rw [this, Units.val_mk0, hπv, WithZero.log_exp, neg_neg]

end abelian

end Ws45.XTheta0

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
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    (idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r = NumberField.PlaceDecomp.decomp E F w ∧
    (unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r = w.asIdeal.inertia (F ≃ₐ[E] F) := by
  classical
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : w.asIdeal.IsMaximal := w.isMaximal

  set T := idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) with hT
  set U := unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) with hU
  have hUT : U ≤ T := unitIdelesTrivialOn_le_idelesTrivialOn (𝓞 E) E _

  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (F ≃ₐ[E] F) w.asIdeal

  have hI_le : w.asIdeal.inertia (F ≃ₐ[E] F) ≤ U.map r :=
    M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw
  have hU_le : U.map r ≤ w.asIdeal.inertia (F ≃ₐ[E] F) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      v (finPart v x) x (hUT hx) rfl w hw φ hφ
    rw [Ws45.XTheta0.placeOrd_eq_zero_of_mem_unitIdelesTrivialOn E v x hx, zpow_zero, inv_one, mul_one] at h1
    exact h1
  have hUeq : U.map r = w.asIdeal.inertia (F ≃ₐ[E] F) := le_antisymm hU_le hI_le
  refine ⟨?_, hUeq⟩

  have hT_le : T.map r ≤ NumberField.PlaceDecomp.decomp E F w := by
    rintro _ ⟨x, hx, rfl⟩
    exact Ws45.XTheta0.idelicArtinMap_mem_decomp E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v (finPart v x) x hx rfl w hw
  refine le_antisymm hT_le ?_

  have hI_T : w.asIdeal.inertia (F ≃ₐ[E] F) ≤ T.map r := hI_le.trans (Subgroup.map_mono hUT)
  have hφT : φ ∈ T.map r := by
    obtain ⟨a, ha⟩ := Ws45.XTheta0.exists_placeOrd_singleIdele_eq_one E v
    have hxT : Ws45.XTheta0.singleIdele E v a ∈ T := Ws45.XTheta0.singleIdele_mem_idelesTrivialOn a
    have h1 := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      v a (Ws45.XTheta0.singleIdele E v a) hxT (Ws45.XTheta0.finPart_singleIdele_self a) w hw φ hφ
    rw [ha, zpow_one] at h1
    have h2 : r (Ws45.XTheta0.singleIdele E v a) ∈ T.map r := ⟨_, hxT, rfl⟩
    have h3 : (r (Ws45.XTheta0.singleIdele E v a) * φ⁻¹)⁻¹ * r (Ws45.XTheta0.singleIdele E v a) ∈ T.map r :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hI_T h1)) h2
    simpa using h3
  intro σ hσ
  obtain ⟨n, hn⟩ := Ws45.XTheta0.exists_mul_pow_inv_mem_inertia E F w φ hφ σ
    (Ws45.XTheta0.decomp_le_stabilizer E F w hσ)
  have h4 : σ * (φ ^ n)⁻¹ * φ ^ n ∈ T.map r := Subgroup.mul_mem _ (hI_T hn) (Subgroup.pow_mem _ hφT n)
  simpa using h4

end S_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
end P2MW
export P2MW.S_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia (solution)
