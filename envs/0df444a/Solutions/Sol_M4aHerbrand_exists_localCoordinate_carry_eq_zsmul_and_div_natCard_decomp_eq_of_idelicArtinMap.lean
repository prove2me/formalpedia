-- Prove2me | solution 1 for M4aHerbrand.exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/852b93f3-fb19-56e9-a124-218fe8e5a240

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_CyclicCarry
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
import Theorems.Thm_NumberField_exists_isMulCommutative_algHom_cyclotomicField_ramificationIdx_eq_one_and_dvd_natCard_decomp
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion_tower
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_ExtCitation_LocalLevel_map_eq_natCard_smul_of_isLocalFundamentalClass
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Theorems.Thm_NumberField_exists_isGalois_compositum
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_M4aHerbrand_exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 32000000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap.M4aHerbrand M4aHerbrand.GenuineDescent groupCohomology"
open HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp Pointwise

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply principalIdeles IdeleGaloisDescent idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt restrictNormalHom_idelicArtinMap_eq exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer"
namespace ArtInv
p2m_open "M4aHerbrand"

theorem exists_pow_index_generates {G : Type*} [Group G] [Finite G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (D : Subgroup G) :
    ∃ (k : ℕ) (hkD : s ^ k ∈ D), (∀ g : D, g ∈ Subgroup.zpowers (⟨s ^ k, hkD⟩ : D)) ∧ k * Nat.card D = Nat.card G := by
  classical

  have hcomm : ∀ g h : G, g * h = h * g := by
    intro g h
    obtain ⟨i, rfl⟩ := hs g
    obtain ⟨j, rfl⟩ := hs h
    exact (Commute.zpow_zpow (Commute.refl s) i j).eq
  haveI : D.Normal := ⟨fun a ha g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
  haveI : D.FiniteIndex := Subgroup.finiteIndex_of_finite
  refine ⟨D.index, Subgroup.pow_index_mem D s, ?_, ?_⟩
  ·
    have hn : orderOf s = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hs
    have hidx : D.index ∣ orderOf s := by rw [hn]; exact Subgroup.index_dvd_card D
    have hidx0 : D.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hord : orderOf (s ^ D.index) = Nat.card D := by
      rw [orderOf_pow_of_dvd hidx0 hidx, hn]
      have := Subgroup.card_mul_index D
      rw [← this, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hidx0)]
    have hle : Subgroup.zpowers (s ^ D.index) ≤ D := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.pow_index_mem D s
    have heq : Subgroup.zpowers (s ^ D.index) = D := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, hord]
    intro g
    have hg : (g : G) ∈ Subgroup.zpowers (s ^ D.index) := by rw [heq]; exact g.2
    obtain ⟨z, hz⟩ := hg
    refine ⟨z, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_zpow]
    exact hz
  · rw [mul_comm]
    exact Subgroup.card_mul_index D

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

noncomputable def localArtinHom
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
  (r.comp (singleIdele E v)).codRestrict _ fun a =>
    idelicArtinMap_mem_decomp E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v a (singleIdele E v a)
      (singleIdele_mem_idelesTrivialOn a) (finPart_singleIdele_self a) w hw

theorem coe_localArtinHom_apply
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) (a : (v.adicCompletion E)ˣ) :
    ((localArtinHom E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw a : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F)
      = r (singleIdele E v a) := rfl

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

theorem exists_compositum (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [IsGalois E F] [IsMulCommutative (F ≃ₐ[E] F)] [IsGalois E F'] [IsMulCommutative (F' ≃ₐ[E] F')] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra E K) (_ : Algebra F K)
      (_ : Algebra F' K) (_ : IsScalarTower E F K) (_ : IsScalarTower E F' K) (_ : IsGalois E K)
      (_ : IsMulCommutative (K ≃ₐ[E] K)),
      ∀ x : K, x ∈ Algebra.adjoin E (Set.range (algebraMap F K) ∪ Set.range (algebraMap F' K)) := by
  obtain ⟨K, _, _, _, _, _, _, _, hgal, hsep⟩ := NumberField.exists_isGalois_compositum E F F'
  haveI := hgal
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K

  have hρF : ∀ σ : K ≃ₐ[E] K, AlgEquiv.restrictNormalHom F σ = 1 → ∀ y : F, σ (algebraMap F K y) = algebraMap F K y := by
    intro σ h y
    have := AlgEquiv.restrictNormal_commutes σ F y
    rw [← this]
    change algebraMap F K (AlgEquiv.restrictNormalHom F σ y) = _
    rw [h, AlgEquiv.one_apply]
  have hρF' : ∀ σ : K ≃ₐ[E] K, AlgEquiv.restrictNormalHom F' σ = 1 → ∀ y : F', σ (algebraMap F' K y) = algebraMap F' K y := by
    intro σ h y
    have := AlgEquiv.restrictNormal_commutes σ F' y
    rw [← this]
    change algebraMap F' K (AlgEquiv.restrictNormalHom F' σ y) = _
    rw [h, AlgEquiv.one_apply]
  have habel : IsMulCommutative (K ≃ₐ[E] K) := by
    refine ⟨⟨fun σ τ => ?_⟩⟩
    have h1 : σ * τ * σ⁻¹ * τ⁻¹ = 1 := by
      apply hsep
      · apply hρF
        simp only [map_mul, map_inv]
        rw [IsMulCommutative.is_comm.comm (AlgEquiv.restrictNormalHom F σ) (AlgEquiv.restrictNormalHom F τ)]
        group
      · apply hρF'
        simp only [map_mul, map_inv]
        rw [IsMulCommutative.is_comm.comm (AlgEquiv.restrictNormalHom F' σ) (AlgEquiv.restrictNormalHom F' τ)]
        group
    calc σ * τ = σ * τ * σ⁻¹ * τ⁻¹ * τ * σ := by group
      _ = τ * σ := by rw [h1, one_mul]
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hgal, habel, ?_⟩
  intro x
  set S : Set K := Set.range (algebraMap F K) ∪ Set.range (algebraMap F' K) with hS
  have hM : IntermediateField.adjoin E S = ⊤ := by
    have hfix : (IntermediateField.adjoin E S).fixingSubgroup = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      apply hsep
      · intro y
        exact hσ _ (IntermediateField.subset_adjoin E S (Set.mem_union_left _ ⟨y, rfl⟩))
      · intro y
        exact hσ _ (IntermediateField.subset_adjoin E S (Set.mem_union_right _ ⟨y, rfl⟩))
    have := IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E S)
    rw [hfix, IntermediateField.fixedField_bot] at this
    exact this.symm
  have hx : x ∈ (IntermediateField.adjoin E S).toSubalgebra := by
    rw [IntermediateField.mem_toSubalgebra, hM]
    exact IntermediateField.mem_top
  rwa [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun y _ => Algebra.IsAlgebraic.isAlgebraic y)] at hx

end M4aHerbrand.ArtInv

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]

    (s : F ≃ₐ[E] F) (hs : ∀ g : (F ≃ₐ[E] F), g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (j : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hj : ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))

    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (pr : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hpr : ∀ x : (AdeleRing (𝓞 F) F)ˣ, pr.hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (a : Eˣ) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxv : finPart v x = Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a)

    (hc : carryFun (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) ∈
      cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))

    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
    (Φ : w.adicCompletion F ≃+* L')
    (_ : ∀ (g : (↥(NumberField.PlaceDecomp.decomp E F w))) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : (↥(NumberField.PlaceDecomp.decomp E F w))) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : (↥(NumberField.PlaceDecomp.decomp E F w))) (y : w.adicCompletion F), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u') :
    ∃ (nw : ℤ) (i : ℕ),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype pr 2).hom
          ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom
            ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom
              ⟨carryFun (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩)) =
        nw • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom u' ∧
      r x = s ^ i ∧
      ((((nw : ℚ) / (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
        (((i : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by

  rename_i hΦ₁ hΦ₂ hΦ₃ _ hbase hθ hu'
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance

  obtain ⟨k, hkD, hkgen, hkcard⟩ : ∃ (k : ℕ) (hkD : s ^ k ∈ NumberField.PlaceDecomp.decomp E F w),
      (∀ g : ↥(NumberField.PlaceDecomp.decomp E F w), g ∈ Subgroup.zpowers (⟨s ^ k, hkD⟩ : ↥(NumberField.PlaceDecomp.decomp E F w))) ∧
      k * Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) = Nat.card (F ≃ₐ[E] F) := by
    exact M4aHerbrand.ArtInv.exists_pow_index_generates s hs (NumberField.PlaceDecomp.decomp E F w)
  set t : ↥(NumberField.PlaceDecomp.decomp E F w) := ⟨s ^ k, hkD⟩ with ht
  have htfin : IsOfFinOrder t := isOfFinOrder_of_finite t

  obtain ⟨m₀, _, F', _, _, _, _, _, hvm₀, -, hF'⟩ :=
    NumberField.exists_isMulCommutative_algHom_cyclotomicField_ramificationIdx_eq_one_and_dvd_natCard_decomp
      E v (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w))) (Nat.card_pos.ne')
  obtain ⟨K, _, _, _, _, _, _, _, _, _, hKgen⟩ : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra E K) (_ : Algebra F K)
      (_ : Algebra F' K) (_ : IsScalarTower E F K) (_ : IsScalarTower E F' K) (_ : IsGalois E K)
      (_ : IsMulCommutative (K ≃ₐ[E] K)),
      ∀ x : K, x ∈ Algebra.adjoin E (Set.range (algebraMap F K) ∪ Set.range (algebraMap F' K)) := by
    exact M4aHerbrand.ArtInv.exists_compositum E F F'

  obtain ⟨𝔯, h𝔯, hram⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd E K
  obtain ⟨𝔣K, -, -, hadmK⟩ :=
    LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E K 𝔯 h𝔯 hram (Module.finrank E K)
  obtain ⟨rK, hrK₁, hrK₂, hrK₃, hrK₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank E K 𝔣K hadmK
  have hcompat : ∀ y : (AdeleRing (𝓞 E) E)ˣ, AlgEquiv.restrictNormalHom F (rK y) = r y := fun y =>
    M4aHerbrand.restrictNormalHom_idelicArtinMap_eq E K F 𝔣K hadmK rK hrK₁ hrK₂ hrK₃ hrK₄ 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ y

  let aw : (w.adicCompletion F)ˣ :=
    Units.map (algebraMap F (w.adicCompletion F) : F →* w.adicCompletion F) (Units.map (algebraMap E F : E →* F) a)
  have hcw : carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw) ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) := by

    have hsmulF : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : F),
        σ • algebraMap F (w.adicCompletion F) y = algebraMap F (w.adicCompletion F) ((σ : F ≃ₐ[E] F) y) := fun σ y => by
      rw [NumberField.PlaceDecomp.smul_def]
      exact NumberField.PlaceDecomp.actRingEquiv_coe σ _
    refine groupCohomology.carryFun_mem_cocycles2 (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw) ?_
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
    change Additive.ofMul (t • aw) = Additive.ofMul aw
    congr 1
    apply Units.ext
    rw [NumberField.PlaceDecomp.coe_smul_units]
    show t • (algebraMap F (w.adicCompletion F) (algebraMap E F (a : E))) = algebraMap F (w.adicCompletion F) (algebraMap E F (a : E))
    rw [hsmulF t, AlgEquiv.commutes]

  have coreII : (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype pr 2).hom
          ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom
            ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom
              ⟨carryFun (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩)) =
      (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩ := by

    have hcomp := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) (MonoidHom.id (F ≃ₐ[E] F)) (NumberField.PlaceDecomp.decomp E F w).subtype j pr 2
    have happ := congrArg (fun T => (ModuleCat.Hom.hom T) ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom
      ⟨carryFun (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩)) hcomp
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
    rw [← happ]

    have hφa : ((Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map j ≫ pr).hom
        (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) = Additive.ofMul aw := by
      rw [Rep.hom_comp]
      show pr.hom (j.hom (Additive.ofMul (Units.map (algebraMap E F : E →* F) a))) = Additive.ofMul aw
      rw [hj]
      erw [hpr]
      congr 1

    have haF : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ).ρ s (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) =
        Additive.ofMul (Units.map (algebraMap E F : E →* F) a) := by
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
      change Additive.ofMul (s • Units.map (algebraMap E F : E →* F) a) = _
      congr 1
      apply Units.ext
      rw [hactF]
      exact AlgEquiv.commutes s (a : E)
    have hzb : carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin
        (((Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map j ≫ pr).hom (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)))
        ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) := by
      rw [hφa]; exact hcw

    have key := groupCohomology.map_carry_H2pi_eq_smul_carry ((MonoidHom.id (F ≃ₐ[E] F)).comp (NumberField.PlaceDecomp.decomp E F w).subtype)
      (NumberField.PlaceDecomp.decomp E F w).subtype_injective s hs hfin k t rfl hkgen htfin
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
      ((Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map j ≫ pr)
      (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)) haF hc hzb
    rw [key]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hkcard
      exact (Nat.card_pos (α := F ≃ₐ[E] F)).ne' hkcard.symm
    have hfac : k / Nat.gcd (orderOf s) k = 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hs, ← hkcard, Nat.gcd_mul_right_left, Nat.div_self (Nat.pos_of_ne_zero hk0)]
    rw [hfac, one_smul]
    congr 1
    exact Subtype.ext (congrArg (carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin) hφa)

  have coreI : ∃ m : ℕ, r x = (s ^ k) ^ m ∧
      (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩ = (m : ℤ) • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom u' := by

    haveI : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F) := NumberField.PlaceDecomp.faithfulSMul_decomp E F w
    haveI : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) L' := ⟨fun {g₁ g₂} h =>
      FaithfulSMul.eq_of_smul_eq_smul (α := w.adicCompletion F) fun y => Φ.injective (by rw [hΦ₃ g₁ y, hΦ₃ g₂ y]; exact h _)⟩
    have hsolv : Group.IsSolvable (↥(NumberField.PlaceDecomp.decomp E F w)) :=
      Group.isSolvable_of_comm (fun g₁ g₂ => Subtype.ext (mul_comm (g₁ : F ≃ₐ[E] F) (g₂ : F ≃ₐ[E] F)))
    obtain ⟨-, hcard, hspan⟩ :=
      ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
        q L' (↥(NumberField.PlaceDecomp.decomp E F w)) hΦ₁ hΦ₂ hsolv K₀ hbase u' hu'

    have hres_inj : Function.Injective
        (groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))) 2).hom := by
      let eT : ↥(NumberField.PlaceDecomp.decomp E F w) →* ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))) := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))) ≃* ↥(NumberField.PlaceDecomp.decomp E F w)).symm.toMonoidHom
      have key : groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))) 2 ≫
          groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ)))) 2 = 𝟙 _ := by
        rw [← groupCohomology.map_comp]
        exact groupCohomology.map_id (B := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ)) (n := 2)
      have hleft : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ),
          (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ)))) 2).hom
            ((groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))) 2).hom y) = y := by
        intro y
        have hy := congrArg (fun T => (ModuleCat.Hom.hom T) y) key
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
        exact hy
      exact Function.LeftInverse.injective hleft

    have hθiso : ∃ θ' : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ), θ ≫ θ' = 𝟙 _ ∧ θ' ≫ θ = 𝟙 _ := by
      let ΦM : (w.adicCompletion F)ˣ →* (↥L')ˣ := Units.map Φ.toRingHom.toMonoidHom
      have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (m : (w.adicCompletion F)ˣ), ΦM (g • m) = g • ΦM m := by
        intro g m
        apply Units.ext
        rw [hΦ₂ g (ΦM m)]
        show Φ ((g • m : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = g • Φ (m : (w.adicCompletion F))
        rw [NumberField.PlaceDecomp.coe_smul_units, hΦ₃ g]
      refine ⟨M4aHerbrand.repHomOfMulEquivariant ΦM hΦM, ?_, ?_⟩
      · refine Rep.hom_ext ?_
        ext z
        rw [Rep.hom_comp, Rep.hom_id]
        show (M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom (θ.hom z) = z
        rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
        refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
        apply Units.ext
        show Φ ((Additive.toMul (θ.hom z) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = ((Additive.toMul z : (↥L')ˣ) : ↥L')
        have h : ((Additive.toMul (θ.hom z) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = Φ.symm ((Additive.toMul z : (↥L')ˣ) : ↥L') :=
          hθ (Additive.toMul z)
        rw [h]
        exact Φ.apply_symm_apply _
      · refine Rep.hom_ext ?_
        ext z
        rw [Rep.hom_comp, Rep.hom_id]
        show θ.hom ((M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom z) = z
        rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
        change Additive.ofMul (Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z))))) = Additive.ofMul (Additive.toMul z)
        congr 1
        apply Units.ext
        have h : ((Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z)))) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) =
            Φ.symm ((ΦM (Additive.toMul z) : (↥L')ˣ) : ↥L') := hθ (ΦM (Additive.toMul z))
        refine h.trans ?_
        show Φ.symm (Φ ((Additive.toMul z : (w.adicCompletion F)ˣ) : (w.adicCompletion F))) = ((Additive.toMul z : (w.adicCompletion F)ˣ) : (w.adicCompletion F))
        exact Φ.symm_apply_apply _

    have hcyc : ∃ m₀ : ℤ, (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩ = m₀ • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom u' := by
      obtain ⟨θ', -, h2⟩ := hθiso
      have hback : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ),
          (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ' 2).hom y) = y := by
        intro y
        have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ' θ 2)
        simp only [h2, groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
          LinearMap.id_apply] at hc'
        exact hc'.symm
      set X' := (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ' 2).hom ((H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩) with hX'
      have hmem : (groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))) 2).hom X' ∈ Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))) 2).hom u'} := by
        rw [hspan ⊤]; trivial
      obtain ⟨m₀, hm₀⟩ := Submodule.mem_span_singleton.mp hmem
      refine ⟨m₀, ?_⟩
      have hXu : X' = m₀ • u' := by
        apply hres_inj
        rw [map_zsmul, ← hm₀]
        exact int_smul_eq_zsmul _ m₀ _
      calc (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩
          = (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom X' := (hback _).symm
        _ = m₀ • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom u' := by rw [hXu, map_zsmul]

    have hkill : (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) : ℤ) • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom u' = 0 := by
      haveI : Fintype (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))) := Fintype.ofFinite _
      have hcT := hcard ⊤
      have h1 : (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w))) • u' = 0 := by
        apply hres_inj
        rw [map_nsmul, map_zero]
        have hN : Nat.card ↥(groupCohomology (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ)) 2) = Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) := by
          rw [hcT, ← Nat.card_eq_fintype_card, Subgroup.card_top]
        rw [← hN]
        exact card_nsmul_eq_zero'
      rw [natCast_zsmul, ← map_nsmul, h1, map_zero]
    obtain ⟨m₀, hX⟩ := hcyc

    have hinv : ∃ m : ℕ, r x = (s ^ k) ^ m ∧ (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) : ℤ) ∣ ((m : ℤ) - m₀) := by

      obtain ⟨wK, hwK⟩ : ∃ wK : HeightOneSpectrum (𝓞 K), wK.under (𝓞 F) = w :=
        ⟨NumberField.PlaceAbove.above F K w, HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above F K w)⟩
      subst hwK
      obtain ⟨ρ, hρsurj, hρres, hρker, hρlift, hρsemi⟩ :=
        NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F K wK
      obtain ⟨ρ', hρ'surj, hρ'res, hρ'ker, hρ'lift, hρ'semi⟩ :=
        NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F' K wK
      have hw' : (wK.under (𝓞 F')).under (𝓞 E) = v := by
        apply HeightOneSpectrum.ext
        rw [← hw]
        show (wK.asIdeal.under (𝓞 F')).under (𝓞 E) = (wK.asIdeal.under (𝓞 F)).under (𝓞 E)
        rw [Ideal.under_under, Ideal.under_under]
      obtain ⟨he', hdvd'⟩ := hF' (wK.under (𝓞 F')) hw'
      have hsolvH : Group.IsSolvable (↥(NumberField.PlaceDecomp.decomp E K wK)) :=
        Group.isSolvable_of_comm (fun g₁ g₂ => Subtype.ext (mul_comm (g₁ : K ≃ₐ[E] K) (g₂ : K ≃ₐ[E] K)))

      obtain ⟨q₂, _, LF, L2, hLFL2, _, _, _, _, _, _, _, _, ΦF, Φ2, hΦF3, hΦ23, hΦF1, hΦ21, hΦF2, hΦ22, hΦcomp, hq₂⟩ :=
        NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion_tower E F K wK
      obtain ⟨K₀F, _, hbaseF⟩ : ∃ (K₀F : IntermediateField ℚ_[q₂] (PadicAlgCl q₂)) (_ : FiniteDimensional ℚ_[q₂] K₀F),
          ExtCitation.LocalLevel.IsBase q₂ LF (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) K₀F := by
        exact M4aHerbrand.ArtInv.exists_isBase q₂ LF (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) hΦF1
      obtain ⟨uF, huF⟩ := (ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q₂ LF (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) hΦF1 hΦF2 hsolv K₀F hbaseF).exists
      obtain ⟨-, hqw⟩ :=
        NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F (wK.under (𝓞 F)) q L' Φ
      have hq₂F : ((q₂ : ℕ) : 𝓞 F) ∈ (wK.under (𝓞 F)).asIdeal := by
        show algebraMap (𝓞 F) (𝓞 K) ((q₂ : ℕ) : 𝓞 F) ∈ wK.asIdeal
        rw [map_natCast]
        exact hq₂

      let ΦFM : (↥LF)ˣ →* ((wK.under (𝓞 F)).adicCompletion F)ˣ := Units.map ΦF.symm.toRingHom.toMonoidHom
      have hΦFM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (y : (↥LF)ˣ), ΦFM (g • y) = g • ΦFM y := by
        intro g y
        apply Units.ext
        show ΦF.symm ((g • y : (↥LF)ˣ) : ↥LF) = ((g • ΦFM y : ((wK.under (𝓞 F)).adicCompletion F)ˣ) : (wK.under (𝓞 F)).adicCompletion F)
        rw [hΦF2 g y, NumberField.PlaceDecomp.coe_smul_units]
        apply ΦF.injective
        rw [hΦF3 g, RingEquiv.apply_symm_apply]
        congr 1
        show (y : ↥LF) = ΦF (ΦF.symm (y : ↥LF))
        exact (ΦF.apply_symm_apply _).symm
      let θF := M4aHerbrand.repHomOfMulEquivariant ΦFM hΦFM
      have hθF : ∀ y : (↥LF)ˣ, ((Additive.toMul (θF.hom (Additive.ofMul y)) : ((wK.under (𝓞 F)).adicCompletion F)ˣ) :
          (wK.under (𝓞 F)).adicCompletion F) = ΦF.symm (y : ↥LF) := fun y => rfl
      have hTR : (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θ 2).hom u' =
          (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θF 2).hom uF :=
        NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E F (wK.under (𝓞 F))
          q hqw L' Φ hΦ₁ hΦ₂ hΦ₃ K₀ hbase θ hθ u' hu' q₂ hq₂F LF ΦF hΦF1 hΦF2 hΦF3 K₀F hbaseF θF hθF uF huF

      haveI : IsMulCommutative (↥(NumberField.PlaceDecomp.decomp E K wK)) := ⟨⟨fun g₁ g₂ => Subtype.ext (mul_comm (g₁ : K ≃ₐ[E] K) (g₂ : K ≃ₐ[E] K))⟩⟩
      haveI hkerN : (ρ.ker).Normal := inferInstance
      let eρ : ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))) ≃* ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker := (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj).symm
      have hL : ∀ y : ↥L2, (y : PadicAlgCl q₂) ∈ LF ↔ ∀ n ∈ ρ.ker, n • y = y := by
        intro y
        constructor
        · intro hy n hn

          set x : (HeightOneSpectrum.under (𝓞 F) wK).adicCompletion F := ΦF.symm ⟨(y : PadicAlgCl q₂), hy⟩ with hx
          have hyx : y = Φ2 (HeightOneSpectrum.Extension.adicCompletionSemialgHom F K
              (⟨wK, rfl⟩ : (HeightOneSpectrum.under (𝓞 F) wK).Extension (𝓞 K)) x) := by
            apply Subtype.ext
            rw [hΦcomp x, hx, RingEquiv.apply_symm_apply]
          have hn1 : ρ n = 1 := (MonoidHom.mem_ker).mp hn
          rw [hyx, ← hΦ23, ← hρsemi, hn1, one_smul]
        · intro hfix

          set z : wK.adicCompletion K := Φ2.symm y with hz
          have hzfix : ∀ τ : ↥(NumberField.PlaceDecomp.decomp F K wK), τ • z = z := by
            intro τ
            obtain ⟨σ, hσ, hσ1⟩ := hρlift τ
            have hσz : σ • z = z := by
              apply Φ2.injective
              rw [hΦ23, hz, RingEquiv.apply_symm_apply]
              exact hfix σ ((MonoidHom.mem_ker).mpr hσ1)
            have hact : σ • z = τ • z := by
              rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
              apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
              rw [NumberField.PlaceDecomp.actRingEquiv_apply, NumberField.PlaceDecomp.actRingEquiv_apply, hσ]
              rfl
            rw [← hact]
            exact hσz
          haveI : IsGalois F K := IsGalois.tower_top_of_isGalois E F K
          obtain ⟨x, hx⟩ :=
            (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom F K wK z).mp hzfix
          have hyx : (y : PadicAlgCl q₂) = ((ΦF x : ↥LF) : PadicAlgCl q₂) := by
            rw [← hΦcomp x, hx, hz, RingEquiv.apply_symm_apply]
          rw [hyx]
          exact (ΦF x).2
      have he : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (h : ↥(NumberField.PlaceDecomp.decomp E K wK)), (QuotientGroup.mk h : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) = eρ g →
          ∀ y : ↥LF, ((g • y : ↥LF) : PadicAlgCl q₂) = ((h • (⟨(y : PadicAlgCl q₂), hLFL2 y.2⟩ : ↥L2) : ↥L2) : PadicAlgCl q₂) := by
        intro g h hgh y
        have hg : ρ h = g := by
          have h1 := congrArg eρ.symm hgh
          rw [MulEquiv.symm_apply_apply] at h1
          rw [← h1]
          rfl
        set x : (HeightOneSpectrum.under (𝓞 F) wK).adicCompletion F := ΦF.symm y with hx
        have hyx : y = ΦF x := by rw [hx, RingEquiv.apply_symm_apply]
        have hy2 : (⟨(y : PadicAlgCl q₂), hLFL2 y.2⟩ : ↥L2) =
            Φ2 (HeightOneSpectrum.Extension.adicCompletionSemialgHom F K
              (⟨wK, rfl⟩ : (HeightOneSpectrum.under (𝓞 F) wK).Extension (𝓞 K)) x) := by
          apply Subtype.ext
          show (y : PadicAlgCl q₂) = _
          rw [hΦcomp x, hyx]
        rw [hy2, ← hΦ23, ← hρsemi, hg, hyx, ← hΦF3, hΦcomp]
      have hbase2 : ExtCitation.LocalLevel.IsBase q₂ L2 (↥(NumberField.PlaceDecomp.decomp E K wK)) K₀F := by
        refine ⟨hbaseF.le.trans hLFL2, fun y => ⟨fun hy h => ?_, fun hfix => ?_⟩⟩
        ·
          have hyF : (y : PadicAlgCl q₂) ∈ LF := hbaseF.le hy
          set yF : ↥LF := ⟨(y : PadicAlgCl q₂), hyF⟩ with hyFdef
          have hfixF : ∀ g : ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))), g • yF = yF := (hbaseF.mem_iff yF).mp hy
          have hy2 : (⟨(yF : PadicAlgCl q₂), hLFL2 yF.2⟩ : ↥L2) = y := Subtype.ext rfl
          apply Subtype.ext
          have key := he (eρ.symm (QuotientGroup.mk h)) h (by rw [MulEquiv.apply_symm_apply]) yF
          rw [hfixF, hy2] at key
          exact key.symm
        ·
          have hyF : (y : PadicAlgCl q₂) ∈ LF := (hL y).mpr (fun n _ => hfix n)
          set yF : ↥LF := ⟨(y : PadicAlgCl q₂), hyF⟩ with hyFdef
          have hy2 : (⟨(yF : PadicAlgCl q₂), hLFL2 yF.2⟩ : ↥L2) = y := Subtype.ext rfl
          show ((yF : ↥LF) : PadicAlgCl q₂) ∈ K₀F
          refine (hbaseF.mem_iff yF).mpr fun g => ?_
          obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (eρ g)
          apply Subtype.ext
          have key := he g h hh yF
          rw [hy2, hfix h] at key
          exact key
      obtain ⟨u2, hu2⟩ := (ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q₂ L2 (↥(NumberField.PlaceDecomp.decomp E K wK)) hΦ21 hΦ22 hsolvH K₀F hbase2).exists

      obtain ⟨ιF, hιF⟩ : ∃ ιF : Rep.res (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ,
          ∀ y : (↥LF)ˣ, (((Additive.toMul (ιF.hom (Additive.ofMul y)) : (↥L2)ˣ) : ↥L2) : PadicAlgCl q₂) = ((y : ↥LF) : PadicAlgCl q₂) := by
        let φρ : ↥(NumberField.PlaceDecomp.decomp E K wK) →* ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))) := eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))
        let fι : (↥LF)ˣ →* (↥L2)ˣ := Units.map (IntermediateField.inclusion hLFL2).toRingHom.toMonoidHom
        have hmk : ∀ h : ↥(NumberField.PlaceDecomp.decomp E K wK), (QuotientGroup.mk h : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) = eρ (φρ h) := fun h => by
          show QuotientGroup.mk h = eρ (eρ.symm (QuotientGroup.mk' (ρ.ker) h))
          rw [MulEquiv.apply_symm_apply]
          rfl
        have hfι : ∀ (h : ↥(NumberField.PlaceDecomp.decomp E K wK)) (y : (↥LF)ˣ), fι (φρ h • y) = h • fι y := by
          intro h y
          apply Units.ext
          apply Subtype.ext
          rw [hΦ22 h (fι y)]
          show (((φρ h • y : (↥LF)ˣ) : ↥LF) : PadicAlgCl q₂) =
            ((h • (⟨((y : ↥LF) : PadicAlgCl q₂), hLFL2 (y : ↥LF).2⟩ : ↥L2) : ↥L2) : PadicAlgCl q₂)
          rw [hΦF2 (φρ h) y]
          exact he (φρ h) h (hmk h) (y : ↥LF)
        refine ⟨Rep.ofHom ⟨(MonoidHom.toAdditive fι).toIntLinearMap, fun h => LinearMap.ext fun z => ?_⟩, fun y => rfl⟩
        change Additive.ofMul (fι (φρ h • (Additive.toMul z : (↥LF)ˣ))) = Additive.ofMul (h • fι (Additive.toMul z : (↥LF)ˣ))
        rw [hfι]
      have hINF : (groupCohomology.map (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) ιF 2).hom uF = Nat.card (ρ.ker) • u2 :=
        ExtCitation.LocalLevel.map_eq_natCard_smul_of_isLocalFundamentalClass q₂ L2 (↥(NumberField.PlaceDecomp.decomp E K wK)) hΦ21 hΦ22 hsolvH K₀F hbase2
          LF hLFL2 (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) hΦF2 (ρ.ker) eρ hL he uF huF u2 hu2 ιF hιF

      let tH : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker := eρ t
      have het : ∀ c : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker, c ∈ Subgroup.zpowers tH := fun c => by
        obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hkgen (eρ.symm c))
        exact Subgroup.mem_zpowers_iff.mpr ⟨z, by rw [← map_zpow, hz, MulEquiv.apply_symm_apply]⟩
      have hetfin : IsOfFinOrder tH := isOfFinOrder_of_finite tH
      let b2 : (↥L2)ˣ := Units.map (IntermediateField.inclusion hLFL2).toRingHom.toMonoidHom (Units.map ΦF.toRingHom.toMonoidHom aw)
      have hb2fix : ∀ n ∈ ρ.ker, n • b2 = b2 := by
        intro n hn
        have hmk1 : (QuotientGroup.mk n : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) = eρ 1 := by
          rw [map_one, QuotientGroup.eq_one_iff]
          exact hn
        have key := he 1 n hmk1 ((Units.map ΦF.toRingHom.toMonoidHom aw : (↥LF)ˣ) : ↥LF)
        rw [one_smul] at key
        apply Units.ext
        apply Subtype.ext
        rw [hΦ22 n b2]
        exact key.symm
      have hb2inv : (Additive.ofMul b2 : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)) ∈ Representation.invariants (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).ρ.comp (ρ.ker).subtype) :=
        fun n => congrArg Additive.ofMul (hb2fix n.1 n.2)
      let aq : ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker) := ⟨Additive.ofMul b2, hb2inv⟩
      have hca : carryFun tH het hetfin aq ∈ cocycles₂ (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker)) := by

        have htaw : t • (aw : ((wK.under (𝓞 F)).adicCompletion F)) = (aw : ((wK.under (𝓞 F)).adicCompletion F)) := by
          show t • (algebraMap F ((wK.under (𝓞 F)).adicCompletion F) (algebraMap E F (a : E))) = algebraMap F ((wK.under (𝓞 F)).adicCompletion F) (algebraMap E F (a : E))
          rw [NumberField.PlaceDecomp.smul_def]
          erw [NumberField.PlaceDecomp.actRingEquiv_coe t]
          show (algebraMap F ((wK.under (𝓞 F)).adicCompletion F)) ((t : F ≃ₐ[E] F) (algebraMap E F (a : E))) = _
          rw [AlgEquiv.commutes]
        obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk_surjective tH
        have hb2h₀ : h₀ • b2 = b2 := by
          have key := he t h₀ hh₀ ((Units.map ΦF.toRingHom.toMonoidHom aw : (↥LF)ˣ) : ↥LF)
          have hty : t • ((Units.map ΦF.toRingHom.toMonoidHom aw : (↥LF)ˣ) : ↥LF) = ((Units.map ΦF.toRingHom.toMonoidHom aw : (↥LF)ˣ) : ↥LF) := by
            show t • ΦF (aw : ((wK.under (𝓞 F)).adicCompletion F)) = ΦF (aw : ((wK.under (𝓞 F)).adicCompletion F))
            rw [← hΦF3 t, htaw]
          rw [hty] at key
          apply Units.ext
          apply Subtype.ext
          rw [hΦ22 h₀ b2]
          exact key.symm
        refine groupCohomology.carryFun_mem_cocycles2 (A := ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker)) tH het hetfin aq ?_
        rw [← hh₀]
        apply Subtype.ext
        change ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).ρ h₀ (Additive.ofMul b2) = Additive.ofMul b2
        rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
        exact congrArg Additive.ofMul hb2h₀
      have hwKv : wK.under (𝓞 E) = v := by
        apply HeightOneSpectrum.ext
        rw [← hw]
        show wK.asIdeal.under (𝓞 E) = (wK.asIdeal.under (𝓞 F)).under (𝓞 E)
        rw [Ideal.under_under]
      have hb2 : ((b2 : ↥L2) : PadicAlgCl q₂) = ((Φ2 (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E K (⟨wK, hwKv⟩ : v.Extension (𝓞 K)) ((Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a : (v.adicCompletion E)ˣ) : v.adicCompletion E)) : ↥L2) : PadicAlgCl q₂) := by
        have h1 : ((b2 : ↥L2) : PadicAlgCl q₂) = ((ΦF (aw : (wK.under (𝓞 F)).adicCompletion F) : ↥LF) : PadicAlgCl q₂) := rfl
        rw [h1, ← hΦcomp]
        congr 2
        have h2 : (aw : (wK.under (𝓞 F)).adicCompletion F) =
            ((WithVal.equiv ((wK.under (𝓞 F)).valuation F)).symm (algebraMap E F (a : E)) : (wK.under (𝓞 F)).adicCompletion F) := rfl
        have h3 : ((Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
            ((WithVal.equiv (v.valuation E)).symm (a : E) : v.adicCompletion E) := rfl
        rw [h2, h3, IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe,
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
        show ((algebraMap F K (algebraMap E F (a : E)) : K) : wK.adicCompletion K) = ((algebraMap E K (a : E) : K) : wK.adicCompletion K)
        rw [← IsScalarTower.algebraMap_apply E F K (a : E)]

      let a_v : (v.adicCompletion E)ˣ := Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a
      let fE := M4aHerbrand.ArtInv.localArtinHom E K 𝔣K hadmK rK hrK₁ hrK₂ hrK₃ hrK₄ v wK hwKv
      have hfE : ∀ z : (v.adicCompletion E)ˣ, ((fE z : ↥(NumberField.PlaceDecomp.decomp E K wK)) : K ≃ₐ[E] K) = rK (M4aHerbrand.ArtInv.singleIdele E v z) :=
        M4aHerbrand.ArtInv.coe_localArtinHom_apply E K 𝔣K hadmK rK hrK₁ hrK₂ hrK₃ hrK₄ v wK hwKv

      have D45c : ∃ m : ℕ, (QuotientGroup.mk (fE a_v) : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) = tH ^ m ∧
          ((infNatTrans ℤ (ρ.ker) 2).app (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).hom
            ((H2π (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker))).hom ⟨carryFun tH het hetfin aq, hca⟩) =
          (m * Nat.card (ρ.ker)) • u2 := by
        exact M4aHerbrand.exists_mk_localArtin_eq_pow_and_infNatTrans_carryFun_eq_smul_of_enlargedLayer E F F' K hKgen v wK hwKv
          ρ hρres ρ' hρ'surj hρ'res hρ'ker hρ'lift he' hdvd' q₂ L2 Φ2 hΦ21 hΦ22 hΦ23 K₀F hbase2 u2 hu2 𝔣K hadmK rK hrK₁ hrK₂ hrK₃ hrK₄
          (M4aHerbrand.ArtInv.singleIdele E v) M4aHerbrand.ArtInv.singleIdele_mem_idelesTrivialOn
          M4aHerbrand.ArtInv.finPart_singleIdele_self fE hfE tH het hetfin a_v b2 hb2 hb2inv hca
      obtain ⟨m, hmk, hPROP6⟩ := D45c

      have hρfE : ρ (fE a_v) = t ^ m := by
        have h1 : eρ.symm (QuotientGroup.mk (fE a_v)) = ρ (fE a_v) := rfl
        rw [← h1, hmk, map_pow]
        show (eρ.symm (eρ t)) ^ m = t ^ m
        rw [MulEquiv.symm_apply_apply]
      have hrx : r x = (s ^ k) ^ m := by
        have hxeq : x = M4aHerbrand.ArtInv.singleIdele E v a_v := M4aHerbrand.ArtInv.eq_singleIdele_of_pins hx hxv
        have h2 : ((fE a_v : ↥(NumberField.PlaceDecomp.decomp E K wK)) : K ≃ₐ[E] K) = rK x := by rw [hfE, ← hxeq]
        rw [← hcompat x, ← h2, ← hρres, hρfE]
        rfl
      refine ⟨m, hrx, ?_⟩

      let ΦFM' : ((wK.under (𝓞 F)).adicCompletion F)ˣ →* (↥LF)ˣ := Units.map ΦF.toRingHom.toMonoidHom
      have hΦFM' : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (y : ((wK.under (𝓞 F)).adicCompletion F)ˣ), ΦFM' (g • y) = g • ΦFM' y := by
        intro g y
        apply Units.ext
        rw [hΦF2 g (ΦFM' y)]
        show ΦF ((g • y : ((wK.under (𝓞 F)).adicCompletion F)ˣ) : ((wK.under (𝓞 F)).adicCompletion F)) = g • ΦF (y : ((wK.under (𝓞 F)).adicCompletion F))
        rw [NumberField.PlaceDecomp.coe_smul_units, hΦF3 g]
      let θF' := M4aHerbrand.repHomOfMulEquivariant ΦFM' hΦFM'
      have hθFθF' : θF ≫ θF' = 𝟙 _ := by
        refine Rep.hom_ext ?_
        ext z
        rw [Rep.hom_comp, Rep.hom_id]
        show θF'.hom (θF.hom z) = z
        rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
        refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
        apply Units.ext
        show ΦF ((Additive.toMul (θF.hom z) : ((wK.under (𝓞 F)).adicCompletion F)ˣ) : ((wK.under (𝓞 F)).adicCompletion F)) = ((Additive.toMul z : (↥LF)ˣ) : ↥LF)
        have hz : ((Additive.toMul (θF.hom z) : ((wK.under (𝓞 F)).adicCompletion F)ˣ) : ((wK.under (𝓞 F)).adicCompletion F)) = ΦF.symm ((Additive.toMul z : (↥LF)ˣ) : ↥LF) := hθF (Additive.toMul z)
        rw [hz]
        exact ΦF.apply_symm_apply _
      have hback : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ),
          (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θF' 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θF 2).hom y) = y := by
        intro y
        have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θF θF' 2)
        simp only [hθFθF', groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at hc'
        exact hc'.symm

      have hTY : (groupCohomology.map (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) ιF 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θF' 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θ 2).hom u')) =
          Nat.card (ρ.ker) • u2 := by
        rw [hTR, hback, hINF]

      have htaw : t • (aw : ((wK.under (𝓞 F)).adicCompletion F)) = (aw : ((wK.under (𝓞 F)).adicCompletion F)) := by
        show t • (algebraMap F ((wK.under (𝓞 F)).adicCompletion F) (algebraMap E F (a : E))) = algebraMap F ((wK.under (𝓞 F)).adicCompletion F) (algebraMap E F (a : E))
        rw [NumberField.PlaceDecomp.smul_def]
        erw [NumberField.PlaceDecomp.actRingEquiv_coe t]
        show (algebraMap F ((wK.under (𝓞 F)).adicCompletion F)) ((t : F ≃ₐ[E] F) (algebraMap E F (a : E))) = _
        rw [AlgEquiv.commutes]
      have haF : ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ)).ρ t (Additive.ofMul aw) = Additive.ofMul aw := by
        rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
        exact congrArg Additive.ofMul (Units.ext (by rw [NumberField.PlaceDecomp.coe_smul_units]; exact htaw))
      let yF : (↥LF)ˣ := Units.map ΦF.toRingHom.toMonoidHom aw
      have hθF'aw : θF'.hom (Additive.ofMul aw) = Additive.ofMul yF := rfl
      have hcy : carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)) t hkgen htfin (Additive.ofMul yF) ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ) := by
        refine groupCohomology.carryFun_mem_cocycles2 (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)) t hkgen htfin (Additive.ofMul yF) ?_
        rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
        refine congrArg Additive.ofMul (Units.ext ?_)
        show ((t • yF : (↥LF)ˣ) : ↥LF) = (yF : ↥LF)
        rw [hΦF2 t yF]
        show t • ΦF (aw : ((wK.under (𝓞 F)).adicCompletion F)) = ΦF (aw : ((wK.under (𝓞 F)).adicCompletion F))
        rw [← hΦF3 t, htaw]
      have hX1 : (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θF' 2).hom ((H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩) =
          (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)) t hkgen htfin (Additive.ofMul yF), hcy⟩ := by
        have key := groupCohomology.map_carry_H2pi_eq_smul_carry (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) Function.injective_id t hkgen htfin 1 t
          (by rw [pow_one]; rfl) hkgen htfin (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ) θF' (Additive.ofMul aw) haF hcw (by rw [hθF'aw]; exact hcy)
        rw [key, Nat.gcd_one_right, Nat.div_one, one_smul]
        rfl

      have hιinv : ∀ z : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ), (ιF.hom z : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)) ∈ Representation.invariants (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).ρ.comp (ρ.ker).subtype) := by
        intro z n
        have h := Rep.hom_comm_apply ιF (n : ↥(NumberField.PlaceDecomp.decomp E K wK)) z

        have hn1 : (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) (n : ↥(NumberField.PlaceDecomp.decomp E K wK)) = 1 := by
          show eρ.symm (QuotientGroup.mk' (ρ.ker) (n : ↥(NumberField.PlaceDecomp.decomp E K wK))) = 1
          rw [show (QuotientGroup.mk' (ρ.ker) (n : ↥(NumberField.PlaceDecomp.decomp E K wK)) : ↥(NumberField.PlaceDecomp.decomp E K wK) ⧸ ρ.ker) = 1 from (QuotientGroup.eq_one_iff _).mpr n.2, map_one]
        have hsrc : (Rep.res (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)).ρ (n : ↥(NumberField.PlaceDecomp.decomp E K wK)) z = z := by
          show ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)).ρ ((eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) (n : ↥(NumberField.PlaceDecomp.decomp E K wK))) z = z
          rw [hn1, map_one]
          rfl
        rw [hsrc] at h
        exact h.symm
      let φq : Rep.res eρ.symm.toMonoidHom (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ) ⟶ (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker)) :=
        Rep.ofHom ⟨LinearMap.codRestrict _ ιF.hom.toLinearMap hιinv, fun c => by
          obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
          refine LinearMap.ext fun z => Subtype.ext ?_
          exact Rep.hom_comm_apply ιF h z⟩
      have hfac : (Rep.resFunctor (QuotientGroup.mk' (ρ.ker))).map φq ≫ Rep.ofHom (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).ρ.quotientToInvariants_lift (ρ.ker)) = ιF := by
        refine Rep.hom_ext ?_
        ext z
        rfl
      have hιyF : ιF.hom (Additive.ofMul yF) = Additive.ofMul b2 := by
        apply Additive.toMul.injective
        apply Units.ext
        apply Subtype.ext
        exact hιF yF
      have hφaq : φq.hom (Additive.ofMul yF) = aq := Subtype.ext hιyF
      have hzq : carryFun tH het hetfin (φq.hom (Additive.ofMul yF)) ∈ cocycles₂ (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker)) := by
        rw [hφaq]; exact hca
      have hX2 : (groupCohomology.map (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) ιF 2).hom ((H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)) t hkgen htfin (Additive.ofMul yF), hcy⟩) =
          ((infNatTrans ℤ (ρ.ker) 2).app (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).hom
            ((H2π (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker))).hom ⟨carryFun tH het hetfin aq, hca⟩) := by
        have hcomp := groupCohomology.map_comp (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)) eρ.symm.toMonoidHom (QuotientGroup.mk' (ρ.ker)) φq
          (Rep.ofHom (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).ρ.quotientToInvariants_lift (ρ.ker))) 2
        rw [hfac] at hcomp
        have happ := congrArg (fun T => (ModuleCat.Hom.hom T)
          ((H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)) t hkgen htfin (Additive.ofMul yF), hcy⟩)) hcomp
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
        rw [happ, groupCohomology.infNatTrans_app]
        congr 1
        have hyFt : ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ)).ρ t (Additive.ofMul yF) = Additive.ofMul yF := by
          rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
          refine congrArg Additive.ofMul (Units.ext ?_)
          show ((t • yF : (↥LF)ˣ) : ↥LF) = (yF : ↥LF)
          rw [hΦF2 t yF]
          show t • ΦF (aw : ((wK.under (𝓞 F)).adicCompletion F)) = ΦF (aw : ((wK.under (𝓞 F)).adicCompletion F))
          rw [← hΦF3 t, htaw]
        have key := groupCohomology.map_carry_H2pi_eq_smul_carry eρ.symm.toMonoidHom eρ.symm.injective t hkgen htfin 1 tH
          (by rw [pow_one]; exact eρ.symm_apply_apply t) het hetfin (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) (↥LF)ˣ) (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker)) φq (Additive.ofMul yF) hyFt hcy hzq
        have e2 : (⟨carryFun tH het hetfin (φq.hom (Additive.ofMul yF)), hzq⟩ : cocycles₂ (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker))) = ⟨carryFun tH het hetfin aq, hca⟩ :=
          Subtype.ext (congrArg (carryFun tH het hetfin) hφaq)
        rw [key, Nat.gcd_one_right, Nat.div_one, one_smul, e2]
      have hTX : (groupCohomology.map (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) ιF 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θF' 2).hom ((H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩)) =
          ((infNatTrans ℤ (ρ.ker) 2).app (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).hom ((H2π (((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K wK)) (↥L2)ˣ)).quotientToInvariants (ρ.ker))).hom ⟨carryFun tH het hetfin aq, hca⟩) := by
        rw [hX1]
        exact hX2

      have hordu2 : ∀ z : ℤ, z • u2 = 0 → (Nat.card (↥(NumberField.PlaceDecomp.decomp E K wK)) : ℤ) ∣ z := by
        intro z hz
        obtain ⟨-, hcard2, hspan2⟩ :=
          ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
            q₂ L2 (↥(NumberField.PlaceDecomp.decomp E K wK)) hΦ21 hΦ22 hsolvH K₀F hbase2 u2 hu2
        haveI : Fintype (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K wK)) := Fintype.ofFinite _
        have hcT2 := hcard2 ⊤
        haveI : Finite ↥(groupCohomology (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K wK)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ)) 2) :=
          Nat.finite_of_card_ne_zero (by rw [hcT2]; exact Fintype.card_ne_zero)
        haveI : Fintype ↥(groupCohomology (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K wK)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ)) 2) := Fintype.ofFinite _
        set u₀ := (groupCohomology.map (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K wK)).subtype (𝟙 (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E K wK)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K wK) (↥L2)ˣ))) 2).hom u2 with hu₀
        have hgen : ∀ y, y ∈ AddSubgroup.zmultiples u₀ := fun y => by
          have hy : y ∈ Submodule.span ℤ {u₀} := by rw [hspan2 ⊤]; trivial
          obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hy
          exact ⟨k, (int_smul_eq_zsmul _ k u₀).symm.trans hk⟩
        have hord : addOrderOf u₀ = Nat.card ↥(NumberField.PlaceDecomp.decomp E K wK) := by
          rw [addOrderOf_eq_card_of_forall_mem_zmultiples hgen, hcT2, ← Nat.card_eq_fintype_card, Subgroup.card_top]
        have hz0 : z • u₀ = 0 := by
          rw [hu₀, ← map_zsmul, hz, map_zero]
        rw [← hord]
        exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz0
      have hcardH : Nat.card (↥(NumberField.PlaceDecomp.decomp E K wK)) = Nat.card (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) * Nat.card (ρ.ker) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, ← Nat.card_congr eρ.toEquiv]
      have hTX' : (groupCohomology.map (eρ.symm.toMonoidHom.comp (QuotientGroup.mk' (ρ.ker))) ιF 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F))))) θF' 2).hom ((H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (wK.under (𝓞 F)))) ((wK.under (𝓞 F)).adicCompletion F)ˣ)) t hkgen htfin (Additive.ofMul aw), hcw⟩)) =
          (m₀ * (Nat.card (ρ.ker) : ℤ)) • u2 := by
        rw [hX, map_zsmul, map_zsmul, hTY, mul_zsmul, natCast_zsmul]
      have hzero : (((m : ℤ) - m₀) * (Nat.card (ρ.ker) : ℤ)) • u2 = 0 := by
        rw [sub_mul, sub_zsmul, ← hTX', hTX, hPROP6, ← natCast_zsmul, Nat.cast_mul]
        simp
      have hdvdH := hordu2 _ hzero
      rw [hcardH, Nat.cast_mul] at hdvdH
      have hker0 : (Nat.card (ρ.ker) : ℤ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := ρ.ker)).ne'
      exact (mul_dvd_mul_iff_right hker0).mp hdvdH
    obtain ⟨m, hrx, c, hc⟩ := hinv
    refine ⟨m, hrx, ?_⟩
    have hm : (m : ℤ) = m₀ + c * (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) : ℤ) := by linarith [hc]
    rw [hX, hm, add_zsmul, mul_zsmul, hkill, zsmul_zero, add_zero]
  obtain ⟨m, hrx, hcoordm'⟩ := coreI
  have core : ∃ m : ℕ, r x = (s ^ k) ^ m ∧
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype pr 2).hom
          ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom
            ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom
              ⟨carryFun (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) s hs hfin (Additive.ofMul (Units.map (algebraMap E F : E →* F) a)), hc⟩)) =
        (m : ℤ) • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E F w))) θ 2).hom u' := ⟨m, hrx, coreII.trans hcoordm'⟩
  obtain ⟨m, hrx, hcoordm⟩ := core

  refine ⟨(m : ℤ), k * m, hcoordm, by rw [pow_mul]; exact hrx, ?_⟩
  have hD : (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hk0 : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hkcard
      exact (Nat.card_pos (α := F ≃ₐ[E] F)).ne' hkcard.symm
    exact_mod_cast this
  congr 1
  rw [← hkcard]
  push_cast
  exact (mul_div_mul_left (m : ℚ) (Nat.card (↥(NumberField.PlaceDecomp.decomp E F w)) : ℚ) hk0).symm

end S_M4aHerbrand_exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap
end P2MW
export P2MW.S_M4aHerbrand_exists_localCoordinate_carry_eq_zsmul_and_div_natCard_decomp_eq_of_idelicArtinMap (solution)
