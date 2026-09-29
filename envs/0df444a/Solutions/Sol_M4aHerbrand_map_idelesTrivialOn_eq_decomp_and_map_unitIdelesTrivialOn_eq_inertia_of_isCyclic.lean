-- Prove2me | solution 1 for M4aHerbrand.map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c7b31f36-04f9-5015-9398-26b7c97dfb54

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
import Theorems.Thm_M4aHerbrand_exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia_of_isCyclic
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia_of_isCyclic.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp

section EngP1D3
open scoped Pointwise

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff unitIdelesTrivialOn mem_unitIdelesTrivialOn_iff principalIdeles exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq"
namespace ArtInv
p2m_open "M4aHerbrand"

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

end M4aHerbrand.ArtInv

end EngP1D3

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff unitIdelesTrivialOn mem_unitIdelesTrivialOn_iff principalIdeles exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq"
namespace CycOnto
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

end M4aHerbrand.CycOnto

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_finPart_apply idelesTrivialOn mem_idelesTrivialOn_iff unitIdelesTrivialOn mem_unitIdelesTrivialOn_iff principalIdeles exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq"
namespace CycOnto
p2m_open "M4aHerbrand"

attribute [local instance] Ideal.Quotient.field in

theorem natCard_inertia_eq_ramificationIdx
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    Nat.card ↥(w.asIdeal.inertia (F ≃ₐ[E] F)) = Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal := by
  haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : (w.under (𝓞 E)).asIdeal.IsMaximal := (w.under (𝓞 E)).isMaximal
  haveI : Algebra.IsSeparable (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal) (𝓞 F ⧸ w.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 E)).ne_bot,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (w.under (𝓞 E)).asIdeal w.asIdeal (F ≃ₐ[E] F),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := (F ≃ₐ[E] F)) (w.under (𝓞 E)).asIdeal w.asIdeal]

theorem exists_norm_valued_eq_exp_neg_inertiaDeg
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    ∃ a : ((w.under (𝓞 E)).adicCompletion E)ˣ,
      (∃ b : (w.adicCompletion F)ˣ,
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
            (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F)) (a : (w.under (𝓞 E)).adicCompletion E)) ∧
      Valued.v (a : (w.under (𝓞 E)).adicCompletion E) =
        WithZero.exp (-(Ideal.inertiaDeg' (w.under (𝓞 E)).asIdeal w.asIdeal : ℤ)) := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _

  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπ0 : (π : w.adicCompletion F) ≠ 0 := by
    intro h
    have : Valued.v ((π : w.adicCompletion F)) = 0 := by rw [h, map_zero]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at this
    exact WithZero.coe_ne_zero this
  let b : (w.adicCompletion F)ˣ := Units.mk0 _ hπ0
  have hvb : Valued.v (b : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    show Valued.v ((π : w.adicCompletion F)) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]

  set Nb : (w.adicCompletion F)ˣ := ∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b with hNb
  have hNb' : Nb = ∏ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b := finprod_eq_prod_of_fintype _
  have hfix : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w), τ • (Nb : w.adicCompletion F) = (Nb : w.adicCompletion F) := by
    intro τ
    rw [← NumberField.PlaceDecomp.coe_smul_units, hNb', Finset.smul_prod', ]
    congr 1
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  obtain ⟨a, ha⟩ := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E F w (Nb : w.adicCompletion F)).mp hfix

  have hvN : Valued.v (Nb : w.adicCompletion F) = WithZero.exp (-1 : ℤ) ^ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
    rw [hNb', Units.coe_prod, map_prod]
    simp_rw [NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.valued_smul, hvb]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have he0 : Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal ≠ 0 := by
    have h := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg E F w
    intro h0
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := ↥(NumberField.PlaceDecomp.decomp E F w))).ne' h
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact Nb.ne_zero ha.symm
  have hva : Valued.v a = WithZero.exp (-(Ideal.inertiaDeg' (w.under (𝓞 E)).asIdeal w.asIdeal : ℤ)) := by
    have h1 : Valued.v (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
        (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F)) a) = Valued.v a ^ Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal :=
      IsDedekindDomain.HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F)) a
    rw [ha, hvN, NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg E F w,
      mul_comm, pow_mul] at h1

    have hva0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v a = WithZero.exp m := by
      obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hva0
      exact ⟨Multiplicative.toAdd u, by rw [← hu]; rfl⟩
    rw [hm, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul] at h1
    have h3 := WithZero.exp_injective h1
    simp only [smul_eq_mul, nsmul_eq_mul, mul_neg, mul_one] at h3
    have he0' : (Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal : ℤ) ≠ 0 := by exact_mod_cast he0
    rw [hm]
    congr 1
    have h4 : (Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal : ℤ) * m =
        (Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal : ℤ) * (-(Ideal.inertiaDeg' (w.under (𝓞 E)).asIdeal w.asIdeal : ℤ)) := by
      linarith [h3]
    exact mul_left_cancel₀ he0' h4
  exact ⟨Units.mk0 a ha0, ⟨b, ha.symm⟩, hva⟩

end M4aHerbrand.CycOnto

open M4aHerbrand.CycOnto in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)] [IsMulCommutative (F ≃ₐ[E] F)]

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
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance

  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
  obtain ⟨k, hkD, hkgen, hkcard⟩ := exists_pow_index_generates s hs (NumberField.PlaceDecomp.decomp E F w)
  set t : ↥(NumberField.PlaceDecomp.decomp E F w) := ⟨s ^ k, hkD⟩ with ht
  have htfin : IsOfFinOrder t := isOfFinOrder_of_finite t

  obtain ⟨Ψ, hΨcarry, hΨsurj, hΨker, hcardH2⟩ :=
    NumberField.PlaceDecomp.exists_carryClassHom_surjective_ker_eq_norms_adicCompletion E F v w hw t hkgen htfin

  obtain ⟨a₀, x₀, hx₀, hx₀v, hx₀D, hgen₀⟩ :=
    M4aHerbrand.exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw

  have hleD : (idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r ≤ NumberField.PlaceDecomp.decomp E F w := by
    rintro _ ⟨x, hx, rfl⟩
    exact M4aHerbrand.ArtInv.idelicArtinMap_mem_decomp E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v (finPart v x) x hx rfl w hw
  have hD : (idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r = NumberField.PlaceDecomp.decomp E F w := by
    refine le_antisymm hleD fun g hg => ?_
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hgen₀ ⟨g, hg⟩)
    exact ⟨x₀ ^ z, Subgroup.zpow_mem _ hx₀ z, by rw [map_zpow]; exact hz⟩
  refine ⟨hD, ?_⟩

  subst hw
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _

  let fA := M4aHerbrand.ArtInv.localArtinHom E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ (w.under (𝓞 E)) w rfl
  have hfA : ∀ a, ((fA a : ↥(NumberField.PlaceDecomp.decomp E F w)) : (F ≃ₐ[E] F)) = r (M4aHerbrand.ArtInv.singleIdele E _ a) := fun a => rfl
  have hpins : ∀ x, x ∈ idelesTrivialOn (𝓞 E) E ({w.under (𝓞 E)}ᶜ : Set (HeightOneSpectrum (𝓞 E))) →
      x = M4aHerbrand.ArtInv.singleIdele E _ (finPart (w.under (𝓞 E)) x) := fun x hx => M4aHerbrand.ArtInv.eq_singleIdele_of_pins hx rfl

  have hfA_surj : Function.Surjective fA := by
    intro g
    have hg : (g : (F ≃ₐ[E] F)) ∈ (idelesTrivialOn (𝓞 E) E ({w.under (𝓞 E)}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r := by
      rw [hD]; exact g.2
    obtain ⟨x, hx, hgx⟩ := hg
    refine ⟨finPart (w.under (𝓞 E)) x, Subtype.ext ?_⟩
    rw [hfA, ← hpins x hx]
    exact hgx

  have hout_bij : Function.Bijective (fun c : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ (⊥ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w)) => Quotient.out c) := by
    constructor
    · exact fun a b h => Quotient.out_injective h
    · intro σ
      refine ⟨QuotientGroup.mk σ, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (⊥ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w)) σ
      change Quotient.out (QuotientGroup.mk σ : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ (⊥ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w))) = σ
      rw [hh, Subgroup.mem_bot.1 h.2, mul_one]
  have hNle : Ψ.ker ≤ fA.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    obtain ⟨b, hb⟩ := (hΨker a).1 ha
    have key := M4aHerbrand.idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      (w.under (𝓞 E)) a (M4aHerbrand.ArtInv.singleIdele E _ a) (M4aHerbrand.ArtInv.singleIdele_mem_idelesTrivialOn a)
      (M4aHerbrand.ArtInv.finPart_singleIdele_self a) w rfl ⊥ b (fun h hh => by rw [Subgroup.mem_bot.1 hh, one_smul])
      ((congrArg (fun y : (w.adicCompletion F)ˣ => (y : w.adicCompletion F))
        (finprod_eq_of_bijective (fun c => Quotient.out c) hout_bij (fun c => rfl))).trans hb)
    rw [Subgroup.map_bot, Subgroup.mem_bot] at key
    exact Subtype.ext key

  have hcardTop : ∀ (X : Type) [Group X], Nat.card (⊤ : Subgroup X) = Nat.card X := fun X _ => Subgroup.card_top
  have hidxN : Ψ.ker.index = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hΨsurj, hcardTop]
    exact hcardH2
  have hidxK : fA.ker.index = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hfA_surj, hcardTop]
  have hDpos : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := Nat.card_pos
  have hKN : fA.ker = Ψ.ker := by
    refine le_antisymm ?_ hNle
    have h1 := Subgroup.relIndex_mul_index hNle
    rw [hidxK, hidxN] at h1
    have h2 : Ψ.ker.relIndex fA.ker = 1 := by
      have h3 : Ψ.ker.relIndex fA.ker * Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) = 1 * Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by rw [h1, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hDpos h3
    exact Subgroup.relIndex_eq_one.1 h2

  have hv0 : ∀ a : ((w.under (𝓞 E)).adicCompletion E)ˣ, Valued.v (a : ((w.under (𝓞 E)).adicCompletion E)) ≠ 0 := fun a => by
    rw [ne_eq, map_eq_zero]; exact a.ne_zero
  let ord : ((w.under (𝓞 E)).adicCompletion E)ˣ →* Multiplicative ℤ :=
    { toFun := fun a => Multiplicative.ofAdd (-WithZero.log (Valued.v (a : ((w.under (𝓞 E)).adicCompletion E))))
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← ofAdd_add, Units.val_mul, map_mul, WithZero.log_mul (hv0 a) (hv0 b), neg_add] }
  have ord_apply : ∀ a, ord a = Multiplicative.ofAdd (-WithZero.log (Valued.v (a : ((w.under (𝓞 E)).adicCompletion E)))) := fun a => rfl
  have mem_ker_ord : ∀ a, a ∈ ord.ker ↔ Valued.v (a : ((w.under (𝓞 E)).adicCompletion E)) = 1 := by
    intro a
    rw [MonoidHom.mem_ker, ord_apply, ofAdd_eq_one, neg_eq_zero]
    constructor
    · intro h
      have := WithZero.exp_log (hv0 a)
      rw [h, WithZero.exp_zero] at this
      exact this.symm
    · intro h; rw [h, WithZero.log_one]

  have hU : (unitIdelesTrivialOn (𝓞 E) E ({w.under (𝓞 E)}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r =
      ((ord.ker.map fA).map (NumberField.PlaceDecomp.decomp E F w).subtype) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_unitIdelesTrivialOn_iff] at hx
      have hxT : x ∈ idelesTrivialOn (𝓞 E) E ({w.under (𝓞 E)}ᶜ : Set (HeightOneSpectrum (𝓞 E))) := hx.2
      have hunit := hx.1 (w.under (𝓞 E)) (by simp)
      set a := finPart (w.under (𝓞 E)) x with hadef
      have ha : a ∈ ord.ker := by
        rw [mem_ker_ord]
        apply le_antisymm
        · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hunit.1
        · have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hunit.2
          have hinv : (((x⁻¹ : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 (w.under (𝓞 E))) = ((a : ((w.under (𝓞 E)).adicCompletion E)))⁻¹ := by
            rw [hadef, ← coe_finPart_apply, map_inv, Units.val_inv_eq_inv_val]
          rw [hinv, map_inv₀] at h2
          exact (inv_le_one₀ (zero_lt_iff.2 (hv0 a))).1 h2
      refine ⟨fA a, ⟨a, ha, rfl⟩, ?_⟩
      rw [Subgroup.coe_subtype, hfA, ← hpins x hxT]
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨M4aHerbrand.ArtInv.singleIdele E _ a, ?_, (hfA a).symm⟩
      rw [SetLike.mem_coe, mem_ker_ord] at ha
      rw [SetLike.mem_coe, mem_unitIdelesTrivialOn_iff]
      refine ⟨fun w' hw' => ?_, (M4aHerbrand.ArtInv.singleIdele_mem_idelesTrivialOn a).1,
        (M4aHerbrand.ArtInv.singleIdele_mem_idelesTrivialOn a).2⟩
      have hw'' : w' = w.under (𝓞 E) := by simpa using hw'
      subst hw''
      constructor
      · rw [← coe_finPart_apply, M4aHerbrand.ArtInv.finPart_singleIdele_self, HeightOneSpectrum.mem_adicCompletionIntegers, ha]
      · rw [← coe_finPart_apply, map_inv, M4aHerbrand.ArtInv.finPart_singleIdele_self, Units.val_inv_eq_inv_val,
          HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ha, inv_one]

  rw [hU]

  haveI : w.asIdeal.IsPrime := w.isPrime
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (F ≃ₐ[E] F) w.asIdeal
  have hsubI : ((ord.ker.map fA).map (NumberField.PlaceDecomp.decomp E F w).subtype) ≤ w.asIdeal.inertia (F ≃ₐ[E] F) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_ker_ord] at ha
    have h1 := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      (w.under (𝓞 E)) a (M4aHerbrand.ArtInv.singleIdele E _ a) (M4aHerbrand.ArtInv.singleIdele_mem_idelesTrivialOn a)
      (M4aHerbrand.ArtInv.finPart_singleIdele_self a) w rfl φ hφ
    have hord0 : placeOrd E (projFin E (M4aHerbrand.ArtInv.singleIdele E _ a)) (w.under (𝓞 E)) = 0 := by
      rw [placeOrd_eq_zero_iff]
      have : ((projFin E (M4aHerbrand.ArtInv.singleIdele E _ a) : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)
          (w.under (𝓞 E)) = (a : ((w.under (𝓞 E)).adicCompletion E)) :=
        congrArg Units.val (M4aHerbrand.ArtInv.finPart_singleIdele_self (E := E) (v := w.under (𝓞 E)) a)
      rw [this, ha]
    rw [hord0, zpow_zero, inv_one, mul_one] at h1
    rw [Subgroup.coe_subtype, hfA]
    exact h1

  have hcardI := M4aHerbrand.CycOnto.natCard_inertia_eq_ramificationIdx E F w
  have hcardD := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg E F w
  set ee := (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal with heedef
  set ff := (w.under (𝓞 E)).asIdeal.inertiaDeg' w.asIdeal with hffdef
  have heff : 0 < ee * ff := by rw [← hcardD]; exact Nat.card_pos
  have hff : 0 < ff := Nat.pos_of_mul_pos_left heff

  obtain ⟨π, hπ⟩ := (w.under (𝓞 E)).valuation_exists_uniformizer E
  have hπv : Valued.v (π : ((w.under (𝓞 E)).adicCompletion E)) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hπ0 : (π : ((w.under (𝓞 E)).adicCompletion E)) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hπv; exact WithZero.zero_ne_coe hπv
  set ϖ : ((w.under (𝓞 E)).adicCompletion E)ˣ := Units.mk0 _ hπ0 with hϖdef
  have hϖlog : WithZero.log (Valued.v (ϖ : ((w.under (𝓞 E)).adicCompletion E))) = -1 := by
    change WithZero.log (Valued.v (π : ((w.under (𝓞 E)).adicCompletion E))) = -1
    rw [hπv, WithZero.log_exp]
  obtain ⟨a₁, ha₁N, ha₁v⟩ := M4aHerbrand.CycOnto.exists_norm_valued_eq_exp_neg_inertiaDeg E F w
  have ha₁ker : a₁ ∈ Ψ.ker := (hΨker a₁).2 ha₁N
  have ha₁log : WithZero.log (Valued.v (a₁ : ((w.under (𝓞 E)).adicCompletion E))) = -(ff : ℤ) := by rw [ha₁v, WithZero.log_exp]

  haveI hNnormal : (Ψ.ker ⊔ ord.ker).Normal := inferInstance
  have hidxM : (Ψ.ker ⊔ ord.ker).index ≤ ff := by
    have hsurj : Function.Surjective (fun i : Fin ff => (QuotientGroup.mk (ϖ ^ (i : ℕ)) : ((w.under (𝓞 E)).adicCompletion E)ˣ ⧸ (Ψ.ker ⊔ ord.ker))) := by
      intro c
      induction c using QuotientGroup.induction_on with
      | H a =>
        set n : ℤ := -WithZero.log (Valued.v (a : ((w.under (𝓞 E)).adicCompletion E))) with hndef
        set q : ℤ := n / ff with hqdef
        set rm : ℤ := n % ff with hrmdef
        have hrm0 : 0 ≤ rm := Int.emod_nonneg _ (by exact_mod_cast hff.ne')
        have hrmlt : rm < ff := Int.emod_lt_of_pos _ (by exact_mod_cast hff)
        have hnqr : n = ff * q + rm := (Int.mul_ediv_add_emod n ff).symm
        refine ⟨⟨rm.toNat, by omega⟩, ?_⟩

        symm
        rw [QuotientGroup.eq]

        have hzpow : (ϖ ^ (rm.toNat : ℕ) : ((w.under (𝓞 E)).adicCompletion E)ˣ) = ϖ ^ rm := by
          rw [← zpow_natCast, Int.toNat_of_nonneg hrm0]
        rw [show ((⟨rm.toNat, by omega⟩ : Fin ff) : ℕ) = rm.toNat from rfl, hzpow]
        have hu : a⁻¹ * ϖ ^ rm * a₁ ^ q ∈ ord.ker := by
          rw [mem_ker_ord]
          have hval : WithZero.log (Valued.v ((a⁻¹ * ϖ ^ rm * a₁ ^ q : ((w.under (𝓞 E)).adicCompletion E)ˣ) : ((w.under (𝓞 E)).adicCompletion E))) = 0 := by
            rw [Units.val_mul, Units.val_mul, map_mul, map_mul, WithZero.log_mul (mul_ne_zero (hv0 _) (hv0 _)) (hv0 _),
              WithZero.log_mul (hv0 _) (hv0 _), Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv,
              Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, Units.val_zpow_eq_zpow_val, map_zpow₀,
              WithZero.log_zpow, hϖlog, ha₁log, smul_eq_mul, smul_eq_mul]

            have : WithZero.log (Valued.v (a : ((w.under (𝓞 E)).adicCompletion E))) = -n := by rw [hndef, neg_neg]
            rw [this, hnqr]; ring
          have h := WithZero.exp_log (hv0 (a⁻¹ * ϖ ^ rm * a₁ ^ q))
          rw [hval, WithZero.exp_zero] at h
          exact h.symm
        have hmem : a⁻¹ * ϖ ^ rm = (a⁻¹ * ϖ ^ rm * a₁ ^ q) * (a₁ ^ q)⁻¹ := by group
        rw [hmem]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.zpow_mem _ ha₁ker q)))
    haveI : Finite (((w.under (𝓞 E)).adicCompletion E)ˣ ⧸ (Ψ.ker ⊔ ord.ker)) := Finite.of_surjective _ hsurj
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa [Subgroup.index] using this

  have h1 := Subgroup.relIndex_mul_index (le_sup_left : Ψ.ker ≤ Ψ.ker ⊔ ord.ker)
  rw [Subgroup.relIndex_sup_left, hidxN, hcardD] at h1

  have hidxM0 : 0 < (Ψ.ker ⊔ ord.ker).index := by
    rcases Nat.eq_zero_or_pos (Ψ.ker ⊔ ord.ker).index with h0 | h0
    · rw [h0, mul_zero] at h1; exact absurd h1.symm heff.ne'
    · exact h0
  have hrel_ge : ee ≤ Ψ.ker.relIndex ord.ker := by
    have : ee * ff ≤ Ψ.ker.relIndex ord.ker * ff := by
      calc ee * ff = Ψ.ker.relIndex ord.ker * (Ψ.ker ⊔ ord.ker).index := h1.symm
        _ ≤ Ψ.ker.relIndex ord.ker * ff := Nat.mul_le_mul_left _ hidxM
    exact Nat.le_of_mul_le_mul_right this hff
  have hcard_img : Nat.card ((ord.ker.map fA).map (NumberField.PlaceDecomp.decomp E F w).subtype) = Ψ.ker.relIndex ord.ker := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (ord.ker.map fA) (NumberField.PlaceDecomp.decomp E F w).subtype
      (Subgroup.subtype_injective _)).toEquiv, ← Subgroup.relIndex_ker, hKN]

  apply Subgroup.eq_of_le_of_card_ge hsubI
  rw [hcardI, hcard_img]
  exact hrel_ge

end S_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia_of_isCyclic
end P2MW
export P2MW.S_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia_of_isCyclic (solution)
